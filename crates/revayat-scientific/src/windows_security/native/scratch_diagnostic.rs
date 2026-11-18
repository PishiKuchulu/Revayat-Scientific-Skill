//! Synchronous, suspended-only volume comparison. No running-actor or detach authority.
use super::{
    Handle,
    authority::{NativeProfileBinding, SuspendedWorker},
    scratch_access::{self as access, Identity, Owned},
    scratch_disk::ScratchVolume,
    scratch_layout,
    scratch_lease::{self, ReceiptPin},
};
use crate::windows_security::{
    activation::native::require_host,
    scratch::{self, access::NativeRequest, file, policy, volume},
};
use anyhow::{Result, ensure};
use registry_authority::native::NtQueryObject;
use std::{
    cell::Cell,
    error::Error,
    fmt,
    ptr::null_mut,
    time::{Duration, Instant},
};

#[path = "scratch_diagnostic_context.rs"]
mod context;

#[link(name = "ntdll")]
unsafe extern "system" {
    fn NtOpenFile(
        handle: *mut Handle,
        access: u32,
        attributes: *const std::ffi::c_void,
        io: Handle,
        share: u32,
        options: u32,
    ) -> i32;
}
#[link(name = "kernel32")]
unsafe extern "system" {
    fn CreateFileW(
        path: *const u16,
        access: u32,
        share: u32,
        security: *const registry_authority::native::Security,
        creation: u32,
        flags: u32,
        template: Handle,
    ) -> Handle;
    fn GetLastError() -> u32;
    fn SetFileInformationByHandle(
        handle: Handle,
        class: u32,
        data: *const std::ffi::c_void,
        size: u32,
    ) -> i32;
    fn CloseHandle(handle: Handle) -> i32;
}
fn wide(text: &str) -> Vec<u16> {
    text.encode_utf16().chain(Some(0)).collect()
}
#[derive(Debug)]
struct ObservationError(scratch::SharedError);
impl fmt::Display for ObservationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}
impl Error for ObservationError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        Some(self.0.as_ref())
    }
}
fn actual<T>(result: scratch::OperationResult<T>) -> Result<T> {
    result.map_err(|error| anyhow::Error::new(ObservationError(error)))
}
fn modeled<T>(result: Result<T>) -> scratch::OperationResult<T> {
    result.map_err(|error| std::sync::Arc::from(error.into_boxed_dyn_error()))
}
fn all(results: impl IntoIterator<Item = Result<()>>) -> Result<()> {
    let errors = results
        .into_iter()
        .filter_map(Result::err)
        .collect::<Vec<_>>();
    if errors.is_empty() {
        Ok(())
    } else {
        Err(crate::windows_security::activation::Failures { errors }.into())
    }
}

/// Counts only actual short-lived native probe owners, including effective-token handles.
/// Failed closes permanently prevent a diagnostic restoration capability from being minted.
#[derive(Default)]
struct ProbeOwners {
    live: Cell<usize>,
    uncertain: Cell<bool>,
    epoch: Cell<Option<u64>>,
}
impl ProbeOwners {
    fn opened(&self, handle: usize) {
        if scratch::valid_handle(handle) {
            self.live.set(self.live.get() + 1);
        }
    }
    fn close(&self, handle: usize) -> Result<()> {
        if !scratch::valid_handle(handle) {
            return Ok(());
        }
        let result = Owned(handle as Handle).close();
        if result.is_ok() && self.live.get() != 0 {
            self.live.set(self.live.get() - 1);
        } else {
            self.uncertain.set(true);
        }
        result
    }
    fn require_retired(&self) -> Result<()> {
        ensure!(
            !self.uncertain.get() && self.live.get() == 0,
            "scratch diagnostic probe retirement is uncertain"
        );
        Ok(())
    }
}
struct DiagnosticScope {
    epoch: Cell<u64>,
    active: Cell<bool>,
    volume: usize,
    profile: usize,
    worker: usize,
}
impl DiagnosticScope {
    fn new(
        volume: &ScratchVolume,
        profile: &NativeProfileBinding<'_>,
        worker: &SuspendedWorker<'_>,
    ) -> Result<Self> {
        bound(volume, profile, worker)?;
        Ok(Self {
            epoch: Cell::new(0),
            active: Cell::new(false),
            volume: volume as *const _ as usize,
            profile: profile as *const _ as usize,
            worker: worker as *const _ as usize,
        })
    }
    fn require_source(
        &self,
        volume: &ScratchVolume,
        profile: &NativeProfileBinding<'_>,
        worker: &SuspendedWorker<'_>,
    ) -> Result<()> {
        ensure!(
            self.volume == volume as *const _ as usize
                && self.profile == profile as *const _ as usize
                && self.worker == worker as *const _ as usize,
            "scratch diagnostic suspension/profile/volume source differs"
        );
        bound(volume, profile, worker)
    }
    fn start(&self, owners: &ProbeOwners) -> Result<()> {
        ensure!(
            !self.active.get() && owners.epoch.get().is_none(),
            "scratch diagnostic probe already active"
        );
        let epoch = self
            .epoch
            .get()
            .checked_add(1)
            .ok_or_else(|| anyhow::anyhow!("scratch diagnostic epoch exhausted"))?;
        self.epoch.set(epoch);
        owners.epoch.set(Some(epoch));
        self.active.set(true);
        Ok(())
    }
    fn retire<'s>(
        &'s self,
        owners: &ProbeOwners,
        volume: &ScratchVolume,
        profile: &NativeProfileBinding<'_>,
        worker: &SuspendedWorker<'_>,
    ) -> Result<DiagnosticAuthorization<'s>> {
        owners.require_retired()?;
        self.require_source(volume, profile, worker)?;
        ensure!(
            self.active.get() && owners.epoch.get() == Some(self.epoch.get()),
            "scratch diagnostic probe retirement belongs to another generation"
        );
        self.active.set(false);
        Ok(DiagnosticAuthorization {
            scope: self,
            epoch: self.epoch.get(),
        })
    }
}
/// Private, generation-bound proof of synchronous native probe retirement under a live suspension.
/// Neither an actor completion nor a caller-supplied boolean can construct this capability.
struct DiagnosticAuthorization<'s> {
    scope: &'s DiagnosticScope,
    epoch: u64,
}
impl DiagnosticAuthorization<'_> {
    fn require(
        &self,
        scope: &DiagnosticScope,
        volume: &ScratchVolume,
        profile: &NativeProfileBinding<'_>,
        worker: &SuspendedWorker<'_>,
    ) -> Result<()> {
        ensure!(
            std::ptr::eq(self.scope, scope)
                && self.epoch == scope.epoch.get()
                && !scope.active.get(),
            "scratch diagnostic retirement belongs to another probe generation"
        );
        scope.require_source(volume, profile, worker)
    }
}
fn bound(
    volume: &ScratchVolume,
    profile: &NativeProfileBinding<'_>,
    worker: &SuspendedWorker<'_>,
) -> Result<()> {
    require_host()?;
    worker.require_profile(profile)?;
    volume.require()?;
    ensure!(
        profile.view().run_id() == volume.intent.run
            && profile.view().state_identity() == volume.intent.state
            && profile.view().package_sid() == volume.intent.package,
        "scratch diagnostic profile/run/volume binding differs"
    );
    Ok(())
}

struct References {
    root: Owned,
    temp: Owned,
    root_id: Identity,
    temp_id: Identity,
}
impl References {
    fn open(volume: &ScratchVolume) -> Result<Self> {
        let mut root = volume.root.duplicate()?;
        let mut temp = Owned(null_mut());
        let result = (|| {
            temp = Owned::open(format!("{}temp", volume.drive_root()), 0x80, 7, 0x2200000)?;
            let root_id = access::identity(root.0, true)?;
            let temp_id = access::identity(temp.0, true)?;
            ensure!(
                root_id == volume.ready.root_id
                    && temp_id.volume == root_id.volume
                    && access::name(root.0)? == volume.native_root()
                    && access::name(temp.0)? == format!("{}temp", volume.native_root()),
                "scratch diagnostic reference directories differ"
            );
            Ok(Self {
                root: Owned(std::mem::replace(&mut root.0, null_mut())),
                temp: Owned(std::mem::replace(&mut temp.0, null_mut())),
                root_id,
                temp_id,
            })
        })();
        access::combine(result, all([temp.close(), root.close()]))
    }
    fn require_directory(&self, handle: usize, index: usize, volume: &ScratchVolume) -> Result<()> {
        let (reference, identity, name) = if index == 0 {
            (&self.root, self.root_id, volume.native_root().to_owned())
        } else {
            (
                &self.temp,
                self.temp_id,
                format!("{}temp", volume.native_root()),
            )
        };
        ensure!(
            access::identity(reference.0, true)? == identity
                && access::identity_id(handle as Handle)? == identity
                && access::name(handle as Handle)? == name,
            "scratch diagnostic opened directory identity differs"
        );
        Ok(())
    }
    fn close(&mut self) -> Result<()> {
        all([self.temp.close(), self.root.close()])
    }
}

fn open(request: &mut NativeRequest, owners: &ProbeOwners) -> Result<()> {
    actual(request.open(
        |call, output| {
            let status = unsafe {
                NtOpenFile(
                    (&mut output.handle as *mut usize).cast(),
                    call.access,
                    (call.object as *const scratch::access::ObjectAttributes).cast(),
                    (&mut output.io as *mut scratch::access::IoStatus).cast(),
                    call.share,
                    call.options,
                )
            };
            owners.opened(output.handle);
            Ok(status)
        },
        || std::process::abort(),
    ))
}
fn inspect(
    handle: usize,
    desired: u32,
    root: &str,
    evidence: &mut volume::Evidence,
    deadline: &dyn Fn() -> Result<()>,
) -> scratch::OperationResult<u32> {
    volume::inspect(
        handle,
        desired,
        root,
        || modeled(deadline()),
        evidence,
        &mut |handle, kind, data, length| {
            let mut returned = 0;
            let status = unsafe {
                NtQueryObject(
                    handle as Handle,
                    kind as i32,
                    data.as_mut_ptr().cast(),
                    length,
                    &mut returned,
                )
            };
            Ok(volume::QueryResult { status, returned })
        },
    )
}
fn host_volumes(volume: &ScratchVolume, deadline: &dyn Fn() -> Result<()>) -> Result<()> {
    let owners = ProbeOwners::default();
    let mut requests = volume::requests(volume.native_root())?;
    let opened = (|| {
        for request in &mut requests {
            deadline()?;
            require_host()?;
            open(request, &owners)?;
        }
        Ok(())
    })();
    let qualified = actual(volume::qualify(
        &mut requests,
        volume.native_root(),
        true,
        |handle, desired, evidence| {
            inspect(handle, desired, volume.native_root(), evidence, deadline)
        },
        |handle| modeled(owners.close(handle)),
    ))
    .map(|_| ());
    access::combine(access::combine(opened, qualified), owners.require_retired())
}
fn policy_probe(
    volume: &ScratchVolume,
    refs: &References,
    context: &context::Context,
    owners: &ProbeOwners,
    deadline: &dyn Fn() -> Result<()>,
) -> Result<Vec<i32>> {
    let mut dirs = [
        NativeRequest::new(volume.native_root(), "lpac", "device"),
        NativeRequest::new(
            format!("{}temp", volume.native_root()),
            "lpac",
            "temp-absolute",
        ),
    ];
    let mut requests = volume::requests(volume.native_root())?;
    let opened = context.scoped(|| {
        context.check(owners)?;
        for request in dirs.iter_mut().chain(requests.iter_mut()) {
            deadline()?;
            context.check(owners)?;
            open(request, owners)?;
        }
        for (tag, mask) in [("w", 0x00000002u32), ("f", 0xC0030080u32)] {
            let probe_path = wide(&format!("{}t60-{tag}", volume.drive_root()));
            // SAFETY: fixed probe leaf on the diagnostic's own scratch root under the
            // scoped impersonation; a created handle is dispositioned and closed here.
            let handle = unsafe {
                CreateFileW(
                    probe_path.as_ptr(),
                    mask,
                    3,
                    null_mut(),
                    1,
                    0x00200080,
                    null_mut(),
                )
            };
            if handle.is_null() || handle as isize == -1 {
                eprintln!("T60 create {tag} mask=0x{mask:08X} err={}", unsafe {
                    GetLastError()
                });
            } else {
                let mut flag = 1u8;
                unsafe {
                    SetFileInformationByHandle(handle, 4, (&mut flag as *mut u8).cast(), 1);
                    CloseHandle(handle);
                }
                eprintln!("T60 create {tag} mask=0x{mask:08X} ok");
            }
        }
        // T62: worker-identical Win32 root opens plus NT-layer root opens.
        for (tag, mask) in [("w80", 0x00000080u32), ("wgen", 0x00120089u32)] {
            let probe_path = wide(volume.drive_root());
            // SAFETY: fixed diagnostic root path under the scoped impersonation.
            let handle = unsafe {
                CreateFileW(
                    probe_path.as_ptr(),
                    mask,
                    7,
                    null_mut(),
                    3,
                    0x02200000,
                    null_mut(),
                )
            };
            if handle.is_null() || handle as isize == -1 {
                eprintln!("T62 {tag} mask=0x{mask:08X} err={}", unsafe {
                    GetLastError()
                });
            } else {
                unsafe {
                    CloseHandle(handle);
                }
                eprintln!("T62 {tag} mask=0x{mask:08X} ok");
            }
        }
        #[repr(C)]
        struct NtAttributes {
            length: u32,
            root: Handle,
            name: *const NtUnicode,
            attributes: u32,
            descriptor: Handle,
            qos: Handle,
        }
        #[repr(C)]
        struct NtUnicode {
            length: u16,
            maximum: u16,
            buffer: *const u16,
        }
        #[repr(C)]
        #[derive(Default)]
        struct NtIo {
            status: i32,
            pad: u32,
            information: u64,
        }
        let nt_root = volume
            .native_root()
            .strip_suffix('\\')
            .unwrap_or(volume.native_root());
        let nt_text = wide(nt_root);
        let nt_unicode = NtUnicode {
            length: ((nt_text.len() - 1) * 2) as u16,
            maximum: (nt_text.len() * 2) as u16,
            buffer: nt_text.as_ptr(),
        };
        let nt_attributes = NtAttributes {
            length: std::mem::size_of::<NtAttributes>() as u32,
            root: null_mut(),
            name: &nt_unicode,
            attributes: 0x40,
            descriptor: null_mut(),
            qos: null_mut(),
        };
        for (tag, mask) in [
            ("nt1", 0x00000001u32),
            ("nt2", 0x00000002u32),
            ("nt20", 0x00100020u32),
        ] {
            let mut handle: Handle = null_mut();
            let mut io = NtIo::default();
            // SAFETY: fixed native root path and exact 48-byte attributes layout,
            // opened under the scoped impersonation; a returned handle is closed here.
            let status = unsafe {
                NtOpenFile(
                    &mut handle,
                    mask,
                    (&nt_attributes as *const NtAttributes).cast(),
                    (&mut io as *mut NtIo).cast(),
                    7,
                    0x200021,
                )
            };
            if status == 0 {
                unsafe {
                    CloseHandle(handle);
                }
                eprintln!("T62 {tag} mask=0x{mask:08X} ok");
            } else {
                eprintln!("T62 {tag} mask=0x{mask:08X} status=0x{status:08X}");
            }
        }
        // T61: distinguish a directory access-check denial from create semantics.
        for (tag, mask, creation, flags) in [
            ("open_write", 0x00000002u32, 3u32, 0x02200000u32),
            ("open_read", 0x00000001u32, 3u32, 0x02200000u32),
            ("open_trav", 0x00100020u32, 3u32, 0x02200000u32),
            ("create_temp", 0x00000002u32, 1u32, 0x00200000u32),
        ] {
            let probe_path = if tag == "create_temp" {
                wide(&format!("{}temp\\t61-leaf", volume.drive_root()))
            } else {
                wide(volume.drive_root())
            };
            // SAFETY: fixed diagnostic paths under the scoped impersonation; any
            // created leaf is dispositioned and every handle closed before returning.
            let handle = unsafe {
                CreateFileW(
                    probe_path.as_ptr(),
                    mask,
                    3,
                    null_mut(),
                    creation,
                    flags,
                    null_mut(),
                )
            };
            if handle.is_null() || handle as isize == -1 {
                eprintln!("T61 {tag} mask=0x{mask:08X} err={}", unsafe {
                    GetLastError()
                });
            } else {
                if creation == 1 {
                    let mut flag = 1u8;
                    unsafe {
                        SetFileInformationByHandle(handle, 4, (&mut flag as *mut u8).cast(), 1);
                    }
                }
                unsafe {
                    CloseHandle(handle);
                }
                eprintln!("T61 {tag} mask=0x{mask:08X} ok");
            }
        }
        context.check(owners)?;
        deadline()
    });
    // All data-bearing probes are inspected and retired as host, including partial-open failures.
    let qualified = actual(volume::qualify(
        &mut requests,
        volume.native_root(),
        false,
        |handle, desired, evidence| {
            inspect(handle, desired, volume.native_root(), evidence, deadline)
        },
        |handle| modeled(owners.close(handle)),
    ));
    let mut cleanup = Vec::new();
    for (index, request) in dirs.iter_mut().enumerate() {
        cleanup.push(actual(request.release(
            |handle| modeled(refs.require_directory(handle, index, volume)),
            |handle| modeled(owners.close(handle)),
        )));
    }
    let dir_statuses = [dirs[0].returned, dirs[1].returned];
    cleanup.push(all(dirs.iter().chain(requests.iter()).map(|request| {
        ensure!(
            !request.has_storage() && !request.pending,
            "scratch diagnostic native storage remained live"
        );
        Ok(())
    })));
    let values =
        qualified.and_then(|values| volume::combine(dir_statuses[0], dir_statuses[1], &values));
    let values = match (opened, values) {
        (Ok(()), values) => values,
        (Err(primary), values) => access::combine(Err(primary), values.map(|_| ())),
    };
    access::combine(values, all(cleanup))
}

fn probe<'s>(
    scope: &'s DiagnosticScope,
    volume: &ScratchVolume,
    refs: &References,
    context: &context::Context,
    profile: &NativeProfileBinding<'_>,
    worker: &SuspendedWorker<'_>,
    deadline: &dyn Fn() -> Result<()>,
) -> (Result<Vec<i32>>, Option<DiagnosticAuthorization<'s>>) {
    let owners = ProbeOwners::default();
    let result = (|| {
        scope.start(&owners)?;
        deadline()?;
        bound(volume, profile, worker)?;
        let policy = policy_probe(volume, refs, context, &owners, deadline)?;
        let errors = context::file_creations(volume, refs, context, &owners, deadline)?;
        file::file_policy_result(&policy, &errors)
    })();
    // The deadline cannot suppress actual retirement or restoration after a completed probe.
    match scope.retire(&owners, volume, profile, worker) {
        Ok(auth) => (result, Some(auth)),
        Err(error) => (access::combine(result, Err(error)), None),
    }
}

struct DiagnosticLease {
    handle: Owned,
    receipt: policy::VolumeReceipt,
    bytes: Option<Vec<u8>>,
    pin: Option<ReceiptPin>,
    possible: bool,
}
impl DiagnosticLease {
    fn begin(volume: &ScratchVolume) -> Result<Self> {
        scratch_lease::no_conflicts(&volume.state, &volume.intent.host)?;
        let mut handle = Owned::open(
            volume.ready.mount.binding.volume.trim_end_matches('\\'),
            0x60000,
            3,
            0,
        )?;
        let result = (|| {
            let before = scratch_lease::read(handle.0)?;
            let after = policy::volume_trial(&before, volume.package_sid())?;
            let receipt = policy::VolumeReceipt {
                run: volume.intent.run.clone(),
                package: volume.intent.package.clone(),
                supported: false,
                root: volume.drive_root().into(),
                disk: volume.ready.mount.binding.disk,
                partition: volume.ready.mount.binding.partition,
                image: scratch::FileIdentity {
                    volume: volume.created.image.volume,
                    high: volume.created.image.high,
                    low: volume.created.image.low,
                },
                before,
                after,
            };
            Ok(Self {
                handle: Owned(std::mem::replace(&mut handle.0, null_mut())),
                receipt,
                bytes: None,
                pin: None,
                possible: false,
            })
        })();
        access::combine(result, handle.close())
    }
    fn require_volume(&self, volume: &ScratchVolume) -> Result<()> {
        let number = scratch_layout::number(self.handle.0)?;
        ensure!(
            number.DeviceType == 7
                && number.DeviceNumber == self.receipt.disk
                && number.PartitionNumber == self.receipt.partition
                && self.receipt.partition != 0,
            "scratch diagnostic volume handle binding differs"
        );
        ensure!(
            self.receipt.run == volume.intent.run
                && self.receipt.package == volume.intent.package
                && self.receipt.image.volume == volume.created.image.volume
                && self.receipt.image.high == volume.created.image.high
                && self.receipt.image.low == volume.created.image.low,
            "scratch diagnostic retained image binding differs"
        );
        Ok(())
    }
    fn install(
        &mut self,
        auth: &DiagnosticAuthorization<'_>,
        scope: &DiagnosticScope,
        volume: &ScratchVolume,
        profile: &NativeProfileBinding<'_>,
        worker: &SuspendedWorker<'_>,
    ) -> Result<()> {
        auth.require(scope, volume, profile, worker)?;
        ensure!(
            !self.possible && self.bytes.is_none(),
            "scratch diagnostic install already attempted"
        );
        self.require_volume(volume)?;
        let bytes = self.receipt.encode()?.into_bytes();
        access::write_record(
            &volume.state,
            &volume.intent.host,
            policy::receipt_name(false),
            &bytes,
        )?;
        self.bytes = Some(bytes);
        self.pin = Some(ReceiptPin::open(
            &volume.state,
            &volume.intent.host,
            policy::receipt_name(false),
            self.bytes.as_ref().unwrap(),
        )?);
        self.require_receipt(volume)?;
        scratch_lease::same(&scratch_lease::read(self.handle.0)?, &self.receipt.before)?;
        self.possible = true; // The durable intent and exact object pin precede even a failed NtSet.
        scratch_lease::write(self.handle.0, &self.receipt.after)?;
        scratch_lease::same(&scratch_lease::read(self.handle.0)?, &self.receipt.after)
    }
    fn require_receipt(&self, volume: &ScratchVolume) -> Result<()> {
        let bytes = self
            .bytes
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("scratch diagnostic receipt bytes absent"))?;
        self.pin
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("scratch diagnostic receipt object unqualified"))?
            .require(
                &volume.state,
                &volume.intent.host,
                policy::receipt_name(false),
                bytes,
            )
    }
    fn restore(
        &mut self,
        auth: Option<&DiagnosticAuthorization<'_>>,
        scope: &DiagnosticScope,
        volume: &ScratchVolume,
        profile: &NativeProfileBinding<'_>,
        worker: &SuspendedWorker<'_>,
    ) -> Result<()> {
        if !self.possible {
            return Ok(());
        }
        auth.ok_or_else(|| anyhow::anyhow!("scratch diagnostic probe retirement is unavailable"))?
            .require(scope, volume, profile, worker)?;
        self.require_volume(volume)?;
        self.require_receipt(volume)?;
        let actual = scratch_lease::read(self.handle.0)?;
        if !crate::windows_security::policy::descriptor_equal(&actual, &self.receipt.before)? {
            scratch_lease::same(&actual, &self.receipt.after)?;
            scratch_lease::write(self.handle.0, &self.receipt.before)?;
        }
        scratch_lease::same(&scratch_lease::read(self.handle.0)?, &self.receipt.before)
    }
    fn close(&mut self) -> Result<()> {
        self.handle.close()
    }
    fn retire_receipt(&mut self, volume: &ScratchVolume) -> Result<()> {
        if let Some(bytes) = &self.bytes {
            self.pin
                .as_mut()
                .ok_or_else(|| anyhow::anyhow!("scratch diagnostic receipt remains unqualified"))?
                .retire(
                    &volume.state,
                    &volume.intent.host,
                    policy::receipt_name(false),
                    bytes,
                )?;
        }
        Ok(())
    }
    fn close_pin(&mut self) -> Result<()> {
        self.pin.as_mut().map_or(Ok(()), ReceiptPin::close)
    }
}

/// Completes all synchronous host probes, descriptor restoration and explicit closes before emitting.
/// A dangerous raw-volume grant is reported and then refused; it never permits the worker to resume.
pub(in crate::windows_security::native) fn compare(
    volume: &ScratchVolume,
    profile: &NativeProfileBinding<'_>,
    worker: &SuspendedWorker<'_>,
    emit: impl FnOnce(&[String]) -> Result<()>,
) -> Result<()> {
    bound(volume, profile, worker)?;
    let scope = DiagnosticScope::new(volume, profile, worker)?;
    let started = Instant::now();
    let deadline = || {
        ensure!(
            started.elapsed() <= Duration::from_secs(10),
            "scratch diagnostic exceeded 10 seconds"
        );
        Ok(())
    };
    let mut refs = References::open(volume)?;
    let mut context = match context::Context::open(
        std::os::windows::io::AsRawHandle::as_raw_handle(&worker.process()),
        &volume.intent.host,
        volume.package_sid(),
    ) {
        Ok(value) => value,
        Err(error) => return access::combine(Err(error), refs.close()),
    };
    let mut lease = match DiagnosticLease::begin(volume) {
        Ok(value) => value,
        Err(error) => return access::combine(Err(error), all([context.close(), refs.close()])),
    };
    let mut quiet = None;
    let mut results = Vec::with_capacity(3);
    let operation = (|| {
        host_volumes(volume, &deadline)?;
        let (baseline, auth) = probe(&scope, volume, &refs, &context, profile, worker, &deadline);
        quiet = auth;
        let baseline = baseline?;
        ensure!(
            baseline.len() == 49 && baseline[..2] == [volume::DENIED; 2],
            "scratch diagnostic baseline directory denial differs"
        );
        results.push(baseline);
        deadline()?;
        lease.install(
            quiet
                .as_ref()
                .ok_or_else(|| anyhow::anyhow!("scratch diagnostic baseline was not retired"))?,
            &scope,
            volume,
            profile,
            worker,
        )?;
        let (modified, auth) = probe(&scope, volume, &refs, &context, profile, worker, &deadline);
        quiet = auth;
        let modified = modified?;
        deadline()?;
        bound(volume, profile, worker)?;
        ensure!(
            modified.len() == results[0].len()
                && modified[..2]
                    .iter()
                    .all(|status| matches!(*status, 0 | volume::DENIED)),
            "scratch diagnostic modified directory results differ"
        );
        results.push(modified);
        Ok(())
    })();
    // Probe failure cannot skip restoration. A failed retirement cannot manufacture its authority.
    let mut result = access::combine(
        operation,
        lease.restore(quiet.as_ref(), &scope, volume, profile, worker),
    );
    if result.is_ok() {
        let (restored, auth) = probe(&scope, volume, &refs, &context, profile, worker, &deadline);
        quiet = auth;
        result = restored.and_then(|restored| {
            ensure!(
                restored == results[0],
                "scratch diagnostic full restored vector differs from baseline"
            );
            results.push(restored);
            Ok(())
        });
    }
    let restoration = lease.restore(quiet.as_ref(), &scope, volume, profile, worker);
    let frames = context.finish_frames();
    let closed = all([lease.close(), context.close(), refs.close()]);
    let safe_cleanup = restoration.is_ok() && closed.is_ok();
    result = access::combine(result, all([restoration, closed]));
    result = access::combine(
        result,
        if safe_cleanup {
            lease.retire_receipt(volume)
        } else {
            lease.close_pin()
        },
    );
    result?;
    deadline()?;
    bound(volume, profile, worker)?;
    let mut frames = frames?;
    let mut rejected = false;
    for (phase, values) in ["baseline", "modified", "restored"]
        .into_iter()
        .zip(&results)
    {
        for (index, object) in ["root", "temp"].into_iter().enumerate() {
            frames.push(format!("WINDOWS_SCRATCH_POLICY phase={phase} object={object} ntstatus=0x{:08X} descriptor_restored=True handles_closed=True cause_claimed=False admission=False", values[index] as u32));
        }
        frames.extend(file::file_policy_frames(phase, values)?);
        rejected |= file::reject_file_policy(values)?;
    }
    emit(&frames)?;
    ensure!(
        !rejected,
        "scratch diagnostic candidate granted raw-volume data/security access"
    );
    Ok(())
}
