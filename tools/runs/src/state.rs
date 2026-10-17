//! Machine state for timings (LONG_RUNS.md): the machine's CPU load from `GetSystemTimes`, whether this process holds the
//! "Lock pages in memory" privilege, and Defender's real-time protection.
//! church_bv compiles this same file (`tests/church_bv/machine.rs`, `#[path]`), so it must depend on nothing but std:
//! its Win32 calls are declared here, as `driver.rs`'s `stdio` declares its own.
#![allow(dead_code)] // each of the two crates uses part of it

use std::ffi::c_void;
use std::process::{Command, Stdio};
use std::time::Duration;

#[repr(C)]
#[derive(Default, Clone, Copy)]
struct FileTime {
    low: u32,
    high: u32,
}

impl FileTime {
    fn get(self) -> u64 {
        (self.high as u64) << 32 | self.low as u64
    }
}

/// A privilege's locally unique id.
#[repr(C)]
#[derive(Default, Clone, Copy, PartialEq, Debug)]
pub struct Luid {
    pub low: u32,
    pub high: i32,
}

#[link(name = "kernel32")]
unsafe extern "system" {
    fn GetSystemTimes(idle: *mut FileTime, kernel: *mut FileTime, user: *mut FileTime) -> i32;
    fn GetCurrentProcess() -> *mut c_void;
    fn CloseHandle(handle: *mut c_void) -> i32;
    fn LoadLibraryW(name: *const u16) -> *mut c_void;
    fn GetProcAddress(module: *mut c_void, name: *const u8) -> *mut c_void;
    fn FreeLibrary(module: *mut c_void) -> i32;
}

#[link(name = "advapi32")]
unsafe extern "system" {
    fn OpenProcessToken(process: *mut c_void, access: u32, token: *mut *mut c_void) -> i32;
    fn GetTokenInformation(token: *mut c_void, class: u32, info: *mut c_void, len: u32, returned: *mut u32) -> i32;
    fn LookupPrivilegeValueW(system: *const u16, name: *const u16, luid: *mut Luid) -> i32;
}

const TOKEN_QUERY: u32 = 8;
const TOKEN_PRIVILEGES: u32 = 3;

/// The machine's processor times since boot, summed over all logical processors, in 100 ns units. Kernel time
/// includes idle time.
#[derive(Clone, Copy, Debug)]
pub struct Times {
    pub idle: u64,
    pub kernel: u64,
    pub user: u64,
}

pub fn times() -> Times {
    let (mut idle, mut kernel, mut user) = (FileTime::default(), FileTime::default(), FileTime::default());
    unsafe { GetSystemTimes(&mut idle, &mut kernel, &mut user) };
    Times { idle: idle.get(), kernel: kernel.get(), user: user.get() }
}

impl Times {
    /// Busy processor seconds (kernel + user - idle) and total processor seconds (wall × logical processors) from
    /// `earlier` to `self`.
    pub fn since(&self, earlier: &Times) -> (f64, f64) {
        let total = (self.kernel + self.user).saturating_sub(earlier.kernel + earlier.user);
        let idle = self.idle.saturating_sub(earlier.idle);
        (total.saturating_sub(idle) as f64 / 1e7, total as f64 / 1e7)
    }

    /// The machine's busy percentage from `earlier` to `self`, with no wait.
    pub fn load_since(&self, earlier: &Times) -> f64 {
        let (busy, total) = self.since(earlier);
        if total > 0.0 { 100.0 * busy / total } else { 0.0 }
    }
}

/// The machine's busy percentage over `window`, waited out here.
pub fn cpu_load(window: Duration) -> f64 {
    let a = times();
    std::thread::sleep(window);
    times().load_since(&a)
}

/// Whether a `TOKEN_PRIVILEGES` buffer (a count, then (LUID low, LUID high, attributes) triples of u32) lists `luid`.
pub fn privileges_contain(buf: &[u32], luid: Luid) -> bool {
    let n = buf.first().copied().unwrap_or(0) as usize;
    (0..n).any(|i| buf.get(1 + 3 * i) == Some(&luid.low) && buf.get(2 + 3 * i) == Some(&(luid.high as u32)))
}

/// Whether this process's token holds `SeLockMemoryPrivilege`, enabled or not: what `whoami /priv` listing it meant.
pub fn lockpriv() -> bool {
    let name: Vec<u16> = "SeLockMemoryPrivilege\0".encode_utf16().collect();
    let mut luid = Luid::default();
    if unsafe { LookupPrivilegeValueW(std::ptr::null(), name.as_ptr(), &mut luid) } == 0 {
        return false;
    }
    let mut token = std::ptr::null_mut();
    if unsafe { OpenProcessToken(GetCurrentProcess(), TOKEN_QUERY, &mut token) } == 0 {
        return false;
    }
    let mut buf = vec![0u32; 1024];
    let mut len = 0;
    let ok = unsafe { GetTokenInformation(token, TOKEN_PRIVILEGES, buf.as_mut_ptr().cast(), (buf.len() * 4) as u32, &mut len) };
    unsafe { CloseHandle(token) };
    ok != 0 && privileges_contain(&buf, luid)
}

/// What Defender's `ProductStatus` settles: bit 0, `MP_STATUS_FLAG_SERVICE_UNAVAILABLE`, means the service is not
/// running, so nothing protects in real time. Anything else is left to `Get-MpComputerStatus`.
pub fn rtp_from_status(product_status: u32) -> Option<bool> {
    (product_status & 1 != 0).then_some(false)
}

/// Defender's real-time protection: MpClient.dll's status (milliseconds) when it settles it, else one PowerShell
/// (about 1 s); `None` if both fail.
pub fn rtp() -> Option<bool> {
    mpclient_status().and_then(rtp_from_status).or_else(rtp_powershell)
}

/// `ProductStatus`, the first field `MpManagerStatusQueryEx` writes (probed on this machine, docs/tier-cycle.md,
/// "Survey: workflow time outside the sweep").
fn mpclient_status() -> Option<u32> {
    let dir = std::env::var("ProgramFiles").ok()?;
    let path: Vec<u16> = format!("{dir}\\Windows Defender\\MpClient.dll\0").encode_utf16().collect();
    type Open = unsafe extern "system" fn(u32, *mut *mut c_void) -> i32;
    type Query = unsafe extern "system" fn(*mut c_void, u32, *mut c_void) -> i32;
    type Close = unsafe extern "system" fn(*mut c_void) -> i32;
    unsafe {
        let module = LoadLibraryW(path.as_ptr());
        if module.is_null() {
            return None;
        }
        let open = GetProcAddress(module, c"MpManagerOpen".as_ptr().cast());
        let query = GetProcAddress(module, c"MpManagerStatusQueryEx".as_ptr().cast());
        let close = GetProcAddress(module, c"MpHandleClose".as_ptr().cast());
        let mut status = None;
        if !open.is_null() && !query.is_null() && !close.is_null() {
            use std::mem::transmute;
            let open = transmute::<*mut c_void, Open>(open);
            let query = transmute::<*mut c_void, Query>(query);
            let close = transmute::<*mut c_void, Close>(close);
            let mut handle = std::ptr::null_mut();
            if open(0, &mut handle) >= 0 {
                let mut info = vec![0u32; 2048]; // 8 KB, zeroed: the status structure is smaller
                if query(handle, 0, info.as_mut_ptr().cast()) >= 0 {
                    status = Some(info[0]);
                }
                close(handle);
            }
        }
        FreeLibrary(module);
        status
    }
}

fn rtp_powershell() -> Option<bool> {
    let o = Command::new("powershell")
        .args(["-NoProfile", "-Command", "(Get-MpComputerStatus).RealTimeProtectionEnabled"])
        .stdin(Stdio::null())
        .output()
        .ok()?;
    match String::from_utf8_lossy(&o.stdout).trim() {
        "True" => Some(true),
        "False" => Some(false),
        _ => None,
    }
}

pub fn rtp_text(r: Option<bool>) -> &'static str {
    match r {
        Some(true) => "True",
        Some(false) => "False",
        None => "?",
    }
}

/// `RTP=False CPU=18%`: the machine-wide part of the state, which any process can read. CPU is the load over a 2 s
/// window, the window `Get-Counter` sampled before.
pub fn rtp_cpu() -> String {
    format!("RTP={} CPU={:.0}%", rtp_text(rtp()), cpu_load(Duration::from_secs(2)))
}

/// `RTP=False CPU=18% lockpriv=True`.
pub fn line() -> String {
    format!("{} lockpriv={}", rtp_cpu(), if lockpriv() { "True" } else { "False" })
}
