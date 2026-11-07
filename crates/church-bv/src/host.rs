//! The host this process runs on: Defender, CPU load and large pages, recorded with every timing.
use super::*;

/// The machine-state reader shared with `tools/runs` (std only, so the file compiles here as it is).
#[cfg(windows)]
#[path = "../../../tools/runs/src/state.rs"]
pub mod state;

/// Defender's real-time protection and the machine's CPU load over 2 s (`RTP=False CPU=18%`), read natively
/// (`tools/runs/src/state.rs`); "machine state unavailable" off Windows.
pub fn rtp_cpu() -> String {
    #[cfg(windows)]
    return state::rtp_cpu();
    #[cfg(not(windows))]
    return "machine state unavailable".to_string();
}

/// `lockpriv=True pages=large`: whether this process holds the "Lock pages in memory" privilege, and whether it
/// allocates from large OS pages. mimalloc enables the privilege itself when the option is on, so both together mean
/// large pages.
pub fn pages_text() -> String {
    #[cfg(windows)]
    let lock = state::lockpriv();
    #[cfg(not(windows))]
    let lock = false;
    let pages = if large_pages_option() && lock { "large" } else { "normal" };
    format!("lockpriv={} pages={pages}", if lock { "True" } else { "False" })
}

/// One line of machine state to print with every timing (LONG_RUNS.md): `RTP=.. CPU=..% lockpriv=.. pages=..`, in
/// about 2 s (the CPU sample).
pub fn machine_state() -> String {
    format!("{} {}", rtp_cpu(), pages_text())
}

/// mimalloc's `allow_large_os_pages` option in this process: the build's default (`.cargo/config.toml`) unless
/// `MIMALLOC_ALLOW_LARGE_OS_PAGES` overrides it.
pub fn large_pages_option() -> bool {
    unsafe extern "C" {
        fn mi_option_get(option: std::ffi::c_int) -> std::ffi::c_long;
    }
    // `mi_option_allow_large_os_pages` in mimalloc v3's option list
    unsafe { mi_option_get(6) != 0 }
}

/// The build turns large pages on: fails if `.cargo/config.toml`'s define stops reaching mimalloc.
#[test]
#[cfg(all(windows, target_env = "msvc"))]
pub fn mimalloc_defaults_to_large_pages() {
    let job = &Job::new(Setup::process());
    if job.setup().var("MIMALLOC_ALLOW_LARGE_OS_PAGES").is_none() {
        assert!(large_pages_option());
    }
}

/// The process turns mimalloc's purge off (`purge_delay` is option 15 in v3's list, -1 for never; `Setup::process` sets it): fails if
/// that stops. Measured in docs/tier-cycle/ ("P1 timed").
#[test]
#[cfg(all(windows, target_env = "msvc"))]
pub fn mimalloc_defaults_to_no_purge() {
    unsafe extern "C" {
        fn mi_option_get(option: std::ffi::c_int) -> std::ffi::c_long;
    }
    let job = &Job::new(Setup::process());
    if job.setup().var("MIMALLOC_PURGE_DELAY").is_none() {
        assert_eq!(unsafe { mi_option_get(15) }, -1);
    }
}

/// `pages_text` is what the driver appends to its machine-state line.
#[test]
fn pages_text_has_both_fields() {
    let t = pages_text();
    assert!(t.starts_with("lockpriv=True pages=") || t.starts_with("lockpriv=False pages="), "{t}");
    assert!(t.ends_with("pages=large") || t.ends_with("pages=normal"), "{t}");
}

/// Prints the machine state (Defender, CPU load) when created and again when dropped, so a timing run records both ends.
/// `MACHINE_BANNER=0` silences it (each state costs about 2 s): `driver::loop_stream` records the state once per loop instead.
pub struct MachineBanner(&'static str);
impl MachineBanner {
    pub fn start(job: &Job, tag: &'static str) -> Self {
        if !job.setup().flag("MACHINE_BANNER", true) {
            return MachineBanner("");
        }
        println!("{tag} machine at start: {}", machine_state());
        MachineBanner(tag)
    }
}
impl Drop for MachineBanner {
    fn drop(&mut self) {
        if !self.0.is_empty() {
            println!("{} machine at end: {}", self.0, machine_state());
        }
    }
}

/// Prints one machine-state line, for a human: `cargo test --release -p church-bv --lib host::machine_state_line --
/// --exact --ignored --nocapture`. The driver composes its own (`driver::machine_state`).
#[test]
#[ignore]
pub fn machine_state_line() {
    println!("machine state: {}", machine_state());
}

/// The driver's worker task for the part of the state that belongs to the children's process and environment.
#[test]
#[ignore]
pub fn pages_line() {
    pages_line_task(&Setup::process())
}

pub fn pages_line_task(setup: &Arc<Setup>) {
    let pages = pages_text();
    println!("pages: {pages}");
    setup.result("pages", pages);
}
