//! The `church-bv` binary's subcommands: the entry points that scripts and `tools/runs` start (docs/loop-experiment.md). Each is the
//! body of an `#[ignore]`d test, run by name instead of by libtest arguments; the settings stay in the environment
//! (`Setup::process`). The test exe still runs the same bodies under their old test names.

use std::process::ExitCode;

/// The subcommands and what they run.
const TABLE: [(&str, fn()); 8] = [
    ("sweep", crate::driver::run_sweep),
    ("worker", crate::driver::run_worker),
    ("loop-stream", crate::driver::run_loop_stream),
    ("proof-cost-split", crate::search::run_proof_cost_split),
    ("rule-set-kernel-check", crate::search::run_rule_set_kernel_check),
    ("ctx-fit", crate::ctx_scorer::run_ctx_fit),
    ("overlap-report", crate::ctx_scorer::run_overlap_report),
    ("q1-report", crate::ctx_scorer::run_q1_report),
];

fn lookup(name: &str) -> Option<fn()> {
    TABLE.iter().find(|(n, _)| *n == name).map(|(_, f)| *f)
}

/// Runs `f` on a thread of its own, named `name`, with the check stack, as the worker threads have (a Windows exe's main thread
/// has 1 MiB and this code recurses deeply). `Err` is a panic, already reported by the panic hook.
pub(crate) fn run_on_thread(name: &str, f: impl FnOnce() + Send + 'static) -> Result<(), ()> {
    std::thread::Builder::new()
        .name(name.into())
        .stack_size(tatic_kernel::CHECK_STACK)
        .spawn(f)
        .expect("start the thread")
        .join()
        .map_err(|_| ())
}

/// `church-bv <subcommand>`: 0 when the entry returns, 101 when it panics (as a failed test exits), 2 for no or an unknown subcommand.
pub fn main() -> ExitCode {
    crate::driver::declare_reentry(&["worker"]);
    let arg = std::env::args().nth(1);
    match arg.as_deref().and_then(lookup) {
        Some(f) => match run_on_thread("entry", f) {
            Ok(()) => ExitCode::SUCCESS,
            Err(()) => ExitCode::from(101),
        },
        None => {
            eprintln!("usage: church-bv <subcommand>   (settings are environment variables; see the doc comment of crates/church-bv/src/driver.rs)");
            TABLE.iter().for_each(|(n, _)| eprintln!("  {n}"));
            ExitCode::from(2)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn names_are_unique_and_all_resolve() {
        let names: Vec<&str> = TABLE.iter().map(|(n, _)| *n).collect();
        assert!(names.iter().all(|n| lookup(n).is_some()));
        let mut sorted = names.clone();
        sorted.sort();
        sorted.dedup();
        assert_eq!(sorted.len(), names.len(), "a subcommand is listed twice");
        assert!(lookup("nonsense").is_none());
    }

    #[test]
    fn entries_run_off_the_main_thread_with_room_to_check_in_place() {
        let caller = std::thread::current().id();
        let (tx, rx) = std::sync::mpsc::channel();
        run_on_thread("t", move || tx.send((std::thread::current().id(), tatic_kernel::has_check_room())).unwrap()).unwrap();
        let (id, room) = rx.recv().unwrap();
        assert_ne!(id, caller);
        assert!(room, "a large check would take a segment on this thread");
    }

    #[test]
    fn a_panicking_entry_is_an_error() {
        assert!(run_on_thread("t", || panic!("expected: the entry panics")).is_err());
    }
}
