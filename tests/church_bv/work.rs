//! Counts of the work a process does at four sites, the gate's cost signal: the same on a busy machine as on a quiet one,
//! up to the miner's speculative work (a few ppm; docs/superpowers/specs/2026-10-23-work-counts-design.md).
use std::sync::atomic::{AtomicU64, Ordering::Relaxed};
use std::sync::{Arc, Mutex};

/// The counted sites, in the order of `NAMES`.
#[derive(Clone, Copy)]
pub enum Site {
    Interp,
    Walk,
    Match,
    Op,
}
pub const NAMES: [&str; 4] = ["interp", "walk", "match", "op"];

/// The counter slot of every thread that has counted, until `take` finds its thread gone. A thread writes only its own
/// slot. Slots are read by `take`, not added up when their thread ends: `thread::scope` returns before its threads'
/// thread-local destructors run (50 of 50 tries, 2026-10-23, plan docs/superpowers/plans/2026-10-23-work-counts.md D1).
static SLOTS: Mutex<Vec<Arc<[AtomicU64; 4]>>> = Mutex::new(Vec::new());
thread_local! {
    static SLOT: Arc<[AtomicU64; 4]> = {
        let s: Arc<[AtomicU64; 4]> = Arc::new(Default::default());
        SLOTS.lock().unwrap().push(s.clone());
        s
    };
}

/// One unit of work at `site`, on this thread.
#[inline]
pub fn count(site: Site) {
    count_n(site, 1);
}

/// `n` units of work at `site`, on this thread. A recursive site sums its nodes in a local and adds them once per call:
/// a thread-local add per node cost 7-8% job CPU (`interp` and `match_pat`, run `2026-10-24-work-overhead-1-2`).
#[inline]
pub fn count_n(site: Site, n: u64) {
    let _ = SLOT.try_with(|s| {
        let c = &s[site as usize];
        c.store(c.load(Relaxed) + n, Relaxed);
    });
}

/// The work counted since the last `take`, summed over this process's threads, with every counter set back to 0. Call it
/// only when no other thread is counting (after a task's threads are joined): a count made during the call may be lost.
pub fn take() -> [u64; 4] {
    let mut slots = SLOTS.lock().unwrap();
    let mut out = [0; 4];
    for s in slots.iter() {
        for (o, c) in out.iter_mut().zip(s.iter()) {
            *o += c.swap(0, Relaxed);
        }
    }
    // a slot that only this list holds belongs to a thread that has ended
    slots.retain(|s| Arc::strong_count(s) > 1);
    out
}

/// The `WORK` line of `counts`: `WORK interp=<n> walk=<n> match=<n> op=<n>`.
pub fn line(counts: [u64; 4]) -> String {
    let kv: Vec<String> = NAMES.iter().zip(counts).map(|(n, c)| format!("{n}={c}")).collect();
    format!("WORK {}", kv.join(" "))
}

/// Counts made on threads a `thread::scope` ran reach `take` as soon as the scope returns, and `take` starts the counters
/// again from 0. It runs `probe` in a child process, so no other test's threads count into it.
#[test]
fn take_sees_scoped_threads() {
    let out = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["work::probe", "--exact", "--ignored", "--nocapture"])
        .env("WORK_PROBE", "1")
        .stdin(std::process::Stdio::null())
        .output()
        .unwrap();
    let text = String::from_utf8_lossy(&out.stdout);
    let lines: Vec<&str> = text.lines().filter(|l| l.starts_with("WORK ")).collect();
    assert_eq!(lines, ["WORK interp=9 walk=0 match=9 op=3", "WORK interp=0 walk=0 match=0 op=0"], "{text}");
}

/// `take_sees_scoped_threads`' child: three scoped threads each build `add(x, y)` (1 op), evaluate it (3 nodes) and match
/// it against itself (3 pattern nodes); then two `WORK` lines.
#[test]
#[ignore]
fn probe() {
    if std::env::var_os("WORK_PROBE").is_none() {
        return;
    }
    use crate::rewrite::{matches, Term, ADD};
    std::thread::scope(|s| {
        for _ in 0..3 {
            s.spawn(|| {
                let t = Term::op(ADD, Term::v(0), Term::v(1));
                assert_eq!(t.interp(4, &[1, 2]), 3);
                assert!(matches(&t, &t));
            });
        }
    });
    println!("{}", line(take()));
    println!("{}", line(take()));
}
