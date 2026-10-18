//! The mine-and-serve loop and the sweeps over it (formerly `scripts/loop_stream.sh` and local sweep scripts). Serving
//! (`search::rule_set_kernel_check`) and mining (`search::rule_miner`) run as tasks of one worker process of this exe (`worker`,
//! `Worker`): each task gets fresh thread-locals, its own environment and its own log, while the pure memos carry over
//! (`task.rs`). Shell drivers spent much of a loop in Git Bash forks (docs/tier-cycle.md, "Loop overhead").
//! To share the machine, launch at low priority and pinned (children inherit both): cmd //c start "" //b //belownormal //affinity 3 ...
//!
//! **One loop:** `LOOP_MODE=none|ref|loop LOOP_OUT=<dir> [options] <exe> driver::loop_stream --exact --ignored --nocapture`.
//! Batch r is the laws OFFSET+r*B .. OFFSET+(r+1)*B of the family's sequence (residue class SPHASE of stride STRIDE). It is served under
//! the rules in force *before* it is mined, so M is what the stream costs when rules arrive as it does. `ref` mines once on all K
//! batches before serving them; `loop` mines each batch after serving it (not the last, which could not change any M); `none` only
//! serves.
//! Options (env, defaults in brackets): FAMILY [add3] (add3|mix3|sbo3|cmp3|cmp3d|u3|u3w, THREE_VAR_FAMILIES in search.rs), STRIDE [7],
//! SPHASE [0], B [150], K [4], OFFSET [0], THREADS [2] (miner pool), ROUNDS [no cap], DEEP3 [1] (add3 only), SPLIT [2] (0|1 restricts
//! everything to one structure-based half of the laws; RULEMINER_SHAPE_SALT picks another split), WARM_RULES=<file> (start with those
//! rules in force), CHECK_FAST [0] (serve without proof building or kernel checks; M is unchanged), MACHINE_STATE [1] (a machine-state
//! line at start and end, about 2 s each). Other variables pass through to the children: RULEMINER_FAST=1 (exact counts without
//! proving every candidate, docs/tier-cycle.md "Miner speedups"), RULEMINER_SHUFFLE=<salt> (hash-ordered law sequence, so batches and
//! phases are random samples), RULEMINER_STEPS (default 200, serving's budget).
//! Extras (docs/superpowers/specs/2026-10-17-law-generator-design.md): every mine with rule rounds also mines a slice of the law
//! generator's laws (`scope_extras`, a shared 16% slice per loop); off with ABLATE=gen; GEN_SOURCE=stream (the stream control)
//! and GEN_N=matched (n capped at what the filtered stream fits, for a same-n pair) are temporary.
//! The children share the lemma statements they check through LOOP_OUT/lemmas.bin (`LEMMA_CACHE`, `lemma_cache.rs`; deleted when
//! the loop starts and ends; a sweep shares one SWEEP_OUT/lemmas.bin across all its loops instead); LEMMA_RECHECK=1 audits it. The driver computes each child's laws (its window of the family's
//! sequence, built once per family) and passes them as a file, LOOP_OUT/laws_<mine|serve>_<name>.txt (`RULEMINER_LAWFILE`,
//! `CHECK_LAWFILE`).
//! Output in LOOP_OUT: rules.txt (the rules in force at the end, then their learned preferences, `winner  OVER  loser` lines), m.tsv (batch, M, laws, rules in force, serve seconds, laws that used
//! up the rule budget: nonzero means a rewrite cycle or growing rules, laws the join closed with no machine proof, terms the join's
//! searches reached: its cost, which M does not show), mine_<name>.log and serve_<skip>.log. The last line printed is
//! `mode=.. B=.. K=.. offset=.. total_M=.. rules=.. exhausted=.. joined=.. reached=..`.
//!
//! **A sweep** (the experiments of docs/loop-result.md): `SWEEP_OUT=<dir> [SALT=1] [LIB=<dir>] [SWEEP="mines own cold"] <exe>
//! driver::sweep --exact --ignored --nocapture` (`MACHINE_STATE=0` skips its two machine-state lines too). Every stage uses `RULEMINER_FAST=1` and `RULEMINER_SHUFFLE=$SALT`. Stages, in order:
//! - `mines`, optionally `:<family>,..` (default sbo3,add3,mix3,cmp3d; u3 only when named): one ref mine per family on its phase-0
//!   stream (`MINES`) -> `lib_<family>/`, summary rows in `<stage>.tsv` (family, seconds, total M, rules, exhausted, joined, reached).
//! - `own`, `cold`, `cross`, `pooled`, `mixed`, optionally `:<family>,<family>` (default cmp3d,add3,sbo3): loops (`LOOPS` settings) on
//!   phases 1-3, seeded with the family's own library, nothing, each other family's library, the pooled library (cmp3d's, add3's and
//!   sbo3's, `pooled.rules`, plus the preferences and rule drops the family learns on it on its phase-0 stream, `pooled_<family>/`; rows in
//!   `pooled_prefs.tsv` as for mines), or the library mined on u3. Libraries are read from `LIB/lib_<family>/rules.txt`
//!   (default LIB = SWEEP_OUT). One row per loop in `<stage>.tsv` (`:` becomes `_`): family, stride-phase, from_<source>, total M,
//!   per-batch M, rules at the end, seconds, exhausted, joined, reached (as in m.tsv, summed over the batches).

use super::*;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::io::{BufRead, BufReader};

/// The process's stdout and stderr pointed at one file, for a task's log (`worker`): one handle (one fd) for both, so they
/// share the file offset as a child's `try_clone`d handles do. std looks the handle up on every write (checked by a probe,
/// docs/tier-cycle.md, "A persistent worker"), so `println!` follows it.
#[cfg(windows)]
mod stdio {
    use std::ffi::c_void;
    use std::os::windows::io::AsRawHandle;
    unsafe extern "system" {
        fn GetStdHandle(which: u32) -> *mut c_void;
        fn SetStdHandle(which: u32, handle: *mut c_void) -> i32;
    }
    const OUT: u32 = -11i32 as u32;
    const ERR: u32 = -12i32 as u32;
    pub struct Saved([*mut c_void; 2]);
    pub fn redirect(f: &std::fs::File) -> Saved {
        // SAFETY: plain Win32 calls; `f` outlives the redirection (`restore` runs before it drops)
        unsafe {
            let saved = Saved([GetStdHandle(OUT), GetStdHandle(ERR)]);
            SetStdHandle(OUT, f.as_raw_handle());
            SetStdHandle(ERR, f.as_raw_handle());
            saved
        }
    }
    pub fn restore(s: Saved) {
        // SAFETY: the handles `redirect` saved, still open
        unsafe {
            SetStdHandle(OUT, s.0[0]);
            SetStdHandle(ERR, s.0[1]);
        }
    }
}
#[cfg(unix)]
mod stdio {
    use std::os::fd::AsRawFd;
    unsafe extern "C" {
        fn dup(fd: i32) -> i32;
        fn dup2(from: i32, to: i32) -> i32;
        fn close(fd: i32) -> i32;
    }
    pub struct Saved([i32; 2]);
    pub fn redirect(f: &std::fs::File) -> Saved {
        // SAFETY: plain libc calls on fds this process owns
        unsafe {
            let saved = Saved([dup(1), dup(2)]);
            dup2(f.as_raw_fd(), 1);
            dup2(f.as_raw_fd(), 2);
            saved
        }
    }
    pub fn restore(s: Saved) {
        // SAFETY: the fds `redirect` duplicated, closed once here
        unsafe {
            dup2(s.0[0], 1);
            dup2(s.0[1], 2);
            close(s.0[0]);
            close(s.0[1]);
        }
    }
}

/// The tests a worker runs as tasks.
fn task_fn(name: &str) -> Option<fn()> {
    Some(match name {
        "search::rule_miner" => crate::search::rule_miner,
        "search::rule_set_kernel_check" => crate::search::rule_set_kernel_check,
        "machine::pages_line" => crate::machine::pages_line,
        "driver::env_echo" => env_echo,
        _ => return None,
    })
}

/// A sweep's children as tasks of one process (`Worker` starts it, with `TATIC_WORKER=1`; it returns at once otherwise).
/// Reads `<test>\t<log>\t<KEY>=<VALUE>...` lines; runs each test on a fresh thread (fresh thread-locals) with the task's
/// pairs over this process's environment (`task::begin`) and its stdout and stderr in the log; answers `WORKER ok` or
/// `WORKER fail` on a line of its own, and exits after a failure (a panic can leave a lock poisoned) or at EOF. A task that
/// starts a process must give it a null stdin, as `Command::output` does: this stdin is the task pipe.
#[test]
#[ignore]
fn worker() {
    if std::env::var_os("TATIC_WORKER").is_none() {
        return;
    }
    for line in std::io::stdin().lines() {
        let line = line.expect("the task pipe");
        let mut fields = line.split('\t');
        let (name, log) = (fields.next().unwrap_or("").to_string(), fields.next().unwrap_or("").to_string());
        let env = fields.filter_map(|f| f.split_once('=')).map(|(k, v)| (k.to_string(), v.to_string())).collect();
        crate::task::begin(env);
        let ok = match std::fs::File::create(&log) {
            Ok(f) => {
                std::io::stdout().flush().unwrap();
                let saved = stdio::redirect(&f);
                let ok = match task_fn(&name) {
                    Some(run) => std::thread::Builder::new().name(name.clone()).spawn(run).unwrap().join().is_ok(),
                    None => {
                        eprintln!("worker: no task {name}");
                        false
                    }
                };
                std::io::stdout().flush().unwrap();
                stdio::restore(saved);
                ok
            }
            Err(e) => {
                eprintln!("worker: cannot create {log}: {e}");
                false
            }
        };
        println!("\nWORKER {}", if ok { "ok" } else { "fail" });
        if !ok {
            return;
        }
    }
}

#[derive(Clone, Default)]
struct LoopCfg {
    /// none|ref|loop
    mode: String,
    out: PathBuf,
    family: String,
    stride: usize,
    sphase: usize,
    b: usize,
    k: usize,
    offset: usize,
    threads: usize,
    rounds: usize,
    deep3: usize,
    split: usize,
    warm: Option<PathBuf>,
    check_fast: bool,
    /// the extras list of this loop's scope (`scope_extras`), shared by the scope's loops
    extras: std::sync::Arc<Vec<(Term, Term)>>,
    /// each of this loop's mines' slice of `extras`, in mining order (a ref loop's one mine, or a loop's mines 0, 1, ...)
    extra_at: Vec<std::ops::Range<usize>>,
    /// further variables for the children (a sweep's RULEMINER_FAST and RULEMINER_SHUFFLE)
    env: Vec<(String, String)>,
}

/// Each mine's slice of a scope's filtered extras list of `len` laws, ordered (loop, mine): `loops` loops of `mines` mines,
/// `n` laws each, a loop's mines sharing its one slice (shared slices, spec §3: the default arm s16 is shared, see `GEN_F`);
/// the shortfall if they do not fit.
fn extra_slices(len: usize, loops: usize, mines: usize, n: usize) -> Result<Vec<std::ops::Range<usize>>, usize> {
    if loops * n > len {
        return Err(loops * n - len);
    }
    Ok((0..loops).flat_map(|i| (0..mines).map(move |_| i * n..(i + 1) * n)).collect())
}

/// The filter drops a twin of a served law (here through `sub(y, 0)`, which normalizes to `y`) and a law with a served
/// law's skeleton, and keeps a law trivial after normalizing and an unrelated law, in order.
#[test]
fn filtered_drops_twins_and_skeletons_only() {
    let p = |a: &str, b: &str| (parse_term(a), parse_term(b));
    let served = [p("and(or(x, y), z)", "or(and(x, z), and(y, z))")];
    let twin = p("and(or(x, sub(y, 0)), z)", "or(and(x, z), and(y, z))");
    let skel = p("and(or(x, y), y)", "or(and(x, y), and(y, y))");
    let trivial = p("sub(x, x)", "and(y, 0)");
    let other = p("add(add(x, y), z)", "add(x, add(y, z))");
    // `Term` has no `Debug`, so compare texts
    let text = |(a, b): (Term, Term)| format!("{} = {}", a.show(), b.show());
    let got: Vec<String> = filtered(&[twin, skel, trivial, other], &served, &mut ClassReps::new()).into_iter().map(text).collect();
    assert_eq!(got, [trivial, other].map(text));
}

/// Whether a mine of `cfg` takes extras: it mines (not `none`) with rule rounds, and `ABLATE=gen` is off.
fn takes_extras(cfg: &LoopCfg, ablated: bool) -> bool {
    !ablated && cfg.rounds > 0 && cfg.mode != "none"
}

/// The mines of one loop of `cfg`: a ref loop mines once, a loop after every batch but its last.
fn mines_of(cfg: &LoopCfg) -> usize {
    if cfg.mode == "ref" { 1 } else { cfg.k.saturating_sub(1) }
}

/// A loop's mines share one n-law range, and the loops' ranges are disjoint, in order.
#[test]
fn extra_slices_are_disjoint_and_full() {
    let shared = extra_slices(100, 3, 2, 10).unwrap();
    assert_eq!(shared.len(), 6);
    for l in 0..3 {
        assert_eq!(shared[2 * l], shared[2 * l + 1], "{shared:?}");
        assert_eq!(shared[2 * l].len(), 10);
    }
    assert!(shared[0].end <= shared[2].start && shared[2].end <= shared[4].start, "{shared:?}");
    // a scope with no laws (a family with no pool): n is 0 and the mine takes nothing
    assert_eq!(extra_slices(0, 1, 1, 0), Ok(vec![0..0]));
}

/// The largest n whose slices a list of `len` laws fits (`extra_slices`' inverse): `GEN_N=matched` caps both sources at the
/// stream list's.
fn fit_n(len: usize, loops: usize) -> usize {
    len / loops
}

/// `fit_n` fits and one more does not, including a list too short for one law per loop.
#[test]
fn fit_n_is_the_largest_that_fits() {
    for len in [292, 42, 166, 2, 0] {
        let n = fit_n(len, 3);
        assert!(extra_slices(len, 3, 2, n).is_ok(), "{len}: {n} does not fit");
        assert!(extra_slices(len, 3, 2, n + 1).is_err(), "{len}: {} fits too", n + 1);
    }
}

/// A list shorter than its slices returns the shortfall.
#[test]
fn extra_slices_refuse_a_short_list() {
    assert_eq!(extra_slices(29, 3, 2, 10), Err(1));
    assert!(extra_slices(30, 3, 2, 10).is_ok());
}

/// Extras exist to be mined into rules: a mine with no rule rounds (the pooled stage's preference mines), a loop that only
/// serves, and any mine under `ABLATE=gen` take none; loop mines and ref mines with rounds take them.
#[test]
fn no_extras_without_rounds() {
    let c = |mode: &str, rounds: usize| LoopCfg { mode: mode.into(), rounds, k: 3, ..Default::default() };
    assert!(takes_extras(&c("loop", usize::MAX), false));
    assert!(takes_extras(&c("ref", usize::MAX), false), "a ref mine with rounds");
    assert!(!takes_extras(&c("ref", 0), false), "a mine with no rule rounds");
    assert!(!takes_extras(&c("loop", 0), false), "a mine with no rule rounds");
    assert!(!takes_extras(&c("loop", usize::MAX), true), "ABLATE=gen");
    assert!(!takes_extras(&c("none", usize::MAX), false), "a loop that only serves");
}

impl LoopCfg {
    fn from_env() -> LoopCfg {
        let mode = env_var("LOOP_MODE").expect("set LOOP_MODE=none|ref|loop").to_string();
        assert!(["none", "ref", "loop"].contains(&mode.as_str()), "LOOP_MODE must be none, ref or loop, got {mode}");
        let cfg = LoopCfg {
            mode,
            out: PathBuf::from(env_var("LOOP_OUT").expect("set LOOP_OUT=<dir>")),
            family: env_var("FAMILY").unwrap_or("add3").into(),
            stride: env_or("STRIDE", 7),
            sphase: env_or("SPHASE", 0),
            b: env_or("B", 150),
            k: env_or("K", 4),
            offset: env_or("OFFSET", 0),
            threads: env_or("THREADS", 2),
            rounds: env_or("ROUNDS", usize::MAX),
            deep3: env_or("DEEP3", 1),
            split: env_or("SPLIT", 2),
            warm: env_var("WARM_RULES").map(PathBuf::from),
            check_fast: env_or("CHECK_FAST", 0usize) == 1,
            extras: Default::default(),
            extra_at: vec![],
            env: vec![],
        };
        if takes_extras(&cfg, ablated("gen")) {
            let mut scope = [cfg];
            scope_extras(&mut scope, &[], &mut Draw::new()).unwrap_or_else(|e| panic!("{e}"));
            let [cfg] = scope;
            return cfg;
        }
        cfg
    }
}

struct Summary {
    total: usize,
    /// M per batch
    ms: Vec<usize>,
    rules: usize,
    exhausted: usize,
    /// laws served with no machine proof by the join, and the terms its searches reached (`JOIN_COST`, which M does not show)
    joined: usize,
    reached: usize,
}

/// The child process that runs this driver's children as tasks (`worker`), started at the first task and again after a
/// failed one, or when a task's process-start variables (`process_start`) differ from its. Dropping it closes the worker's
/// stdin and waits for it, so no worker outlives its driver.
struct Worker {
    proc: std::sync::Mutex<Option<WorkerProc>>,
}

struct WorkerProc {
    child: std::process::Child,
    stdin: std::process::ChildStdin,
    stdout: BufReader<std::process::ChildStdout>,
    start: Vec<(String, String)>,
}

/// The pairs of `env` read when a process starts (mimalloc's options, std's `RUST_MIN_STACK` and `RUST_BACKTRACE`), the last
/// of each name winning: a worker serves only tasks that agree on them.
fn process_start(env: &[(String, String)]) -> Vec<(String, String)> {
    let start: std::collections::BTreeMap<&str, &str> =
        env.iter().filter(|(k, _)| k.starts_with("MIMALLOC_") || k.starts_with("RUST_")).map(|(k, v)| (k.as_str(), v.as_str())).collect();
    start.into_iter().map(|(k, v)| (k.to_string(), v.to_string())).collect()
}

impl Worker {
    fn new() -> Worker {
        Worker { proc: std::sync::Mutex::new(None) }
    }

    /// Runs test `name` of this exe with `env` added, output to `log`; returns whether it succeeded.
    fn run(&self, name: &str, env: &[(String, String)], log: &Path) -> bool {
        // an earlier run's log must not survive a task that fails before creating its own: callers read the log either way
        match std::fs::remove_file(log) {
            Err(e) if e.kind() != std::io::ErrorKind::NotFound => panic!("cannot clear {}: {e}", log.display()),
            _ => {}
        }
        let mut slot = self.proc.lock().unwrap_or_else(|e| e.into_inner());
        let start = process_start(env);
        if slot.as_ref().is_some_and(|p| p.start != start) {
            Self::stop(slot.take().unwrap());
        }
        let p = slot.get_or_insert_with(|| Self::spawn(start));
        let fields: Vec<String> = [name.to_string(), log.display().to_string()].into_iter().chain(env.iter().map(|(k, v)| format!("{k}={v}"))).collect();
        assert!(fields.iter().all(|f| !f.contains(['\t', '\n', '\r'])), "a task field holds a tab or a newline: {fields:?}");
        let sent = writeln!(p.stdin, "{}", fields.join("\t")).and_then(|_| p.stdin.flush()).is_ok();
        // a failed task ends the worker; EOF before a reply means it died (its log is then partial, as a crashed child's)
        let ok = sent && (&mut p.stdout).lines().map_while(Result::ok).find_map(|l| l.strip_prefix("WORKER ").map(|r| r == "ok")) == Some(true);
        if !ok {
            Self::stop(slot.take().unwrap());
        }
        ok
    }

    fn spawn(start: Vec<(String, String)>) -> WorkerProc {
        let mut child = Command::new(std::env::current_exe().unwrap())
            .args(["driver::worker", "--exact", "--ignored", "--nocapture"])
            .envs(start.iter().cloned())
            .env("TATIC_WORKER", "1")
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .spawn()
            .expect("start the worker");
        let (stdin, stdout) = (child.stdin.take().unwrap(), BufReader::new(child.stdout.take().unwrap()));
        WorkerProc { child, stdin, stdout, start }
    }

    /// Closes the worker's stdin, reads its stdout to EOF (libtest's closing lines must not meet a closed pipe) and waits.
    fn stop(p: WorkerProc) {
        let WorkerProc { mut child, stdin, mut stdout, .. } = p;
        drop(stdin);
        let _ = std::io::copy(&mut stdout, &mut std::io::sink());
        let _ = child.wait();
    }
}

impl Drop for Worker {
    fn drop(&mut self) {
        if let Some(p) = self.proc.get_mut().unwrap_or_else(|e| e.into_inner()).take() {
            Self::stop(p);
        }
    }
}

fn append(path: &Path, text: &str) {
    std::fs::OpenOptions::new().create(true).append(true).open(path).unwrap().write_all(text.as_bytes()).unwrap();
}

/// A machine-state line on stderr (about 2 s), logged pieces in `<out>/machine_state_<when>.log`: `RTP` and `CPU` are
/// machine-wide, so read here; `lockpriv` and `pages` belong to the children's process and environment, so a worker
/// task (`machine::pages_line`, with the children's `env`) reports them. `MACHINE_STATE=0` skips it, in a loop or a sweep.
fn machine_state(when: &str, env: &[(String, String)], worker: &Worker, out: &Path) {
    if env_or("MACHINE_STATE", 1usize) == 0 {
        return;
    }
    std::fs::create_dir_all(out).unwrap();
    let log = out.join(format!("machine_state_{when}.log"));
    worker.run("machine::pages_line", env, &log);
    let text = std::fs::read_to_string(&log).unwrap_or_default();
    let pages = text.lines().find_map(|l| l.strip_prefix("pages: ")).unwrap_or("pages unavailable");
    eprintln!("machine at {when}: machine state: {} {pages}", crate::machine::rtp_cpu());
}

/// Prints `env_var(k)` for each name in `ECHO` (a comma list) and a nonce unique to this process; panics when
/// `ECHO_PANIC=1`. A task for `worker_runs_tasks`.
#[test]
#[ignore]
fn env_echo() {
    static NONCE: std::sync::OnceLock<u128> = std::sync::OnceLock::new();
    let nonce = NONCE.get_or_init(|| std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos());
    for k in env_var("ECHO").unwrap_or("").split(',').filter(|k| !k.is_empty()) {
        println!("ECHO {k}={}", env_var(k).unwrap_or("<unset>"));
    }
    println!("ECHO nonce={nonce}");
    assert!(env_var("ECHO_PANIC") != Some("1"), "env_echo panicked on request");
}

/// A worker runs each task with its own environment and log, leaks no variable from one task to the next, starts afresh
/// after a failed task, and is replaced when a task's process-start variables differ. Starts processes:
/// `cargo test --release --test church_bv driver::worker_runs_tasks -- --exact --ignored --nocapture`.
#[test]
#[ignore]
fn worker_runs_tasks() {
    let dir = std::env::temp_dir().join(format!("worker_runs_tasks_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let kv = |k: &str, v: &str| (k.to_string(), v.to_string());
    let log = |i: usize| dir.join(format!("{i}.log"));
    let w = Worker::new();
    let ok = [
        w.run("driver::env_echo", &[kv("ECHO", "A,B,C"), kv("A", "1"), kv("C", "x=y")], &log(1)),
        w.run("driver::env_echo", &[kv("ECHO", "A,B"), kv("B", "2")], &log(2)),
        w.run("driver::env_echo", &[kv("ECHO_PANIC", "1")], &log(3)),
        w.run("driver::env_echo", &[kv("ECHO", "A")], &log(4)),
        w.run("driver::no_such_task", &[], &log(5)),
        w.run("driver::env_echo", &[], &dir.join("missing").join("6.log")),
        w.run("driver::env_echo", &[kv("RUST_BACKTRACE", "0")], &log(7)),
        w.run("driver::env_echo", &[kv("RUST_BACKTRACE", "0")], &log(8)),
        w.run("driver::env_echo", &[], &log(9)),
    ];
    assert_eq!(ok, [true, true, false, true, false, false, true, true, true]);
    let text = |i: usize| std::fs::read_to_string(log(i)).unwrap();
    let echoes = |i: usize| text(i).lines().filter(|l| !l.starts_with("ECHO nonce=")).map(String::from).collect::<Vec<_>>();
    let nonce = |i: usize| text(i).lines().find_map(|l| l.strip_prefix("ECHO nonce=").map(String::from)).unwrap();
    assert_eq!(echoes(1), ["ECHO A=1", "ECHO B=<unset>", "ECHO C=x=y"]);
    assert_eq!(echoes(2), ["ECHO A=<unset>", "ECHO B=2"], "no variable leaks from task 1");
    assert!(text(3).contains("env_echo panicked on request"), "3.log: {}", text(3));
    assert!(text(5).contains("no task driver::no_such_task"), "5.log: {}", text(5));
    assert_eq!(nonce(1), nonce(2), "tasks 1 and 2 ran in one worker");
    assert_ne!(nonce(2), nonce(4), "a fresh worker after the panic");
    assert_eq!(nonce(7), nonce(8), "tasks with the same process-start variables share a worker");
    assert_ne!(nonce(8), nonce(9), "a different RUST_BACKTRACE gets a fresh worker");
    for i in [1, 2, 4, 7, 8, 9] {
        assert!(text(i).lines().all(|l| l.starts_with("ECHO ")), "{i}.log holds only its task's lines: {}", text(i));
    }
    drop(w);
    std::fs::remove_dir_all(&dir).unwrap();
}

/// A task whose log cannot be cleared stops the driver, as the old per-child `File::create(log).unwrap()` did, rather than
/// leaving an earlier run's log to be read as this one's (`run_loop`'s serve reads it whatever `run` returns). The log is
/// held open without sharing, so neither the driver nor a worker can remove or recreate it.
#[cfg(windows)]
#[test]
fn worker_never_leaves_a_stale_log() {
    use std::os::windows::fs::OpenOptionsExt;
    let log = std::env::temp_dir().join(format!("worker_stale_{}.log", std::process::id()));
    std::fs::write(&log, "CHECKED 1 laws\n").unwrap();
    let held = std::fs::OpenOptions::new().read(true).share_mode(0).open(&log).unwrap();
    let w = Worker::new();
    let ran = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| w.run("driver::env_echo", &[], &log)));
    drop(held);
    drop(w);
    std::fs::remove_file(&log).unwrap();
    assert!(ran.is_err(), "run returned {ran:?} with the earlier log still in place");
}

/// Writes to `path` the laws a child with `env` (over this process's environment) would take from `family`'s sequence, as
/// `lhs = rhs` lines for `RULEMINER_LAWFILE`/`CHECK_LAWFILE`, and returns the variable that passes them. The driver builds a
/// family's law pool once (`family_laws` keeps it) where every child used to rebuild it: 35% of a sweep's loops
/// (docs/tier-cycle.md).
fn write_laws(family: &str, env: &[(String, String)], path: &Path, var: &str) -> (String, String) {
    let get = |k: &str, d: usize| env.iter().rev().find(|(kk, _)| kk == k).map_or_else(|| env_or(k, d), |(_, v)| v.parse().unwrap());
    std::fs::write(path, laws_text(&family_laws(family, &get, 4, family_vars(family), 7))).unwrap();
    (var.to_string(), path.display().to_string())
}

/// `cfg`'s value of the child variable `k`: its `env`, then this process's, as `run_loop`'s children read it.
fn cfg_var(cfg: &LoopCfg, k: &str, d: usize) -> usize {
    cfg.env.iter().rev().find(|(kk, _)| kk == k).map_or_else(|| env_or(k, d), |(_, v)| v.parse().unwrap())
}

/// The laws a child of `cfg` takes at stride phase `phase`: `laws` of them from `skip`, through the variables `run_loop` gives
/// its children.
fn stream_laws(cfg: &LoopCfg, phase: usize, skip: usize, laws: usize) -> Vec<(Term, Term)> {
    let env = |k: &str, d: usize| match k {
        "RULEMINER_DEEP3" => cfg.deep3,
        "RULEMINER_STRIDE" => cfg.stride,
        "RULEMINER_PHASE" => phase,
        "RULEMINER_SHAPE" => cfg.split,
        "RULEMINER_SKIP" => skip,
        "RULEMINER_LAWS" => laws,
        _ => cfg_var(cfg, k, d),
    };
    family_laws(&cfg.family, &env, 4, family_vars(&cfg.family), 7).into_iter().map(|(_, a, b)| (a, b)).collect()
}

/// The laws `cfg`'s loop serves, and its mines mine: its K batches of B from OFFSET.
fn served_laws(cfg: &LoopCfg) -> Vec<(Term, Term)> {
    stream_laws(cfg, cfg.sphase, cfg.offset, cfg.b * cfg.k)
}

fn law_text((a, b): &(Term, Term)) -> String {
    format!("{} = {}", a.show(), b.show())
}

/// A law's skeleton: every variable (a lone lowercase letter) written `v`, the smaller side first.
fn skeleton(l: &(Term, Term)) -> String {
    let b = law_text(l).into_bytes();
    let e: String = (0..b.len())
        .map(|i| {
            let alone = (i == 0 || !b[i - 1].is_ascii_alphanumeric()) && (i + 1 == b.len() || !b[i + 1].is_ascii_alphanumeric());
            if alone && b[i].is_ascii_lowercase() { 'v' } else { b[i] as char }
        })
        .collect();
    let (a, c) = e.split_once(" = ").unwrap();
    if a <= c { format!("{a} = {c}") } else { format!("{c} = {a}") }
}

/// What a sweep's scopes share while their extras are drawn: the class representatives and each family's generator laws.
struct Draw {
    reps: ClassReps,
    laws: hashbrown::HashMap<(String, usize, usize), std::sync::Arc<Vec<(Term, Term)>>>,
}

impl Draw {
    fn new() -> Draw {
        Draw { reps: ClassReps::new(), laws: Default::default() }
    }

    /// `grammar_laws` for `cfg`'s family, `deep3` and salt, generated once per sweep.
    fn grammar(&mut self, cfg: &LoopCfg) -> std::sync::Arc<Vec<(Term, Term)>> {
        let k = (cfg.family.clone(), cfg.deep3, cfg_var(cfg, "RULEMINER_SHUFFLE", 0));
        self.laws
            .entry(k)
            .or_insert_with_key(|k| {
                let t0 = std::time::Instant::now();
                let l = grammar_laws(&k.0, k.1, k.2);
                println!("GEN_LAWS {}: {} laws in {:.1}s", k.0, l.len(), t0.elapsed().as_secs_f64());
                std::sync::Arc::new(l)
            })
            .clone()
    }
}

/// The filter chain (spec §1): the laws of `source` that, against `served`, are no twin after normalizing (a law trivial
/// after normalizing is kept) and have no served law's skeleton, in `source`'s order.
fn filtered(source: &[(Term, Term)], served: &[(Term, Term)], reps: &mut ClassReps) -> Vec<(Term, Term)> {
    let keys: hashbrown::HashSet<String> = served.iter().filter_map(|(a, b)| reps.key(a, b)).collect();
    let skels: hashbrown::HashSet<String> = served.iter().map(skeleton).collect();
    let mut out = vec![];
    for l in source {
        if !reps.key(&l.0, &l.1).is_some_and(|k| keys.contains(&k)) && !skels.contains(&skeleton(l)) {
            out.push(*l);
        }
    }
    out
}

/// The share of the filtered list each loop's mines take: 0.16 in shared slices had the lowest M of the generator arms
/// over salts 1-20 (runs `2026-10-18-gen-round-a` and `-b`, docs/tier-cycle.md "The law generator as a stage").
const GEN_F: f64 = 0.16;

/// Draws one scope's extras (spec §1-3): `scope`'s loops (a stage's 3 loops of one family and source, or one ref mine)
/// against the laws they serve and those of `also` (for a ref mine, every loop the sweep runs). n = ⌊`GEN_F` × L⌋ with L
/// the generator's filtered list, in shared slices; with `GEN_SOURCE=stream` (the control arm, temporary) the slices come
/// from the stream phases the scope does not serve, from the one after its last, filtered alike. `GEN_N=matched`
/// (temporary) caps n at what the filtered stream list fits (`fit_n`), whichever the source, so a grammar arm and its
/// stream control take the same n: the stream is too short for the control at `GEN_F`'s n. Sets each loop's `extras` and
/// `extra_at`, or says by how much the list is short.
fn scope_extras(scope: &mut [LoopCfg], also: &[LoopCfg], draw: &mut Draw) -> Result<(), String> {
    let served: Vec<(Term, Term)> = scope.iter().chain(also).flat_map(served_laws).collect();
    let c = scope[0].clone();
    let grammar = filtered(&draw.grammar(&c), &served, &mut draw.reps);
    let mut n = (GEN_F * grammar.len() as f64) as usize;
    let source = env_var("GEN_SOURCE").unwrap_or("grammar");
    let matched = match env_var("GEN_N") {
        None => false,
        Some("matched") => true,
        Some(s) => panic!("GEN_N must be matched, got {s}"),
    };
    let mines = mines_of(&c);
    let stream = (source == "stream" || matched).then(|| {
        let own: Vec<usize> = scope.iter().map(|c| c.sphase).collect();
        let last = *own.iter().max().unwrap();
        let raw: Vec<(Term, Term)> =
            (1..=c.stride).map(|i| (last + i) % c.stride).filter(|q| !own.contains(q)).flat_map(|q| stream_laws(&c, q, 0, usize::MAX)).collect();
        let kept = filtered(&raw, &served, &mut draw.reps);
        println!("GEN {}: stream {} laws, {} after the filter", c.out.display(), raw.len(), kept.len());
        kept
    });
    if matched {
        n = n.min(fit_n(stream.as_ref().unwrap().len(), scope.len()));
    }
    let laws = match source {
        "grammar" => grammar,
        "stream" => stream.unwrap(),
        s => panic!("GEN_SOURCE must be grammar or stream, got {s}"),
    };
    let at = extra_slices(laws.len(), scope.len(), mines, n)
        .map_err(|short| format!("{}: {source} list of {} laws is {short} short of {} loops x {n}", c.out.display(), laws.len(), scope.len()))?;
    println!("GEN {}: L {} n {n} source {source}", c.out.display(), laws.len());
    let laws = std::sync::Arc::new(laws);
    for (i, cfg) in scope.iter_mut().enumerate() {
        cfg.extras = laws.clone();
        cfg.extra_at = at[i * mines..(i + 1) * mines].to_vec();
    }
    Ok(())
}

/// One loop; its children share the lemma file `lemmas`, which the caller owns (creates nothing, deletes it when done).
fn run_loop(cfg: &LoopCfg, lemmas: &Path, worker: &Worker) -> Summary {
    let (out, rules) = (&cfg.out, cfg.out.join("rules.txt"));
    std::fs::create_dir_all(out).unwrap();
    let s = |v: usize| v.to_string();
    let mut common: Vec<(String, String)> = [
        ("RULEMINER_FAMILY", cfg.family.clone()),
        ("CHECK_FAMILY", cfg.family.clone()),
        ("RULEMINER_DEEP3", s(cfg.deep3)),
        ("RULEMINER_STRIDE", s(cfg.stride)),
        ("RULEMINER_PHASE", s(cfg.sphase)),
        ("RULEMINER_SHAPE", s(cfg.split)),
        // one machine-state line per loop or sweep instead of one per child
        ("MACHINE_BANNER", "0".to_string()),
        ("LEMMA_CACHE", lemmas.display().to_string()),
    ]
    .into_iter()
    .map(|(k, v)| (k.to_string(), v))
    .collect();
    common.extend(cfg.env.iter().cloned());
    let with = |extra: &[(&str, String)]| common.iter().cloned().chain(extra.iter().map(|(k, v)| (k.to_string(), v.clone()))).collect::<Vec<_>>();
    let count = || parse_rules(&std::fs::read_to_string(&rules).unwrap()).len();
    let mine = |name: &str, skip: usize, laws: usize, slot: usize| {
        let log = out.join(format!("mine_{name}.log"));
        let mut env = with(&[
            ("RULEMINER_PERM", s(1)),
            ("RULEMINER_THREADS", s(cfg.threads)),
            ("RULEMINER_ROUNDS", s(cfg.rounds)),
            ("RULEMINER_SKIP", s(skip)),
            ("RULEMINER_LAWS", s(laws)),
            ("RULEMINER_BASE", rules.display().to_string()),
        ]);
        env.push(write_laws(&cfg.family, &env, &out.join(format!("laws_mine_{name}.txt")), "RULEMINER_LAWFILE"));
        if let Some(at) = cfg.extra_at.get(slot) {
            let extra: String = cfg.extras[at.clone()].iter().map(|l| law_text(l) + "\n").collect();
            println!("GEN_EXTRA {name}: {} laws", at.len());
            std::fs::write(out.join(format!("laws_extra_{name}.txt")), &extra).unwrap();
            append(Path::new(&env.last().unwrap().1), &extra);
        }
        assert!(worker.run("search::rule_miner", &env, &log), "rule_miner failed (see {})", log.display());
        // the chosen rules, then the learned preferences (`winner  OVER  loser` lines; the library file carries both)
        let text = std::fs::read_to_string(&log).unwrap();
        // the base rules a preference phase dropped leave the file
        let rule = |l: &str| (!l.contains("  OVER  ")).then(|| l.trim().split_once(" -> ")).flatten().map(|(a, b)| (parse_term(a.trim()), parse_term(b.trim())));
        let dropped: hashbrown::HashSet<RuleKey> = text.lines().filter_map(|l| l.strip_prefix("RULEMINER drop (")).filter_map(|l| l.split_once("): ")).filter_map(|(_, r)| rule(r)).collect();
        if !dropped.is_empty() {
            let kept: String = std::fs::read_to_string(&rules).unwrap().lines().filter(|l| !rule(l).is_some_and(|r| dropped.contains(&r))).map(|l| format!("{l}\n")).collect();
            std::fs::write(&rules, kept).unwrap();
        }
        let chosen: String = text
            .lines()
            .filter(|l| (l.contains("RULEMINER chosen") || l.contains("RULEMINER prefer")) && l.contains(" -> "))
            .map(|l| format!("{}\n", l.split_once("): ").map_or(l, |(_, r)| r)))
            .collect();
        append(&rules, &chosen);
    };
    // (M, laws, laws that used up the rule budget, laws joined, terms the join reached) of the batch at `skip`
    let serve = |skip: usize| {
        let log = out.join(format!("serve_{skip}.log"));
        let mut env = with(&[("CHECK_FAST", s(cfg.check_fast as usize)), ("RULEMINER_SKIP", s(skip)), ("RULEMINER_LAWS", s(cfg.b)), ("CHECK_RULES", rules.display().to_string())]);
        env.push(write_laws(&cfg.family, &env, &out.join(format!("laws_serve_{skip}.txt")), "CHECK_LAWFILE"));
        worker.run("search::rule_set_kernel_check", &env, &log);
        // CHECKED <n> laws kernel-checked (<k> with no whole-term machine proof), <p> not proved, <x> used up the rule budget
        let text = std::fs::read_to_string(&log).unwrap();
        let line = text.lines().find(|l| l.starts_with("CHECKED ")).unwrap_or_else(|| panic!("no CHECKED line (see {})", log.display()));
        let nums = |line: &str| line.split(|c: char| !c.is_ascii_digit()).filter_map(|w| w.parse().ok()).collect::<Vec<usize>>();
        let &[n, k, p, x] = &nums(line)[..] else { panic!("unexpected CHECKED line: {line}") };
        // JOINED <j> of them by the join, <s> searches reaching <r> terms
        let line = text.lines().find(|l| l.starts_with("JOINED ")).unwrap_or_else(|| panic!("no JOINED line (see {})", log.display()));
        let &[j, _, r] = &nums(line)[..] else { panic!("unexpected JOINED line: {line}") };
        (n - k + p, n + p, x, j, r)
    };
    match &cfg.warm {
        Some(w) => {
            std::fs::copy(w, &rules).unwrap_or_else(|e| panic!("WARM_RULES {}: {e}", w.display()));
        }
        _ => std::fs::write(&rules, "").unwrap(),
    }
    std::fs::write(out.join("m.tsv"), "").unwrap();
    if cfg.mode == "ref" {
        mine("ref", cfg.offset, cfg.b * cfg.k, 0);
    }
    let (mut ms, mut exhausted, mut joined, mut reached) = (vec![], 0, 0, 0);
    for r in 0..cfg.k {
        let (skip, t0) = (cfg.offset + r * cfg.b, std::time::Instant::now());
        let (m, laws, ex, j, rc) = serve(skip);
        append(&out.join("m.tsv"), &format!("{r}\t{m}\t{laws}\t{}\t{}\t{ex}\t{j}\t{rc}\n", count(), t0.elapsed().as_secs()));
        ms.push(m);
        (exhausted, joined, reached) = (exhausted + ex, joined + j, reached + rc);
        if cfg.mode == "loop" && r + 1 < cfg.k {
            mine(&r.to_string(), skip, cfg.b, r);
        }
    }
    let sum = Summary { total: ms.iter().sum(), ms, rules: count(), exhausted, joined, reached };
    println!("mode={} B={} K={} offset={} total_M={} rules={} exhausted={} joined={} reached={}", cfg.mode, cfg.b, cfg.k, cfg.offset, sum.total, sum.rules, sum.exhausted, sum.joined, sum.reached);
    sum
}

#[test]
#[ignore]
fn loop_stream() {
    let worker = Worker::new();
    let cfg = LoopCfg::from_env();
    machine_state("start", &cfg.env, &worker, &cfg.out);
    let lemmas = cfg.out.join("lemmas.bin");
    let _ = std::fs::remove_file(&lemmas);
    run_loop(&cfg, &lemmas, &worker);
    let _ = std::fs::remove_file(&lemmas);
    machine_state("end", &cfg.env, &worker, &cfg.out);
}

/// The ref mines: (family, stride, split, B); each mines K=4 batches of its phase-0 stream (6 threads, no round cap, full serving check).
/// u3 (the union of add3, sbo3 and cmp3d) is mined only when named (`mines:u3`).
const MINES: [(&str, usize, usize, usize); 5] =
    [("sbo3", 11, 2, 50), ("add3", 7, 2, 50), ("mix3", 1, 1, 50), ("cmp3d", 15, 2, 100), ("u3", 11, 2, 100)];
/// The loops' stride per family; each loop serves K=3 batches of B=100 on phases 1-3 (6 threads, no round cap, CHECK_FAST).
const LOOPS: [(&str, usize); 4] = [("cmp3d", 15), ("add3", 7), ("sbo3", 11), ("mix3", 7)];

#[test]
#[ignore]
fn sweep() {
    let out = PathBuf::from(env_var("SWEEP_OUT").expect("set SWEEP_OUT=<dir>"));
    std::fs::create_dir_all(&out).unwrap();
    let salt: usize = env_or("SALT", 1);
    let lib = env_var("LIB").map(PathBuf::from).unwrap_or_else(|| out.clone());
    let stages = env_var("SWEEP").unwrap_or("mines own cold");
    // Large pages off in the children: most are short, each pays the 64 MiB large-page commit up front, and a sweep with them
    // on cost 0.3-2.9 s more CPU and 60% more peak memory (docs/tier-cycle.md, "How often the large-page stall hits a sweep").
    let env: Vec<(String, String)> = [("RULEMINER_FAST", "1".to_string()), ("RULEMINER_SHUFFLE", salt.to_string()), ("MIMALLOC_ALLOW_LARGE_OS_PAGES", "0".to_string())]
        .into_iter()
        .map(|(k, v)| (k.to_string(), v))
        .collect();
    let base = |mode: &str, out: PathBuf, family: &str| LoopCfg {
        mode: mode.into(),
        out,
        family: family.into(),
        stride: 1,
        sphase: 0,
        b: 100,
        k: 3,
        offset: 0,
        threads: 6,
        rounds: usize::MAX,
        deep3: 1,
        split: 2,
        warm: None,
        check_fast: true,
        extras: Default::default(),
        extra_at: vec![],
        env: env.clone(),
    };
    let library = |fam: &str| lib.join(format!("lib_{fam}")).join("rules.txt");
    // `MINES_WARM=<sweep dir>`: each ref mine starts from that sweep's pooled library for its family, where there is one
    // (docs/tier-cycle.md, "Promotion as an iterated sweep": one iteration lowers the best loops 157 to 142, a second adds nothing)
    let mines_warm = |fam: &str| env_var("MINES_WARM").map(|d| PathBuf::from(d).join(format!("pooled_{fam}")).join("rules.txt")).filter(|p| p.exists());
    let stage_fams = |stage: &'static str| stage.split_once(':').unwrap_or((stage, if stage == "mines" { "sbo3,add3,mix3,cmp3d" } else { "cmp3d,add3,sbo3" }));
    let ref_cfg = |fam: &str| {
        let &(fam, stride, split, b) = MINES.iter().find(|m| m.0 == fam).unwrap_or_else(|| panic!("no ref mine for {fam}"));
        LoopCfg { stride, split, b, k: 4, check_fast: false, warm: mines_warm(fam), ..base("ref", out.join(format!("lib_{fam}")), fam) }
    };
    let srcs = |name: &str, fam: &'static str| -> Vec<&'static str> {
        match name {
            "own" => vec![fam],
            "cold" => vec!["none"],
            "cross" => ["cmp3d", "add3", "sbo3"].into_iter().filter(|s| *s != fam).collect(),
            "pooled" => vec!["pooled"],
            "mixed" => vec!["u3"],
            _ => panic!("unknown stage {name}"),
        }
    };
    let loop_cfgs = |stage: &str, fam: &str, src: &str| -> Vec<LoopCfg> {
        let stride = LOOPS.iter().find(|l| l.0 == fam).unwrap_or_else(|| panic!("no loop stride for {fam}")).1;
        let warm = match src {
            "none" => None,
            "pooled" => Some(out.join(format!("pooled_{fam}")).join("rules.txt")),
            s => Some(library(s)),
        };
        (1..=3).map(|p| LoopCfg { stride, sphase: p, warm: warm.clone(), ..base("loop", out.join(format!("{}_{fam}_{p}_{src}", stage.replace(':', "_"))), fam) }).collect()
    };
    // every scope's extras, drawn before the first stage, so a list too short for its slices stops the sweep before any work
    let mut scopes: Vec<Vec<LoopCfg>> = vec![];
    for stage in stages.split_whitespace() {
        let (name, fams) = stage_fams(stage);
        for fam in fams.split(',') {
            if name == "mines" {
                scopes.push(vec![ref_cfg(fam)]);
            } else {
                scopes.extend(srcs(name, fam).into_iter().map(|src| loop_cfgs(stage, fam, src)));
            }
        }
    }
    // a ref mine's library is served on the loops of every family the sweep runs (each family's phase 1-3 batches once);
    // a sweep of mines alone runs no loop, so its ref mines filter against their own batches only
    let mut loops: Vec<LoopCfg> = scopes.iter().flatten().filter(|c| c.mode == "loop").cloned().collect();
    loops.sort_by(|a, b| (&a.family, a.sphase).cmp(&(&b.family, b.sphase)));
    loops.dedup_by(|a, b| (&a.family, a.sphase) == (&b.family, b.sphase));
    let (mut draw, mut short) = (Draw::new(), vec![]);
    for scope in &mut scopes {
        if !scope.iter().all(|c| takes_extras(c, ablated("gen"))) {
            continue;
        }
        let also = if scope[0].mode == "ref" { &loops[..] } else { &[] };
        if let Err(e) = scope_extras(scope, also, &mut draw) {
            short.push(e);
        }
    }
    assert!(short.is_empty(), "extras lists too short for their slices:\n{}", short.join("\n"));
    let drawn: hashbrown::HashMap<PathBuf, LoopCfg> = scopes.into_iter().flatten().map(|c| (c.out.clone(), c)).collect();
    let with_extras = |cfg: LoopCfg| match drawn.get(&cfg.out) {
        Some(d) => LoopCfg { extras: d.extras.clone(), extra_at: d.extra_at.clone(), ..cfg },
        None => cfg,
    };
    // one lemma file for every loop of the sweep: all its processes run this exe, so every statement in it was checked by this build
    let lemmas = out.join("lemmas.bin");
    let _ = std::fs::remove_file(&lemmas);
    let worker = Worker::new();
    machine_state("start", &env, &worker, &out);
    for stage in stages.split_whitespace() {
        let (name, fams) = stage_fams(stage);
        let tsv = out.join(format!("{}.tsv", stage.replace(':', "_")));
        std::fs::write(&tsv, "").unwrap();
        if name == "mines" {
            for fam in fams.split(',') {
                let cfg = with_extras(ref_cfg(fam));
                let t0 = std::time::Instant::now();
                let s = run_loop(&cfg, &lemmas, &worker);
                append(&tsv, &format!("{}\t{}\t{}\t{}\t{}\t{}\t{}\n", cfg.family, t0.elapsed().as_secs(), s.total, s.rules, s.exhausted, s.joined, s.reached));
            }
            continue;
        }
        let pooled = out.join("pooled.rules");
        let pooled_for = |fam: &str| out.join(format!("pooled_{fam}")).join("rules.txt");
        if name == "pooled" {
            // a section per library (`library_sections`; `parse_rules` reads a rule two libraries share once)
            let text: String = ["cmp3d", "add3", "sbo3"].iter().map(|fam| format!("# library {fam}\n{}\n", std::fs::read_to_string(library(fam)).unwrap().trim_end())).collect();
            std::fs::write(&pooled, &text).unwrap();
            let units = out.join("pooled.units");
            std::fs::write(&units, units_text(&joinability_units(&text, 4, env_or("RULEMINER_STEPS", 200i64)))).unwrap();
            std::fs::write(out.join("pooled_prefs.tsv"), "").unwrap();
            // the libraries' rules can conflict (two right sides for one left side, say); each family learns which wins, and which
            // rules where two libraries' normal forms meet to drop (`drop_units`), on its phase-0 stream: a mine with no rule
            // rounds, only preferences (`RULEMINER_PREFS`), on the pooled library
            for fam in fams.split(',') {
                let &(fam, stride, split, b) = MINES.iter().find(|m| m.0 == fam).unwrap_or_else(|| panic!("no ref mine for {fam}"));
                let mut cfg = LoopCfg { stride, split, b, k: 4, rounds: 0, warm: Some(pooled.clone()), ..base("ref", pooled_for(fam).parent().unwrap().into(), fam) };
                cfg.env.push(("RULEMINER_PREFS".into(), "1".into()));
                cfg.env.push(("RULEMINER_UNITS".into(), units.display().to_string()));
                let t0 = std::time::Instant::now();
                let s = run_loop(&cfg, &lemmas, &worker);
                append(&out.join("pooled_prefs.tsv"), &format!("{fam}\t{}\t{}\t{}\t{}\t{}\t{}\n", t0.elapsed().as_secs(), s.total, s.rules, s.exhausted, s.joined, s.reached));
            }
        }
        for fam in fams.split(',') {
            for src in srcs(name, fam) {
                for cfg in loop_cfgs(stage, fam, src) {
                    let cfg = with_extras(cfg);
                    let p = cfg.sphase;
                    let t0 = std::time::Instant::now();
                    let s = run_loop(&cfg, &lemmas, &worker);
                    let ms: Vec<String> = s.ms.iter().map(|m| m.to_string()).collect();
                    append(&tsv, &format!("{fam}\t{}-{p}\tfrom_{src}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n", cfg.stride, s.total, ms.join(","), s.rules, t0.elapsed().as_secs(), s.exhausted, s.joined, s.reached));
                }
            }
        }
    }
    let _ = std::fs::remove_file(&lemmas);
    machine_state("end", &env, &worker, &out);
}
