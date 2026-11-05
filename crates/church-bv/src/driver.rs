//! The mine-and-serve loop and the sweeps over it (formerly `scripts/loop_stream.sh` and local sweep scripts). Serving
//! (`search::rule_set_kernel_check`) and mining (`search::rule_miner`) run as tasks of one worker process of this exe (`worker`,
//! `Worker`): each task gets its own `Setup` (environment, results, caches), a `Job` per rewriting thread and its own log,
//! while the pure memos carry over (`task.rs`, `job::hidden_state_is_classified`). Shell drivers spent much of a loop in Git Bash forks (docs/tier-cycle/, "Loop overhead").
//! To share the machine, launch at low priority and pinned (children inherit both): cmd //c start "" //b //belownormal //affinity 3 ...
//!
//! The laws come from the streams (spec docs/superpowers/specs/2026-10-22-class-table-normal-form-design.md §9):
//! `search::stream_sequence(salt, STREAM_LEVELS)`, the operator-set streams round-robin, and a phase is its residue
//! class mod `STREAM_STRIDE` (`search::residue`). A sweep's loops serve phases 1-3; a single loop serves SPHASE (default
//! 0). Phase 0 fed the mines' extras until 2026-10-28; they now come from a deeper sequence (`scope_extras`), and the
//! stride stays, so the loops' laws do.
//!
//! **One loop:** `LOOP_MODE=none|ref|loop LOOP_OUT=<dir> [options] church-bv loop-stream`.
//! Batch r is the laws OFFSET+r*B .. OFFSET+(r+1)*B of phase SPHASE of the stream sequence at salt RULEMINER_SHUFFLE. It is
//! served under the rules in force *before* it is mined, so M is what the stream costs when rules arrive as it does. The mode
//! picks the loop's mines (`schedule`): `ref` mines once on all K batches before serving them; `loop` mines each batch after
//! serving it (not the last, which could not change any M); `none` only serves.
//! Options (env, defaults in brackets): SPHASE [0], B [150], K [4], OFFSET [0], THREADS [2] (miner pool), ROUNDS [no cap],
//! WARM_RULES=<file> (start with those rules in force), CHECK_FAST [0] (serve without proof building or kernel checks; M is
//! unchanged), MACHINE_STATE [1] (a machine-state line at start and end, about 2 s each). Other variables pass through to the
//! children: RULEMINER_FAST=1 (exact counts without proving every candidate, docs/tier-cycle/ "Miner speedups"),
//! RULEMINER_SHUFFLE=<salt> (the stream sequence's salt).
//! Extras (docs/superpowers/specs/2026-10-17-law-generator-design.md, docs/tier-cycle/ "Count and slicing"): every mine
//! with rule rounds also mines its own `EXTRAS_N` laws, the next the filter keeps from the stream sequence grown as deep
//! as the held-out bands (`scope_extras`, fresh slices); off with ABLATE=gen; GEN_DRAW=d draws them from the sequence at
//! salt + 1000 d instead. POOL=p with EXTRAS_SELECT=first|small|ctx hands each mine p x n laws and the miner keeps n: the first n, or the n stragglers with the fewest rewrite steps (then the smallest normal form; a shortfall is filled with the pool's other laws in order), or (`ctx`, with CTX_WEIGHTS=<weights file>, `RULEMINER_CTX_WEIGHTS`) the stragglers the context model scores highest; `first` with POOL>1 only serves as a control
//! under that mine's base rules (`RULEMINER_EXTRAS_*`, `miner::kept_indices`). POOL>1 needs a selector. POOL_DUMP=1 (with
//! `first`) also writes each mine's classified pool to LOOP_OUT/dump_<name>_pool.tsv and the served stragglers' normal forms to
//! dump_<name>_served.txt (`RULEMINER_POOL_DUMP`, `miner::dump_pool`, `ctx_scorer::pool_tsv`); the mine is unchanged.
//! The children share the lemma statements they check through LOOP_OUT/lemmas.bin (`LEMMA_CACHE`, `lemma_cache.rs`; deleted when
//! the loop starts and ends; a sweep shares one SWEEP_OUT/lemmas_<lane>.bin across the loops of each of its SWEEP_LANES lanes
//! instead); LEMMA_RECHECK=1 audits it. The driver computes each child's laws (its window of the stream sequence, built once
//! per process and salt) and passes them as a file, LOOP_OUT/laws_<mine|serve>_<name>.txt (`RULEMINER_LAWFILE`,
//! `CHECK_LAWFILE`).
//! Output in LOOP_OUT: rules.txt (the rules in force at the end), m.tsv (batch, M, laws, rules in force, serve seconds, laws that used
//! up the rule budget: nonzero means a rewrite cycle or growing rules, laws the join closed with no machine proof, terms the join's
//! searches reached: its cost, which M does not show, and the distinct class-table replacements the batch used, each with
//! a proof (spec decision 2: apart from M)), mine_<name>.log and serve_<skip>.log, each with a `.results` file
//! beside it (the task's `key<TAB>value` records from `Setup::result`, which the driver reads). The last line printed is
//! `mode=.. mines=.. B=.. K=.. offset=.. total_M=.. rules=.. exhausted=.. joined=.. reached=..`.
//!
//! **A sweep** (the gate's unit, `scripts/streams_ab.sh`): `SWEEP_OUT=<dir> [SALT=1] church-bv sweep`
//! (`MACHINE_STATE=0` skips its two machine-state lines too). It uses `RULEMINER_FAST=1` and
//! `RULEMINER_SHUFFLE=$SALT`. Its one stage, `cold` (or `cold:streams`): three loops on phases 1-3 from no rules, in
//! `cold_streams_streams_<phase>_none/`, one row each in `cold_streams.tsv` (`:` becomes `_`): family, stride-phase,
//! from_none, total M, per-batch M, rules at the end, seconds, exhausted, joined, reached (as in m.tsv, summed over the batches).

use super::*;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::io::{BufRead, BufReader};

/// The process's stdout and stderr pointed at one file, for a task's log (`worker`): one handle (one fd) for both, so they
/// share the file offset as a child's `try_clone`d handles do. std looks the handle up on every write (checked by a probe,
/// docs/tier-cycle/, "A persistent worker"), so `println!` follows it.
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
fn task_fn(name: &str) -> Option<fn(&Arc<Setup>)> {
    Some(match name {
        "search::rule_miner" => crate::miner::run,
        "search::rule_set_kernel_check" => crate::search::rule_set_kernel_check_task,
        "machine::pages_line" => crate::machine::pages_line_task,
        "driver::env_echo" => env_echo_task,
        _ => return None,
    })
}

/// A sweep's children as tasks of one process (`Worker` starts it, with `TATIC_WORKER=1`; it returns at once otherwise).
/// Reads `<test>\t<log>\t<KEY>=<VALUE>...` lines; runs each test on a fresh thread (fresh pure thread-local memos) with the task's
/// pairs over this process's environment (its `Setup`), its stdout and stderr in the log and its result records
/// (`Setup::result`) in `results_path(log)`; answers `WORKER ok` or
/// `WORKER fail` on a line of its own, and exits after a failure (a panic can leave a lock poisoned) or at EOF. A task that
/// starts a process must give it a null stdin, as `Command::output` does: this stdin is the task pipe.
#[test]
#[ignore]
fn worker() {
    if std::env::var_os("TATIC_WORKER").is_some() {
        run_worker();
    }
}

/// The worker loop (the `worker` subcommand; the test above runs it only when `Worker` started this process).
pub fn run_worker() {
    for line in std::io::stdin().lines() {
        let line = line.expect("the task pipe");
        let mut fields = line.split('\t');
        let (name, log) = (fields.next().unwrap_or("").to_string(), fields.next().unwrap_or("").to_string());
        let env = fields.filter_map(|f| f.split_once('=')).map(|(k, v)| (k.to_string(), v.to_string())).collect();
        let ok = match (std::fs::File::create(&log), std::fs::File::create(results_path(Path::new(&log)))) {
            (Ok(f), Ok(results)) => {
                std::io::stdout().flush().unwrap();
                let saved = stdio::redirect(&f);
                // after the redirect: the setup's reads as it is built print ENV lines (`Setup::var`), which go in the log
                let setup = Setup::for_task(env, results);
                let ok = match task_fn(&name) {
                    Some(run) => std::thread::Builder::new().name(name.clone()).spawn(move || run(&setup)).unwrap().join().is_ok(),
                    None => {
                        eprintln!("worker: no task {name}");
                        false
                    }
                };
                if let Some(n) = crate::classes::Classes::memo_len() {
                    println!("CLASS_MEMO {n}");
                }
                println!("{}", crate::work::line(crate::work::take()));
                std::io::stdout().flush().unwrap();
                stdio::restore(saved);
                ok
            }
            (Err(e), _) | (_, Err(e)) => {
                eprintln!("worker: cannot create {log} or its result file: {e}");
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
    /// the loop's mines (`schedule`), in order, and the mode they were scheduled from (for the summary line only)
    mines: Vec<Mine>,
    mode: String,
    out: PathBuf,
    sphase: usize,
    b: usize,
    k: usize,
    offset: usize,
    threads: usize,
    rounds: usize,
    warm: Option<PathBuf>,
    check_fast: bool,
    /// the extras list of this loop's scope (`scope_extras`), shared by the scope's loops
    extras: std::sync::Arc<Vec<(Term, Term)>>,
    /// each of `mines`' slice of `extras`
    extra_at: Vec<std::ops::Range<usize>>,
    /// the extras variables, checked once by `scope_extras` and written to each mine's environment by `run_loop`
    plan: crate::miner::ExtrasPlan,
    /// further variables for the children (a sweep's RULEMINER_FAST and RULEMINER_SHUFFLE)
    env: Vec<(String, String)>,
}

/// Each mine's slice of a scope's extras list of `len` laws, ordered (loop, mine): `loops` loops of `mines` mines, each
/// mine its own `n` laws (fresh slices: at equal laws per loop they beat a loop's mines sharing one slice, see `EXTRAS_N`);
/// the shortfall if they do not fit.
fn extra_slices(len: usize, loops: usize, mines: usize, n: usize) -> Result<Vec<std::ops::Range<usize>>, usize> {
    let k = loops * mines;
    if k * n > len {
        return Err(k * n - len);
    }
    Ok((0..k).map(|j| j * n..(j + 1) * n).collect())
}

/// The filter drops a twin of a served law (here through `sub(y, 0)`, which normalizes to `y`), a law with a served
/// law's skeleton, a law trivial after normalizing (its sides equal below their roots) and a twin of a held-out law, and
/// keeps an unrelated law.
#[test]
fn the_filter_drops_twins_skeletons_and_trivial_laws() {
    let p = |a: &str, b: &str| (parse_term(a), parse_term(b));
    let served = [p("and(or(x, y), z)", "or(and(x, z), and(y, z))")];
    let held = [p("or(and(x, y), z)", "and(or(x, z), or(y, z))")];
    let twin = p("and(or(x, sub(y, 0)), z)", "or(and(x, z), and(y, z))");
    let skel = p("and(or(x, y), y)", "or(and(x, y), and(y, y))");
    let trivial = p("add(sub(x, x), y)", "add(0, y)");
    let held_twin = p("or(and(x, sub(y, 0)), z)", "and(or(x, z), or(y, z))");
    let other = p("add(add(x, y), z)", "add(x, add(y, z))");
    // `Term` has no `Debug`, so compare texts
    let text = |(a, b): (Term, Term)| format!("{} = {}", a.show(), b.show());
    let kept = |held: &[(Term, Term)]| -> Vec<String> {
        let keep = filter(&served, held);
        [twin, skel, trivial, held_twin, other].into_iter().filter(|l| keep(l)).map(text).collect()
    };
    assert_eq!(kept(&[]), [held_twin, other].map(text), "with no held-out laws the held-out twin stays");
    assert_eq!(kept(&held), [other].map(text));
}

/// The `JOIN_VISIT` each mine runs with, as text for its env: 100 unless `MINE_JOIN_VISIT` says otherwise. Serving and the
/// held-out check keep the process's own (1000); a mine's search time is 99% failed joins, so a lower budget there
/// saves CPU at level held-out M (docs/tier-cycle/, "A join budget for the mines alone").
fn mine_join_visit(setup: &Setup) -> String {
    setup.or("MINE_JOIN_VISIT", 100u32).to_string()
}

/// Whether the mines of `cfg` take extras: it has mines with rule rounds, and `ABLATE=gen` is off.
fn takes_extras(cfg: &LoopCfg, ablated: bool) -> bool {
    !ablated && cfg.rounds > 0 && !cfg.mines.is_empty()
}

/// One mine of a loop: once `at` batches are served, on `laws` laws from `skip`; `name` names its log and law files.
#[derive(Clone)]
struct Mine {
    at: usize,
    skip: usize,
    laws: usize,
    name: String,
}

/// The mines `LOOP_MODE` schedules over K batches of B from OFFSET: `none` none, `ref` one on all K batches before the first
/// is served, `loop` one on each batch after serving it, but not the last (it could not change any M).
fn schedule(mode: &str, offset: usize, b: usize, k: usize) -> Vec<Mine> {
    match mode {
        "none" => vec![],
        "ref" => vec![Mine { at: 0, skip: offset, laws: b * k, name: "ref".into() }],
        "loop" => (0..k.saturating_sub(1)).map(|r| Mine { at: r + 1, skip: offset + r * b, laws: b, name: r.to_string() }).collect(),
        _ => panic!("LOOP_MODE must be none, ref or loop, got {mode}"),
    }
}

/// Every mine gets its own n laws: the slices are disjoint, in order, and cover the first loops × mines × n laws.
#[test]
fn extra_slices_are_disjoint_and_full() {
    let fresh = extra_slices(100, 3, 2, 10).unwrap();
    assert_eq!(fresh, (0..6).map(|j| 10 * j..10 * (j + 1)).collect::<Vec<_>>());
    // n 0: every mine takes nothing
    assert_eq!(extra_slices(0, 1, 1, 0), Ok(vec![0..0]));
}

/// A list shorter than its slices returns the shortfall.
#[test]
fn extra_slices_refuse_a_short_list() {
    assert_eq!(extra_slices(59, 3, 2, 10), Err(1));
    assert!(extra_slices(60, 3, 2, 10).is_ok());
}

/// Distinct laws for the selection tests: law `i` is `add(.. add(x, y) .. y) = 0` with `i` additions, so its size grows with `i`.
fn nested_laws(count: usize) -> Vec<(Term, Term)> {
    (0..count).map(|i| ((0..i).fold(Term::v(0), |t, _| Term::op(ADD, t, Term::v(1))), Term::ZERO)).collect()
}


/// The miner names a straggler `a.show() = b.show()` (`read_named_laws`) and credits it by that name; the extras file is
/// written with `law_text`. The labels join the two, so they must stay equal.
#[test]
fn law_text_equals_the_names_the_miner_reads_back() {
    let laws = nested_laws(5);
    let path = std::env::temp_dir().join(format!("law_text_names_{}.txt", std::process::id()));
    std::fs::write(&path, laws.iter().map(|l| law_text(l) + "\n").collect::<String>()).unwrap();
    let names: Vec<String> = crate::search::read_named_laws(path.to_str().unwrap()).into_iter().map(|n| n.0).collect();
    std::fs::remove_file(&path).unwrap();
    assert_eq!(names, laws.iter().map(law_text).collect::<Vec<_>>());
}

#[test]
fn extra_slices_refuse_a_pool_that_does_not_fit() {
    // 3 loops x 2 mines x (pool 4 x n 319) laws needed
    assert_eq!(extra_slices(6 * 4 * 319 - 1, 3, 2, 4 * 319), Err(1));
    assert!(extra_slices(6 * 4 * 319, 3, 2, 4 * 319).is_ok());
}

/// Review Focus 4: the stream phases are disjoint residue classes, so no two of the loops' phases share a law, and
/// their windows tile each class.
#[test]
fn stream_phases_are_disjoint_residue_classes() {
    let seq: Vec<(Term, Term)> = (0..200).map(|i| (Term::v(0), (0..i).fold(Term::v(1), |t, _| Term::op(ADD, t, Term::v(2))))).collect();
    let phase = |p: usize| residue(&seq, p, 0, usize::MAX);
    let all: Vec<_> = (0..STREAM_STRIDE).flat_map(phase).collect();
    assert_eq!(all.len(), seq.len());
    let distinct: hashbrown::HashSet<_> = all.iter().collect();
    assert_eq!(distinct.len(), seq.len(), "a law in two phases");
    assert!(residue(&seq, 1, 0, 10) == phase(1)[..10] && residue(&seq, 1, 10, 10) == phase(1)[10..20]);
}

/// `ref` mines all K batches before the first is served, `loop` each batch after serving it but the last, `none` never.
#[test]
fn loop_modes_schedule_their_mines() {
    let at = |mode: &str| schedule(mode, 10, 100, 3).into_iter().map(|m| (m.at, m.skip, m.laws, m.name)).collect::<Vec<_>>();
    assert_eq!(at("ref"), [(0, 10, 300, "ref".to_string())]);
    assert_eq!(at("loop"), [(1, 10, 100, "0".to_string()), (2, 110, 100, "1".to_string())]);
    assert_eq!(at("none"), []);
}

/// `JOIN_VISIT` for the mines alone: 100 (landed 2026-10-30; serving and the held-out check keep 1000, `MINE_JOIN_VISIT`
/// overrides). At n 319 it keeps held-out M (5166 against 5340) at 21% of the job CPU (docs/tier-cycle/, "A join budget
/// for the mines alone").
#[test]
fn mines_join_with_a_budget_of_100_unless_overridden() {
    assert_eq!(mine_join_visit(&Setup::with_env(vec![])), "100");
    assert_eq!(mine_join_visit(&Setup::with_env(vec![("MINE_JOIN_VISIT".into(), "250".into())])), "250");
}

/// Extras exist to be mined into rules: a mine with no rule rounds, a loop that only
/// serves, and any mine under `ABLATE=gen` take none; loop mines and ref mines with rounds take them.
#[test]
fn no_extras_without_rounds() {
    let c = |mode: &str, rounds: usize| LoopCfg { mines: schedule(mode, 0, 100, 3), rounds, k: 3, ..Default::default() };
    assert!(takes_extras(&c("loop", usize::MAX), false));
    assert!(takes_extras(&c("ref", usize::MAX), false), "a ref mine with rounds");
    assert!(!takes_extras(&c("ref", 0), false), "a mine with no rule rounds");
    assert!(!takes_extras(&c("loop", 0), false), "a mine with no rule rounds");
    assert!(!takes_extras(&c("loop", usize::MAX), true), "ABLATE=gen");
    assert!(!takes_extras(&c("none", usize::MAX), false), "a loop that only serves");
}

impl LoopCfg {
    /// One loop from the environment. Its extras come from a scope of this loop alone, so they differ from the ones it
    /// got inside a sweep: `scope_extras` filters against every loop's served laws and slices among all of them.
    fn from_env(setup: &Setup) -> LoopCfg {
        let (b, k, offset) = (setup.or("B", 150), setup.or("K", 4), setup.or("OFFSET", 0));
        let mode = setup.var("LOOP_MODE").expect("set LOOP_MODE=none|ref|loop");
        let cfg = LoopCfg {
            mines: schedule(mode, offset, b, k),
            mode: mode.into(),
            out: PathBuf::from(setup.var("LOOP_OUT").expect("set LOOP_OUT=<dir>")),
            sphase: setup.or("SPHASE", 0),
            b,
            k,
            offset,
            threads: setup.or("THREADS", 2),
            rounds: setup.or("ROUNDS", usize::MAX),
            warm: setup.var("WARM_RULES").map(PathBuf::from),
            check_fast: setup.flag("CHECK_FAST", false),
            extras: Default::default(),
            extra_at: vec![],
            plan: Default::default(),
            env: vec![],
        };
        if takes_extras(&cfg, setup.ablated("gen")) {
            let mut scope = [cfg];
            scope_extras(setup, &mut scope).unwrap_or_else(|e| panic!("{e}"));
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
    /// laws served with no machine proof by the join, and the terms its searches reached (`Job::join_cost`, which M does not show)
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

/// Where a task logging to `log` leaves its result records: `<log stem>.results` beside it.
fn results_path(log: &Path) -> PathBuf {
    log.with_extension("results")
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

    /// Runs test `name` of this exe with `env` added, output to `log`; returns its result records (`Setup::result`), or
    /// `None` if it failed.
    fn run(&self, name: &str, env: &[(String, String)], log: &Path) -> Option<Vec<(String, String)>> {
        // an earlier run's log and records must not survive a task that fails before creating its own
        let results = results_path(log);
        for f in [log, &results] {
            match std::fs::remove_file(f) {
                Err(e) if e.kind() != std::io::ErrorKind::NotFound => panic!("cannot clear {}: {e}", f.display()),
                _ => {}
            }
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
            return None;
        }
        let text = std::fs::read_to_string(&results).unwrap_or_else(|e| panic!("cannot read {}: {e}", results.display()));
        let record = |l: &str| l.split_once('\t').map(|(k, v)| (k.to_string(), v.to_string())).unwrap_or_else(|| panic!("a result line with no tab: {l:?}"));
        Some(text.lines().map(record).collect())
    }

    fn spawn(start: Vec<(String, String)>) -> WorkerProc {
        let mut child = Command::new(std::env::current_exe().unwrap())
            .args(reentry())
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

/// `f(item, lane)` for every item on `lanes` threads, item `i` on lane `i % lanes`; the results in `items`' order. Fixed,
/// not the next free lane: a lane's worker carries its lemma file and memos into its next item, so a timing-picked lane
/// made an item's work counts depend on which items ran before it (2026-10-24 review, `work-assoc-*`: loop 3 changed
/// lanes in 4 of 10 salts).
fn run_lanes<T: Sync, R: Send>(items: &[T], lanes: usize, f: impl Fn(&T, usize) -> R + Sync) -> Vec<R> {
    let lanes = lanes.max(1);
    let out: Vec<std::sync::Mutex<Option<R>>> = items.iter().map(|_| std::sync::Mutex::new(None)).collect();
    std::thread::scope(|s| {
        for lane in 0..lanes {
            let (out, f) = (&out, &f);
            s.spawn(move || {
                for i in (lane..items.len()).step_by(lanes) {
                    *out[i].lock().unwrap() = Some(f(&items[i], lane));
                }
            });
        }
    });
    out.into_iter().map(|m| m.into_inner().unwrap().unwrap()).collect()
}

/// Every item runs once, its result lands at its own index, item `i` runs on lane `i % lanes` whatever the timing, and
/// the lanes run items at once.
#[test]
fn run_lanes_keeps_order_and_overlaps() {
    let busy = std::sync::atomic::AtomicUsize::new(0);
    let (peak, items) = (std::sync::atomic::AtomicUsize::new(0), (0..12).collect::<Vec<usize>>());
    let out = run_lanes(&items, 3, |&i, lane| {
        let now = busy.fetch_add(1, std::sync::atomic::Ordering::SeqCst) + 1;
        peak.fetch_max(now, std::sync::atomic::Ordering::SeqCst);
        // hold the lane until another lane is busy too (or a deadline), so overlap is observed, not hoped for
        let t0 = std::time::Instant::now();
        while peak.load(std::sync::atomic::Ordering::SeqCst) < 2 && t0.elapsed() < std::time::Duration::from_secs(5) {
            std::thread::yield_now();
        }
        busy.fetch_sub(1, std::sync::atomic::Ordering::SeqCst);
        (i * 10, lane)
    });
    assert_eq!(out.iter().map(|r| r.0).collect::<Vec<_>>(), items.iter().map(|i| i * 10).collect::<Vec<_>>());
    assert_eq!(out.iter().map(|r| r.1).collect::<Vec<_>>(), items.iter().map(|i| i % 3).collect::<Vec<_>>());
    assert!(peak.into_inner() >= 2, "lanes never overlapped");
    assert_eq!(run_lanes(&[] as &[usize], 2, |&i, _| i), Vec::<usize>::new());
}

fn append(path: &Path, text: &str) {
    std::fs::OpenOptions::new().create(true).append(true).open(path).unwrap().write_all(text.as_bytes()).unwrap();
}

/// A machine-state line on stderr (about 2 s), logged pieces in `<out>/machine_state_<when>.log`: `RTP` and `CPU` are
/// machine-wide, so read here; `lockpriv` and `pages` belong to the children's process and environment, so a worker
/// task (`machine::pages_line`, with the children's `env`) reports them. `MACHINE_STATE=0` skips it, in a loop or a sweep.
fn machine_state(when: &str, env: &[(String, String)], worker: &Worker, out: &Path) {
    if !Setup::process().flag("MACHINE_STATE", true) {
        return;
    }
    std::fs::create_dir_all(out).unwrap();
    let log = out.join(format!("machine_state_{when}.log"));
    let records = worker.run("machine::pages_line", env, &log).unwrap_or_default();
    let pages = records.iter().find(|(k, _)| k == "pages").map_or("pages unavailable", |(_, v)| v.as_str());
    eprintln!("machine at {when}: machine state: {} {pages}", crate::machine::rtp_cpu());
}

/// Prints the task's variable `k` for each name in `ECHO` (a comma list), also handing each to the driver as a result record, and a
/// nonce unique to this process; counts one `op` when `ECHO_WORK=1` and panics when `ECHO_PANIC=1`. A task for `worker_runs_tasks`.
#[test]
#[ignore]
fn env_echo() {
    env_echo_task(&Setup::process())
}

fn env_echo_task(setup: &Arc<Setup>) {
    static NONCE: std::sync::OnceLock<u128> = std::sync::OnceLock::new();
    let nonce = NONCE.get_or_init(|| std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos());
    for k in setup.var("ECHO").unwrap_or("").split(',').filter(|k| !k.is_empty()) {
        println!("ECHO {k}={}", setup.var(k).unwrap_or("<unset>"));
        setup.result(k, setup.var(k).unwrap_or("<unset>"));
    }
    println!("ECHO nonce={nonce}");
    if setup.flag("ECHO_WORK", false) {
        crate::work::count(crate::work::Site::Op);
    }
    assert!(!setup.flag("ECHO_PANIC", false), "env_echo panicked on request");
}

/// A worker runs each task with its own environment, log and result records, leaks no variable or record from one task to
/// the next (task 10 reuses task 9's log; task 1's count is not in task 2's WORK line), starts afresh
/// after a failed task, and is replaced when a task's process-start variables differ. Starts processes:
/// `cargo test --release -p church-bv --lib driver::worker_runs_tasks -- --exact --ignored --nocapture`.
#[test]
#[ignore]
fn worker_runs_tasks() {
    let dir = std::env::temp_dir().join(format!("worker_runs_tasks_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let kv = |k: &str, v: &str| (k.to_string(), v.to_string());
    let log = |i: usize| dir.join(format!("{i}.log"));
    let w = Worker::new();
    let records = [
        w.run("driver::env_echo", &[kv("ECHO", "A,B,C"), kv("A", "1"), kv("C", "x=y"), kv("ECHO_WORK", "1")], &log(1)),
        w.run("driver::env_echo", &[kv("ECHO", "A,B"), kv("B", "2")], &log(2)),
        w.run("driver::env_echo", &[kv("ECHO_PANIC", "1")], &log(3)),
        w.run("driver::env_echo", &[kv("ECHO", "A")], &log(4)),
        w.run("driver::no_such_task", &[], &log(5)),
        w.run("driver::env_echo", &[], &dir.join("missing").join("6.log")),
        w.run("driver::env_echo", &[kv("RUST_BACKTRACE", "0")], &log(7)),
        w.run("driver::env_echo", &[kv("RUST_BACKTRACE", "0")], &log(8)),
        w.run("driver::env_echo", &[], &log(9)),
        w.run("driver::env_echo", &[kv("ECHO", "B"), kv("B", "3")], &log(9)),
    ];
    let ok = records.iter().map(Option::is_some).collect::<Vec<_>>();
    assert_eq!(ok, [true, true, false, true, false, false, true, true, true, true]);
    let pairs = |r: &[(&str, &str)]| r.iter().map(|&(k, v)| kv(k, v)).collect::<Vec<_>>();
    assert_eq!(records[0], Some(pairs(&[("A", "1"), ("B", "<unset>"), ("C", "x=y")])));
    assert_eq!(records[1], Some(pairs(&[("A", "<unset>"), ("B", "2")])), "no record leaks from task 1");
    assert_eq!(records[9], Some(pairs(&[("B", "3")])), "task 10, on task 9's log, has only its own records");
    let text = |i: usize| std::fs::read_to_string(log(i)).unwrap();
    let echoes = |i: usize| text(i).lines().filter(|l| !l.starts_with("ECHO nonce=") && !l.starts_with("WORK ") && !l.starts_with("ENV ")).map(String::from).collect::<Vec<_>>();
    let nonce = |i: usize| text(i).lines().find_map(|l| l.strip_prefix("ECHO nonce=").map(String::from)).unwrap();
    assert_eq!(echoes(1), ["ECHO A=1", "ECHO B=<unset>", "ECHO C=x=y"]);
    // the setup's own reads, made as it is built (`Setup::var`'s ENV lines), are in the task's log, not on the task pipe
    assert!(text(1).lines().any(|l| l.starts_with("ENV ABLATE")), "1.log: {}", text(1));
    assert_eq!(echoes(2), ["ECHO A=<unset>", "ECHO B=2"], "no variable leaks from task 1");
    assert!(text(3).contains("env_echo panicked on request"), "3.log: {}", text(3));
    assert!(text(5).contains("no task driver::no_such_task"), "5.log: {}", text(5));
    assert_eq!(nonce(1), nonce(2), "tasks 1 and 2 ran in one worker");
    assert_ne!(nonce(2), nonce(4), "a fresh worker after the panic");
    assert_eq!(nonce(7), nonce(8), "tasks with the same process-start variables share a worker");
    assert_ne!(nonce(8), nonce(9), "a different RUST_BACKTRACE gets a fresh worker");
    for i in [1, 2, 4, 7, 8, 9] {
        let log = text(i);
        let lines: Vec<&str> = log.lines().filter(|l| !l.starts_with("ECHO ") && !l.starts_with("ENV ")).collect();
        let work = if i == 1 { "WORK interp=0 walk=0 match=0 op=1" } else { "WORK interp=0 walk=0 match=0 op=0" };
        assert_eq!(lines, [work], "{i}.log holds its task's lines and one WORK line, with only its own counts: {log}");
    }
    drop(w);
    std::fs::remove_dir_all(&dir).unwrap();
}

/// A task whose log cannot be cleared stops the driver, as the old per-child `File::create(log).unwrap()` did, rather than
/// leaving an earlier run's log or records to be read as this one's. The log is
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

/// Writes to `path` the laws a child with `env` (over this process's environment) would take from the stream sequence, as
/// `lhs = rhs` lines for `RULEMINER_LAWFILE`/`CHECK_LAWFILE`, and returns the variable that passes them. The sequence is
/// built once per process and salt (`stream_sequence`), where children would each rebuild it.
fn write_laws(setup: &Setup, env: &[(String, String)], path: &Path, var: &str) -> (String, String) {
    let get = |k: &str| env.iter().rev().find(|(kk, _)| kk == k).map_or_else(|| setup.var(k).map(str::to_owned), |(_, v)| Some(v.clone()));
    let laws: Vec<(String, Term, Term)> = window(&get).into_iter().map(|(a, b)| (String::new(), a, b)).collect();
    std::fs::write(path, laws_text(&laws)).unwrap();
    (var.to_string(), path.display().to_string())
}

/// The law window `get`'s `RULEMINER_*` variables select: phase `RULEMINER_PHASE`'s residue class of
/// `stream_sequence(RULEMINER_SHUFFLE)` (spec §9, plan R1).
fn window(get: &dyn Fn(&str) -> Option<String>) -> Vec<(Term, Term)> {
    let seq = stream_sequence(num(get, "RULEMINER_SHUFFLE", 0), STREAM_LEVELS);
    residue(&seq, num(get, "RULEMINER_PHASE", 0), num(get, "RULEMINER_SKIP", 0), num(get, "RULEMINER_LAWS", 250))
}

/// `cfg`'s value of the child variable `k`: its `env`, then this process's, as `run_loop`'s children read it.
fn cfg_var(cfg: &LoopCfg, k: &str) -> Option<String> {
    cfg.env.iter().rev().find(|(kk, _)| kk == k).map_or_else(|| Setup::process().var(k).map(str::to_owned), |(_, v)| Some(v.clone()))
}

/// The laws a child of `cfg` takes at phase `phase`: `laws` of them from `skip`, through the variables `run_loop` gives its
/// children.
fn window_laws(cfg: &LoopCfg, phase: usize, skip: usize, laws: usize) -> Vec<(Term, Term)> {
    let env = |k: &str| match k {
        "RULEMINER_PHASE" => Some(phase.to_string()),
        "RULEMINER_SKIP" => Some(skip.to_string()),
        "RULEMINER_LAWS" => Some(laws.to_string()),
        _ => cfg_var(cfg, k),
    };
    window(&env)
}

/// The laws `cfg`'s loop serves, and its mines mine: its K batches of B from OFFSET.
fn served_laws(cfg: &LoopCfg) -> Vec<(Term, Term)> {
    window_laws(cfg, cfg.sphase, cfg.offset, cfg.b * cfg.k)
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

/// The filter chain (spec §1) as a predicate: it keeps a law that is not trivial after normalizing (a trivial law follows
/// from equalities of its subterms, which may be served laws), is no twin of a law in `served` or `held` (so no held-out
/// law reaches a mine) and has no served law's skeleton.
fn filter(served: &[(Term, Term)], held: &[(Term, Term)]) -> impl Fn(&(Term, Term)) -> bool {
    let keys: hashbrown::HashSet<(Term, Term)> = served.iter().chain(held).filter_map(|(a, b)| twin_key(a, b)).collect();
    let skels: hashbrown::HashSet<String> = served.iter().map(skeleton).collect();
    move |l| twin_key(&l.0, &l.1).is_some_and(|k| !keys.contains(&k)) && !skels.contains(&skeleton(l))
}

/// Laws each mine takes from its scope's extras (n): fresh slices of 317-319 had held-out M 5291 against 6400 for the
/// earlier shared slices of the 2-growth phase 0, at 7.0 G of walk against 1.5 (run `2026-10-27-xgrid-f4950h`, gate
/// salts 1-3). Over the measured fresh arms (n 319-688) held-out M fell about 770 per e-fold of n with no knee and walk
/// grew about linearly in n, so n is a price (docs/tier-cycle/ "Count and slicing"); nothing below 319 was measured.
/// The variable `EXTRAS_N` overrides it.
const EXTRAS_N: usize = 319;

/// Draws one scope's extras (spec §1-3; docs/tier-cycle/ "Count and slicing"): the stream sequence at the scope's
/// salt (+ 1000 × `GEN_DRAW`, default 0) grown as deep as the deepest held-out band (`held_levels`), every phase and
/// size, the first laws the filter keeps against the laws `scope`'s loops serve and the held-out laws, n (`EXTRAS_N`)
/// for each mine in fresh slices. Sets each loop's `extras` and `extra_at`, or says by how much the sequence is short.
fn scope_extras(setup: &Setup, scope: &mut [LoopCfg]) -> Result<(), String> {
    use crate::classes::{held_laws, held_levels, HELD_BANDS};
    let served: Vec<(Term, Term)> = scope.iter().flat_map(served_laws).collect();
    let held: Vec<(Term, Term)> = HELD_BANDS.into_iter().flat_map(held_laws).collect();
    let c = scope[0].clone();
    let salt = num(&|k| cfg_var(&c, k), "RULEMINER_SHUFFLE", 0) + 1000 * setup.or("GEN_DRAW", 0usize);
    let plan = crate::miner::ExtrasPlan::from_vars(setup, EXTRAS_N)?;
    let (n, pool, mines) = (plan.n, plan.pool, c.mines.len());
    // built once per process and salt (its `STREAMS` lines give the time)
    let deep = stream_sequence(salt, held_levels(HELD_BANDS.into_iter().max().unwrap()));
    let keep = filter(&served, &held);
    // with `EXTRAS_SELECT` each mine gets its whole pool and the miner keeps n (`ExtrasPlan::child_env`, `run_loop`)
    let per_mine = plan.per_mine();
    let laws: Vec<(Term, Term)> = deep.iter().filter(|l| keep(l)).take(scope.len() * mines * per_mine).copied().collect();
    let at = extra_slices(laws.len(), scope.len(), mines, per_mine).map_err(|short| {
        format!("{}: the extras sequence of {} laws keeps {}, {short} short of {} loops x {mines} mines x POOL {pool} x n {n}", c.out.display(), deep.len(), laws.len(), scope.len())
    })?;
    println!("GEN {}: n {n}, pool {pool}, select {:?}, {} laws from a sequence of {}", c.out.display(), plan.by, laws.len(), deep.len());
    let laws = std::sync::Arc::new(laws);
    for (i, cfg) in scope.iter_mut().enumerate() {
        cfg.extras = laws.clone();
        cfg.extra_at = at[i * mines..(i + 1) * mines].to_vec();
        cfg.plan = plan.clone();
    }
    Ok(())
}

/// One loop; its children share the lemma file `lemmas`, which the caller owns (creates nothing, deletes it when done).
fn run_loop(setup: &Setup, cfg: &LoopCfg, lemmas: &Path, worker: &Worker) -> Summary {
    let (out, rules) = (&cfg.out, cfg.out.join("rules.txt"));
    std::fs::create_dir_all(out).unwrap();
    let s = |v: usize| v.to_string();
    let mut common: Vec<(String, String)> = [
        ("RULEMINER_PHASE", s(cfg.sphase)),
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
    // the mine `cfg.mines[slot]`
    let mine = |slot: usize| {
        let Mine { skip, laws, ref name, .. } = cfg.mines[slot];
        let log = out.join(format!("mine_{name}.log"));
        let mut env = with(&[
            ("RULEMINER_THREADS", s(cfg.threads)),
            ("RULEMINER_ROUNDS", s(cfg.rounds)),
            ("RULEMINER_SKIP", s(skip)),
            ("RULEMINER_LAWS", s(laws)),
            ("RULEMINER_BASE", rules.display().to_string()),
        ]);
        // before the law file: the extras below append to `env.last()`
        env.push(("JOIN_VISIT".into(), mine_join_visit(setup)));
        env.push(write_laws(setup, &env, &out.join(format!("laws_mine_{name}.txt")), "RULEMINER_LAWFILE"));
        if let Some(at) = cfg.extra_at.get(slot) {
            let extra: String = cfg.extras[at.clone()].iter().map(|l| law_text(l) + "\n").collect();
            let plan = &cfg.plan;
            println!("GEN_EXTRA {name}: {} laws, keep {}", at.len(), if plan.by.is_some() { plan.n } else { at.len() });
            std::fs::write(out.join(format!("laws_extra_{name}.txt")), &extra).unwrap();
            let lawfile = env.last().unwrap().1.clone();
            let served = crate::search::read_named_laws(&lawfile).len();
            append(Path::new(&lawfile), &extra);
            // the miner reads the pool from line `served` and keeps `plan.n` of it; the dump is a switch of the miner (`MinerConfig::pool_dump`)
            env.extend(plan.child_env(served, &out.join(format!("dump_{name}"))));
        }
        let records = worker.run("search::rule_miner", &env, &log).unwrap_or_else(|| panic!("rule_miner failed (see {})", log.display()));
        // the chosen rules
        let chosen: String = records.iter().filter(|(k, _)| k == "chosen").map(|(_, r)| format!("{r}\n")).collect();
        append(&rules, &chosen);
    };
    // (M, laws, laws that used up the rule budget, laws joined, terms the join reached, class-table replacements used) of the batch at `skip`
    let serve = |skip: usize| {
        let log = out.join(format!("serve_{skip}.log"));
        let mut env = with(&[("CHECK_FAST", s(cfg.check_fast as usize)), ("RULEMINER_SKIP", s(skip)), ("RULEMINER_LAWS", s(cfg.b)), ("CHECK_RULES", rules.display().to_string())]);
        env.push(write_laws(setup, &env, &out.join(format!("laws_serve_{skip}.txt")), "CHECK_LAWFILE"));
        let records = worker.run("search::rule_set_kernel_check", &env, &log).unwrap_or_else(|| panic!("rule_set_kernel_check failed (see {})", log.display()));
        let count = |key: &str| -> usize {
            let v = records.iter().find(|(k, _)| k == key).map(|(_, v)| v).unwrap_or_else(|| panic!("no {key} record (see {})", log.display()));
            v.parse().unwrap_or_else(|_| panic!("record {key} is not a count: {v}"))
        };
        // laws kernel-checked (`free` of them with no whole-term machine proof), not proved, out of rule budget, joined
        let (n, k, p, x, j, r, cl) = (count("proved"), count("free"), count("none"), count("exhausted"), count("joined"), count("reached"), count("classes"));
        (n - k + p, n + p, x, j, r, cl)
    };
    match &cfg.warm {
        Some(w) => {
            std::fs::copy(w, &rules).unwrap_or_else(|e| panic!("WARM_RULES {}: {e}", w.display()));
        }
        _ => std::fs::write(&rules, "").unwrap(),
    }
    std::fs::write(out.join("m.tsv"), "").unwrap();
    // the mines after `served` batches
    let mines_after = |served: usize| (0..cfg.mines.len()).filter(|&i| cfg.mines[i].at == served).for_each(&mine);
    mines_after(0);
    let (mut ms, mut exhausted, mut joined, mut reached) = (vec![], 0, 0, 0);
    for r in 0..cfg.k {
        let (skip, t0) = (cfg.offset + r * cfg.b, std::time::Instant::now());
        let (m, laws, ex, j, rc, cl) = serve(skip);
        append(&out.join("m.tsv"), &format!("{r}\t{m}\t{laws}\t{}\t{}\t{ex}\t{j}\t{rc}\t{cl}\n", count(), t0.elapsed().as_secs()));
        ms.push(m);
        (exhausted, joined, reached) = (exhausted + ex, joined + j, reached + rc);
        mines_after(r + 1);
    }
    let sum = Summary { total: ms.iter().sum(), ms, rules: count(), exhausted, joined, reached };
    println!("mode={} mines={} B={} K={} offset={} total_M={} rules={} exhausted={} joined={} reached={}", cfg.mode, cfg.mines.len(), cfg.b, cfg.k, cfg.offset, sum.total, sum.rules, sum.exhausted, sum.joined, sum.reached);
    sum
}

#[test]
#[ignore]
fn loop_stream() {
    run_loop_stream()
}

pub fn run_loop_stream() {
    let setup = &Setup::process();
    let worker = Worker::new();
    let cfg = LoopCfg::from_env(setup);
    machine_state("start", &cfg.env, &worker, &cfg.out);
    let lemmas = cfg.out.join("lemmas.bin");
    let _ = std::fs::remove_file(&lemmas);
    run_loop(setup, &cfg, &lemmas, &worker);
    let _ = std::fs::remove_file(&lemmas);
    machine_state("end", &cfg.env, &worker, &cfg.out);
}

#[test]
#[ignore]
fn sweep() {
    run_sweep()
}

pub fn run_sweep() {
    let setup = &Setup::process();
    let out = PathBuf::from(setup.var("SWEEP_OUT").expect("set SWEEP_OUT=<dir>"));
    std::fs::create_dir_all(&out).unwrap();
    let salt: usize = setup.or("SALT", 1);
    // Large pages off in the children: most are short, each pays the 64 MiB large-page commit up front, and a sweep with them
    // on cost 0.3-2.9 s more CPU and 60% more peak memory (docs/tier-cycle/, "How often the large-page stall hits a sweep").
    let env: Vec<(String, String)> = [("RULEMINER_FAST", "1".to_string()), ("RULEMINER_SHUFFLE", salt.to_string()), ("MIMALLOC_ALLOW_LARGE_OS_PAGES", "0".to_string())]
        .into_iter()
        .map(|(k, v)| (k.to_string(), v))
        .collect();
    let (b, k) = (100, 3);
    let base = |out: PathBuf, sphase: usize| LoopCfg {
        mines: schedule("loop", 0, b, k),
        mode: "loop".into(),
        out,
        sphase,
        b,
        k,
        offset: 0,
        // LOOP_THREADS: the scoring workers of the loops (the miner's choice does not depend on it,
        // docs/runs/2026-10-18/scripts/threads_check.sh)
        threads: setup.or("LOOP_THREADS", 6),
        rounds: usize::MAX,
        warm: None,
        check_fast: true,
        extras: Default::default(),
        extra_at: vec![],
        plan: Default::default(),
        env: env.clone(),
    };
    // the one stage: three cold loops on phases 1-3 of the streams (spec §10)
    let mut cfgs: Vec<LoopCfg> = (1..=3).map(|p| base(out.join(format!("cold_streams_streams_{p}_none")), p)).collect();
    // the extras are drawn before any work, so a list too short for its slices stops the sweep first
    if cfgs.iter().all(|c| takes_extras(c, setup.ablated("gen"))) {
        if let Err(e) = scope_extras(setup, &mut cfgs) {
            panic!("extras lists too short for their slices:\n{e}");
        }
    }
    // the loops run on `SWEEP_LANES` (default 2) lanes, loop i on lane i % lanes (`run_lanes`); 2 × 6 mining threads fit the 12-thread cap. A lane has its own
    // worker and lemma file (all its processes run this exe, so every statement in it was checked by this build; one shared
    // file would race on its save). SWEEP_LANES=1 for timings.
    let lanes: usize = setup.or("SWEEP_LANES", 2usize).max(1);
    let lemmas: Vec<PathBuf> = (0..lanes).map(|l| out.join(format!("lemmas_{l}.bin"))).collect();
    lemmas.iter().for_each(|l| drop(std::fs::remove_file(l)));
    let workers: Vec<Worker> = (0..lanes).map(|_| Worker::new()).collect();
    machine_state("start", &env, &workers[0], &out);
    let tsv = out.join("cold_streams.tsv");
    std::fs::write(&tsv, "").unwrap();
    let ran = run_lanes(&cfgs, lanes, |cfg, l| {
        let t0 = std::time::Instant::now();
        let s = run_loop(setup, cfg, &lemmas[l], &workers[l]);
        (s, t0.elapsed().as_secs())
    });
    for (cfg, (s, secs)) in cfgs.iter().zip(ran) {
        let ms: Vec<String> = s.ms.iter().map(|m| m.to_string()).collect();
        append(&tsv, &format!("streams\t{STREAM_STRIDE}-{}\tfrom_none\t{}\t{}\t{}\t{secs}\t{}\t{}\t{}\n", cfg.sphase, s.total, ms.join(","), s.rules, s.exhausted, s.joined, s.reached));
    }
    lemmas.iter().for_each(|l| drop(std::fs::remove_file(l)));
    machine_state("end", &env, &workers[0], &out);
    // this thread's own work (the stream sequence, the extras lists) and the lanes' (their tasks' lines are in their logs)
    println!("{}", crate::work::line(crate::work::take()));
}

#[test]
fn reentry_defaults_to_the_libtest_form() {
    assert_eq!(reentry(), ["driver::worker", "--exact", "--ignored", "--nocapture"]);
}

static REENTRY: std::sync::OnceLock<Vec<String>> = std::sync::OnceLock::new();

/// Declares how this exe is started as a worker (`Worker::spawn`'s arguments), once per process: the `church-bv` binary says
/// `["worker"]`; the test exe never declares and gets the libtest form.
pub fn declare_reentry(args: &[&str]) {
    declare_in(&REENTRY, args);
}

fn declare_in(cell: &std::sync::OnceLock<Vec<String>>, args: &[&str]) {
    cell.set(args.iter().map(|a| a.to_string()).collect()).expect("the worker's re-entry arguments are declared once");
}

#[test]
#[should_panic(expected = "declared once")]
fn a_second_reentry_declaration_panics() {
    let cell = std::sync::OnceLock::new();
    declare_in(&cell, &["worker"]);
    declare_in(&cell, &["worker"]);
}

fn reentry() -> Vec<String> {
    REENTRY.get().cloned().unwrap_or_else(|| ["driver::worker", "--exact", "--ignored", "--nocapture"].map(String::from).to_vec())
}
