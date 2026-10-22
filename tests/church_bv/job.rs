//! A task's configuration (`Setup`) and one rewriting thread's state (`Job`), passed explicitly
//! (docs/superpowers/plans/2026-10-21-rewrite-context.md). A `driver::worker` task builds one `Setup`; the one-test process
//! uses `Setup::process()`. Each thread that rewrites owns one `Job` over its task's `Setup`.

use std::fmt::Display;
use std::str::FromStr;
use std::sync::atomic::{AtomicU64, Ordering::Relaxed};
use std::sync::{Arc, Mutex, OnceLock};

type Env = hashbrown::HashMap<String, String>;

/// A task's configuration, read once when it is built: its environment, and the values parsed from it on hot paths.
pub struct Setup {
    env: Env,
    /// `ABLATE`'s comma list.
    ablate: Vec<String>,
    /// `nops()`: how many of `OP_INFO` the miner enumerates.
    nops: usize,
    /// The task's result file (`result`); `None` in a process that runs one test.
    results: Mutex<Option<std::fs::File>>,
}

impl Setup {
    /// The one-test process's setup: the process's environment and `<exe>.env`, no task pairs, no result file.
    pub fn process() -> Arc<Setup> {
        static PROCESS_SETUP: OnceLock<Arc<Setup>> = OnceLock::new();
        PROCESS_SETUP.get_or_init(|| Arc::new(Setup::from_env(merge_env(process_env(), exe_env().as_deref(), &[])))).clone()
    }

    /// A `driver::worker` task's setup: the process's environment with the task's `pairs` over it, results to `results`.
    pub fn for_task(pairs: Vec<(String, String)>, results: std::fs::File) -> Arc<Setup> {
        let mut s = Setup::from_env(merge_env(process_env(), exe_env().as_deref(), &pairs));
        s.results = Mutex::new(Some(results));
        Arc::new(s)
    }

    fn from_env(env: Env) -> Setup {
        let ablate = env.get("ABLATE").map(|v| v.split(',').map(String::from).collect()).unwrap_or_default();
        let mut s = Setup { env, ablate, nops: 0, results: Mutex::new(None) };
        s.nops = if s.flag("MINER_SUB", false) { 5 } else { 4 };
        s
    }

    /// The environment variable `k`, or `None` when unset.
    pub fn var(&self, k: &str) -> Option<&str> {
        self.env.get(&*env_name(k)).map(String::as_str)
    }

    /// The environment variable `k` parsed as `T`, or `d` when unset or unparsable.
    pub fn or<T: FromStr>(&self, k: &str, d: T) -> T {
        self.var(k).and_then(|v| v.parse().ok()).unwrap_or(d)
    }

    /// The environment variable `k` as a switch: `d` when unset, off at `0`, on at any other value. Every church_bv switch
    /// reads this way.
    pub fn flag(&self, k: &str, d: bool) -> bool {
        self.var(k).map_or(d, |v| v != "0")
    }

    /// Whether the rewriter's rule `name` is switched off by `ABLATE` (comma list: comm, assoc, chain, tree, collapse, join,
    /// promoted, ruleset, a built-in rule's name, `prove_eq`'s eq_truth, eq_pos, shrmask, and the driver's gen).
    pub fn ablated(&self, name: &str) -> bool {
        self.ablate.iter().any(|x| x == name)
    }

    /// How many of `OP_INFO` the miner enumerates: `sub` only with `MINER_SUB=1`.
    pub fn nops(&self) -> usize {
        self.nops
    }

    /// Hands the driver one record of this task's outcome: a `key<TAB>value` line in the task's result file, which
    /// `Worker::run` returns, in order, as `(key, value)` pairs. Does nothing in a process that runs one test.
    pub fn result(&self, key: &str, value: impl Display) {
        use std::io::Write;
        let value = value.to_string();
        assert!(![key, value.as_str()].iter().any(|f| f.contains(['\t', '\n', '\r'])), "a result field holds a tab or a newline: {key:?} {value:?}");
        if let Some(f) = self.results.lock().unwrap_or_else(|e| e.into_inner()).as_mut() {
            writeln!(f, "{key}\t{value}").expect("write a task result");
        }
    }
}

/// `k` as the environment stores it: upper-cased on Windows, where names ignore case.
fn env_name(k: &str) -> std::borrow::Cow<'_, str> {
    if cfg!(windows) && k.bytes().any(|b| b.is_ascii_lowercase()) { k.to_ascii_uppercase().into() } else { k.into() }
}

/// The process's environment, leaving out names and values that are not Unicode.
fn process_env() -> impl Iterator<Item = (String, String)> {
    std::env::vars_os().filter_map(|(k, v)| Some((k.into_string().ok()?, v.into_string().ok()?)))
}

/// `<exe>.env`'s text (lines `KEY=VALUE`), so a profiler launcher that cannot pass env (the elevated Samply task) runs the
/// same configuration.
fn exe_env() -> Option<String> {
    std::env::current_exe().map(|mut p| { p.as_mut_os_string().push(".env"); p }).and_then(std::fs::read_to_string).ok()
}

/// The task's environment from its three sources, later ones over earlier: the process's, `<exe>.env` for names the
/// process does not set, then the task's pairs. Names are upper-cased on Windows.
fn merge_env(process: impl Iterator<Item = (String, String)>, exe_env: Option<&str>, task: &[(String, String)]) -> Env {
    let mut env: Env = process.map(|(k, v)| (env_name(&k).into_owned(), v)).collect();
    for (k, v) in exe_env.into_iter().flat_map(str::lines).filter_map(|l| l.split_once('=')) {
        env.entry(env_name(k.trim()).into_owned()).or_insert_with(|| v.trim().to_string());
    }
    for (k, v) in task {
        env.insert(env_name(k).into_owned(), v.clone());
    }
    env
}

/// One rewriting thread's state over its task's `Setup`. Tasks 4-7 of the plan move the rewriter's thread-locals here.
pub struct Job {
    id: u64,
    setup: Arc<Setup>,
}

/// The next `Job::id`: unique in the process, so `Job::with_rules` can tell a job from its replacement.
static NEXT_JOB: AtomicU64 = AtomicU64::new(0);

impl Job {
    pub fn new(setup: Arc<Setup>) -> Job {
        Job { id: NEXT_JOB.fetch_add(1, Relaxed), setup }
    }

    pub fn setup(&self) -> &Arc<Setup> {
        &self.setup
    }
}

#[test]
fn task_pairs_override_the_process_and_exe_env_fills_only_unset_names() {
    let p = [("A".to_string(), "proc".to_string()), ("B".to_string(), "proc".to_string())];
    let env = merge_env(p.into_iter(), Some("B=file\nC=file\n"), &[("A".into(), "task".into())]);
    assert_eq!((env["A"].as_str(), env["B"].as_str(), env["C"].as_str()), ("task", "proc", "file"));
}

#[test]
fn flags_are_off_only_at_zero() {
    let s = Setup::from_env(merge_env([("X".to_string(), "0".to_string()), ("Y".to_string(), "no".to_string())].into_iter(), None, &[]));
    assert_eq!((s.flag("X", true), s.flag("Y", false), s.flag("Z", true)), (false, true, true));
}

#[test]
fn every_job_has_its_own_id() {
    let s = Setup::process();
    assert_ne!(Job::new(s.clone()).id, Job::new(s).id);
}
