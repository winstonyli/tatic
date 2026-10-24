//! A task's configuration (`Setup`) and one rewriting thread's state (`Job`), passed explicitly
//! (docs/superpowers/plans/2026-10-21-rewrite-context.md). A `driver::worker` task builds one `Setup`; the one-test process
//! uses `Setup::process()`. Each thread that rewrites owns one `Job` over its task's `Setup`.

use std::fmt::Display;
use std::str::FromStr;
use std::sync::atomic::{AtomicU64, Ordering::Relaxed};
use std::sync::{Arc, Mutex, OnceLock};

use tatic::kernel::{Expr, PExpr, Postulates, Scope};

use crate::rewrite::{Conflict, JoinCost, JoinStoreUse, RewriteState, Rule, RuleKey, Rules, TableRule, Term};

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
    /// The fixed rules and their table rows, built at first use (the driver process builds a `Setup` only to read
    /// configuration).
    fixed: OnceLock<Vec<Rule>>,
    fixed_table: OnceLock<Vec<TableRule>>,
    /// The lemma cache's file and counters (`lemma_cache`).
    pub lemmas: crate::lemma_cache::TaskCache,
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

    /// The process's setup with `pairs` over its environment and no result file: a test's job with a switch set.
    pub fn with_env(pairs: Vec<(String, String)>) -> Arc<Setup> {
        Arc::new(Setup::from_env(merge_env(process_env(), exe_env().as_deref(), &pairs)))
    }

    fn from_env(env: Env) -> Setup {
        let ablate = env.get("ABLATE").map(|v| v.split(',').map(String::from).collect()).unwrap_or_default();
        let mut s = Setup {
            env,
            ablate,
            nops: 0,
            results: Mutex::new(None),
            fixed: OnceLock::new(),
            fixed_table: OnceLock::new(),
            lemmas: Default::default(),
        };
        s.nops = if s.flag("MINER_SUB", false) { 5 } else { 4 };
        s
    }

    /// The environment variable `k`, or `None` when unset.
    pub fn var(&self, k: &str) -> Option<&str> {
        self.env.get(&*env_name(k)).map(String::as_str)
    }

    /// The environment variable `k` parsed as `T` (`parsed`).
    pub fn or<T: FromStr>(&self, k: &str, d: T) -> T {
        parsed(k, self.var(k), d)
    }

    /// The environment variable `k` as a switch: `d` when unset, off at `0`, on at any other value. Every church_bv switch
    /// reads this way.
    pub fn flag(&self, k: &str, d: bool) -> bool {
        self.var(k).map_or(d, |v| v != "0")
    }

    /// Whether the rewriter's rule `name` is switched off by `ABLATE` (comma list: comm, assoc, chain, tree, collapse, join,
    /// promoted, a built-in rule's name, the class table's normal form classes, `prove_eq`'s eq_truth, eq_pos,
    /// eq_classes, shrmask, and the driver's gen). Parsed once: `rule_step` asks for every rule it tries, and reading the
    /// environment each time was 11% of a mine (docs/tier-cycle.md).
    pub fn ablated(&self, name: &str) -> bool {
        self.ablate.iter().any(|x| x == name)
    }

    /// How many of `OP_INFO` the miner enumerates: `sub` only with `MINER_SUB=1`.
    pub fn nops(&self) -> usize {
        self.nops
    }

    /// The rules that do not change during the task (`rewrite::build_fixed_rules`).
    pub fn fixed_rules(&self) -> &[Rule] {
        self.fixed.get_or_init(|| crate::rewrite::build_fixed_rules())
    }

    /// `fixed_rules` as the rule table's rows.
    pub(crate) fn fixed_table(&self) -> &[TableRule] {
        self.fixed_table.get_or_init(|| self.fixed_rules().iter().map(|r| TableRule::new(r.name, r.lhs, r.rhs)).collect())
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

/// The value `v` of the variable `k` parsed as `T`, or `d` when unset. A value that does not parse stops the run: a typo
/// would otherwise mine under the default unseen.
pub fn parsed<T: FromStr>(k: &str, v: Option<&str>, d: T) -> T {
    v.map_or(d, |v| v.parse().unwrap_or_else(|_| panic!("{k}={v}: not a valid {}", std::any::type_name::<T>())))
}

#[test]
fn or_reads_a_number_or_its_default_and_stops_at_a_typo() {
    let s = Setup::from_env(merge_env([("N".to_string(), "12".to_string()), ("BAD".to_string(), "1O".to_string())].into_iter(), None, &[]));
    assert_eq!((s.or("N", 0usize), s.or("UNSET", 7usize)), (12, 7));
    let err = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| s.or("BAD", 0usize))).expect_err("a typo stops the run");
    let msg = err.downcast_ref::<String>().cloned().unwrap_or_default();
    assert!(msg.contains("BAD=1O"), "{msg}");
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
/// same configuration. The exe's path is canonical first: started by its 8.3 short path, `current_exe` names the short
/// file, and `<short>.env` does not exist.
fn exe_env() -> Option<String> {
    std::env::current_exe().and_then(std::fs::canonicalize).map(|mut p| { p.as_mut_os_string().push(".env"); p }).and_then(std::fs::read_to_string).ok()
}

/// `<exe>.env` is read when the exe is started by its 8.3 short path, as the ablations driver starts it. `current_exe`
/// then names the short file (`B_PROM~1.EXE`), whose `.env` does not exist: every B arm of the driver's ablations ran
/// unablated until 2026-10-24 (docs/tier-cycle.md, "Ablations of the class table").
#[cfg(windows)]
#[test]
fn exe_env_is_found_from_a_short_path() {
    use std::os::windows::process::CommandExt;
    let dir = std::env::temp_dir().join(format!("exe_env_short_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let exe = dir.join("long_exe_name.exe");
    std::fs::copy(std::env::current_exe().unwrap(), &exe).unwrap();
    std::fs::write(dir.join("long_exe_name.exe.env"), "EXE_ENV_PROBE=found\n").unwrap();
    let short = std::process::Command::new("cmd").raw_arg(format!("/c for %I in (\"{}\") do @echo %~sI", exe.display())).output().unwrap();
    let short = String::from_utf8_lossy(&short.stdout).trim().to_string();
    assert!(short.ends_with("LONG_E~1.EXE"), "no 8.3 name for {}: {short:?}", exe.display());
    let out = std::process::Command::new(&short)
        .args(["job::exe_env_probe", "--exact", "--ignored", "--nocapture"])
        .env("EXE_ENV_PROBE_RUN", "1")
        .stdin(std::process::Stdio::null())
        .output()
        .unwrap();
    let text = String::from_utf8_lossy(&out.stdout).to_string();
    std::fs::remove_dir_all(&dir).unwrap();
    assert!(text.lines().any(|l| l == "EXE_ENV_PROBE found"), "{text}");
}

/// `exe_env_is_found_from_a_short_path`'s child: prints what its `.env` set.
#[test]
#[ignore]
fn exe_env_probe() {
    if std::env::var_os("EXE_ENV_PROBE_RUN").is_some() {
        println!("EXE_ENV_PROBE {}", Setup::process().var("EXE_ENV_PROBE").unwrap_or("<unset>"));
    }
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

/// One rewriting thread's state over its task's `Setup`.
pub struct Job {
    id: u64,
    setup: Arc<Setup>,
    /// Replaced only by `with_rules`, which puts the outer rules back.
    rules: Rules,
    /// The rewriting in progress.
    pub rw: RewriteState,
    /// Rules being proved by `prove_rule` through the rewriter (`rewrite::proving`); `rule_step` skips them.
    pub blocked: Vec<RuleKey>,
    /// The join store this job feeds or reads (`JoinStore`), if any.
    pub join_store: Option<JoinStoreUse>,
    /// The join's cost so far, which M does not show (a joined law is free in M).
    pub join_cost: JoinCost,
    /// `RULE_CONFLICTS=1` (experiment): while `Some`, for each (rule that rewrote a term, later rule that would also have),
    /// how many terms; `print_rule_conflicts` lists them.
    pub conflicts: Option<hashbrown::HashMap<Conflict, u64>>,
    /// The lemmas bound as parameters so far, and the proofs that mention them.
    pub lemmas: Lemmas,
    /// The distinct class-table replacements `classes::Classes::step` used, each with a proof (spec decision 2: counted
    /// apart from M, as a learning cost).
    pub table_steps: hashbrown::HashSet<(Term, Term)>,
}

/// A job's lemmas: each is checked once and bound as a parameter of its statement (`rewrite::shared_lemma`), so a law
/// using it is checked against the parameter; `rewrite::discharge` ends them all. Everything here may mention the
/// parameters, so it lives and ends with them.
#[derive(Default)]
pub struct Lemmas {
    /// `shared_lemma`'s (parameter, statement) by key.
    pub bound: hashbrown::HashMap<String, (PExpr, PExpr)>,
    /// The parameters' builder and, per lemma, its scope and proof (`None`: a statement loaded from `LEMMA_CACHE`). A
    /// proof may use the lemmas bound before it (a mined rule proved through a machine proof uses its case lemmas).
    pub params: Option<(Postulates, Vec<(Scope, Option<PExpr>)>)>,
    /// `machine::add_tree_law` results (a proof over the parameters, or none) by width, variable count and the two terms:
    /// the rewriter asks for the same pair again for every law and every mined candidate that reaches the same subterm.
    pub tree_laws: hashbrown::HashMap<(usize, usize, Term, Term), Option<(PExpr, PExpr)>>,
}

impl Lemmas {
    /// Whether `e : ty`, against the parameters bound so far.
    pub fn holds(&self, e: &Expr, ty: &Expr) -> Result<(), String> {
        match &self.params {
            Some((ps, ..)) => ps.check_open(e, ty),
            None => crate::encoding::holds(e, ty),
        }
    }
    /// `holds`, panicking with `name` when it fails.
    pub fn ck(&self, name: &str, e: &Expr, ty: &Expr) {
        crate::encoding::checked(name, self.holds(e, ty))
    }
}

/// The next `Job::id`: unique in the process, so `Job::with_rules` can tell a job from its replacement.
static NEXT_JOB: AtomicU64 = AtomicU64::new(0);

impl Job {
    /// A job with the built-in rules of `setup` alone, both switches off.
    pub fn new(setup: Arc<Setup>) -> Job {
        let rules = Rules::new(&setup, vec![]);
        Job { id: NEXT_JOB.fetch_add(1, Relaxed), setup, rules, rw: RewriteState::default(), blocked: vec![], join_store: None, join_cost: JoinCost::default(), conflicts: None, lemmas: Lemmas::default(), table_steps: Default::default() }
    }

    pub fn setup(&self) -> &Arc<Setup> {
        &self.setup
    }

    pub fn rules(&self) -> &Rules {
        &self.rules
    }

    /// `f` with `rules` installed; the job's rules are put back after. Panics if `f` left this job holding other rules,
    /// or swapped it for another job.
    pub fn with_rules<T>(&mut self, rules: Rules, f: impl FnOnce(&mut Job) -> T) -> T {
        let (id, outer) = (self.id, std::mem::replace(&mut self.rules, rules));
        let installed = self.rules.clone();
        let out = f(self);
        assert!(self.id == id && self.rules.is(&installed), "a job's rules were replaced outside with_rules");
        self.rules = outer;
        out
    }

    /// `f` with `mined` in place of the job's mined rules, its switches kept (`with_rules`).
    pub fn with_mined<T>(&mut self, mined: Vec<(Term, Term)>, f: impl FnOnce(&mut Job) -> T) -> T {
        let rules = self.rules.with_mined(&self.setup, mined);
        self.with_rules(rules, f)
    }

    /// Runs `f` with the class-table steps it takes counted apart, and keeps them (in `table_steps`) only when `f` returns
    /// `Some`: the replacements a closed law used (spec decision 2), whichever phase took them.
    pub fn steps_if_closed<R>(&mut self, f: impl FnOnce(&mut Job) -> Option<R>) -> Option<R> {
        let kept = std::mem::take(&mut self.table_steps);
        let r = f(self);
        let used = std::mem::replace(&mut self.table_steps, kept);
        if r.is_some() {
            self.table_steps.extend(used);
        }
        r
    }

    /// `f`, and what it spent from this job's budget and counters.
    pub fn spent<T>(&mut self, f: impl FnOnce(&mut Job) -> T) -> (T, Spent) {
        let (budget, fallbacks, cycle_cuts, join) = (self.rw.budget, self.rw.fallbacks, self.rw.cycle_cuts, self.join_cost);
        let out = f(self);
        let spent = Spent { steps: budget - self.rw.budget, fallbacks: self.rw.fallbacks - fallbacks, cycle_cuts: self.rw.cycle_cuts - cycle_cuts, join: self.join_cost.since(join) };
        (out, spent)
    }

    /// `f` under a step budget of `budget`, and what it spent (`spent`); the caller's budget is put back after.
    pub fn measured<T>(&mut self, budget: i64, f: impl FnOnce(&mut Job) -> T) -> (T, Spent) {
        let outer = std::mem::replace(&mut self.rw.budget, budget);
        let out = self.spent(f);
        self.rw.budget = outer;
        out
    }
}

/// What a call spent (`Job::spent`): rule applications, whole-term machine proofs, cycle cuts and join work.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Spent {
    pub steps: i64,
    pub fallbacks: u64,
    pub cycle_cuts: u64,
    pub join: JoinCost,
}

#[test]
fn spent_counts_what_its_call_used_and_leaves_the_budget_used() {
    let job = &mut Job::new(Setup::process());
    job.rw.budget = 100;
    let ((), spent) = job.spent(|job| {
        (job.rw.budget, job.rw.fallbacks, job.rw.cycle_cuts, job.join_cost.met) = (93, job.rw.fallbacks + 2, job.rw.cycle_cuts + 1, 3);
    });
    assert_eq!(spent, Spent { steps: 7, fallbacks: 2, cycle_cuts: 1, join: JoinCost { met: 3, ..JoinCost::default() } });
    assert_eq!(job.rw.budget, 93);
}

#[test]
fn measured_runs_under_its_budget_and_puts_the_callers_back() {
    let job = &mut Job::new(Setup::process());
    job.rw.budget = 1234;
    let (inside, spent) = job.measured(crate::rewrite::LAW_STEPS, |job| {
        job.rw.budget -= 7;
        job.rw.budget
    });
    assert_eq!((inside, spent.steps, job.rw.budget), (crate::rewrite::LAW_STEPS - 7, 7, 1234));
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
fn var_reads_the_process_environment() {
    for k in ["PATH", "Path", "path"] {
        // names ignore case on Windows only
        let want = std::env::var(k).ok();
        assert_eq!(Setup::process().var(k), want.as_deref(), "{k}");
    }
    assert_eq!(Setup::process().var("CHURCH_BV_SURELY_UNSET"), None);
}

#[test]
fn a_switch_is_off_only_at_0_and_its_default_when_unset() {
    let s = Setup::from_env(merge_env([("Z".to_string(), "0".to_string()), ("O".to_string(), "1".to_string()), ("T".to_string(), "2".to_string())].into_iter(), None, &[]));
    for d in [false, true] {
        assert_eq!(s.flag("U", d), d);
    }
    assert!(!s.flag("Z", true));
    assert!(s.flag("O", false));
    assert!(s.flag("T", false)); // `== 1` read this as off
}

#[test]
fn with_rules_puts_the_outer_rules_back() {
    use crate::rewrite::parse_term;
    let s = Setup::process();
    let mut job = Job::new(s.clone());
    let outer = job.rules().clone();
    let inner = Rules::new(&s, vec![(parse_term("add(x, 0)"), parse_term("x"))]);
    let seen = job.with_rules(inner.clone(), |job| job.rules().is(&inner));
    assert!(seen && job.rules().is(&outer));
}

/// A test's switch: `with_env` lays its pairs over the process's environment.
#[test]
fn with_env_sets_a_switch() {
    let s = Setup::with_env(vec![("ABLATE".into(), "classes,eq_classes".into())]);
    assert!(s.ablated("classes") && s.ablated("eq_classes") && !s.ablated("comm"));
}

/// Table steps taken inside `steps_if_closed` are kept only when it returns `Some` (spec decision 2: a closed law's
/// steps), and the steps counted before it stay either way.
#[test]
fn steps_are_kept_only_for_a_closed_law() {
    use crate::rewrite::parse_term;
    let job = &mut Job::new(Setup::process());
    let (p, q) = ((parse_term("x"), parse_term("y")), (parse_term("y"), parse_term("x")));
    job.table_steps.insert(p);
    let open = job.steps_if_closed(|job| {
        job.table_steps.insert(q);
        None::<()>
    });
    assert!(open.is_none() && job.table_steps.len() == 1 && job.table_steps.contains(&p));
    let closed = job.steps_if_closed(|job| {
        job.table_steps.insert(q);
        Some(())
    });
    assert!(closed.is_some() && job.table_steps.contains(&p) && job.table_steps.contains(&q));
}

#[test]
#[should_panic(expected = "replaced outside with_rules")]
fn with_rules_catches_a_swapped_job() {
    let s = Setup::process();
    let (mut a, mut b) = (Job::new(s.clone()), Job::new(s.clone()));
    a.with_rules(Rules::new(&s, vec![]), |job| std::mem::swap(job, &mut b));
}

#[test]
fn every_job_has_its_own_id() {
    let s = Setup::process();
    assert_ne!(Job::new(s.clone()).id, Job::new(s).id);
}

/// State a church_bv source line holds outside `Setup` and `Job`, or a step around `Job`'s guards.
#[derive(Debug, PartialEq)]
enum Hidden<'a> {
    /// a static inside a `thread_local!` block
    ThreadLocal(&'a str),
    /// a process-wide mutable static (`static mut`, or one whose type names a lock, a once-cell or an atomic) other than
    /// a `SharedMemo`
    ProcessWide(&'a str),
    /// a whole job swapped or assigned (`mem::swap/replace/take(&mut job, ..)`, `*job = ..`), which would get past
    /// `with_rules`' identity check
    JobSwap,
    /// a job bound under another name than `job` (a parameter or field typed `Job`, `&Job` or `&mut Job`, or a `let` of
    /// `Job::new`), which `job_swap` could not follow
    JobAlias(&'a str),
}

/// The `static` declared on `line`: whether `mut`, its name and its type.
fn declared(line: &str) -> Option<(bool, &str, &str)> {
    let rest = ["pub(crate) static ", "pub static ", "static "].iter().find_map(|p| line.trim_start().strip_prefix(p))?;
    let (is_mut, rest) = rest.strip_prefix("mut ").map_or((false, rest), |r| (true, r));
    let (name, ty) = rest.split_once(':')?;
    Some((is_mut, name.trim(), ty))
}

/// Whether `line` swaps, replaces, takes or assigns a whole job (not one of its fields).
fn job_swap(line: &str) -> bool {
    let assigned = line.trim_start().strip_prefix("*job").is_some_and(|r| r.trim_start().strip_prefix('=').is_some_and(|r| !r.starts_with('=')));
    let moved = ["mem::swap(", "mem::replace(", "mem::take("].iter().any(|m| {
        line.split(m).skip(1).any(|arg| {
            let arg = arg.trim_start();
            let arg = arg.strip_prefix("&mut").map_or(arg, str::trim_start);
            let arg = arg.strip_prefix('*').unwrap_or(arg);
            arg.strip_prefix("job").is_some_and(|r| r.trim_start().starts_with([',', ')']))
        })
    });
    assigned || moved
}

/// The name a job is bound to on `line` when it is not `job`: a parameter or field typed `Job`, `&Job` or `&mut Job`, or a
/// `let` of `Job::new` (the whole pattern, for a tuple).
fn job_alias(line: &str) -> Option<&str> {
    let ident = |c: char| c.is_alphanumeric() || c == '_';
    for ty in [": &mut Job", ": &Job", ": Job"] {
        for (i, _) in line.match_indices(ty) {
            if line[i + ty.len()..].starts_with(ident) {
                continue;
            }
            let name = line[..i].rsplit(|c: char| !ident(c)).next().unwrap_or_default();
            if name != "job" {
                return Some(name);
            }
        }
    }
    let (pat, value) = line.trim_start().strip_prefix("let ")?.split_once('=')?;
    let value = value.trim_start().trim_start_matches('(');
    let value = value.strip_prefix("&mut").or_else(|| value.strip_prefix('&')).map_or(value, str::trim_start);
    let pat = pat.split(':').next()?.trim();
    let name = pat.strip_prefix("mut ").unwrap_or(pat);
    (value.starts_with("Job::new(") && name != "job").then_some(name)
}

/// What `text` (one source file) holds or does that `hidden_state_is_classified` checks, by line number. A static inside a
/// `thread_local!` block is a `ThreadLocal`, whatever its type; comment lines are skipped.
fn hidden(text: &str) -> Vec<(usize, Hidden<'_>)> {
    let mut out = vec![];
    // the brace depth inside a `thread_local!` block, 0 outside one
    let mut depth = 0i32;
    for (i, line) in text.lines().enumerate() {
        if line.trim_start().starts_with("//") {
            continue;
        }
        // a block opens on a line that starts with `thread_local!`; a one-line `thread_local! { static X: .. }` declares
        // after the brace
        let opens = line.trim_start().strip_prefix("thread_local!");
        let decl = declared(line).or_else(|| declared(opens?.trim_start().strip_prefix('{')?));
        if depth > 0 || opens.is_some() {
            if let Some((_, name, _)) = decl {
                out.push((i + 1, Hidden::ThreadLocal(name)));
            }
            depth += line.matches('{').count() as i32 - line.matches('}').count() as i32;
            continue;
        }
        if let Some((is_mut, name, ty)) = decl {
            let mutable = is_mut || ["Mutex", "RwLock", "Once", "LazyLock", "Atomic"].iter().any(|m| ty.contains(m));
            if mutable && !ty.contains("SharedMemo") {
                out.push((i + 1, Hidden::ProcessWide(name)));
            }
        }
        if job_swap(line) {
            out.push((i + 1, Hidden::JobSwap));
        }
        if let Some(name) = job_alias(line) {
            out.push((i + 1, Hidden::JobAlias(name)));
        }
    }
    out
}

#[test]
fn hidden_finds_thread_locals_process_wide_statics_and_job_swaps() {
    use Hidden::*;
    let tl = "thread_local! {\n    /// doc {\n    static A: Cell<u8> = const { Cell::new(0) };\n    static B: Mutex<u8> = Mutex::new(0);\n}\nstatic C: u8 = 0;";
    assert_eq!(hidden(tl), vec![(3, ThreadLocal("A")), (4, ThreadLocal("B"))]);
    assert_eq!(hidden("    thread_local! { static D: RefCell<u8> = Default::default(); }"), vec![(1, ThreadLocal("D"))]);
    assert_eq!(hidden("    static X: std::sync::OnceLock<u8> = std::sync::OnceLock::new();"), vec![(1, ProcessWide("X"))]);
    assert_eq!(hidden("pub static Y: [std::sync::atomic::AtomicU64; 3] = x;"), vec![(1, ProcessWide("Y"))]);
    assert_eq!(hidden("static mut Z: u8 = 0;"), vec![(1, ProcessWide("Z"))]);
    assert_eq!(hidden("static M: crate::task::SharedMemo<u8, std::sync::Arc<u8>> = SharedMemo::new();"), vec![]);
    assert_eq!(hidden("// static mut Z: u8 = 0;"), vec![]);
    assert_eq!(hidden("    let s = \"thread_local! { static E: u8 = 0; }\";"), vec![]);
    for swap in ["std::mem::swap(job, &mut other);", "let j = mem::replace(&mut *job, fresh);", "mem::take(&mut job)", "    *job = Job::new(s);"] {
        assert_eq!(hidden(swap), vec![(1, JobSwap)], "{swap}");
    }
    for field in ["std::mem::take(&mut job.lemmas)", "mem::replace(&mut job.rw, inner)", "*job == other", "*jobs = vec![]"] {
        assert_eq!(hidden(field), vec![], "{field}");
    }
    for (alias, name) in [
        ("fn f(j: &mut Job) {", "j"),
        ("fn g(&self, other: &Job, n: usize)", "other"),
        ("    owned: Job,", "owned"),
        ("    let (mut a, mut b) = (Job::new(s.clone()), Job::new(s));", "(mut a, mut b)"),
        ("    let mut fresh = Job::new(s);", "fresh"),
        ("    let other = &mut Job::new(s);", "other"),
    ] {
        assert_eq!(hidden(alias), vec![(1, JobAlias(name))], "{alias}");
    }
    for named in ["fn f(job: &mut Job, jobs: Vec<Job>) -> Job {", "let job = &mut Job::new(Setup::process());", "let out = run(&mut Job::new(s));", "kind: JobKind,"] {
        assert_eq!(hidden(named), vec![], "{named}");
    }
}

/// Every piece of hidden state in church_bv is classified: a thread-local is a pure memo on `THREAD_LOCAL` (D3 of
/// docs/superpowers/plans/2026-10-21-rewrite-context.md), a process-wide mutable static is a `SharedMemo` or on
/// `PROCESS_WIDE`, and only `job.rs` replaces a whole job or names one other than `job` (so the swap scan sees every job). Everything else a task or a rewrite carries lives in its `Setup`
/// or `Job`, so a `driver::worker` task never sees another task's state, nor a job another job's.
#[test]
fn hidden_state_is_classified() {
    const THREAD_LOCAL: [(&str, &str, &str); 7] = [
        ("rewrite.rs", "OP_CACHE", "op results by operator and operand values"),
        ("rewrite.rs", "BUFS", "scratch buffers, emptied before each use"),
        ("rewrite.rs", "TERMS", "enumerated terms by size and shape"),
        ("rewrite.rs", "CLOSED", "memo's closed library terms by key"),
        ("rewrite.rs", "COUNTING", "the one Counting plan, shared"),
        ("encoding.rs", "CONSTANTS", "gen_memo: closed constants by slot"),
        ("encoding.rs", "BODIES", "gen_memo: closed case-tree bodies by truth table"),
    ];
    const PROCESS_WIDE: [(&str, &str, &str); 7] = [
        ("rewrite.rs", "TABLE", "the term table: interning is pure"),
        ("classes.rs", "CLASSES", "the class table: built once from the baked-in key, pure"),
        ("rewrite.rs", "CACHE", "promoted_rules parses a constant table"),
        ("lemma_cache.rs", "ID", "the running exe's identity"),
        ("driver.rs", "NONCE", "env_echo's per-process nonce, process-wide on purpose"),
        ("job.rs", "PROCESS_SETUP", "the one-test process's Setup; tasks build their own"),
        ("job.rs", "NEXT_JOB", "job ids, unique per process on purpose"),
    ];
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/church_bv");
    let (mut bad, mut seen) = (vec![], vec![]);
    for entry in std::fs::read_dir(&dir).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_none_or(|e| e != "rs") {
            continue;
        }
        let file = path.file_name().unwrap().to_str().unwrap().to_string();
        let listed = |list: &[(&str, &str, &str)], name: &str| list.iter().any(|p| p.0 == file && p.1 == name);
        for (line, h) in hidden(&std::fs::read_to_string(&path).unwrap()) {
            let ok = match h {
                Hidden::ThreadLocal(name) => listed(&THREAD_LOCAL, name),
                Hidden::ProcessWide(name) => listed(&PROCESS_WIDE, name),
                Hidden::JobSwap | Hidden::JobAlias(_) => file == "job.rs",
            };
            if !ok {
                bad.push(format!("{file}:{line} {h:?}"));
            }
            if let Hidden::ThreadLocal(name) | Hidden::ProcessWide(name) = h {
                seen.push((file.clone(), name.to_string()));
            }
        }
    }
    assert!(bad.is_empty(), "hidden state that is not classified: {bad:?}");
    // a listed static that is gone leaves the list
    let stale: Vec<_> = THREAD_LOCAL.iter().chain(&PROCESS_WIDE).filter(|p| !seen.iter().any(|(f, n)| f == p.0 && n == p.1)).map(|p| p.1).collect();
    assert!(stale.is_empty(), "listed statics that no longer exist: {stale:?}");
}
