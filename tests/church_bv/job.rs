//! A task's configuration (`Setup`) and one rewriting thread's state (`Job`), passed explicitly
//! (docs/superpowers/plans/2026-10-21-rewrite-context.md). A `driver::worker` task builds one `Setup`; the one-test process
//! uses `Setup::process()`. Each thread that rewrites owns one `Job` over its task's `Setup`.

use std::fmt::Display;
use std::str::FromStr;
use std::sync::atomic::{AtomicU64, Ordering::Relaxed};
use std::sync::{Arc, Mutex, OnceLock};

use tatic::kernel::{Expr, PExpr, Postulates, Scope};

use crate::rewrite::{JoinCost, JoinStoreUse, Pref, RewriteState, Rule, RuleKey, Rules, TableRule, Term};

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
    /// `RULESET`'s rules, the fixed rules and their table rows, built at first use (the driver process builds a `Setup`
    /// only to read configuration).
    rule_set: OnceLock<Vec<(Term, Term)>>,
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

    fn from_env(env: Env) -> Setup {
        let ablate = env.get("ABLATE").map(|v| v.split(',').map(String::from).collect()).unwrap_or_default();
        let mut s = Setup {
            env,
            ablate,
            nops: 0,
            results: Mutex::new(None),
            rule_set: OnceLock::new(),
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
    /// promoted, ruleset, a built-in rule's name, `prove_eq`'s eq_truth, eq_pos, shrmask, and the driver's gen). Parsed once:
    /// `rule_step` asks for every rule it tries, and reading the environment each time was 11% of a mine (docs/tier-cycle.md).
    pub fn ablated(&self, name: &str) -> bool {
        self.ablate.iter().any(|x| x == name)
    }

    /// How many of `OP_INFO` the miner enumerates: `sub` only with `MINER_SUB=1`.
    pub fn nops(&self) -> usize {
        self.nops
    }

    /// The mined rule set `RULESET` selects (`rewrite::build_rule_set`).
    pub fn rule_set(&self) -> &[(Term, Term)] {
        self.rule_set.get_or_init(|| crate::rewrite::build_rule_set(self.var("RULESET")))
    }

    /// The rules that do not change during the task (`rewrite::build_fixed_rules`).
    pub fn fixed_rules(&self) -> &[Rule] {
        self.fixed.get_or_init(|| crate::rewrite::build_fixed_rules(self))
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
    pub conflicts: Option<hashbrown::HashMap<Pref, u64>>,
    /// The lemmas bound as parameters so far, and the proofs that mention them.
    pub lemmas: Lemmas,
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
    /// A job with the built-in rules of `setup` alone, no preferences, both switches off.
    pub fn new(setup: Arc<Setup>) -> Job {
        let rules = Rules::new(&setup, vec![]);
        Job { id: NEXT_JOB.fetch_add(1, Relaxed), setup, rules, rw: RewriteState::default(), blocked: vec![], join_store: None, join_cost: JoinCost::default(), conflicts: None, lemmas: Lemmas::default() }
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

    /// `f` with `mined` in place of the job's mined rules, its preferences and switches kept (`with_rules`).
    pub fn with_mined<T>(&mut self, mined: Vec<(Term, Term)>, f: impl FnOnce(&mut Job) -> T) -> T {
        let rules = self.rules.with_mined(&self.setup, mined);
        self.with_rules(rules, f)
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
