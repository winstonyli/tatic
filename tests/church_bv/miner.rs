//! The rule miner (`search::rule_miner`, search note section 36) in named parts: the laws and their stragglers (`laws`), the
//! candidates (`candidates`), their proofs (`Prover`), the evaluation of rule sets (`Scorer`), the greedy rounds and their
//! lookahead (`Rounds`), the preference phase (`prefs_phase`) and the closing report (`Rounds::report`).
use super::rewrite::Node;
use super::*;

/// A scored law: name, sides, the sides' normal forms under the base rules, its machine proofs there and the time taken.
type Scored = (String, Term, Term, [Term; 2], u64, std::time::Duration);

/// The phase clock: `phase(label)` prints the seconds since the previous mark.
struct Clock(std::cell::Cell<Instant>);

impl Clock {
    fn phase(&self, label: &str) {
        println!("RULEMINER time {label}: {:.1}s", self.0.replace(Instant::now()).elapsed().as_secs_f64());
    }
}

/// Every `RULEMINER_*` switch of `rule_miner`, read once (defaults in `new`), except the law window's (`RULEMINER_LAWS`,
/// `_SHAPE`, `_SHAPE_SALT`, `_PHASE`, `_STRIDE` and the like), which `family_laws` reads through the `env` it is given.
pub struct MinerConfig {
    /// `MULMINER_MAX`: largest constant in the mul family.
    pub max: u32,
    /// `RULEMINER_TRIALS`: candidate cap.
    pub trials: usize,
    /// `RULEMINER_PERM`: 0 strict rule order, 1 ties broken by `tie_greater`, 2 no order check.
    pub perm: usize,
    /// `RULEMINER_STEPS`: per-law rewrite budget once a base set is loaded.
    pub steps: usize,
    /// `RULEMINER_VARS`: variable cap of cross-side rules.
    pub vars: usize,
    /// `RULEMINER_ROUNDS`: greedy rounds (default no cap: the mine stops when no candidate gains; a cap trimmed general rules,
    /// docs/tier-cycle.md "cmp3d's library lost its general rules"; with `RULEMINER_SHOW=1`, 0 just lists the candidates).
    pub rounds: usize,
    /// `RULEMINER_THREADS`: scoring threads, clamped to 1..=12.
    pub threads: usize,
    /// `RULEMINER_ANY`, `_SHOW`, `_FAST`: switches (`Setup::flag`), off by default.
    pub any_op: bool,
    pub show: bool,
    pub fast: bool,
    /// `RULEMINER_FAMILY`: the law family (default `mul`); with `lawfile` it still sets the variable count.
    pub family: String,
    /// `RULEMINER_BASE=<file>`: rules (`lhs -> rhs` lines) and their preferences in force throughout (section 74).
    pub base: Option<String>,
    /// `RULEMINER_LAWFILE=<file>`: mine from these `lhs = rhs` lines (a proposer's band) instead of the family's window.
    pub lawfile: Option<String>,
    /// `RULEMINER_GUARD=<k>`: about k machine-free laws scored with the stragglers (default 120, 0 = off).
    pub guard: usize,
    /// `RULEMINER_EXTRA=<file>`: extra candidates (`lhs -> rhs` lines).
    pub extra: Option<String>,
    /// `RULEMINER_NODUPLHS` (switch, on by default): drop candidates whose left side already has a rule in `base`.
    pub no_dup_lhs: bool,
    /// `RULEMINER_PREFS` (switch, off by default): run the preference phase.
    pub prefs: bool,
    /// `RULEMINER_UNITS=<file>`: the base's drop units, read only with `prefs`.
    pub units: Option<String>,
}

impl MinerConfig {
    pub fn new(s: &Setup) -> Self {
        let flag = |k: &str| s.flag(k, false);
        let path = |k: &str| s.var(k).map(String::from);
        MinerConfig {
            max: s.or("MULMINER_MAX", 7) as u32,
            trials: s.or("RULEMINER_TRIALS", 400),
            perm: s.or("RULEMINER_PERM", 0),
            steps: s.or("RULEMINER_STEPS", 200),
            vars: s.or("RULEMINER_VARS", 4),
            rounds: s.or("RULEMINER_ROUNDS", usize::MAX),
            threads: s.or("RULEMINER_THREADS", 1).clamp(1, 12),
            any_op: flag("RULEMINER_ANY"),
            show: flag("RULEMINER_SHOW"),
            fast: flag("RULEMINER_FAST"),
            family: s.var("RULEMINER_FAMILY").unwrap_or("mul").into(),
            base: path("RULEMINER_BASE"),
            lawfile: path("RULEMINER_LAWFILE"),
            guard: s.or("RULEMINER_GUARD", 120),
            extra: path("RULEMINER_EXTRA"),
            no_dup_lhs: s.flag("RULEMINER_NODUPLHS", true),
            prefs: flag("RULEMINER_PREFS"),
            units: path("RULEMINER_UNITS"),
        }
    }
}

pub fn run(setup: &Arc<Setup>) {
    let job = &mut Job::new(setup.clone());
    tatic::kernel::scoped(|| {
        // the join store this mine feeds from this thread (`JoinStore`); the scoring workers read a copy of it
        set_join_store(Some(JoinStoreUse::Feed(JoinStore::default())));
        let clock = Clock(std::cell::Cell::new(Instant::now()));
        let _banner = MachineBanner::start(job, "RULEMINER");
        let _save = lemma_cache::Save(setup.clone());
        let cfg = MinerConfig::new(setup);
        // the stragglers are the laws left with the base's rules
        let base_text = cfg.base.as_ref().map(|f| std::fs::read_to_string(f).unwrap()).unwrap_or_default();
        let (base, base_prefs) = (parse_rules(&base_text), parse_prefs(&base_text));
        // P0: everything on this thread below runs under the base rules and preferences, apart from what installs its own
        let base_rules = job.rules().with_mined(setup, base.clone()).with_prefs(base_prefs.clone());
        job.with_rules(base_rules, |job| {
            let (laws, budget) = laws(job, &cfg, base.is_empty(), &clock);
            let (cands, rivals) = candidates(&laws, &cfg, &base);
            clock.phase("candidate generation");
            // keep candidates whose left side matches a subterm of some straggler's normalized terms
            let applicable = |l: &Term| {
                laws.stragglers.iter().any(|s| {
                    let mut subs = vec![];
                    s.3[0].subterms(&mut subs);
                    s.3[1].subterms(&mut subs);
                    subs.iter().any(|t| matches(l, t))
                })
            };
            let trials = cfg.trials;
            let cands: Vec<(Term, Term)> = cands.into_iter().filter(|(l, _)| applicable(l)).take(trials).collect();
            println!("RULEMINER {} applicable candidates (cap {trials})", cands.len());
            if cfg.show {
                for (l, r) in &cands {
                    println!("RULEMINER candidate: {} -> {}", l.show(), r.show());
                }
            }
            // each candidate is proved independently, on `RULEMINER_THREADS` workers; the proving reads the base rules and the step
            // budget of this thread, so the workers copy them. `RULEMINER_FAST` scores without rule proofs (`shared_lemma`), so there only a
            // round's winner is proved (`proved_lazily`), and an unprovable one gives way to the next best
            let rules = job.rules().mined().to_vec();
            let prover = |prefs| Prover { rules: rules.clone(), prefs, budget, n: laws.n };
            let provable: Vec<(Term, Term)> = if cfg.fast { cands.clone() } else { prover(None).filter(job, &cands, cfg.threads).into_iter().map(|i| cands[i]).collect() };
            println!("RULEMINER {} provable candidates of {} proposed", provable.len(), cands.len());
            clock.phase("provable filter");
            let scorer = Scorer::new(&laws, &cfg, base.clone());
            // also on a thread of its own (`Rounds::play`), so it installs the base preferences itself: the old code proved under
            // the ones every evaluation on this thread left installed, which were these
            let prover = prover(Some(base_prefs.clone()));
            let mut rounds = Rounds::new(&scorer, &prover, &provable, &rivals, &base_prefs, &cfg, &clock);
            let Chosen { chosen, covered, .. } = rounds.play(job);
            prefs_phase(job, &scorer, &chosen, &base, &base_prefs, &cfg, &clock);
            rounds.report(&covered);
        });
        set_join_store(None);
    });
}

/// The laws mined for: the stragglers (laws the base rules leave with a machine proof, or do not close) and a guard sample
/// of the machine-free ones, scored with them (`scored`: stragglers first, so `si < stragglers.len()` is a straggler).
struct Laws {
    stragglers: Vec<Scored>,
    scored: Vec<Scored>,
    guard_w: i64,
    n: usize,
    kv: usize,
}

/// The laws of `cfg` and their stragglers under the rules installed on this thread (P1, P2). The `i64` is the step budget
/// this thread is left with (Q5 of docs/superpowers/plans/2026-10-21-rewrite-context.md): the proofs of `Prover` run under it.
fn laws(job: &mut Job, cfg: &MinerConfig, base_empty: bool, clock: &Clock) -> (Laws, i64) {
    let max = cfg.max;
    let family = cfg.family.as_str();
    // `add3` laws have three variables (the candidate generator below still builds patterns over at most two)
    let (n, nv, kv) = (4usize, 2usize, if family_vars(&family) == 3 { 3usize } else { 2 });
    let fallbacks = || MACHINE_FALLBACKS.with(|c| c.get());
    // stragglers under the built-in rules
    let mut stragglers: Vec<Scored> = vec![];
    // a lawfile is a proposer's band (docs/tier-cycle.md)
    let laws = match &cfg.lawfile {
        Some(f) => read_named_laws(f),
        None => family_laws(job.setup(), &family, &|k: &str, d: usize| job.setup().or(k, d), n, nv, max),
    };
    clock.phase("law building");
    let mut unproved = 0usize;
    let mut clean: Vec<(String, Term, Term)> = vec![]; // laws that are already machine-free under the base rules (for `RULEMINER_GUARD`)
    // `RULEMINER_FAST` counts the base rules' machine proofs the way it scores candidates: without building them. Carry-over:
    // P1 runs under the base rules and preferences P0 installed
    let counting = job.rules().counting(cfg.fast);
    job.with_rules(counting, |job| {
        for (name, t1, t2) in laws.iter().cloned() {
            if !t1.is_law(&t2, kv) || [&t1, &t2].iter().any(|t| Machine::parse(t).is_some_and(|m| m.carries() > carry_cap(job))) {
                continue;
            }
            let before = fallbacks();
            let t = Instant::now();
            // base rules may loop; the step budget bounds them (the built-in rules never reach it)
            RULE_BUDGET.with(|b| b.set(if base_empty { i64::MAX / 2 } else { cfg.steps as i64 }));
            let r = rewrite_plan(job, n, kv, &t1, &t2);
            let took = t.elapsed();
            let fell = fallbacks() - before;
            // a law the rewriter cannot close at all counts as a straggler too (fixed once it is proved machine-free)
            unproved += r.is_none() as usize;
            let fell = if r.is_none() { fell.max(1) } else { fell };
            if r.is_none() || fell > 0 {
                RULE_BUDGET.with(|b| b.set(if base_empty { i64::MAX / 2 } else { cfg.steps as i64 }));
                let normal = [rewrite(job, &t1, n, kv).0, rewrite(job, &t2, n, kv).0];
                println!("RULEMINER straggler {name}: {} = {} ({fell} machine proofs, {took:?}{})", normal[0].show(), normal[1].show(), if r.is_none() { ", UNPROVED" } else { "" });
                stragglers.push((name, t1, t2, normal, fell, took));
            } else {
                clean.push((name, t1, t2));
            }
        }
    });
    // what the last law's rewriting left, carried to the proofs (nothing until then rewrites on this thread)
    let left = RULE_BUDGET.with(|b| b.get());
    let base_time: f64 = stragglers.iter().map(|s| s.5.as_secs_f64()).sum();
    println!("RULEMINER {family}: {} stragglers of {} laws, {:.1}s base ({unproved} unproved)", stragglers.len(), laws.len(), base_time);
    clock.phase("laws and stragglers");
    // `RULEMINER_GUARD=<k>` (default 120, 0 = off): about k of the already machine-free laws are scored with the stragglers, so a candidate that breaks them loses
    // the same 1000 per law as it gains per straggler fixed (the miner otherwise sees only the stragglers and cannot see a regression)
    let guard_k = cfg.guard;
    let mut scored = stragglers.clone();
    let mut guard_w = 1000i64; // each sampled guard law stands for clean/sampled laws, so a regression costs that many times 1000
    if guard_k > 0 && !clean.is_empty() {
        let (step, w) = guard_plan(clean.len(), guard_k);
        guard_w = w;
        for (name, t1, t2) in clean.iter().step_by(step) {
            scored.push((name.clone(), *t1, *t2, [*t1, *t2], 1, std::time::Duration::ZERO));
        }
        println!("RULEMINER guard: {} machine-free laws scored of {} (weight {guard_w} each)", scored.len() - stragglers.len(), clean.len());
    }
    (Laws { stragglers, scored, guard_w, n, kv }, left)
}

/// The candidate rules for the stragglers (P3, P4), one per left side, and the other right sides of each left side (`rivals`).
fn candidates(laws: &Laws, cfg: &MinerConfig, base: &[(Term, Term)]) -> (Vec<(Term, Term)>, hashbrown::HashMap<Term, Vec<(Term, Term)>>) {
    let (n, kv, stragglers) = (laws.n, laws.kv, &laws.stragglers);
    // RULEMINER_PERM=1: ties in the rule order are broken by `tie_greater` (reassociation rules; section 70), 2: no order check; the step budget
    // and the same-term check in `rule_step` still back up termination, and soundness is unaffected
    let ok_order = |l: &Term, r: &Term| match cfg.perm {
        0 => rule_order_ok(l, r),
        1 => rule_order_or_tie(l, r),
        _ => true, // 2: no order check at all (the miner's own cross-side rules are not ordered either)
    };
    // goal-directed candidates: abstract each arithmetic subterm of a straggler's normalized terms into a pattern over
    // at most two variables (cutting subterms into variables), and look for a smaller term over the same variables
    // with the same values at width 4 (a pool of all terms up to 5 nodes, indexed by value)
    let psize = 5;
    let mut by_size: Vec<Vec<Term>> = vec![vec![]; psize + 1];
    by_size[1] = vec![Term::v(0), Term::v(1), Term::ZERO, Term::ONES];
    for sz in 2..=psize {
        let mut level = vec![];
        for x in &by_size[sz - 1] {
            level.push(Term::op(SHL1, *x, Term::ZERO));
            level.push(Term::op(SHR1, *x, Term::ZERO));
        }
        for i in 1..sz - 1 {
            for l in &by_size[i] {
                for r in &by_size[sz - 1 - i] {
                    for o in [0usize, 1, 2, 3, 4] {
                        level.push(Term::op(o, *l, *r));
                    }
                }
            }
        }
        by_size[sz] = level;
    }
    // the pool's terms and the patterns looked up in it use at most two variables (`abstractions(sub, 2)`), so signatures over
    // two give the same equalities as over `kv`, at 256 bytes instead of 4096 for the three-variable families
    let mut memo = ValueMemo::exhaustive(n, 2);
    let mut index: hashbrown::HashMap<Vec<u8>, Vec<Term>> = Default::default();
    for t in by_size.iter().flatten() {
        index.entry(memo.values(t).to_vec()).or_default().push(*t);
    }
    // `lt` terms (one-bit values) only as roots, indexed apart: their 0/1 values must not meet the n-bit constants
    let mut index_lt: hashbrown::HashMap<Vec<u8>, Vec<Term>> = Default::default();
    for a in by_size.iter().take(4).flatten() {
        for b in by_size.iter().take(4).flatten() {
            let t = Term::op(LT, *a, *b);
            index_lt.entry(memo.values(&t).to_vec()).or_default().push(t);
        }
    }
    println!("RULEMINER pool of {} terms, {} distinct functions", by_size.iter().map(|v| v.len()).sum::<usize>(), index.len());
    // RULEMINER_ANY=1: also abstract subterms without add/sub (constant folding inside shifts and bitwise nodes)
    let any_op = cfg.any_op;
    // patterns seen (`None`), and cross-side rules seen (`Some(rhs)`)
    let mut seen_pat: hashbrown::HashSet<(Term, Option<Term>)> = Default::default();
    let mut cands: Vec<(Term, Term)> = vec![];
    for st in stragglers {
        let mut subs = vec![];
        st.3[0].subterms(&mut subs);
        st.3[1].subterms(&mut subs);
        for sub in subs.iter().filter(|t| matches!(*t.node(), Node::Op(LT, ..)) || (any_op || t.uses_add()) && t.size() >= if any_op { 2 } else { 3 }) {
            for (pat, _) in abstractions(sub, 2) {
                let Node::Op(..) = *pat.node() else { continue };
                if !seen_pat.insert((pat, None)) || pat.size() > 9 {
                    continue;
                }
                let is_lt = matches!(*pat.node(), Node::Op(LT, ..));
                let Some(group) = (if is_lt { &index_lt } else { &index }).get(memo.values(&pat)) else { continue };
                let uses = |t: &Term, v: usize| t.has_var(v);
                let _ = is_lt;
                for r in group.iter().filter(|r| ok_order(&pat, r) && (0..2).all(|v| !uses(r, v) || uses(&pat, v))) {
                    cands.push((pat, *r));
                }
            }
        }
    }
    // cross-side candidates: a subterm of one normalized side and a subterm of the other with the same value, both
    // abstracted by the same cuts (up to four variables): the rule `abstract(s) -> abstract(s')`
    let cross_cap = cfg.vars;
    for st in stragglers {
        let (mut sl, mut sr) = (vec![], vec![]);
        st.3[0].subterms(&mut sl);
        st.3[1].subterms(&mut sr);
        for (xs, ys) in [(&sl, &sr), (&sr, &sl)] {
            for x in xs.iter().filter(|t| t.uses_add() && t.size() >= 3 && t.size() <= 13) {
                for y in ys.iter().filter(|t| t.size() <= 13 && *t != x) {
                    if !(1..=4).all(|w| x.plausibly_equals(y, w, kv)) {
                        continue;
                    }
                    for (pat, cuts) in abstractions(x, cross_cap) {
                        let Node::Op(..) = *pat.node() else { continue };
                        if cuts.len() <= 2 || pat.size() > 13 {
                            continue; // up to two variables is the pool route's job
                        }
                        // express y with the same cuts, through placeholders V(4+j)
                        let mut yy = *y;
                        for (j, c) in cuts.iter().enumerate() {
                            yy = replace_term(&yy, c, &Term::v(4 + j));
                        }
                        // renumbered only when bare: a cut-free variable below 4 has no index to take
                        if !bare(&yy) {
                            continue;
                        }
                        let rhs = renum_placeholders(&yy);
                        // `x = y` holds for the straggler's variables, but the cuts become free variables, so the rule itself is checked:
                        // one that only held through a relation between the cuts would be scored every round and then fail its proof
                        if yy.size() < pat.size() + 4 && seen_pat.insert((pat, Some(rhs))) && (1..=4).all(|w| pat.plausibly_equals(&rhs, w, cuts.len())) {
                            // not ordered: orienting cross-side rules by the rule order raised M in every family (docs/tier-cycle.md,
                            // "A rewrite cycle"); a growing one can cycle with the built-in rules until the step budget runs out
                            cands.push((pat, rhs));
                        }
                    }
                }
            }
        }
    }
    // extra candidates join the miner's own before the one-per-left-side pass
    if let Some(path) = &cfg.extra {
        let extra = read_rule_file(path);
        println!("RULEMINER {} extra candidates from {path}", extra.len());
        cands.extend(extra);
    }
    // `RULEMINER_NODUPLHS` (default on, 0 = off): drop candidates whose left side already has a rule in force (`RULEMINER_BASE`); the one-per-left-side pass
    // below only sees this mine's candidates, so a later mine could otherwise add a second, competing rewrite for the same pattern
    if cfg.no_dup_lhs {
        let before = cands.len();
        let in_force: hashbrown::HashSet<&Term> = base.iter().map(|(l, _)| l).collect();
        cands.retain(|(l, _)| !in_force.contains(l));
        println!("RULEMINER dropped {} candidates whose left side is already in force", before - cands.len());
    }
    // per left side, the smallest right side only, ties by `show()`. Scoring every right side instead (each left side's rival
    // orientations) fixed add3's `sub` chains but raised M on cmp3d and sbo3 and made cmp3d's mine 4.5x slower (docs/tier-cycle.md)
    // an identity (a pattern's pool group holds the pattern itself) never gains, and as the smallest right side it would displace
    // its left side's real candidates
    cands.retain(|(l, r)| l != r);
    cands.sort_by_cached_key(|(l, r)| (l.size(), l.show(), r.size(), r.show()));
    cands.dedup();
    // rivals: the other right sides of each left side; a round's winner gives way to a rival that gains more on the same laws,
    // unless the mine finished with the winner is worth more (the lookahead after the rounds' `pick`)
    // (docs/tier-cycle.md, "Preferences and rival orientations in the miner")
    let mut rivals: hashbrown::HashMap<Term, Vec<(Term, Term)>> = Default::default();
    for (l, r) in &cands {
        rivals.entry(*l).or_default().push((*l, *r));
    }
    rivals.values_mut().for_each(|v| {
        v.remove(0);
    });
    cands.dedup_by(|a, b| a.0 == b.0);
    println!("RULEMINER {} oriented candidates (one per left side)", cands.len());
    (cands, rivals)
}

/// The patterns obtained from `t` by cutting subterms into variables: (pattern, cut subterms in variable order).
fn abstractions(t: &Term, cap: usize) -> Vec<(Term, Vec<Term>)> {
    let mut out = vec![];
    if !matches!(*t.node(), Node::Zero | Node::Ones) {
        out.push((Term::v(0), vec![*t]));
    } else {
        out.push((*t, vec![]));
    }
    if let Node::Op(o, a, b) = *t.node() {
        for (pa, ca) in abstractions(&a, cap) {
            for (pb, cb) in abstractions(&b, cap) {
                // renumber the right pattern's variables after the left's, merging equal cut subterms
                let mut cuts = ca.clone();
                let mut map = vec![];
                for c in &cb {
                    let at = cuts.iter().position(|x| x == c).unwrap_or_else(|| {
                        cuts.push(*c);
                        cuts.len() - 1
                    });
                    map.push(at);
                }
                if cuts.len() > cap {
                    continue;
                }
                out.push((Term::op(o, pa, renum_vars(&pb, &map)), cuts));
            }
        }
    }
    out.retain(|(_, c)| c.len() <= cap);
    out
}

/// `p` with each variable `i` renamed to `map[i]`.
fn renum_vars(p: &Term, map: &[usize]) -> Term {
    match *p.node() {
        Node::V(i) => Term::v(map[i]),
        Node::Op(o, a, b) => Term::op(o, renum_vars(&a, map), renum_vars(&b, map)),
        _ => *p,
    }
}

/// Whether every variable of `t` is a placeholder (`V(4+j)`).
fn bare(t: &Term) -> bool {
    match *t.node() {
        Node::V(i) => i >= 4,
        Node::Op(_, a, b) => bare(&a) && bare(&b),
        _ => true,
    }
}

/// `t` with each placeholder `V(4+j)` renamed to `V(j)`.
fn renum_placeholders(t: &Term) -> Term {
    match *t.node() {
        Node::V(i) => Term::v(i - 4),
        Node::Op(o, a, b) => Term::op(o, renum_placeholders(&a), renum_placeholders(&b)),
        _ => *t,
    }
}

/// Proves candidate rules against the rules and step budget it copies to each proving thread (the base rules, and the
/// budget P1 left: Q5).
struct Prover {
    rules: Vec<(Term, Term)>,
    /// The preferences to install, `None` for none. The provable filter installs none (Q1): its worker threads prove with
    /// no preferences, while with one thread it runs on this thread, under the base preferences `run` installed.
    prefs: Option<Vec<Pref>>,
    budget: i64,
    n: usize,
}

impl Prover {
    /// The job's rules with `rules` as the run-time rules and, if any, `prefs` as the preferences (otherwise the job's
    /// stay: Q1); and `budget` as the step budget.
    fn install(&self, job: &Job) -> Rules {
        let rules = job.rules().with_mined(job.setup(), self.rules.clone());
        RULE_BUDGET.with(|b| b.set(self.budget));
        match &self.prefs {
            Some(prefs) => rules.with_prefs(prefs.clone()),
            None => rules,
        }
    }

    fn holds(&self, job: &Job, (l, r): &(Term, Term)) -> bool {
        prove_rule(job, self.n, l.max_var().max(r.max_var()) + 1, l, r).is_some()
    }

    /// Proves one rule in an intern scope of its own; leaves the default budget installed after.
    fn prove(&self, job: &mut Job, rule: &(Term, Term)) -> bool {
        tatic::kernel::scoped(|| {
            let ok = job.with_rules(self.install(job), |job| self.holds(job, rule));
            RULE_BUDGET.with(|b| b.set(i64::MAX / 2));
            ok
        })
    }

    /// The indices of the candidates that are proved, in order, on `threads` workers (one intern scope each; one thread
    /// proves on this thread).
    fn filter(&self, job: &mut Job, cands: &[(Term, Term)], threads: usize) -> Vec<usize> {
        // carry-over: with one thread, the base preferences `run` installed stay (Q1); a worker's job has none
        let prove = |job: &mut Job, idx: &[usize]| -> Vec<usize> {
            tatic::kernel::scoped(|| job.with_rules(self.install(job), |job| idx.iter().copied().filter(|&i| self.holds(job, &cands[i])).collect()))
        };
        let threads = threads.clamp(1, 12);
        let mut ok: Vec<usize> = if threads == 1 {
            prove(job, &(0..cands.len()).collect::<Vec<_>>())
        } else {
            std::thread::scope(|sc| {
                let handles: Vec<_> = (0..threads)
                    .map(|t| {
                        let idx: Vec<usize> = (t..cands.len()).step_by(threads).collect();
                        let (prove, setup) = (&prove, job.setup().clone());
                        std::thread::Builder::new().stack_size(256 << 20).spawn_scoped(sc, move || prove(&mut Job::new(setup), &idx)).unwrap()
                    })
                    .collect();
                handles.into_iter().flat_map(|h| h.join().unwrap()).collect()
            })
        };
        ok.sort_unstable();
        ok
    }
}

/// Evaluates rule sets on the scored laws; shared by the scoring workers.
struct Scorer<'a> {
    laws: &'a Laws,
    cfg: &'a MinerConfig,
    /// the base rules in force, all of them until the preference phase drops some
    base_now: std::sync::Mutex<Vec<(Term, Term)>>,
    all_laws: Vec<usize>,
    law_evals: std::sync::atomic::AtomicUsize,
    law_reuses: std::sync::atomic::AtomicUsize,
    /// the join's work on the scoring workers (`JoinCost`)
    join_workers: std::sync::Mutex<JoinCost>,
}

impl<'a> Scorer<'a> {
    fn new(laws: &'a Laws, cfg: &'a MinerConfig, base: Vec<(Term, Term)>) -> Self {
        Scorer {
            laws,
            cfg,
            base_now: std::sync::Mutex::new(base),
            all_laws: (0..laws.scored.len()).collect(),
            law_evals: std::sync::atomic::AtomicUsize::new(0),
            law_reuses: std::sync::atomic::AtomicUsize::new(0),
            join_workers: std::sync::Mutex::new(JoinCost::default()),
        }
    }

    /// cumulative greedy: each round adds the candidate that, on top of the rules chosen so far, fixes the most
    /// stragglers (no whole-term machine proof) and then shrinks the normalized terms most; a straggler often needs two
    /// rules together, which a one-rule-at-a-time score cannot see
    /// `score_laws` rewrites the scored laws `which` under the base rules plus `extra`: per law, whether it needs fewer machine proofs
    /// than under the built-in rules alone, the size of its normalized terms (stragglers only) and, with `record`, every term
    /// `rule_step` was asked about with the rule that fired on it, and every term the join examined. A candidate whose left side
    /// matches none of the terms where it would come first (`Fired::preempted_by`: the run-time rules are tried most specific first,
    /// not in the order added), and that is a join step at none of the join's terms (`Trace::touched_by`), cannot change a law's
    /// rewriting or join, so its laws keep the result under the rules chosen so far.
    /// `prefs`: the rule preferences in force (`Rules::with_prefs`).
    fn score_laws(&self, job: &mut Job, extra: &[(Term, Term)], prefs: &[Pref], which: &[usize], record: bool, seed: Option<RewriteMemo>) -> (Vec<(bool, i64, Trace)>, RewriteMemo) {
        let (n, kv, cfg) = (self.laws.n, self.laws.kv, self.cfg);
        let fallbacks = || MACHINE_FALLBACKS.with(|c| c.get());
        REWRITE_MEMO.with(|m| *m.borrow_mut() = Some(seed.unwrap_or_else(|| RewriteMemo::new(kv))));
        let steps = cfg.steps as i64;
        let budget = || RULE_BUDGET.with(|b| b.set(steps));
        // counting only under `RULEMINER_FAST`, or when the caller asked for it (rivals, below). Carry-over: the old code
        // installed these rules and `prefs` and left them installed, which nothing read: every later rewrite on this thread
        // is another `score_laws` or a `Prover::prove`, and each installs its own
        let rules = job.rules().with_mined(job.setup(), self.base_now.lock().unwrap().iter().chain(extra).cloned().collect()).with_prefs(prefs.to_vec());
        let rules = rules.counting(cfg.fast || rules.score_only());
        let out = job.with_rules(rules, |job| {
            which
                .iter()
                .map(|&si| {
                    let s = &self.laws.scored[si];
                    budget();
                    if record {
                        RULE_TRACE.with(|t| *t.borrow_mut() = Some(vec![]));
                    }
                    let before = fallbacks();
                    let ok = rewrite_plan(job, n, kv, &s.1, &s.2).is_some();
                    let fixed = ok && fallbacks() - before < s.4;
                    budget();
                    // the rule order's own measure: operator nodes first, then variable occurrences
                    let measure = |t: &Term| {
                        let mut occ = [0usize; 8];
                        t.occurrences(&mut occ);
                        let (c, a) = rule_weight(t);
                        (c + a.iter().sum::<i64>()) * 16 + occ.iter().sum::<usize>() as i64
                    };
                    let size = if si < self.laws.stragglers.len() { measure(&rewrite(job, &s.1, n, kv).0) + measure(&rewrite(job, &s.2, n, kv).0) } else { 0 };
                    let mut seen: hashbrown::HashSet<(Term, Fired)> = Default::default();
                    let trace = Trace::new(RULE_TRACE.with(|t| t.borrow_mut().take()).unwrap_or_default().into_iter().filter(|t| seen.insert(*t)).collect());
                    (fixed, size, trace)
                })
                .collect()
        });
        let memo = REWRITE_MEMO.with(|m| m.borrow_mut().take()).unwrap();
        RULE_BUDGET.with(|b| b.set(i64::MAX / 2));
        (out, memo)
    }

    fn summarize(ev: &[(bool, i64, Trace)]) -> (Vec<bool>, i64) {
        (ev.iter().map(|e| e.0).collect::<Vec<bool>>(), ev.iter().map(|e| e.1).sum::<i64>())
    }

    /// The stragglers covered.
    fn count(&self, f: &[bool]) -> i64 {
        f.iter().take(self.laws.stragglers.len()).filter(|c| **c).count() as i64
    }

    /// The guard laws covered.
    fn guarded(&self, f: &[bool]) -> i64 {
        f.iter().skip(self.laws.stragglers.len()).filter(|c| **c).count() as i64
    }

    /// what a round's gain measures, as a total: a rule's gain is the value it adds
    fn value(&self, s: &Chosen) -> i64 {
        self.count(&s.covered) * 1000 + self.guarded(&s.covered) * self.laws.guard_w - s.size
    }
}

/// the rules chosen so far and, under them, each law's evaluation, the stragglers and guard laws they cover and the total size
struct Chosen {
    chosen: Vec<(Term, Term)>,
    eval: Vec<(bool, i64, Trace)>,
    covered: Vec<bool>,
    size: i64,
}

/// rounds not yet committed, oldest first: the state before each, its round, its winner's pending proof and its `chosen` line
struct Open {
    before: Chosen,
    round: usize,
    proof: Option<usize>,
    line: String,
    rule: String,
}

/// A rule set as a key: a round depends only on the set of rules chosen so far (`RuleTable::sorted` sorts them).
fn key(c: &[(Term, Term)]) -> Vec<(Term, Term)> {
    let mut v = c.to_vec();
    v.sort();
    v
}

/// The greedy rounds over the provable candidates, their lookahead and the proofs of their winners (P6-P8), all on this
/// thread; the scoring workers share only the `Scorer`.
struct Rounds<'a> {
    scorer: &'a Scorer<'a>,
    prover: &'a Prover,
    provable: &'a [(Term, Term)],
    rivals: &'a hashbrown::HashMap<Term, Vec<(Term, Term)>>,
    base_prefs: &'a [Pref],
    cfg: &'a MinerConfig,
    clock: &'a Clock,
    /// under `RULEMINER_FAST` the candidates are proved here, once each, against the base rules as the eager filter would
    proofs: Vec<Option<bool>>,
    /// a round's winner is proved on a thread of its own while the next round is scored (`speculate`, set for the main path's
    /// rounds and lookahead's greedy paths): the round takes it as provable (`assumed`) and is committed when its proof is in,
    /// and a failed proof rolls the rounds back to it (`play`). Any other proof of a pending candidate waits for its result
    proof_tx: std::sync::mpsc::Sender<(usize, bool)>,
    proof_rx: std::sync::mpsc::Receiver<(usize, bool)>,
    pending: hashbrown::HashSet<usize>,
    speculate: bool,
    spawn_req: Option<usize>,
    assumed: Vec<usize>,
    /// a round depends only on the set of rules chosen so far, and alternatives' greedy paths often reach the same set in
    /// another order, so picks and finished values are kept by set; the kept alternative's path is also the next rounds' own
    picks: hashbrown::HashMap<Vec<(Term, Term)>, Vec<((Term, Term), i64)>>,
    /// a set's finished value and the rounds finishing took, valid under any cap of at least that many rounds
    finished: hashbrown::HashMap<Vec<(Term, Term)>, (i64, usize)>,
    /// the last evaluation's memo, under its rules: an entry holds under other rules when no rule in or out touches a term of its
    /// trace (`RewriteMemo::filtered`), so each evaluation is seeded with what the rules that changed cannot touch
    state_memo: Option<(Vec<(Term, Term)>, RewriteMemo)>,
    state_time: std::time::Duration,
    /// the join's work on this thread from here on (`JoinCost`), and the time spent bounding the candidates' gains
    join_main: JoinCost,
    bound_time: std::time::Duration,
    scorings: usize,
    skipped: usize,
}

impl<'a> Rounds<'a> {
    fn new(scorer: &'a Scorer<'a>, prover: &'a Prover, provable: &'a [(Term, Term)], rivals: &'a hashbrown::HashMap<Term, Vec<(Term, Term)>>, base_prefs: &'a [Pref], cfg: &'a MinerConfig, clock: &'a Clock) -> Self {
        let (proof_tx, proof_rx) = std::sync::mpsc::channel::<(usize, bool)>();
        Rounds {
            scorer,
            prover,
            provable,
            rivals,
            base_prefs,
            cfg,
            clock,
            proofs: vec![if cfg.fast { None } else { Some(true) }; provable.len()],
            proof_tx,
            proof_rx,
            pending: Default::default(),
            speculate: false,
            spawn_req: None,
            assumed: vec![],
            picks: Default::default(),
            finished: Default::default(),
            state_memo: None,
            state_time: std::time::Duration::ZERO,
            join_main: JoinCost::now(),
            bound_time: std::time::Duration::ZERO,
            scorings: 0,
            skipped: 0,
        }
    }

    fn resolve(&mut self, i: usize) -> bool {
        loop {
            if let Some(b) = self.proofs[i] {
                return b;
            }
            let (j, b) = self.proof_rx.recv().unwrap();
            self.pending.remove(&j);
            self.proofs[j] = Some(b);
        }
    }

    fn prove_one(&mut self, job: &mut Job, i: usize) -> bool {
        if self.pending.contains(&i) { self.resolve(i) } else { self.prover.prove(job, &self.provable[i]) }
    }

    fn state(&mut self, job: &mut Job, chosen: Vec<(Term, Term)>) -> Chosen {
        let t0 = Instant::now();
        let seed = self.state_memo.take().map(|(was, memo)| {
            let changed: Vec<&(Term, Term)> = was.iter().chain(&chosen).filter(|r| was.contains(*r) != chosen.contains(*r)).collect();
            memo.filtered(|tr| !changed.iter().any(|r| tr.touched_by(r, |_| true)))
        });
        let (eval, grown) = self.scorer.score_laws(job, &chosen, self.base_prefs, &self.scorer.all_laws, true, seed);
        self.state_memo = Some((chosen.clone(), grown));
        let (covered, size) = Scorer::summarize(&eval);
        self.state_time += t0.elapsed();
        Chosen { chosen, eval, covered, size }
    }

    /// one round on top of `s`: its alternatives with their gains, largest first: a rival orientation of the winner that gains
    /// more, if one is proved, then the winner
    fn pick(&mut self, job: &mut Job, s: &Chosen) -> Vec<((Term, Term), i64)> {
        let (scorer, provable, rivals, base_prefs, cfg) = (self.scorer, self.provable, self.rivals, self.base_prefs, self.cfg);
        let (stragglers, guard_w) = (&scorer.laws.stragglers, scorer.laws.guard_w);
        let (chosen, base_eval, covered, size) = (&s.chosen, &s.eval, &s.covered, s.size);
        // a candidate changes only the laws whose rewriting asked about a term its left side matches, or whose join examined a
        // term it is a step at (`affected`, `Trace::touched_by`), so its gain is at most
        // 1000 per affected uncovered straggler, `guard_w` per affected uncovered guard law and the affected stragglers' whole size
        // a candidate can only rewrite a term where it comes before the rule that fired (`Fired::preempted_by`), unless a
        // preference makes it a winner (the trace was made without the candidate)
        // the run-time order of every rule in play, ranked once (`run_order` builds strings)
        let t0 = Instant::now();
        let mut ranked: Vec<(Term, Term)> = scorer.base_now.lock().unwrap().iter().chain(chosen).chain(provable.iter()).cloned().collect();
        ranked.sort_by_cached_key(|(l, r)| run_order(l, r));
        let rank: hashbrown::HashMap<(Term, Term), usize> = ranked.into_iter().enumerate().map(|(i, r)| (r, i)).collect();
        // every law's trace at once (`TraceIndex`: a term shared by many laws' traces is matched once), the candidates split
        // over the scoring threads; each candidate's laws are the same whichever thread finds them
        let index = TraceIndex::new(base_eval.iter().map(|e| &e.2));
        let touched = |rule: &(Term, Term)| {
            let anywhere = base_prefs.iter().any(|(w, _)| w == rule);
            let before = |fired: &(Term, Term)| rank.get(fired).is_none_or(|&f| rank[rule] < f);
            index.touched(rule, |fired| anywhere || fired.preempted_by(before))
        };
        let threads = cfg.threads.clamp(1, 12);
        let affected: Vec<Vec<usize>> = std::thread::scope(|sc| {
            let handles: Vec<_> = (0..threads)
                .map(|t| {
                    let touched = &touched;
                    sc.spawn(move || (t..provable.len()).step_by(threads).map(|i| touched(&provable[i])).collect::<Vec<_>>())
                })
                .collect();
            let mut parts: Vec<_> = handles.into_iter().map(|h| h.join().unwrap().into_iter()).collect();
            (0..provable.len()).map(|i| parts[i % threads].next().unwrap()).collect()
        });
        let bound = |i: usize| -> i64 {
            let gain = |si: usize, w: i64| if covered[si] { 0 } else { w };
            affected[i].iter().map(|&si| if si < stragglers.len() { gain(si, 1000) + base_eval[si].1 } else { gain(si, guard_w) }).sum()
        };
        let mut order: Vec<(i64, usize)> = (0..provable.len()).map(|i| (bound(i), i)).collect();
        order.sort_by_key(|&(b, i)| (std::cmp::Reverse(b), i));
        self.bound_time += t0.elapsed();
        // the candidates are scored on `RULEMINER_THREADS` workers (default 1; keep at most 12), each with its own intern
        // scope, a chunk at a time in order of their bound; scoring stops at a bound below the best gain so far, since those
        // candidates cannot win, so the choice does not depend on the thread count or the chunking. Each candidate is scored from
        // an empty memo: a memo kept across a worker's candidates made a gain depend on which candidates that worker scored before
        // (its join entries are inexact by design), so the choice depended on scheduling, and it saved no time (docs/decisions/
        // 2026-10-17-monotone-join.md, "Spike of the snapshot"). The join store is shared instead, read-only: the workers read
        // the copy frozen as the round starts, which only this thread's searches fed (docs/tier-cycle.md, "Spike of the join
        // store"). Expressions are per thread, so each worker grows its own (1.5x
        // faster scoring on cmp3d, docs/tier-cycle.md, "Miner speedups")
        // a rule's gain on top of the rules chosen so far; it changes only the laws `aff` it can touch
        let score_rule = |job: &mut Job, rule: &(Term, Term), aff: &[usize]| -> (i64, Vec<bool>, i64) {
            let mut with = chosen.clone();
            with.push(*rule);
            let (fresh, _) = scorer.score_laws(job, &with, base_prefs, aff, true, None);
            scorer.law_evals.fetch_add(scorer.all_laws.len(), std::sync::atomic::Ordering::Relaxed);
            scorer.law_reuses.fetch_add(scorer.all_laws.len() - aff.len(), std::sync::atomic::Ordering::Relaxed);
            let mut ev: Vec<(bool, i64)> = base_eval.iter().map(|e| (e.0, e.1)).collect();
            for (&si, f) in aff.iter().zip(&fresh) {
                ev[si] = (f.0, f.1);
            }
            let (f, sz) = (ev.iter().map(|e| e.0).collect::<Vec<bool>>(), ev.iter().map(|e| e.1).sum::<i64>());
            ((scorer.count(&f) - scorer.count(covered)) * 1000 + (scorer.guarded(&f) - scorer.guarded(covered)) * guard_w + (size - sz), f, sz)
        };
        // the winner's left side with another right side: same affected laws, proved only if it would win
        // rivals are not proved before scoring, so they are scored by counting only (`Rules::counting`); scoring compiles no plans, so an
        // unprovable rival (`sub(x, shl1(x, 0)) -> sub(shr1(0, 0), x)` once the promoted rules are out) is never proved
        let rivals_of = |i: usize| rivals.get(&provable[i].0).map_or(&[][..], |v| &v[..]);
        // a job: candidate `i`, or with `Some(k)` the `k`th rival of the winner `i`
        let score_job = |job: &mut Job, (i, k): (usize, Option<usize>)| match k {
            None => score_rule(job, &provable[i], &affected[i]),
            Some(k) => {
                let counting = job.rules().counting(true);
                job.with_rules(counting, |job| score_rule(job, &rivals_of(i)[k], &affected[i]))
            }
        };
        // best gain first, ties to the earlier candidate; the first one that is proved wins, and an unprovable one reopens the
        // candidates whose bound reaches the next best
        let mut results: Vec<Option<(i64, Vec<bool>, i64)>> = vec![None; provable.len()];
        let mut next = 0;
        let (winner, rival_gains) = std::thread::scope(|sc| {
            // one queue for all workers: each takes the next candidate when it is free, so a chunk ends when its last
            // candidate is scored rather than when the slowest worker's fixed share is; the winner's rivals go through it too,
            // each scored on its own, so their gains do not depend on which worker scored them
            let (done_tx, done_rx) = std::sync::mpsc::channel();
            let (work, queue) = std::sync::mpsc::channel::<(usize, Option<usize>)>();
            let queue = std::sync::Arc::new(std::sync::Mutex::new(queue));
            // the join store as this round starts, for the workers
            let frozen = frozen_join_store();
            for _ in 0..threads {
                let (done_tx, score_job, queue, join_workers, frozen, setup) = (done_tx.clone(), &score_job, queue.clone(), &scorer.join_workers, frozen.clone(), job.setup().clone());
                let worker = move || {
                    let job = &mut Job::new(setup);
                    set_join_store(frozen.map(JoinStoreUse::Read));
                    let before = JoinCost::now();
                    tatic::kernel::scoped(|| {
                        loop {
                            let Ok(item) = queue.lock().unwrap().recv() else { break };
                            done_tx.send((item, score_job(job, item))).unwrap();
                        }
                    });
                    join_workers.lock().unwrap().add_since(before);
                };
                std::thread::Builder::new().stack_size(256 << 20).spawn_scoped(sc, worker).unwrap();
            }
            let winner = loop {
                let best = (0..provable.len()).filter(|&i| self.proofs[i] != Some(false)).filter_map(|i| results[i].as_ref().map(|r| (r.0, i))).filter(|r| r.0 > 0).max_by_key(|&(g, i)| (g, std::cmp::Reverse(i)));
                let floor = best.map_or(1, |b| b.0);
                let chunk: Vec<usize> = order[next..].iter().take_while(|&&(b, _)| b >= floor).take(threads * 4).map(|&(_, i)| i).collect();
                if chunk.is_empty() {
                    let Some((_, i)) = best else { break None };
                    let known = self.proofs[i];
                    let ok = match known {
                        Some(ok) => ok,
                        None if self.speculate => {
                            self.assumed.push(i);
                            if self.pending.insert(i) {
                                self.spawn_req = Some(i);
                            }
                            true
                        }
                        None => {
                            let ok = self.prove_one(job, i);
                            self.proofs[i] = Some(ok);
                            ok
                        }
                    };
                    if ok {
                        break Some(i);
                    }
                    continue;
                }
                next += chunk.len();
                for &i in &chunk {
                    work.send((i, None)).unwrap();
                }
                for ((i, _), r) in done_rx.iter().take(chunk.len()) {
                    results[i] = Some(r);
                }
            };
            let mut gains = vec![0; winner.map_or(0, |i| rivals_of(i).len())];
            for k in 0..gains.len() {
                work.send((winner.unwrap(), Some(k))).unwrap();
            }
            for ((_, k), r) in done_rx.iter().take(gains.len()) {
                gains[k.unwrap()] = r.0;
            }
            (winner, gains)
        });
        self.scorings += next;
        self.skipped += provable.len() - next;
        self.clock.phase(&format!("round over {} of {} candidates", next, provable.len()));
        let Some(i) = winner else { return vec![] };
        let g = results[i].as_ref().unwrap().0;
        // in the rivals' order, as when they were scored one after another here
        let mut rival: Option<((Term, Term), i64)> = None;
        for (rv, &rg) in rivals_of(i).iter().zip(&rival_gains) {
            if rg > rival.as_ref().map_or(g, |r| r.1) && self.prover.prove(job, rv) {
                rival = Some((*rv, rg));
            }
        }
        rival.into_iter().chain([(provable[i], g)]).collect()
    }

    /// a rival's larger round gain can lead to a worse finished set (docs/tier-cycle.md, "The cold loss is a greedy path loss"), so
    /// both are finished greedily (rivals taken, no lookahead) and the better finished set's choice is kept, ties to the rival.
    /// Looking ahead over runners-up too lost ("Lookahead on rival swaps")
    fn then(&mut self, job: &mut Job, s: &Chosen, rule: &(Term, Term)) -> Chosen {
        self.state(job, s.chosen.iter().chain([rule]).cloned().collect())
    }

    fn pick_kept(&mut self, job: &mut Job, s: &Chosen) -> Vec<((Term, Term), i64)> {
        let kk = key(&s.chosen);
        if let Some(v) = self.picks.get(&kk) {
            return v.clone();
        }
        let v = self.pick(job, s);
        self.picks.insert(kk, v.clone());
        v
    }

    /// the value of `chosen` finished greedily (each round's first alternative) in at most `rounds` more rounds; while
    /// speculating, each pick's assumed winner is proved on a thread of its own (`spawn`)
    fn finish(&mut self, job: &mut Job, mut chosen: Vec<(Term, Term)>, rounds: usize, spawn: &dyn Fn(usize)) -> i64 {
        let (mut path, mut left) = (vec![], rounds);
        let (v, mut d) = loop {
            let kk = key(&chosen);
            if let Some(&(v, d)) = self.finished.get(&kk).filter(|e| e.1 <= left) {
                break (v, d);
            }
            let s = self.state(job, chosen);
            if left == 0 {
                return self.scorer.value(&s); // cut by the round cap: not kept
            }
            let alts = self.pick_kept(job, &s);
            if let Some(j) = self.spawn_req.take() {
                spawn(j);
            }
            let Some((rule, _)) = alts.into_iter().next() else {
                let v = self.scorer.value(&s);
                self.finished.insert(kk, (v, 0));
                break (v, 0);
            };
            path.push(kk);
            chosen = s.chosen;
            chosen.push(rule);
            left -= 1;
        };
        for kk in path.into_iter().rev() {
            d += 1;
            self.finished.insert(kk, (v, d));
        }
        v
    }

    /// commits the open rounds whose proofs hold, oldest first, until `keep` are left; at a failed proof, voids the rounds built
    /// on it (their picks too, as the failed winner is never picked again) and returns it, to be played again
    fn settle(&mut self, job: &mut Job, open: &mut Vec<Open>, keep: usize) -> Option<Open> {
        while open.len() > keep {
            let o = open.remove(0);
            if o.proof.is_none_or(|i| self.resolve(i)) {
                println!("{}", o.line);
                job.setup().result("chosen", &o.rule);
                continue;
            }
            println!("RULEMINER rolled back to round {}: its winner {} is not provable", o.round, o.proof.map_or(String::new(), |i| rule_show(&self.provable[i])));
            for v in std::iter::once(&o).chain(open.iter()) {
                self.picks.remove(&key(&v.before.chosen));
            }
            for v in open.drain(..) {
                if let Some(i) = v.proof {
                    self.resolve(i);
                }
            }
            return Some(o);
        }
        None
    }

    /// The rounds, from no rules chosen until no candidate gains (or `RULEMINER_ROUNDS`): the final rule set.
    fn play(&mut self, job: &mut Job) -> Chosen {
        let (prover, provable, tx, setup) = (self.prover, self.provable, self.proof_tx.clone(), job.setup().clone());
        std::thread::scope(|sc| {
            let spawn = |i: usize| {
                let (tx, rule, setup) = (tx.clone(), &provable[i], setup.clone());
                std::thread::Builder::new().stack_size(256 << 20).spawn_scoped(sc, move || tx.send((i, prover.prove(&mut Job::new(setup), rule))).unwrap()).unwrap();
            };
            let (mut s, mut round, mut open) = (self.state(job, vec![]), 0, Vec::<Open>::new());
            loop {
                self.speculate = true;
                let alts = if round < self.cfg.rounds { self.pick_kept(job, &s) } else { vec![] };
                self.speculate = false;
                // the main path's assumption is the round's own pending proof (`proof`)
                self.assumed.clear();
                let proof = self.spawn_req.take();
                proof.map(spawn);
                let Some(mut rule) = alts.first().map(|a| a.0) else {
                    match self.settle(job, &mut open, 0) {
                        Some(o) => (s, round) = (o.before, o.round),
                        None => break s,
                    }
                    continue;
                };
                if alts.len() > 1 {
                    // lookahead plays whole greedy paths from settled rounds, taking each pick's winner as provable while it is proved
                    // in the background; a path that took an unprovable winner voids the picks that offered it and the finished values
                    // (any may rest on it), and the paths are played again
                    if let Some(o) = self.settle(job, &mut open, 0) {
                        (s, round) = (o.before, o.round);
                        continue;
                    }
                    if !proof.is_none_or(|i| self.resolve(i)) {
                        println!("RULEMINER rolled back to round {round}: its winner {} is not provable", proof.map_or(String::new(), |i| rule_show(&provable[i])));
                        self.picks.remove(&key(&s.chosen));
                        continue;
                    }
                    let rest = self.cfg.rounds - round - 1;
                    let values = loop {
                        self.speculate = true;
                        let values: Vec<i64> = alts.iter().map(|(r, _)| self.finish(job, s.chosen.iter().chain([r]).cloned().collect(), rest, &spawn)).collect();
                        self.speculate = false;
                        let failed: Vec<usize> = std::mem::take(&mut self.assumed).into_iter().filter(|&i| !self.resolve(i)).collect();
                        if failed.is_empty() {
                            break values;
                        }
                        println!("RULEMINER lookahead played again: {} is not provable", failed.iter().map(|&i| rule_show(&provable[i])).collect::<Vec<_>>().join(", "));
                        self.picks.retain(|_, v| !v.iter().any(|(r, _)| failed.iter().any(|&i| provable[i] == *r)));
                        self.finished.clear();
                    };
                    let best = (0..alts.len()).max_by_key(|&a| (values[a], std::cmp::Reverse(a))).unwrap();
                    for (a, ((l, r), g)) in alts.iter().enumerate() {
                        println!("RULEMINER lookahead: {} {} -> {} (+{g}) finishes at {}", if a == best { "keep" } else { "    " }, l.show(), r.show(), values[a]);
                    }
                    rule = alts[best].0;
                }
                let next = self.then(job, &s, &rule);
                let line = format!("RULEMINER chosen (+{} fixed, -{} size): {} -> {}", self.scorer.count(&next.covered) - self.scorer.count(&s.covered), s.size - next.size, rule.0.show(), rule.1.show());
                self.clock.phase("rule-set evaluation");
                open.push(Open { before: s, round, proof, line, rule: rule_show(&rule) });
                (s, round) = (next, round + 1);
                // the newest three rounds stay open: a winner's proof (about 87 ms on cmp3d) runs while the next three rounds are
                // scored (about 60 ms each at 6 threads); docs/tier-cycle.md, "Why six threads gave little"
                if let Some(o) = self.settle(job, &mut open, 3) {
                    (s, round) = (o.before, o.round);
                }
            }
        })
    }

    /// The closing report (P10): the scoring's reuse and skips, lazy proofs, times, the join's work and the stragglers the
    /// final rules `covered` leaves.
    fn report(&self, covered: &[bool]) {
        let (scorer, stragglers) = (self.scorer, &self.scorer.laws.stragglers);
        println!("RULEMINER scoring reused {} of {} law evaluations", scorer.law_reuses.load(std::sync::atomic::Ordering::Relaxed), scorer.law_evals.load(std::sync::atomic::Ordering::Relaxed));
        println!("RULEMINER the gain bound skipped {} of {} candidate scorings", self.skipped, self.scorings + self.skipped);
        if self.cfg.fast {
            let p = &self.proofs;
            println!("RULEMINER lazy proofs: {} proved, {} failed", p.iter().filter(|x| **x == Some(true)).count(), p.iter().filter(|x| **x == Some(false)).count());
        }
        println!("RULEMINER time in rule-set evaluations: {:.1}s", self.state_time.as_secs_f64());
        println!("RULEMINER time bounding candidates' gains: {:.1}s", self.bound_time.as_secs_f64());
        let mut j = *scorer.join_workers.lock().unwrap();
        j.add_since(self.join_main);
        println!("RULEMINER join: {} searches reaching {} terms, {} met, {} memo hits, {:.1}s searching ({:.1}s in failed searches)", j.searches, j.reached, j.met, j.hits, j.nanos as f64 / 1e9, j.failed_nanos as f64 / 1e9);
        println!("RULEMINER join store: {} joins served, {:.1}s querying", j.stored, j.store_nanos as f64 / 1e9);
        println!("RULEMINER {} of {} stragglers covered by the chosen rules", covered.iter().take(stragglers.len()).filter(|c| **c).count(), stragglers.len());
        for (st, c) in stragglers.iter().zip(covered) {
            if !c {
                println!("RULEMINER uncovered: {}", st.0);
            }
        }
    }
}

/// learned preferences (docs/tier-cycle.md, "Rule order"): where two rules in force both rewrite a term of the scored laws, the
/// first one in order does; each round tries letting the other win, one pair at a time, and dropping each unit of a pooled base
/// (`drop_units`: the rules where one library's normal forms meet another's), and keeps the move with the largest gain (the
/// rule rounds' gain), until none gains. Only with `RULEMINER_PREFS=1`: a family's own rules rarely conflict, so the phase pays
/// off on a pooled library (`driver::sweep`) and barely in a loop's mines, where it doubled the mine time ("Preferences and
/// rival orientations in the miner") (P9)
fn prefs_phase(job: &mut Job, scorer: &Scorer, chosen: &[(Term, Term)], base: &[(Term, Term)], base_prefs: &[Pref], cfg: &MinerConfig, clock: &Clock) {
    let (all_laws, guard_w) = (&scorer.all_laws, scorer.laws.guard_w);
    // `RULEMINER_UNITS=<file>`: the base's drop units (`joinability_units`, built once per pooled library by `driver::sweep`)
    let units = cfg.units.as_ref().filter(|_| cfg.prefs).map_or(vec![], |f| parse_units(&std::fs::read_to_string(f).unwrap()));
    for (u, rules) in units.iter().enumerate() {
        println!("RULEMINER drop unit {u}: {}", rules.iter().map(|(l, r)| format!("{} -> {}", l.show(), r.show())).collect::<Vec<_>>().join("; "));
    }
    let mut dropped: Vec<usize> = vec![];
    let set_base = |dropped: &[usize]| {
        *scorer.base_now.lock().unwrap() = base.iter().filter(|r| !dropped.iter().any(|&u| units[u].contains(r))).cloned().collect();
    };
    let mut prefs = base_prefs.to_vec();
    while cfg.prefs {
        RULE_CONFLICTS.with(|c| *c.borrow_mut() = Some(Default::default()));
        let (now, _) = scorer.score_laws(job, chosen, &prefs, all_laws, false, None);
        let mut conflicts: Vec<Pref> = RULE_CONFLICTS.with(|c| c.borrow_mut().take()).unwrap().into_keys().collect();
        let shown = |(w, l): &Pref| (rule_show(w), rule_show(l));
        conflicts.sort_by_cached_key(shown);
        let (f0, size0) = Scorer::summarize(&now);
        // through `score_laws`, which installs its own rules and preferences (carry-over: as before)
        let mut gain = |prefs: &[Pref]| {
            let (f, sz) = Scorer::summarize(&scorer.score_laws(job, chosen, prefs, all_laws, false, None).0);
            (scorer.count(&f) - scorer.count(&f0)) * 1000 + (scorer.guarded(&f) - scorer.guarded(&f0)) * guard_w + (size0 - sz)
        };
        // a flip's move key is the pair it makes (winner, loser); a drop's is its unit's index
        let flipped = |(w, l): &Pref| prefs.iter().filter(|p| (&p.0, &p.1) != (l, w)).cloned().chain([(*w, *l)]).collect::<Vec<_>>();
        let mut moves: Vec<(i64, Result<Pref, usize>)> = conflicts.iter().map(|(w, l)| (*l, *w)).map(|f| (gain(&flipped(&f)), Ok(f))).collect();
        for u in (0..units.len()).filter(|u| !dropped.contains(u)) {
            set_base(&[&dropped[..], &[u]].concat());
            moves.push((gain(&prefs), Err(u)));
        }
        set_base(&dropped);
        // a drop removes many rules at once, so it needs two laws' worth of gain: on one law it overfit (salt 1's sbo3)
        // ties to the first move in text order
        let text = |m: &Result<Pref, usize>| m.as_ref().map(shown).map_err(|u| *u);
        let best = moves.into_iter().filter(|(g, m)| *g > if m.is_err() { 1999 } else { 0 }).max_by(|a, b| a.0.cmp(&b.0).then_with(|| text(&b.1).cmp(&text(&a.1))));
        clock.phase(&format!("preference round over {} conflicts and {} drop units", conflicts.len(), units.len() - dropped.len()));
        match best {
            None => break,
            Some((g, Ok((w, l)))) => {
                println!("RULEMINER prefer (+{g} gain): {}  OVER  {}", rule_show(&w), rule_show(&l));
                job.setup().result("prefer", format!("{}  OVER  {}", rule_show(&w), rule_show(&l)));
                prefs = flipped(&(w, l));
            }
            Some((g, Err(u))) => {
                for (l, r) in &units[u] {
                    println!("RULEMINER drop (+{g} gain): {} -> {}", l.show(), r.show());
                    job.setup().result("drop", format!("{} -> {}", l.show(), r.show()));
                }
                dropped.push(u);
                set_base(&dropped);
            }
        }
    }
}
