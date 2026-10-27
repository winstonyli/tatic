//! The rule miner (`search::rule_miner`, search note section 36) in named parts: the laws and their stragglers (`laws`), the
//! candidates (`candidates`), their proofs (`Prover`), the evaluation of rule sets (`Scorer`), the greedy rounds
//! (`Rounds`) and the closing report (`Rounds::report`).
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
/// `_PHASE`, `_SKIP`), which the driver reads when it writes the law file (`driver::write_laws`).
pub struct MinerConfig {
    /// `RULEMINER_ROUNDS`: greedy rounds (default no cap: the mine stops when no candidate gains; a cap trimmed general rules,
    /// docs/tier-cycle.md "cmp3d's library lost its general rules").
    pub rounds: usize,
    /// `RULEMINER_THREADS`: scoring threads, clamped to 1..=12.
    pub threads: usize,
    /// `RULEMINER_FAST` (switch, off by default): score without rule proofs, proving only each round's winner.
    pub fast: bool,
    /// `RULEMINER_BASE=<file>`: rules (`lhs -> rhs` lines) in force throughout (section 74).
    pub base: Option<String>,
    /// `RULEMINER_LAWFILE=<file>` (required): mine from these `lhs = rhs` lines.
    pub lawfile: String,
    /// `RULEMINER_GUARD=<k>`: about k machine-free laws scored with the stragglers (default 120, 0 = off).
    pub guard: usize,
    /// `RULEMINER_NODUPLHS` (switch, on by default): drop candidates whose left side already has a rule in `base`.
    pub no_dup_lhs: bool,
}

impl MinerConfig {
    pub fn new(s: &Setup) -> Self {
        MinerConfig {
            rounds: s.or("RULEMINER_ROUNDS", usize::MAX),
            threads: s.or("RULEMINER_THREADS", 1).clamp(1, 12),
            fast: s.flag("RULEMINER_FAST", false),
            base: s.var("RULEMINER_BASE").map(String::from),
            lawfile: s.var("RULEMINER_LAWFILE").expect("RULEMINER_LAWFILE: the laws to mine").to_string(),
            guard: s.or("RULEMINER_GUARD", 120),
            no_dup_lhs: s.flag("RULEMINER_NODUPLHS", true),
        }
    }
}

/// The most candidates a mine scores.
const CANDIDATE_CAP: usize = 400;

/// The variable cap of the cross-side rules.
const CROSS_VARS: usize = 4;

pub fn run(setup: &Arc<Setup>) {
    mine(setup, &[]);
}

/// The mine `run` does, with `extra` candidates joining the miner's own (the rollback test's false ones): the chosen rules,
/// as `rule_show` lines, and how many winners failed their proofs and rolled the rounds back.
fn mine(setup: &Arc<Setup>, extra: &[(Term, Term)]) -> (Vec<String>, usize) {
    let job = &mut Job::new(setup.clone());
    tatic::kernel::scoped(|| {
        // the join store this mine feeds from its main job (`JoinStore`); the scoring workers read a copy of it
        job.join_store = Some(JoinStoreUse::Feed(JoinStore::default()));
        let clock = Clock(std::cell::Cell::new(Instant::now()));
        let _banner = MachineBanner::start(job, "RULEMINER");
        let _save = lemma_cache::Save(setup.clone());
        let cfg = MinerConfig::new(setup);
        // the stragglers are the laws left with the base's rules
        let base_text = cfg.base.as_ref().map(|f| std::fs::read_to_string(f).unwrap()).unwrap_or_default();
        let base = parse_rules(&base_text);
        // P0: everything on this thread below runs under the base rules, apart from what installs its own
        let base_rules = job.rules().with_mined(setup, base.clone());
        job.with_rules(base_rules, |job| {
            // base rules may loop; a step budget per law bounds them (the built-in rules never reach it)
            let budget = if base.is_empty() { UNBOUNDED } else { LAW_STEPS };
            let laws = laws(job, &cfg, budget, &clock);
            let (cands, rivals) = candidates(&laws, &cfg, &base, extra);
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
            let cands: Vec<(Term, Term)> = cands.into_iter().filter(|(l, _)| applicable(l)).take(CANDIDATE_CAP).collect();
            println!("RULEMINER {} applicable candidates (cap {CANDIDATE_CAP})", cands.len());
            // each candidate is proved independently, on `RULEMINER_THREADS` workers; the proving reads the base rules of
            // this thread, so the workers copy them. `RULEMINER_FAST` scores without rule proofs (`shared_lemma`), so there only a
            // round's winner is proved (`proved_lazily`), and an unprovable one gives way to the next best
            let rules = job.rules().mined().to_vec();
            let prover = Prover { rules, n: laws.n };
            let provable: Vec<(Term, Term)> = if cfg.fast { cands.clone() } else { prover.filter(job, &cands, cfg.threads).into_iter().map(|i| cands[i]).collect() };
            println!("RULEMINER {} provable candidates of {} proposed", provable.len(), cands.len());
            clock.phase("provable filter");
            let scorer = Scorer::new(&laws, &cfg, base.clone());
            let mut rounds = Rounds::new(&scorer, &prover, &provable, &rivals, &cfg, &clock);
            // the main job's join work from here on
            let (Chosen { chosen, covered, .. }, main) = job.spent(|job| rounds.play(job));
            rounds.report(&covered, main.join);
            (chosen.iter().map(rule_show).collect(), rounds.proofs.iter().filter(|p| **p == Some(false)).count())
        })
    })
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

/// The laws of `cfg` and their stragglers under the rules installed on this thread (P1, P2), each rewritten under `budget`
/// steps.
fn laws(job: &mut Job, cfg: &MinerConfig, budget: i64, clock: &Clock) -> Laws {
    let (n, kv) = (4usize, STREAM_VARS);
    // stragglers under the built-in rules
    let mut stragglers: Vec<Scored> = vec![];
    let laws = read_named_laws(&cfg.lawfile);
    clock.phase("law building");
    let mut unproved = 0usize;
    let mut clean: Vec<(String, Term, Term)> = vec![]; // laws that are already machine-free under the base rules (for `RULEMINER_GUARD`)
    // `RULEMINER_FAST` counts the base rules' machine proofs the way it scores candidates: without building them. Carry-over:
    // P1 runs under the base rules P0 installed
    let counting = job.rules().counting(cfg.fast);
    job.with_rules(counting, |job| {
        for (name, t1, t2) in laws.iter().cloned() {
            if !t1.is_law(&t2, kv) || [&t1, &t2].iter().any(|t| Machine::parse(t).is_some_and(|m| m.carries() > carry_cap(job))) {
                continue;
            }
            let t = Instant::now();
            let (r, spent) = job.measured(budget, |job| rewrite_plan(job, n, kv, &t1, &t2));
            let took = t.elapsed();
            let fell = spent.fallbacks;
            // a law the rewriter cannot close at all counts as a straggler too (fixed once it is proved machine-free)
            unproved += r.is_none() as usize;
            let fell = if r.is_none() { fell.max(1) } else { fell };
            if r.is_none() || fell > 0 {
                let (normal, _) = job.measured(budget, |job| [rewrite(job, &t1, n, kv).0, rewrite(job, &t2, n, kv).0]);
                println!("RULEMINER straggler {name}: {} = {} ({fell} machine proofs, {took:?}{})", normal[0].show(), normal[1].show(), if r.is_none() { ", UNPROVED" } else { "" });
                stragglers.push((name, t1, t2, normal, fell, took));
            } else {
                clean.push((name, t1, t2));
            }
        }
    });
    let base_time: f64 = stragglers.iter().map(|s| s.5.as_secs_f64()).sum();
    println!("RULEMINER {} stragglers of {} laws, {:.1}s base ({unproved} unproved)", stragglers.len(), laws.len(), base_time);
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
    Laws { stragglers, scored, guard_w, n, kv }
}

/// The candidate rules for the stragglers (P3, P4), one per left side, and the other right sides of each left side (`rivals`).
fn candidates(laws: &Laws, cfg: &MinerConfig, base: &[(Term, Term)], extra: &[(Term, Term)]) -> (Vec<(Term, Term)>, hashbrown::HashMap<Term, Vec<(Term, Term)>>) {
    let (n, kv, stragglers) = (laws.n, laws.kv, &laws.stragglers);
    // the pool's rules go down in the rule order, ties broken by `tie_greater` (reassociation rules; section 70); the step
    // budget and the same-term check in `rule_step` still back up termination, and soundness is unaffected
    // goal-directed candidates: abstract each arithmetic subterm of a straggler's normalized terms into a pattern over
    // at most `POOL_VARS` variables (cutting subterms into variables), and look for a smaller term over the same variables
    // with the same values (`Pool`)
    let mut pool = Pool::new(n);
    println!("RULEMINER pool of {} terms, {} distinct functions", pool.terms, pool.index.len());
    // patterns seen (`None`), and cross-side rules seen (`Some(rhs)`)
    let mut seen_pat: hashbrown::HashSet<(Term, Option<Term>)> = Default::default();
    let mut cands: Vec<(Term, Term)> = vec![];
    for st in stragglers {
        let mut subs = vec![];
        st.3[0].subterms(&mut subs);
        st.3[1].subterms(&mut subs);
        for sub in subs.iter().filter(|t| matches!(*t.node(), Node::Op(LT, ..)) || t.uses_add() && t.size() >= 3) {
            for (pat, _) in abstractions(sub, POOL_VARS) {
                let Node::Op(..) = *pat.node() else { continue };
                if !seen_pat.insert((pat, None)) || pat.size() > 9 {
                    continue;
                }
                for r in pool.equal(&pat).iter().filter(|r| rule_order_or_tie(&pat, r) && (0..POOL_VARS).all(|v| !r.has_var(v) || pat.has_var(v))) {
                    cands.push((pat, *r));
                }
            }
        }
    }
    // cross-side candidates: a subterm of one normalized side and a subterm of the other with the same value, both
    // abstracted by the same cuts (up to four variables): the rule `abstract(s) -> abstract(s')`
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
                    for (pat, cuts) in abstractions(x, CROSS_VARS) {
                        let Node::Op(..) = *pat.node() else { continue };
                        if cuts.len() <= 2 || pat.size() > 13 {
                            continue; // up to two variables is the pool route's job; at three both routes look (the pool's right sides are up to 5 nodes, these any size)
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
    cands.extend_from_slice(extra);
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
    // rivals: the other right sides of each left side; a round's winner gives way to a rival that gains more on the same laws
    // (`Rounds::pick`; docs/tier-cycle.md, "Preferences and rival orientations in the miner")
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

/// The pool route's variables: over three the miner finds small rules that carry to unseen laws (held-out M -6.9% against
/// two, docs/tier-cycle.md, "A pool route over three variables finds them").
const POOL_VARS: usize = 3;

/// The pool route's terms: every term of up to 5 nodes over `POOL_VARS` variables and the constants, by their values on every
/// width-n input (4096 bytes a term over three variables at width 4); `lt` terms (one-bit values) only as roots over two terms
/// of up to 3 nodes, indexed apart so their 0/1 values never meet the n-bit constants.
struct Pool {
    memo: ValueMemo<u8>,
    index: hashbrown::HashMap<Vec<u8>, Vec<Term>>,
    index_lt: hashbrown::HashMap<Vec<u8>, Vec<Term>>,
    /// The terms outside `lt`.
    terms: usize,
}

impl Pool {
    fn new(n: usize) -> Pool {
        let size = 5;
        let mut by_size: Vec<Vec<Term>> = vec![vec![]; size + 1];
        by_size[1] = (0..POOL_VARS).map(Term::v).chain([Term::ZERO, Term::ONES]).collect();
        for sz in 2..=size {
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
        let mut pool = Pool { memo: ValueMemo::exhaustive(n, POOL_VARS), index: Default::default(), index_lt: Default::default(), terms: 0 };
        for t in by_size.iter().flatten() {
            pool.index.entry(pool.memo.values(t).to_vec()).or_default().push(*t);
            pool.terms += 1;
        }
        for a in by_size.iter().take(4).flatten() {
            for b in by_size.iter().take(4).flatten() {
                let t = Term::op(LT, *a, *b);
                pool.index_lt.entry(pool.memo.values(&t).to_vec()).or_default().push(t);
            }
        }
        pool
    }

    /// The pool's terms equal to `pat` (over at most `POOL_VARS` variables) on every input.
    fn equal(&mut self, pat: &Term) -> &[Term] {
        let index = if matches!(*pat.node(), Node::Op(LT, ..)) { &self.index_lt } else { &self.index };
        index.get(self.memo.values(pat)).map_or(&[], |g| g.as_slice())
    }
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

/// Proves candidate rules against the rules it copies to each proving thread (the base ones). The step
/// budget is `proving`'s own: every rewrite of `prove_rule` runs under it.
struct Prover {
    rules: Vec<(Term, Term)>,
    n: usize,
}

impl Prover {
    /// `rules` as the run-time rules, with both switches off whatever the caller has on.
    fn install(&self, setup: &Setup) -> Rules {
        Rules::new(setup, self.rules.clone())
    }

    fn holds(&self, job: &mut Job, (l, r): &(Term, Term)) -> bool {
        prove_rule(job, self.n, l.max_var().max(r.max_var()) + 1, l, r).is_some()
    }

    /// Proves one rule in an intern scope of its own.
    fn prove(&self, job: &mut Job, rule: &(Term, Term)) -> bool {
        tatic::kernel::scoped(|| {
            let rules = self.install(job.setup());
            job.with_rules(rules, |job| self.holds(job, rule))
        })
    }

    /// The indices of the candidates that are proved, in order, on `threads` workers (one intern scope each; one thread
    /// proves on this thread).
    fn filter(&self, job: &mut Job, cands: &[(Term, Term)], threads: usize) -> Vec<usize> {
        let prove = |job: &mut Job, idx: &[usize]| -> Vec<usize> {
            tatic::kernel::scoped(|| {
                let rules = self.install(job.setup());
                job.with_rules(rules, |job| idx.iter().copied().filter(|&i| self.holds(job, &cands[i])).collect())
            })
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
    /// the base rules in force
    base: Vec<(Term, Term)>,
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
            base,
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
    fn score_laws(&self, job: &mut Job, extra: &[(Term, Term)], which: &[usize], record: bool, seed: Option<RewriteMemo>) -> (Vec<(bool, i64, Trace)>, RewriteMemo) {
        let (n, kv, cfg) = (self.laws.n, self.laws.kv, self.cfg);
        job.rw.memo = Some(seed.unwrap_or_else(|| RewriteMemo::new(kv)));
        let steps = LAW_STEPS;
        // counting only under `RULEMINER_FAST`, or when the caller asked for it (rivals, below). Carry-over: the old code
        // installed these rules and left them installed, which nothing read: every later rewrite on this thread
        // is another `score_laws` or a `Prover::prove`, and each installs its own
        let rules = job.rules().with_mined(job.setup(), self.base.iter().chain(extra).cloned().collect());
        let rules = rules.counting(cfg.fast || rules.score_only());
        let out = job.with_rules(rules, |job| {
            which
                .iter()
                .map(|&si| {
                    let s = &self.laws.scored[si];
                    if record {
                        job.rw.trace = Some(vec![]);
                    }
                    let (ok, spent) = job.measured(steps, |job| rewrite_plan(job, n, kv, &s.1, &s.2).is_some());
                    let fixed = ok && spent.fallbacks < s.4;
                    // the rule order's own measure: operator nodes first, then variable occurrences
                    let measure = |t: &Term| {
                        let mut occ = [0usize; 8];
                        t.occurrences(&mut occ);
                        let (c, a) = rule_weight(t);
                        (c + a.iter().sum::<i64>()) * 16 + occ.iter().sum::<usize>() as i64
                    };
                    let normal = |job: &mut Job| measure(&rewrite(job, &s.1, n, kv).0) + measure(&rewrite(job, &s.2, n, kv).0);
                    let size = if si < self.laws.stragglers.len() { job.measured(steps, normal).0 } else { 0 };
                    let mut seen: hashbrown::HashSet<(Term, Fired)> = Default::default();
                    let trace = Trace::new(job.rw.trace.take().unwrap_or_default().into_iter().filter(|t| seen.insert(*t)).collect());
                    (fixed, size, trace)
                })
                .collect()
        });
        let memo = job.rw.memo.take().unwrap();
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

/// The greedy rounds over the provable candidates and the proofs of their winners (P6-P8), all on this
/// thread; the scoring workers share only the `Scorer`.
struct Rounds<'a> {
    scorer: &'a Scorer<'a>,
    prover: &'a Prover,
    provable: &'a [(Term, Term)],
    rivals: &'a hashbrown::HashMap<Term, Vec<(Term, Term)>>,
    cfg: &'a MinerConfig,
    clock: &'a Clock,
    /// under `RULEMINER_FAST` the candidates are proved here, once each, against the base rules as the eager filter would
    proofs: Vec<Option<bool>>,
    /// a round's winner is proved on a thread of its own while the next round is scored (`speculate`, set for the rounds'
    /// picks): the round takes it as provable and is committed when its proof is in, and a failed proof rolls the rounds back
    /// to it (`play`). Any other proof of a pending candidate waits for its result
    proof_tx: std::sync::mpsc::Sender<(usize, Result<bool, WorkerPanicked>)>,
    proof_rx: std::sync::mpsc::Receiver<(usize, Result<bool, WorkerPanicked>)>,
    pending: hashbrown::HashSet<usize>,
    speculate: bool,
    spawn_req: Option<usize>,
    /// the last evaluation's memo, under its rules: an entry holds under other rules when no rule in or out touches a term of its
    /// trace (`RewriteMemo::filtered`), so each evaluation is seeded with what the rules that changed cannot touch
    state_memo: Option<(Vec<(Term, Term)>, RewriteMemo)>,
    state_time: std::time::Duration,
    /// the time spent bounding the candidates' gains
    bound_time: std::time::Duration,
    scorings: usize,
    skipped: usize,
    /// rivals' proofs (`best_rival`), proved and failed, and their time: unlike a winner's, on this thread
    rival_proofs: [usize; 2],
    rival_time: std::time::Duration,
}

/// The candidates a round scores, by their gain's bound, largest first, ties to the earlier: those not chosen already. A
/// chosen rule changes nothing, so a scoring mismatch that gave it a gain would win every round and the mine would never
/// end (run 2026-10-22-hidden-twins-2: `add(0, x) -> x` 8631 times, `rewrite::a_cached_failed_join_yields_to_a_stored_path`).
fn by_bound(provable: &[(Term, Term)], chosen: &[(Term, Term)], bound: impl Fn(usize) -> i64) -> Vec<(i64, usize)> {
    let mut order: Vec<(i64, usize)> = (0..provable.len()).filter(|&i| !chosen.contains(&provable[i])).map(|i| (bound(i), i)).collect();
    order.sort_by_key(|&(b, i)| (std::cmp::Reverse(b), i));
    order
}

/// The rival that replaces a round's winner of gain `g`: in the rivals' order, each that gains more than the best so far and
/// proves; a rival already chosen is passed over, as `by_bound` passes over a chosen candidate.
fn best_rival(rivals: &[(Term, Term)], gains: &[i64], g: i64, chosen: &[(Term, Term)], mut prove: impl FnMut(&(Term, Term)) -> bool) -> Option<((Term, Term), i64)> {
    let mut rival: Option<((Term, Term), i64)> = None;
    for (rv, &rg) in rivals.iter().zip(gains) {
        if !chosen.contains(rv) && rg > rival.as_ref().map_or(g, |r| r.1) && prove(rv) {
            rival = Some((*rv, rg));
        }
    }
    rival
}


/// A worker thread's result sent to the thread waiting on it: the worker panicked.
#[derive(Debug)]
struct WorkerPanicked;

/// Runs a worker's `f` and `send`s its result, or that it panicked, then lets the panic go on to the worker's scope. The
/// waiter keeps a sender, so a worker that died without sending hung it at 0 CPU (a band-17 mine, run
/// `2026-10-25-held-seen`); now it fails at once on `expect`.
fn relay<T>(f: impl FnOnce() -> T, send: impl FnOnce(Result<T, WorkerPanicked>)) {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)) {
        Ok(t) => send(Ok(t)),
        Err(p) => {
            send(Err(WorkerPanicked));
            std::panic::resume_unwind(p)
        }
    }
}
impl<'a> Rounds<'a> {
    fn new(scorer: &'a Scorer<'a>, prover: &'a Prover, provable: &'a [(Term, Term)], rivals: &'a hashbrown::HashMap<Term, Vec<(Term, Term)>>, cfg: &'a MinerConfig, clock: &'a Clock) -> Self {
        let (proof_tx, proof_rx) = std::sync::mpsc::channel::<(usize, Result<bool, WorkerPanicked>)>();
        Rounds {
            scorer,
            prover,
            provable,
            rivals,
            cfg,
            clock,
            proofs: vec![if cfg.fast { None } else { Some(true) }; provable.len()],
            proof_tx,
            proof_rx,
            pending: Default::default(),
            speculate: false,
            spawn_req: None,
            state_memo: None,
            state_time: std::time::Duration::ZERO,
            bound_time: std::time::Duration::ZERO,
            scorings: 0,
            skipped: 0,
            rival_proofs: [0; 2],
            rival_time: std::time::Duration::ZERO,
        }
    }

    fn resolve(&mut self, i: usize) -> bool {
        loop {
            if let Some(b) = self.proofs[i] {
                return b;
            }
            let (j, b) = self.proof_rx.recv().unwrap();
            let b = b.expect("a proof thread panicked");
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
        let (eval, grown) = self.scorer.score_laws(job, &chosen, &self.scorer.all_laws, true, seed);
        self.state_memo = Some((chosen.clone(), grown));
        let (covered, size) = Scorer::summarize(&eval);
        self.state_time += t0.elapsed();
        Chosen { chosen, eval, covered, size }
    }

    /// one round on top of `s`: the rule it takes, with its gain: the winner, or a rival orientation of it that gains more and
    /// proves (docs/tier-cycle.md, "With small rules, the lookahead buys nothing: take the rival")
    fn pick(&mut self, job: &mut Job, s: &Chosen) -> Option<((Term, Term), i64)> {
        let (scorer, provable, rivals, cfg) = (self.scorer, self.provable, self.rivals, self.cfg);
        let (stragglers, guard_w) = (&scorer.laws.stragglers, scorer.laws.guard_w);
        let (chosen, base_eval, covered, size) = (&s.chosen, &s.eval, &s.covered, s.size);
        // a candidate changes only the laws whose rewriting asked about a term its left side matches, or whose join examined a
        // term it is a step at (`affected`, `Trace::touched_by`), so its gain is at most
        // 1000 per affected uncovered straggler, `guard_w` per affected uncovered guard law and the affected stragglers' whole size
        // a candidate can only rewrite a term where it comes before the rule that fired (`Fired::preempted_by`; the trace was
        // made without the candidate)
        // the run-time order of every rule in play, ranked once (`run_order` builds strings)
        let t0 = Instant::now();
        let mut ranked: Vec<(Term, Term)> = scorer.base.iter().chain(chosen).chain(provable.iter()).cloned().collect();
        ranked.sort_by_cached_key(|(l, r)| run_order(l, r));
        let rank: hashbrown::HashMap<(Term, Term), usize> = ranked.into_iter().enumerate().map(|(i, r)| (r, i)).collect();
        // every law's trace at once (`TraceIndex`: a term shared by many laws' traces is matched once), the candidates split
        // over the scoring threads; each candidate's laws are the same whichever thread finds them
        let index = TraceIndex::new(base_eval.iter().map(|e| &e.2));
        let touched = |rule: &(Term, Term)| {
            let before = |fired: &(Term, Term)| rank.get(fired).is_none_or(|&f| rank[rule] < f);
            index.touched(rule, |fired| fired.preempted_by(before))
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
        let order = by_bound(provable, chosen, bound);
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
            let (fresh, _) = scorer.score_laws(job, &with, aff, true, None);
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
            let frozen = job.join_store.as_ref().and_then(JoinStoreUse::frozen);
            for _ in 0..threads {
                let (done_tx, score_job, queue, join_workers, frozen, setup) = (done_tx.clone(), &score_job, queue.clone(), &scorer.join_workers, frozen.clone(), job.setup().clone());
                let worker = move || {
                    let job = &mut Job::new(setup);
                    job.join_store = frozen.map(JoinStoreUse::Read);
                    let ((), spent) = job.spent(|job| {
                        tatic::kernel::scoped(|| loop {
                            let Ok(item) = queue.lock().unwrap().recv() else { break };
                            relay(|| score_job(job, item), |r| done_tx.send((item, r)).unwrap());
                        })
                    });
                    join_workers.lock().unwrap().add(spent.join);
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
                    let r = r.expect("a scoring thread panicked");
                    results[i] = Some(r);
                }
            };
            let mut gains = vec![0; winner.map_or(0, |i| rivals_of(i).len())];
            for k in 0..gains.len() {
                work.send((winner.unwrap(), Some(k))).unwrap();
            }
            for ((_, k), r) in done_rx.iter().take(gains.len()) {
                let r = r.expect("a scoring thread panicked");
                gains[k.unwrap()] = r.0;
            }
            (winner, gains)
        });
        self.scorings += next;
        self.skipped += order.len() - next;
        self.clock.phase(&format!("round over {} of {} candidates", next, provable.len()));
        let Some(i) = winner else { return None };
        let g = results[i].as_ref().unwrap().0;
        // in the rivals' order, as when they were scored one after another here
        let (t, mut proved) = (Instant::now(), [0usize; 2]);
        let rival = best_rival(rivals_of(i), &rival_gains, g, chosen, |rv| {
            let b = self.prover.prove(job, rv);
            proved[!b as usize] += 1;
            if !b {
                println!("RULEMINER rival not provable: {}", rule_show(rv));
            }
            b
        });
        (self.rival_proofs[0], self.rival_proofs[1]) = (self.rival_proofs[0] + proved[0], self.rival_proofs[1] + proved[1]);
        self.rival_time += t.elapsed();
        Some(rival.unwrap_or((provable[i], g)))
    }

    /// commits the open rounds whose proofs hold, oldest first, until `keep` are left; at a failed proof, voids the rounds built
    /// on it and returns it, to be played again (its failed winner is never picked again)
    fn settle(&mut self, job: &mut Job, open: &mut Vec<Open>, keep: usize) -> Option<Open> {
        while open.len() > keep {
            let o = open.remove(0);
            if o.proof.is_none_or(|i| self.resolve(i)) {
                println!("{}", o.line);
                job.setup().result("chosen", &o.rule);
                continue;
            }
            println!("RULEMINER rolled back to round {}: its winner {} is not provable", o.round, o.proof.map_or(String::new(), |i| rule_show(&self.provable[i])));
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
                std::thread::Builder::new().stack_size(256 << 20).spawn_scoped(sc, move || relay(|| prover.prove(&mut Job::new(setup), rule), |r| tx.send((i, r)).unwrap())).unwrap();
            };
            let (mut s, mut round, mut open) = (self.state(job, vec![]), 0, Vec::<Open>::new());
            loop {
                self.speculate = true;
                let picked = if round < self.cfg.rounds { self.pick(job, &s) } else { None };
                self.speculate = false;
                let proof = self.spawn_req.take();
                proof.map(spawn);
                let Some((rule, _)) = picked else {
                    match self.settle(job, &mut open, 0) {
                        Some(o) => (s, round) = (o.before, o.round),
                        None => break s,
                    }
                    continue;
                };
                let next = self.state(job, s.chosen.iter().chain([&rule]).cloned().collect());
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

    /// The closing report (P10): the scoring's reuse and skips, lazy proofs, times, the join's work (the workers', and the
    /// main job's, `join_main`) and the stragglers the final rules `covered` leaves.
    fn report(&self, covered: &[bool], join_main: JoinCost) {
        let (scorer, stragglers) = (self.scorer, &self.scorer.laws.stragglers);
        println!("RULEMINER scoring reused {} of {} law evaluations", scorer.law_reuses.load(std::sync::atomic::Ordering::Relaxed), scorer.law_evals.load(std::sync::atomic::Ordering::Relaxed));
        println!("RULEMINER the gain bound skipped {} of {} candidate scorings", self.skipped, self.scorings + self.skipped);
        if self.cfg.fast {
            let p = &self.proofs;
            println!("RULEMINER lazy proofs: {} proved, {} failed", p.iter().filter(|x| **x == Some(true)).count(), p.iter().filter(|x| **x == Some(false)).count());
        }
        println!("RULEMINER rival proofs: {} proved, {} failed, {:.1}s", self.rival_proofs[0], self.rival_proofs[1], self.rival_time.as_secs_f64());
        println!("RULEMINER time in rule-set evaluations: {:.1}s", self.state_time.as_secs_f64());
        println!("RULEMINER time bounding candidates' gains: {:.1}s", self.bound_time.as_secs_f64());
        let mut j = *scorer.join_workers.lock().unwrap();
        j.add(join_main);
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

/// A round's candidates leave out the rules already chosen, and the rest go by bound, largest first, ties to the earlier.
#[test]
fn a_round_never_offers_a_chosen_rule() {
    let r = |l: &str, rhs: &str| (parse_term(l), parse_term(rhs));
    let provable = [r("add(0, x)", "x"), r("sub(x, x)", "0"), r("xor(x, x)", "0")];
    let bounds = [5, 9, 7];
    assert_eq!(by_bound(&provable, &[provable[1]], |i| bounds[i]), vec![(7, 2), (5, 0)]);
    assert_eq!(by_bound(&provable, &[], |i| if i == 1 { 5 } else { bounds[i] }), vec![(7, 2), (5, 0), (5, 1)]);
}

/// A winner's rival already chosen is passed over, however much it claims; the next rival that gains more and proves wins.
#[test]
fn a_round_never_offers_a_chosen_rival() {
    let r = |l: &str, rhs: &str| (parse_term(l), parse_term(rhs));
    let rivals = [r("sub(x, x)", "0"), r("sub(x, x)", "and(x, 0)"), r("sub(x, x)", "xor(x, x)")];
    let chosen = [rivals[0]];
    assert!(best_rival(&rivals, &[9, 4, 7], 3, &chosen, |_| true) == Some((rivals[2], 7)));
    assert!(best_rival(&rivals, &[9, 4, 7], 3, &chosen, |rv| *rv != rivals[2]) == Some((rivals[1], 4)));
    assert!(best_rival(&rivals, &[9, 2, 1], 3, &chosen, |_| true) == None);
}

#[test]
fn a_provers_rules_ignore_the_callers_switches() {
    let prover = Prover { rules: vec![], n: 4 };
    let job = &mut Job::new(Setup::process());
    let counting = job.rules().counting(true).tracing(true);
    let installed = job.with_rules(counting, |job| prover.install(job.setup()));
    assert!(installed.is(&installed.counting(false).tracing(false)), "a prover proves with both switches off");
}

/// The pool route looks patterns up over three variables, `lt` roots too: a pattern's group is the pool's terms equal to it on
/// every input (docs/tier-cycle.md, "A pool route over three variables finds them").
#[test]
fn the_pool_finds_terms_over_three_variables() {
    let mut pool = Pool::new(4);
    let p = parse_term;
    assert!(pool.equal(&p("sub(add(x, z), add(y, z))")).contains(&p("sub(x, y)")));
    assert!(!pool.equal(&p("sub(add(x, z), add(y, z))")).contains(&p("sub(x, z)")));
    assert!(pool.equal(&p("lt(x, and(and(y, z), y))")).contains(&p("lt(x, and(y, z))")));
}

/// A worker that panics fails the thread waiting for its result instead of hanging it: the waiter keeps a sender, so the
/// channel never closes (a band-17 mine hung at 0 CPU after a join step panicked, run `2026-10-25-held-seen`).
#[test]
fn a_panicked_worker_fails_its_waiter() {
    let (end_tx, end_rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let waited = std::panic::catch_unwind(|| {
            std::thread::scope(|sc| {
                let (tx, rx) = std::sync::mpsc::channel();
                for i in 0..2usize {
                    let tx = tx.clone();
                    sc.spawn(move || relay(|| if i == 1 { panic!("worker {i}") } else { i }, |r| drop(tx.send(r))));
                }
                rx.iter().take(2).map(|r: Result<usize, WorkerPanicked>| r.expect("a worker panicked")).sum::<usize>()
            })
        });
        let _ = end_tx.send(waited.is_err());
    });
    assert_eq!(end_rx.recv_timeout(std::time::Duration::from_secs(30)), Ok(true), "the waiter panics, not hangs");
}

/// Laws of a stream mine (the first of `2026-10-23-cold-streams`' phase-3 mine 1) for `a_false_winner_rolls_the_rounds_back`.
const ROLLBACK_LAWS: &str = "\
add(and(x, add(z, -1)), and(y, add(x, -1))) = add(and(y, add(x, -1)), and(x, add(z, -1)))
xor(shr1(-1, 0), xor(y, xor(z, -1))) = xor(xor(z, -1), xor(y, shr1(xor(x, xor(-1, x)), 0)))
sub(x, sub(z, shr1(sub(shr1(-1, 0), y), 0))) = sub(shr1(sub(shr1(-1, 0), y), 0), sub(z, x))
sub(y, xor(z, sub(x, shr1(x, 0)))) = sub(y, xor(z, sub(x, shr1(xor(sub(0, -1), x), 0))))
and(add(x, and(x, z)), add(x, and(y, z))) = and(add(x, and(z, y)), add(x, and(x, and(z, x))))
xor(x, xor(-1, and(xor(y, z), xor(x, y)))) = xor(xor(-1, y), and(xor(x, y), xor(x, z)))
xor(-1, or(xor(and(x, y), y), xor(x, z))) = xor(x, xor(-1, and(or(z, y), or(xor(y, x), z))))
or(y, or(z, sub(or(or(x, z), y), -1))) = or(or(z, y), sub(or(y, or(z, x)), -1))
add(sub(x, -1), xor(z, add(y, xor(x, z)))) = sub(x, xor(z, sub(xor(x, xor(-1, z)), y)))
add(add(y, z), and(add(x, x), add(x, y))) = add(y, add(z, and(shl1(x, 0), add(x, y))))
xor(x, xor(xor(-1, y), shl1(xor(x, xor(y, z)), 0))) = xor(xor(-1, x), xor(y, shl1(xor(xor(x, z), y), 0)))
sub(sub(z, x), sub(y, shl1(shl1(-1, 0), 0))) = sub(sub(z, y), sub(x, shl1(shl1(-1, 0), 0)))
sub(0, xor(y, sub(xor(x, y), xor(y, z)))) = sub(xor(sub(-1, y), sub(xor(x, y), xor(z, y))), -1)
or(or(x, y), shr1(or(x, or(y, z)), 0)) = or(x, or(y, or(shr1(or(z, y), 0), shr1(x, 0))))
and(xor(y, and(z, y)), shr1(and(x, y), 0)) = and(xor(y, z), and(y, xor(z, shr1(and(y, x), 0))))
and(sub(z, x), shr1(and(y, z), 0)) = and(shr1(y, 0), and(sub(z, x), shr1(z, 0)))
and(and(x, shr1(z, 0)), and(y, shl1(shl1(-1, 0), 0))) = and(shr1(z, 0), and(and(y, x), shl1(shl1(-1, 0), 0)))
or(add(y, add(add(x, -1), x)), add(y, or(y, z))) = or(add(y, or(y, z)), add(add(x, x), add(y, -1)))
add(xor(x, z), add(y, add(-1, and(x, y)))) = add(y, add(-1, add(and(x, y), xor(x, z))))
sub(sub(-1, z), add(x, add(x, add(x, y)))) = sub(0, add(x, add(add(x, x), add(z, sub(y, -1)))))
sub(sub(z, x), add(-1, or(add(-1, y), sub(x, y)))) = sub(z, add(x, add(-1, or(add(y, -1), sub(x, y)))))
and(and(x, y), xor(z, sub(y, xor(xor(x, y), -1)))) = and(x, and(y, xor(z, sub(y, sub(-1, xor(y, x))))))
and(add(add(z, z), -1), add(x, and(y, z))) = and(add(x, and(z, and(y, z))), add(z, add(z, -1)))
xor(x, xor(y, shl1(xor(x, xor(-1, z)), 0))) = xor(xor(y, x), shl1(xor(z, xor(-1, x)), 0))
";

/// A winner whose proof fails rolls the rounds back to its round, and the mine plays on without it (`Rounds::settle`):
/// offered a false but attractive candidate, a `RULEMINER_FAST` mine picks it, rolls back and ends where it would have
/// without it. Replaces `RULEMINER_EXTRA` and `docs/runs/2026-10-12/scripts/spec_rollback.sh` (CU4a).
#[test]
fn a_false_winner_rolls_the_rounds_back() {
    let path = std::env::temp_dir().join(format!("rollback_laws_{}.txt", std::process::id()));
    std::fs::write(&path, ROLLBACK_LAWS).unwrap();
    let setup = Setup::with_env(vec![("RULEMINER_LAWFILE".into(), path.display().to_string()), ("RULEMINER_FAST".into(), "1".into())]);
    let r = |l: &str, rhs: &str| (parse_term(l), parse_term(rhs));
    // it collapses every `sub`, so laws whose sides differ only inside one become `0 = 0`: it wins round 0
    let false_rule = r("sub(x, y)", "0");
    let (plain, plain_failed) = mine(&setup, &[]);
    let (chosen, failed) = mine(&setup, &[false_rule]);
    std::fs::remove_file(&path).ok();
    assert_eq!((plain_failed, failed), (0, 1), "the false rule won a round and failed its proof");
    // the rounds after the rollback replay the plain mine's (the false rule's left side has no candidate of its own here)
    assert_eq!(chosen, plain);
}
