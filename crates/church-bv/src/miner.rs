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
    /// docs/tier-cycle/ "cmp3d's library lost its general rules").
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
    /// `RULEMINER_EXTRAS_FROM=<i>`, `_KEEP=<n>`, `_BY=first|small|ctx` (all three or none): the lawfile's laws from line `i` are a
    /// pool of extras and the mine keeps `n` of them (`kept_indices`); the laws before `i` are always read.
    pub extras: Option<ExtrasKeep>,
    /// `RULEMINER_POOL_DUMP=<prefix>` (with `extras` by `first`): before cutting the pool, classify it and write the raw facts
    /// the context scorer needs to `<prefix>_pool.tsv` (`ctx_scorer::pool_tsv`) and `<prefix>_served.txt` (the served
    /// stragglers' normal forms); the mine itself runs as without it.
    pub pool_dump: Option<String>,
    /// `RULEMINER_CTX_WEIGHTS=<file>` (required by `_BY=ctx`): the context model's weights (`ctx_scorer::LAYOUT`).
    pub ctx_weights: Option<String>,
}

/// How a mine picks its extras from the pool: `First` the first `n`, `Small` the stragglers the base rules leave, fewest
/// rewrite steps then smallest normal form first, any shortfall filled with the pool's other laws in order
/// (docs/superpowers/specs/2026-10-31-context-aware-selector-design.md); `Ctx` the same stragglers, highest context-model score
/// first (`RULEMINER_CTX_WEIGHTS`, docs/superpowers/specs/2026-11-01-context-aware-scorer-design.md).
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Keep {
    First,
    Small,
    Ctx,
}

impl Keep {
    /// The driver variable `EXTRAS_SELECT` / `RULEMINER_EXTRAS_BY`.
    pub fn parse(s: &str) -> Result<Keep, String> {
        match s {
            "first" => Ok(Keep::First),
            "small" => Ok(Keep::Small),
            "ctx" => Ok(Keep::Ctx),
            _ => Err(format!("EXTRAS_SELECT: expected first, small or ctx, got {s}")),
        }
    }
}

/// The lawfile's pool of extras starts at line `from`; the mine keeps `n` of it, chosen `by`.
#[derive(Clone, Copy, Debug)]
pub struct ExtrasKeep {
    pub from: usize,
    pub n: usize,
    pub by: Keep,
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
            extras: s.var("RULEMINER_EXTRAS_FROM").map(|from| {
                let need = |k: &str| s.var(k).unwrap_or_else(|| panic!("RULEMINER_EXTRAS_FROM needs {k}"));
                let num = |k: &str| need(k).parse::<usize>().unwrap_or_else(|_| panic!("{k}={} is not a count", need(k)));
                ExtrasKeep {
                    from: from.parse().unwrap_or_else(|_| panic!("RULEMINER_EXTRAS_FROM={from} is not a count")),
                    n: num("RULEMINER_EXTRAS_KEEP"),
                    by: Keep::parse(need("RULEMINER_EXTRAS_BY")).unwrap_or_else(|e| panic!("RULEMINER_EXTRAS_BY: {e}")),
                }
            }),
            pool_dump: s.var("RULEMINER_POOL_DUMP").map(String::from),
            ctx_weights: s.var("RULEMINER_CTX_WEIGHTS").map(String::from),
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
    tatic_kernel::scoped(|| {
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
            let laws = laws(job, &cfg, &base, budget, &clock);
            let (chosen, rolled_back) = cover(job, &laws, &cfg, &base, &clock, extra, false);
            (chosen.iter().map(rule_show).collect(), rolled_back)
        })
    })
}

/// The rounds of a mine over `laws`: the chosen rules and how many winners failed their proofs and rolled the rounds back.
/// `quiet` mines without a trace: no `chosen` record, no report or time lines (`mine` is loud; the pool dump covers the
/// served stragglers alone and must leave the loop's `rules.txt` and the logs as a mine without it does).
fn cover(job: &mut Job, laws: &Laws, cfg: &MinerConfig, base: &[(Term, Term)], clock: &Clock, extra: &[(Term, Term)], quiet: bool) -> (Vec<(Term, Term)>, usize) {
    let (cands, rivals) = candidates(laws, cfg.no_dup_lhs, base, extra, !quiet);
    if !quiet {
        clock.phase("candidate generation");
    }
    // keep candidates whose left side matches a subterm of some straggler's normalized terms
    let applicable = |l: &Term| laws.stragglers.iter().any(|s| reaches(l, s));
    let cands: Vec<(Term, Term)> = cands.into_iter().filter(|(l, _)| applicable(l)).take(CANDIDATE_CAP).collect();
    if !quiet {
        println!("RULEMINER {} applicable candidates (cap {CANDIDATE_CAP})", cands.len());
    }
    // each candidate is proved independently, on `RULEMINER_THREADS` workers; the proving reads the base rules of
    // this thread, so the workers copy them. `RULEMINER_FAST` scores without rule proofs (`shared_lemma`), so there only a
    // round's winner is proved (`proved_lazily`), and an unprovable one gives way to the next best
    let rules = job.rules().mined().to_vec();
    let prover = Prover { rules, n: laws.n };
    let provable: Vec<(Term, Term)> = if cfg.fast { cands.clone() } else { prover.filter(job, &cands, cfg.threads).into_iter().map(|i| cands[i]).collect() };
    if !quiet {
        println!("RULEMINER {} provable candidates of {} proposed", provable.len(), cands.len());
        clock.phase("provable filter");
    }
    let scorer = Scorer::new(laws, cfg, base.to_vec());
    let mut rounds = Rounds::new(&scorer, &prover, &provable, &rivals, cfg, clock);
    rounds.quiet = quiet;
    // the main job's join work from here on
    let (Chosen { chosen, covered, .. }, main) = job.spent(|job| rounds.play(job));
    if !quiet {
        rounds.report(&covered, main.join);
    }
    (chosen, rounds.proofs.iter().filter(|p| **p == Some(false)).count())
}

/// Whether each of the pool's `laws` is still a straggler with the `base` rules and the `chosen` ones installed (`mine`'s
/// own installation), each rewritten under `budget` steps.
fn still_stragglers(job: &mut Job, base: &[(Term, Term)], chosen: &[(Term, Term)], pool: &[(String, Term, Term)], budget: i64, fast: bool) -> Vec<bool> {
    let setup = job.setup().clone();
    let rules = job.rules().with_mined(&setup, base.iter().chain(chosen).cloned().collect());
    job.with_rules(rules, |job| classify(job, pool, budget, fast, false).iter().map(|o| matches!(o, Outcome::Straggler(..))).collect())
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
fn laws(job: &mut Job, cfg: &MinerConfig, base: &[(Term, Term)], budget: i64, clock: &Clock) -> Laws {
    let named = read_named_laws(&cfg.lawfile);
    clock.phase("law building");
    laws_for(job, named, cfg, base, budget, clock, true)
}

/// `laws_of` over the laws a mine reads: all of `named`, or, with `extras`, its served laws and `extras.n` of the pool after
/// them. `First` cuts the pool before classifying, so it costs and chooses what a file without the pool does; `Small`
/// classifies the pool and keeps its stragglers first, the fewest rewrite steps then the smallest normal form first.
fn laws_for(job: &mut Job, mut named: Vec<(String, Term, Term)>, cfg: &MinerConfig, base: &[(Term, Term)], budget: i64, clock: &Clock, loud: bool) -> Laws {
    let (guard_k, fast) = (cfg.guard, cfg.fast);
    let Some(x) = &cfg.extras else { return laws_of(job, named, guard_k, fast, budget, clock, loud) };
    if x.by == Keep::First {
        if let Some(prefix) = &cfg.pool_dump {
            dump_pool(job, &named, x.from, cfg, base, budget, clock, prefix);
        }
        named = kept_indices(named.len(), x.from, x.n, &|_| None).into_iter().map(|i| named[i].clone()).collect();
        return laws_of(job, named, guard_k, fast, budget, clock, loud);
    }
    let outcomes = classify(job, &named, budget, fast, loud);
    let from = x.from.min(named.len());
    let by_steps = |i: usize| match outcomes[i] {
        Outcome::Straggler(ref s, _, steps) => Some((steps, (s.3[0].size() + s.3[1].size()) as i64)),
        _ => None,
    };
    // `Ctx` ranks the same stragglers by the model's score (position 0 = highest) instead of by cost
    let by_model = (x.by == Keep::Ctx).then(|| ctx_pool_ranks(&named, &outcomes, from, cfg));
    let rank = |i: usize| match &by_model {
        Some(ranks) => ranks[i - from].map(|pos| (pos, 0)),
        None => by_steps(i),
    };
    let keep = kept_indices(named.len(), x.from, x.n, &rank);
    if loud {
        let pool_stragglers = (from..named.len()).filter(|&i| rank(i).is_some()).count();
        println!("RULEMINER extras: kept {} of {} pool laws, {pool_stragglers} stragglers in the pool", keep.len() - from, named.len() - from);
        let steps = |it: &mut dyn Iterator<Item = usize>| it.filter_map(|i| rank(i).map(|_| i)).fold((0i64, 0i64, 0usize), |(s, m, c), i| match outcomes[i] { Outcome::Straggler(.., v) => (s + v, m.max(v), c + 1), _ => (s, m, c) });
        let (kept, all) = (steps(&mut keep.iter().copied().filter(|&i| i >= from)), steps(&mut (from..named.len())));
        println!("RULEMINER extras steps: kept {} stragglers, sum {}, max {}; pool {} stragglers, sum {}, max {}", kept.2, kept.0, kept.1, all.2, all.0, all.1);
        if by_model.is_some() {
            let small = kept_indices(named.len(), x.from, x.n, &by_steps);
            println!("RULEMINER extras ctx-vs-small: {} of {} kept differ", kept_differ(&keep, &small, from), keep.len() - from);
        }
        clock.phase("extras selection");
    }
    assemble(keep.into_iter().map(|i| outcomes[i].clone()).collect(), guard_k, loud, clock)
}

/// The context scorer's view of `named` (outcomes `outcomes`, pool from `from`): each pool law with its raw facts (`uncovered`
/// is false: that needs a served-only cover, `dump_pool`) and the served stragglers' normal forms. One home for the facts the
/// dump writes and the `Ctx` rank scores.
fn pool_laws(named: &[(String, Term, Term)], outcomes: &[Outcome], from: usize) -> (Vec<crate::ctx_scorer::PoolLaw>, Vec<(Term, Term)>) {
    let pool = (from..named.len())
        .map(|i| {
            let (steps, size, fallbacks) = match &outcomes[i] {
                Outcome::Straggler(s, _, steps) => (*steps, (s.3[0].size() + s.3[1].size()) as i64, s.4),
                _ => (0, 0, 0),
            };
            crate::ctx_scorer::PoolLaw { law: (named[i].1.clone(), named[i].2.clone()), straggler: matches!(outcomes[i], Outcome::Straggler(..)), steps, size, fallbacks: fallbacks as _, uncovered: false }
        })
        .collect();
    let served = outcomes[..from]
        .iter()
        .filter_map(|o| match o {
            Outcome::Straggler(s, ..) => Some((s.3[0].clone(), s.3[1].clone())),
            _ => None,
        })
        .collect();
    (pool, served)
}

/// The rank of each pool law (indexed `i - from`) under the context model `RULEMINER_CTX_WEIGHTS` names: the stragglers by
/// descending score (`ctx_scorer::ctx_ranks`), `None` for the rest. A model that cannot be read or does not fit the miner's
/// features stops the mine.
fn ctx_pool_ranks(named: &[(String, Term, Term)], outcomes: &[Outcome], from: usize, cfg: &MinerConfig) -> Vec<Option<i64>> {
    use crate::ctx_scorer::{ctx_ranks, runtime_cols, runtime_rows, Model, LAYOUT};
    fn refuse(path: &str, why: impl std::fmt::Display) -> ! {
        panic!("RULEMINER_CTX_WEIGHTS={path}: {why}")
    }
    let path = cfg.ctx_weights.as_deref().expect("RULEMINER_EXTRAS_BY=ctx needs RULEMINER_CTX_WEIGHTS (the model's weights file)");
    let text = std::fs::read_to_string(path).unwrap_or_else(|e| refuse(path, e));
    let model = Model::from_text(&text, LAYOUT).unwrap_or_else(|e| refuse(path, e));
    if model.width() != runtime_cols().len() {
        refuse(path, format!("model width {} is not the miner's {}", model.width(), runtime_cols().len()));
    }
    let (pool, served) = pool_laws(named, outcomes, from);
    if pool.is_empty() {
        return vec![];
    }
    let scores: Vec<f64> = runtime_rows(&pool, &served).iter().map(|r| model.score(r)).collect();
    ctx_ranks(&scores, &pool.iter().map(|p| p.straggler).collect::<Vec<_>>())
}

/// How many of the pool laws (indices `>= from`) in `keep` are not in `other`.
fn kept_differ(keep: &[usize], other: &[usize], from: usize) -> usize {
    keep.iter().filter(|&&i| i >= from && !other.contains(&i)).count()
}

/// The pool dump (`MinerConfig::pool_dump`) of `named`, whose pool starts at line `from`: classify every law under the
/// installed base, cover the served stragglers alone (a quiet `cover`), and write, per pool law, whether it is a straggler
/// (steps, normal-form size, machine proofs) and whether it stays one under `base` plus those rules, with the served
/// stragglers' normal forms. Nothing here changes what the mine goes on to do.
#[allow(clippy::too_many_arguments)]
fn dump_pool(job: &mut Job, named: &[(String, Term, Term)], from: usize, cfg: &MinerConfig, base: &[(Term, Term)], budget: i64, clock: &Clock, prefix: &str) {
    let from = from.min(named.len());
    let outcomes = classify(job, named, budget, cfg.fast, false);
    let (pool, served_forms) = pool_laws(named, &outcomes, from);
    let served_normal_forms: String = served_forms.iter().map(|(l, r)| format!("{} = {}\n", l.show(), r.show())).collect();
    let (chosen, _) = cover(job, &assemble(outcomes[..from].to_vec(), cfg.guard, false, clock), cfg, base, clock, &[], true);
    let uncovered = still_stragglers(job, base, &chosen, &named[from..], budget, cfg.fast);
    let rows: Vec<(usize, String, Option<(i64, i64, u64)>, bool)> = pool
        .iter()
        .enumerate()
        .map(|(j, p)| (j, named[from + j].0.clone(), p.straggler.then_some((p.steps, p.size, p.fallbacks)), uncovered[j] && p.straggler))
        .collect();
    std::fs::write(format!("{prefix}_pool.tsv"), crate::ctx_scorer::pool_tsv(&rows)).expect("write the pool dump");
    std::fs::write(format!("{prefix}_served.txt"), served_normal_forms).expect("write the served stragglers");
}

/// The indices of the `len` laws a mine reads, ascending: the served laws `..from` and `n` of the pool `from..`. The pool's
/// stragglers (the laws `rank` gives `Some`) come first, smallest rank first and equal ranks in stream order, then, short of
/// `n`, its other laws in order; `rank` of `None` everywhere is the pool's first `n`. Asked of pool indices only.
pub(crate) fn kept_indices(len: usize, from: usize, n: usize, rank: &dyn Fn(usize) -> Option<(i64, i64)>) -> Vec<usize> {
    let from = from.min(len);
    let mut keep: Vec<usize> = (0..from).collect();
    let (mut s, rest): (Vec<usize>, Vec<usize>) = (from..len).partition(|&i| rank(i).is_some());
    s.sort_by_key(|&i| rank(i)); // stable
    let mut picked: Vec<usize> = s.into_iter().chain(rest).take(n).collect();
    picked.sort_unstable();
    keep.extend(picked);
    keep
}

/// `laws` for any named laws, `guard_k` guard laws and counting mode `fast`; `loud` prints the mine's report lines.
fn laws_of(job: &mut Job, laws: Vec<(String, Term, Term)>, guard_k: usize, fast: bool, budget: i64, clock: &Clock, loud: bool) -> Laws {
    assemble(classify(job, &laws, budget, fast, loud), guard_k, loud, clock)
}

/// What the base rules do to one law: `Skipped` (no law, or over the carry cap), `Clean` (no machine proof needed; it feeds the
/// guard sample) or a `Straggler`, whose flag says the rewriter could not close it at all and whose count is the rewrite steps
/// the classification spent on it (a deterministic cost; `Keep::Small`).
#[derive(Clone)]
enum Outcome {
    Skipped,
    Clean(String, Term, Term),
    Straggler(Scored, bool, i64),
}

/// The outcome of each of `laws` under the rules installed on this thread (P1, P2), in order, each rewritten under `budget`
/// steps; `loud` prints a line per straggler. Selecting among laws (`kept_indices`) happens between this and `assemble`.
fn classify(job: &mut Job, laws: &[(String, Term, Term)], budget: i64, fast: bool, loud: bool) -> Vec<Outcome> {
    let (n, kv) = (4usize, STREAM_VARS);
    let mut out: Vec<Outcome> = vec![];
    // `RULEMINER_FAST` counts the base rules' machine proofs the way it scores candidates: without building them. Carry-over:
    // P1 runs under the base rules P0 installed
    let counting = job.rules().counting(fast);
    job.with_rules(counting, |job| {
        for (name, t1, t2) in laws.iter().cloned() {
            if !t1.is_law(&t2, kv) || [&t1, &t2].iter().any(|t| Machine::parse(t).is_some_and(|m| m.carries() > carry_cap(job))) {
                out.push(Outcome::Skipped);
                continue;
            }
            let t = Instant::now();
            let (r, spent) = job.measured(budget, |job| rewrite_plan(job, n, kv, &t1, &t2));
            let took = t.elapsed();
            let fell = spent.fallbacks;
            // a law the rewriter cannot close at all counts as a straggler too (fixed once it is proved machine-free)
            let unproved = r.is_none();
            let fell = if unproved { fell.max(1) } else { fell };
            if unproved || fell > 0 {
                let (normal, _) = job.measured(budget, |job| [rewrite(job, &t1, n, kv).0, rewrite(job, &t2, n, kv).0]);
                if loud {
                    println!("RULEMINER straggler {name}: {} = {} ({fell} machine proofs, {took:?}{})", normal[0].show(), normal[1].show(), if unproved { ", UNPROVED" } else { "" });
                }
                out.push(Outcome::Straggler((name, t1, t2, normal, fell, took), unproved, spent.steps));
            } else {
                out.push(Outcome::Clean(name, t1, t2));
            }
        }
    });
    out
}

/// The `Laws` of classified `outcomes`: the stragglers, and a guard sample of `guard_k` of the clean laws scored with them.
fn assemble(outcomes: Vec<Outcome>, guard_k: usize, loud: bool, clock: &Clock) -> Laws {
    let (n, kv) = (4usize, STREAM_VARS);
    let total = outcomes.len();
    let mut stragglers: Vec<Scored> = vec![];
    let mut unproved = 0usize;
    let mut clean: Vec<(String, Term, Term)> = vec![]; // laws that are already machine-free under the base rules (for `RULEMINER_GUARD`)
    for o in outcomes {
        match o {
            Outcome::Skipped => {}
            Outcome::Clean(name, t1, t2) => clean.push((name, t1, t2)),
            Outcome::Straggler(s, u, _) => {
                unproved += u as usize;
                stragglers.push(s);
            }
        }
    }
    let base_time: f64 = stragglers.iter().map(|s| s.5.as_secs_f64()).sum();
    if loud {
        println!("RULEMINER {} stragglers of {total} laws, {:.1}s base ({unproved} unproved)", stragglers.len(), base_time);
        clock.phase("laws and stragglers");
    }
    // `RULEMINER_GUARD=<k>` (default 120, 0 = off): about k of the already machine-free laws are scored with the stragglers, so a candidate that breaks them loses
    // the same 1000 per law as it gains per straggler fixed (the miner otherwise sees only the stragglers and cannot see a regression)
    let mut scored = stragglers.clone();
    let mut guard_w = 1000i64; // each sampled guard law stands for clean/sampled laws, so a regression costs that many times 1000
    if guard_k > 0 && !clean.is_empty() {
        let (step, w) = guard_plan(clean.len(), guard_k);
        guard_w = w;
        for (name, t1, t2) in clean.iter().step_by(step) {
            scored.push((name.clone(), *t1, *t2, [*t1, *t2], 1, std::time::Duration::ZERO));
        }
        if loud {
            println!("RULEMINER guard: {} machine-free laws scored of {} (weight {guard_w} each)", scored.len() - stragglers.len(), clean.len());
        }
    }
    Laws { stragglers, scored, guard_w, n, kv }
}

/// Whether a candidate left side `l` matches a subterm of the straggler's normalized terms.
fn reaches(l: &Term, s: &Scored) -> bool {
    let mut subs = vec![];
    s.3[0].subterms(&mut subs);
    s.3[1].subterms(&mut subs);
    subs.iter().any(|t| matches(l, t))
}

/// The candidate rules for the stragglers (P3, P4), one per left side, and the other right sides of each left side (`rivals`).
fn candidates(laws: &Laws, no_dup_lhs: bool, base: &[(Term, Term)], extra: &[(Term, Term)], loud: bool) -> (Vec<(Term, Term)>, hashbrown::HashMap<Term, Vec<(Term, Term)>>) {
    let (n, kv, stragglers) = (laws.n, laws.kv, &laws.stragglers);
    // the pool's rules go down in the rule order, ties broken by `tie_greater` (reassociation rules; section 70); the step
    // budget and the same-term check in `rule_step` still back up termination, and soundness is unaffected
    // goal-directed candidates: abstract each arithmetic subterm of a straggler's normalized terms into a pattern over
    // at most `POOL_VARS` variables (cutting subterms into variables), and look for a smaller term over the same variables
    // with the same values (`Pool`)
    let mut pool = Pool::new(n);
    if loud {
        println!("RULEMINER pool of {} terms, {} distinct functions", pool.terms, pool.index.len());
    }
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
                            // not ordered: orienting cross-side rules by the rule order raised M in every family (docs/tier-cycle/,
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
    if no_dup_lhs {
        let before = cands.len();
        let in_force: hashbrown::HashSet<&Term> = base.iter().map(|(l, _)| l).collect();
        cands.retain(|(l, _)| !in_force.contains(l));
        if loud {
            println!("RULEMINER dropped {} candidates whose left side is already in force", before - cands.len());
        }
    }
    // per left side, the smallest right side only, ties by `Term`'s order. Scoring every right side instead (each left side's rival
    // orientations) fixed add3's `sub` chains but raised M on cmp3d and sbo3 and made cmp3d's mine 4.5x slower (docs/tier-cycle/)
    // an identity (a pattern's pool group holds the pattern itself) never gains, and as the smallest right side it would displace
    // its left side's real candidates
    cands.retain(|(l, r)| l != r);
    cands.sort_by_key(|(l, r)| (l.size(), *l, r.size(), *r));
    cands.dedup();
    // rivals: the other right sides of each left side; a round's winner gives way to a rival that gains more on the same laws
    // (`Rounds::pick`; docs/tier-cycle/, "Preferences and rival orientations in the miner")
    let mut rivals: hashbrown::HashMap<Term, Vec<(Term, Term)>> = Default::default();
    for (l, r) in &cands {
        rivals.entry(*l).or_default().push((*l, *r));
    }
    rivals.values_mut().for_each(|v| {
        v.remove(0);
    });
    cands.dedup_by(|a, b| a.0 == b.0);
    if loud {
        println!("RULEMINER {} oriented candidates (one per left side)", cands.len());
    }
    (cands, rivals)
}

/// The pool route's variables: over three the miner finds small rules that carry to unseen laws (held-out M -6.9% against
/// two, docs/tier-cycle/, "A pool route over three variables finds them").
const POOL_VARS: usize = 3;

/// The pool route's terms: every term of up to 5 nodes over `POOL_VARS` variables and the constants, by their values on every
/// width-n input (4096 bytes a term over three variables at width 4); `lt` terms (one-bit values) only as roots over two terms
/// of up to 3 nodes, indexed apart so their 0/1 values never meet the n-bit constants.
struct Pool {
    memo: ValueMemo<u8>,
    /// The terms by value class (`ValueMemo::class`), comparisons apart.
    index: hashbrown::HashMap<u32, Vec<Term>>,
    index_lt: hashbrown::HashMap<u32, Vec<Term>>,
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
            pool.index.entry(pool.memo.class(t)).or_default().push(*t);
            pool.terms += 1;
        }
        for a in by_size.iter().take(4).flatten() {
            for b in by_size.iter().take(4).flatten() {
                let t = Term::op(LT, *a, *b);
                pool.index_lt.entry(pool.memo.class(&t)).or_default().push(t);
            }
        }
        pool
    }

    /// The pool's terms equal to `pat` (over at most `POOL_VARS` variables) on every input.
    fn equal(&mut self, pat: &Term) -> &[Term] {
        let class = self.memo.class(pat);
        let index = if matches!(*pat.node(), Node::Op(LT, ..)) { &self.index_lt } else { &self.index };
        index.get(&class).map_or(&[], |g| g.as_slice())
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
        tatic_kernel::scoped(|| {
            let rules = self.install(job.setup());
            job.with_rules(rules, |job| self.holds(job, rule))
        })
    }

    /// The indices of the candidates that are proved, in order, on `threads` workers (one intern scope each; one thread
    /// proves on this thread).
    fn filter(&self, job: &mut Job, cands: &[(Term, Term)], threads: usize) -> Vec<usize> {
        let prove = |job: &mut Job, idx: &[usize]| -> Vec<usize> {
            tatic_kernel::scoped(|| {
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
    /// no `chosen` record and no progress lines (`cover`)
    quiet: bool,
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
            quiet: false,
        }
    }

    fn phase(&self, label: &str) {
        if !self.quiet {
            self.clock.phase(label);
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
    /// proves (docs/tier-cycle/, "With small rules, the lookahead buys nothing: take the rival")
    fn pick(&mut self, job: &mut Job, s: &Chosen) -> Option<((Term, Term), i64)> {
        let (scorer, provable, rivals, cfg) = (self.scorer, self.provable, self.rivals, self.cfg);
        let (stragglers, guard_w) = (&scorer.laws.stragglers, scorer.laws.guard_w);
        let (chosen, base_eval, covered, size) = (&s.chosen, &s.eval, &s.covered, s.size);
        // a candidate changes only the laws whose rewriting asked about a term its left side matches, or whose join examined a
        // term it is a step at (`affected`, `Trace::touched_by`), so its gain is at most
        // 1000 per affected uncovered straggler, `guard_w` per affected uncovered guard law and the affected stragglers' whole size
        // a candidate can only rewrite a term where it comes before the rule that fired (`Fired::preempted_by`; the trace was
        // made without the candidate)
        // the run-time order of every rule in play, ranked once
        let t0 = Instant::now();
        let mut ranked: Vec<(Term, Term)> = scorer.base.iter().chain(chosen).chain(provable.iter()).cloned().collect();
        ranked.sort_by_key(|(l, r)| run_order(l, r));
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
        // the copy frozen as the round starts, which only this thread's searches fed (docs/tier-cycle/, "Spike of the join
        // store"). Expressions are per thread, so each worker grows its own (1.5x
        // faster scoring on cmp3d, docs/tier-cycle/, "Miner speedups")
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
                        tatic_kernel::scoped(|| loop {
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
        self.phase(&format!("round over {} of {} candidates", next, provable.len()));
        let Some(i) = winner else { return None };
        let g = results[i].as_ref().unwrap().0;
        // in the rivals' order, as when they were scored one after another here
        let (t, mut proved, quiet) = (Instant::now(), [0usize; 2], self.quiet);
        let rival = best_rival(rivals_of(i), &rival_gains, g, chosen, |rv| {
            let b = self.prover.prove(job, rv);
            proved[!b as usize] += 1;
            if !b && !quiet {
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
                if !self.quiet {
                    println!("{}", o.line);
                    job.setup().result("chosen", &o.rule);
                }
                continue;
            }
            if !self.quiet {
                println!("RULEMINER rolled back to round {}: its winner {} is not provable", o.round, o.proof.map_or(String::new(), |i| rule_show(&self.provable[i])));
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
                self.phase("rule-set evaluation");
                open.push(Open { before: s, round, proof, line, rule: rule_show(&rule) });
                (s, round) = (next, round + 1);
                // the newest three rounds stay open: a winner's proof (about 87 ms on cmp3d) runs while the next three rounds are
                // scored (about 60 ms each at 6 threads); docs/tier-cycle/, "Why six threads gave little"
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
            println!("RULEMINER label: {} {}", *c as u8, st.0);
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
/// every input (docs/tier-cycle/, "A pool route over three variables finds them").
#[test]
fn the_pool_finds_terms_over_three_variables() {
    let mut pool = Pool::new(4);
    let p = parse_term;
    assert!(pool.equal(&p("sub(add(x, z), add(y, z))")).contains(&p("sub(x, y)")));
    assert!(!pool.equal(&p("sub(add(x, z), add(y, z))")).contains(&p("sub(x, z)")));
    assert!(pool.equal(&p("lt(x, and(and(y, z), y))")).contains(&p("lt(x, and(y, z))")));
}

/// `classify` gives one outcome per law, in the input's order: a false equation is skipped, a law the built-in rules close
/// is clean, and the stream mine's laws (`ROLLBACK_LAWS`) leave stragglers.
#[test]
fn classify_orders_outcomes_like_the_input() {
    let named = |s: &str| {
        let (a, b) = s.split_once(" = ").unwrap();
        (s.to_string(), parse_term(a), parse_term(b))
    };
    let mut laws = vec![named("add(x, y) = add(x, z)"), named("and(x, y) = and(y, x)")];
    laws.extend(ROLLBACK_LAWS.lines().map(named));
    let job = &mut Job::new(Setup::process());
    // one letter per outcome (the kernel scope lets nothing but plain values out)
    let out: String = tatic_kernel::scoped(|| {
        classify(job, &laws, UNBOUNDED, false, false)
            .iter()
            .map(|o| match o {
                Outcome::Skipped => 'k',
                Outcome::Clean(..) => 'c',
                Outcome::Straggler(..) => 's',
            })
            .collect()
    });
    assert_eq!(out.len(), laws.len());
    assert!(out.starts_with("kc"), "a false equation is no law, and commuting `and` needs no machine proof: {out}");
    assert!(out[2..].contains('s'), "the stream mine's laws leave stragglers: {out}");
}

#[test]
fn kept_indices_keeps_the_served_laws_and_n_of_the_pool() {
    let none = |_: usize| None;
    // 3 served laws, a pool of 6, keep 2
    assert_eq!(kept_indices(9, 3, 2, &none), vec![0, 1, 2, 3, 4], "no straggler ranked: the pool's first n (`first`)");
    let s = |i: usize| (i == 5 || i == 7).then_some((0, 0)); // stragglers at indices 5 and 7, equally ranked
    assert_eq!(kept_indices(9, 3, 2, &s), vec![0, 1, 2, 5, 7], "stragglers first, in order");
    assert_eq!(kept_indices(9, 3, 3, &s), vec![0, 1, 2, 3, 5, 7], "the shortfall is the first other pool law");
    assert_eq!(kept_indices(9, 3, 0, &s), vec![0, 1, 2], "keep 0 reads no extra");
    assert_eq!(kept_indices(9, 3, 6, &s), (0..9).collect::<Vec<_>>(), "keep exactly the pool keeps the pool");
    assert_eq!(kept_indices(9, 3, 99, &s), (0..9).collect::<Vec<_>>(), "keep past the pool keeps the pool");
    assert_eq!(kept_indices(4, 9, 2, &none), vec![0, 1, 2, 3], "from past the end: all served, no pool");
    // a rank orders the stragglers, smallest first; equal ranks keep the stream order
    let c = |i: usize| [None, None, None, None, Some((0, 9)), Some((0, 2)), None, Some((0, 2)), Some((0, 5))][i];
    assert_eq!(kept_indices(9, 3, 2, &c), vec![0, 1, 2, 5, 7], "the two cheapest, the tie in stream order");
    assert_eq!(kept_indices(9, 3, 3, &c), vec![0, 1, 2, 5, 7, 8], "the third cheapest (rank (0, 5))");
    assert_eq!(kept_indices(9, 3, 5, &c), vec![0, 1, 2, 3, 4, 5, 7, 8], "a shortfall fills with the first other pool law, as for a constant rank");
    // the miner's rank is (steps, normal-form size): under an empty base every step count is 0 and the size decides
    let r = |i: usize| [None, None, None, Some((0, 30)), Some((0, 8)), Some((0, 20)), Some((2, 4))][i];
    assert_eq!(kept_indices(7, 3, 2, &r), vec![0, 1, 2, 4, 5], "equal steps: the smaller normal forms");
    assert_eq!(kept_indices(7, 3, 3, &r), vec![0, 1, 2, 3, 4, 5], "steps come first: the dearer small term waits");
    assert_eq!(Keep::parse("first"), Ok(Keep::First));
    assert_eq!(Keep::parse("small"), Ok(Keep::Small));
    assert!(Keep::parse("bogus").unwrap_err().contains("EXTRAS_SELECT"));
}

/// The served laws of `ROLLBACK_LAWS` with the pool `[clean, straggler]` after them (a law `and` commutes away; the
/// straggler is the first of the served file's own).
fn served_and_pool() -> (usize, String, String, String) {
    let named = |s: &str| {
        let (a, b) = s.split_once(" = ").unwrap();
        (s.to_string(), parse_term(a), parse_term(b))
    };
    let served: Vec<_> = ROLLBACK_LAWS.lines().map(named).collect();
    let job = &mut Job::new(Setup::process());
    let strag: String = tatic_kernel::scoped(|| {
        let out = classify(job, &served, UNBOUNDED, true, false);
        out.iter().zip(&served).find(|(o, _)| matches!(o, Outcome::Straggler(..))).expect("a straggler among the served laws").1 .0.clone()
    });
    (served.len(), ROLLBACK_LAWS.to_string(), "and(x, y) = and(y, x)".to_string(), strag)
}

/// The names of the stragglers `laws_for` leaves a mine with (a whole mine is too slow to run per case).
fn straggler_names(text: &str, extras: Option<ExtrasKeep>) -> Vec<String> {
    straggler_names_dumping(text, extras, None)
}

/// `straggler_names` with the pool dump to `prefix` (`RULEMINER_POOL_DUMP`).
fn straggler_names_dumping(text: &str, extras: Option<ExtrasKeep>, prefix: Option<String>) -> Vec<String> {
    straggler_names_with(text, extras, prefix, None)
}

/// `straggler_names_dumping` with the context model's weights file (`RULEMINER_CTX_WEIGHTS`).
fn straggler_names_with(text: &str, extras: Option<ExtrasKeep>, prefix: Option<String>, weights: Option<&str>) -> Vec<String> {
    let named = |s: &str| {
        let (a, b) = s.split_once(" = ").unwrap();
        (s.to_string(), parse_term(a), parse_term(b))
    };
    let laws: Vec<_> = text.lines().map(named).collect();
    let mut env = vec![("RULEMINER_LAWFILE".to_string(), "unused".to_string()), ("RULEMINER_FAST".to_string(), "1".to_string()), ("RULEMINER_GUARD".to_string(), "0".to_string())];
    env.extend(weights.map(|w| ("RULEMINER_CTX_WEIGHTS".to_string(), w.to_string())));
    let setup = Setup::with_env(env);
    let job = &mut Job::new(setup.clone());
    let clock = Clock(std::cell::Cell::new(Instant::now()));
    let mut cfg = MinerConfig::new(&setup);
    (cfg.extras, cfg.pool_dump) = (extras, prefix);
    tatic_kernel::scoped(|| laws_for(job, laws, &cfg, &[], UNBOUNDED, &clock, false).stragglers.iter().map(|s| s.0.clone()).collect())
}

/// The pool dump of a `first` mine writes one line per pool law with its facts and the served stragglers' normal forms, and
/// the mine reads the laws it would without it.
#[test]
fn the_pool_dump_writes_facts_and_changes_nothing() {
    let (from, served, clean, strag) = served_and_pool();
    let both = format!("{served}{clean}\n{strag}\n");
    let ex = Some(ExtrasKeep { from, n: 1, by: Keep::First });
    let prefix = std::env::temp_dir().join(format!("pool_dump_{}", std::process::id())).display().to_string();
    let without = straggler_names(&both, ex);
    let with = straggler_names_dumping(&both, ex, Some(prefix.clone()));
    let (pool_file, served_file) = (format!("{prefix}_pool.tsv"), format!("{prefix}_served.txt"));
    let (pool, forms) = (std::fs::read_to_string(&pool_file).unwrap(), std::fs::read_to_string(&served_file).unwrap());
    std::fs::remove_file(&pool_file).ok();
    std::fs::remove_file(&served_file).ok();
    assert_eq!(with, without, "the dump changes no law the mine reads");
    let pool = crate::ctx_scorer::read_pool(&pool);
    assert_eq!(pool.len(), 2, "one line per pool law, not per kept law");
    assert!(!pool[0].straggler && !pool[0].uncovered, "the clean law is no straggler");
    assert!(pool[1].straggler && pool[1].steps >= 0 && pool[1].size > 0 && pool[1].fallbacks > 0);
    assert_eq!(forms.lines().count(), straggler_names(&served, None).len(), "one normal form per served straggler");
}

/// `small` keeps the pool's straggler over its clean law that comes first; `first` keeps the clean law and is today's
/// mine (the pool's cost is not paid); `KEEP=0` and a `FROM` past the end are the served laws alone and the whole file.
#[test]
fn the_pool_is_cut_by_the_stragglers_verdict() {
    let (from, served, clean, strag) = served_and_pool();
    let both = format!("{served}{clean}\n{strag}\n");
    let ex = |n, by| Some(ExtrasKeep { from, n, by });
    let base = straggler_names(&served, None);
    let by_straggler = straggler_names(&both, ex(1, Keep::Small));
    assert_eq!(by_straggler.len(), base.len() + 1, "the pool's straggler joins the served stragglers");
    assert_eq!(by_straggler.last(), Some(&strag));
    assert_eq!(straggler_names(&both, ex(1, Keep::First)), base, "the first pool law is the clean one: no new straggler");
    assert_eq!(straggler_names(&both, ex(0, Keep::Small)), base, "keep 0 reads no extra");
    assert_eq!(straggler_names(&both, Some(ExtrasKeep { from: 1000, n: 1, by: Keep::Small })), straggler_names(&both, None), "from past the end is the whole file as served");
}

/// A one-column context model (`ctx33-v1` layout, 33 wide): score = `w` times column `col`.
fn one_column_model(col: usize, w: i32) -> String {
    format!("layout ctx33-v1\nwidth 33\nkeep {col}\nmean 0\nscale 1\nw {w}\n")
}

/// The all-zero model: every law scores 0.
fn zero_model() -> String {
    "layout ctx33-v1\nwidth 33\nkeep 0\nmean 0\nscale 1\nw 0\n".to_string()
}

/// `text` written to a fresh weights file (named by `tag` and this process); the path.
fn weights_file(tag: &str, text: &str) -> String {
    let path = std::env::temp_dir().join(format!("ctx_weights_{tag}_{}.txt", std::process::id()));
    std::fs::write(&path, text).unwrap();
    path.display().to_string()
}

/// The stragglers `laws_for` leaves under `EXTRAS_BY=ctx` with the model `model`, then the weights file removed.
fn ctx_names(text: &str, extras: ExtrasKeep, tag: &str, model: &str) -> Vec<String> {
    let path = weights_file(tag, model);
    let names = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| straggler_names_with(text, Some(extras), None, Some(&path))));
    std::fs::remove_file(&path).ok();
    names.unwrap_or_else(|e| std::panic::resume_unwind(e))
}

/// The pool of `ROLLBACK_LAWS` after its first two laws (the served ones): per pool law its name, whether it is a straggler
/// and its `runtime_rows` (what the context model scores).
fn rollback_pool() -> (usize, Vec<String>, Vec<bool>, Vec<Vec<f32>>) {
    let named: Vec<(String, Term, Term)> = ROLLBACK_LAWS
        .lines()
        .map(|s| {
            let (a, b) = s.split_once(" = ").unwrap();
            (s.to_string(), parse_term(a), parse_term(b))
        })
        .collect();
    let from = 2;
    let job = &mut Job::new(Setup::with_env(vec![("RULEMINER_FAST".to_string(), "1".to_string())]));
    let rows = tatic_kernel::scoped(|| {
        let outcomes = classify(job, &named, UNBOUNDED, true, false);
        let (pool, served) = pool_laws(&named, &outcomes, from);
        (pool.iter().map(|p| p.straggler).collect::<Vec<_>>(), crate::ctx_scorer::runtime_rows(&pool, &served))
    });
    (from, named[from..].iter().map(|n| n.0.clone()).collect(), rows.0, rows.1)
}

#[test]
fn keep_parses_ctx_and_names_the_variable_on_error() {
    assert_eq!(Keep::parse("ctx"), Ok(Keep::Ctx));
    assert!(Keep::parse("bogus").unwrap_err().contains("ctx"), "the error lists the choices");
}

/// A zero model scores every law alike, so ranks fall back to the stream order and `ctx` keeps what `small` keeps when the
/// pool holds one straggler.
#[test]
fn a_ctx_pool_with_a_zero_model_keeps_the_straggler_like_small() {
    let (from, served, clean, strag) = served_and_pool();
    let both = format!("{served}{clean}\n{strag}\n");
    let ex = |by| ExtrasKeep { from, n: 1, by };
    let by_ctx = ctx_names(&both, ex(Keep::Ctx), "zero", &zero_model());
    assert_eq!(by_ctx, straggler_names(&both, Some(ex(Keep::Small))));
    assert_eq!(by_ctx.last(), Some(&strag), "the pool's straggler is kept over the clean law before it");
}

#[test]
#[should_panic(expected = "RULEMINER_CTX_WEIGHTS")]
fn ctx_without_weights_names_the_variable() {
    let (from, served, clean, strag) = served_and_pool();
    straggler_names_with(&format!("{served}{clean}\n{strag}\n"), Some(ExtrasKeep { from, n: 1, by: Keep::Ctx }), None, None);
}

#[test]
#[should_panic(expected = "RULEMINER_CTX_WEIGHTS")]
fn ctx_refuses_a_missing_weights_file() {
    let (from, served, clean, strag) = served_and_pool();
    let gone = std::env::temp_dir().join(format!("ctx_weights_gone_{}.txt", std::process::id())).display().to_string();
    straggler_names_with(&format!("{served}{clean}\n{strag}\n"), Some(ExtrasKeep { from, n: 1, by: Keep::Ctx }), None, Some(&gone));
}

#[test]
#[should_panic(expected = "layout")]
fn ctx_refuses_weights_of_another_layout() {
    let (from, served, clean, strag) = served_and_pool();
    ctx_names(&format!("{served}{clean}\n{strag}\n"), ExtrasKeep { from, n: 1, by: Keep::Ctx }, "layout", &zero_model().replace("ctx33-v1", "ctx35-v1"));
}

#[test]
#[should_panic(expected = "width")]
fn ctx_refuses_weights_of_another_width() {
    let (from, served, clean, strag) = served_and_pool();
    ctx_names(&format!("{served}{clean}\n{strag}\n"), ExtrasKeep { from, n: 1, by: Keep::Ctx }, "width", "layout ctx33-v1\nwidth 5\nkeep 0\nmean 0\nscale 1\nw 0\n");
}

#[test]
fn ctx_with_n_zero_reads_no_extra() {
    let (from, served, clean, strag) = served_and_pool();
    let both = format!("{served}{clean}\n{strag}\n");
    assert_eq!(ctx_names(&both, ExtrasKeep { from, n: 0, by: Keep::Ctx }, "n0", &zero_model()), straggler_names(&served, None));
}

/// The pool facts the ctx rank scores (`pool_laws` over `classify`) are the ones the dump wrote, which the model was fit on.
#[test]
fn ctx_pool_facts_equal_the_dump_rows() {
    let (from, text) = (2, ROLLBACK_LAWS);
    let prefix = std::env::temp_dir().join(format!("ctx_parity_{}", std::process::id())).display().to_string();
    straggler_names_dumping(text, Some(ExtrasKeep { from, n: 1, by: Keep::First }), Some(prefix.clone()));
    let (pool_file, served_file) = (format!("{prefix}_pool.tsv"), format!("{prefix}_served.txt"));
    let (tsv, forms) = (std::fs::read_to_string(&pool_file).unwrap(), std::fs::read_to_string(&served_file).unwrap());
    std::fs::remove_file(&pool_file).ok();
    std::fs::remove_file(&served_file).ok();
    let named: Vec<(String, Term, Term)> = text
        .lines()
        .map(|s| {
            let (a, b) = s.split_once(" = ").unwrap();
            (s.to_string(), parse_term(a), parse_term(b))
        })
        .collect();
    let job = &mut Job::new(Setup::with_env(vec![("RULEMINER_FAST".to_string(), "1".to_string())]));
    let (dumped, live) = tatic_kernel::scoped(|| {
        let dumped = crate::ctx_scorer::read_pool(&tsv);
        let dumped_served: Vec<(Term, Term)> = forms.lines().map(|l| l.split_once(" = ").map(|(a, b)| (parse_term(a), parse_term(b))).unwrap()).collect();
        let outcomes = classify(job, &named, UNBOUNDED, true, false);
        let (pool, served) = pool_laws(&named, &outcomes, from);
        let facts = |p: &[crate::ctx_scorer::PoolLaw]| p.iter().map(|l| (l.straggler, l.steps, l.size, l.fallbacks)).collect::<Vec<_>>();
        ((facts(&dumped), crate::ctx_scorer::runtime_rows(&dumped, &dumped_served)), (facts(&pool), crate::ctx_scorer::runtime_rows(&pool, &served)))
    });
    assert!(live.0.iter().any(|f| f.0), "the fixture's pool has stragglers");
    assert_eq!(live, dumped);
}

/// `ctx` keeps the pool straggler the model scores highest, not the one with the fewest steps: a one-column model of either
/// sign keeps the straggler with that column's extreme value, and the two signs keep different laws.
#[test]
fn ctx_follows_the_model_not_the_steps() {
    let (from, names, straggler, rows) = rollback_pool();
    assert!(straggler.iter().filter(|&&s| s).count() >= 3, "the fixture's pool needs several stragglers to order");
    let ex = ExtrasKeep { from, n: 1, by: Keep::Ctx };
    let text = ROLLBACK_LAWS;
    let pick = |col: usize, up: bool| {
        let ss: Vec<usize> = (0..names.len()).filter(|&i| straggler[i]).collect();
        // first of the extreme: equal scores keep the stream order
        ss.iter().copied().fold(ss[0], |best, i| if (up && rows[i][col] > rows[best][col]) || (!up && rows[i][col] < rows[best][col]) { i } else { best })
    };
    let col = (1..crate::ctx_scorer::PER_LAW).find(|&c| pick(c, true) != pick(c, false)).expect("some per-law column separates the pool's stragglers");
    let (up, down) = (ctx_names(text, ex, "up", &one_column_model(col, 1)), ctx_names(text, ex, "down", &one_column_model(col, -1)));
    assert_eq!(up.last(), Some(&names[pick(col, true)]), "a positive weight keeps the highest column value (from offset {from})");
    assert_eq!(down.last(), Some(&names[pick(col, false)]), "a negative weight keeps the lowest");
}

#[test]
fn ctx_reports_how_many_kept_differ_from_small() {
    assert_eq!(kept_differ(&[0, 1, 4, 6], &[0, 1, 5, 6], 2), 1);
    assert_eq!(kept_differ(&[0, 1, 4, 6], &[0, 1, 4, 6], 2), 0);
    assert_eq!(kept_differ(&[0, 1], &[0, 1], 5), 0, "no pool laws kept");
}

/// What a quiet `cover` of the stream mine's laws (`ROLLBACK_LAWS`) under `setup` does: how many rules it chose and, per law
/// (as plain values, the kernel scope lets no terms out), whether it is a straggler under the base (by `classify` and by
/// `still_stragglers` with nothing chosen) and with the chosen rules.
struct QuietCover {
    chosen: usize,
    by_classify: Vec<bool>,
    none: Vec<bool>,
    with: Vec<bool>,
}

fn quiet_cover(setup: &Arc<Setup>) -> QuietCover {
    let laws: Vec<(String, Term, Term)> = ROLLBACK_LAWS
        .lines()
        .map(|s| {
            let (a, b) = s.split_once(" = ").unwrap();
            (s.to_string(), parse_term(a), parse_term(b))
        })
        .collect();
    let job = &mut Job::new(setup.clone());
    let clock = Clock(std::cell::Cell::new(Instant::now()));
    let (chosen, by_classify, none, with) = tatic_kernel::scoped(|| {
        let cfg = MinerConfig::new(setup);
        let l = laws_of(job, laws.clone(), 0, true, UNBOUNDED, &clock, false);
        let chosen = cover(job, &l, &cfg, &[], &clock, &[], true).0;
        let by_classify: Vec<bool> = classify(job, &laws, UNBOUNDED, true, false).iter().map(|o| matches!(o, Outcome::Straggler(..))).collect();
        let (none, with) = (still_stragglers(job, &[], &[], &laws, UNBOUNDED, true), still_stragglers(job, &[], &chosen, &laws, UNBOUNDED, true));
        (chosen.len(), by_classify, none, with)
    });
    QuietCover { chosen, by_classify, none, with }
}

fn fast_env(file: &std::path::Path) -> Vec<(String, String)> {
    vec![("RULEMINER_LAWFILE".to_string(), "unused".to_string()), ("RULEMINER_FAST".to_string(), "1".to_string()), ("CTX_TEST_RESULTS".to_string(), file.display().to_string())]
}

/// With nothing chosen the pool's stragglers are the base's; a rule the quiet cover chose closes at least one of them.
#[test]
fn a_chosen_rule_flips_a_straggler_to_covered() {
    let setup = Setup::with_env(fast_env(std::path::Path::new("unused")));
    let QuietCover { chosen, by_classify, none, with } = quiet_cover(&setup);
    assert!(chosen > 0, "the stream mine's laws leave a rule to choose");
    assert_eq!(none, by_classify, "no chosen rules is the base classification");
    let (a, b) = (none.iter().filter(|s| **s).count(), with.iter().filter(|s| **s).count());
    assert!(a > 0 && b < a, "the chosen rules close a straggler: {a} -> {b}");
    assert!(with.iter().zip(&none).all(|(w, n)| !w || *n), "a clean law stays clean");
}

/// A quiet cover leaves no `chosen` record in the setup's result file.
#[test]
fn a_quiet_cover_records_no_chosen_rule() {
    let file = std::env::temp_dir().join(format!("quiet_cover_{}.tsv", std::process::id()));
    let setup = Setup::for_task(fast_env(&file), std::fs::File::create(&file).unwrap());
    let chosen = quiet_cover(&setup).chosen;
    let recorded = std::fs::read_to_string(&file).unwrap();
    std::fs::remove_file(&file).ok();
    assert!(chosen > 0);
    assert!(!recorded.contains("chosen"), "a quiet cover records nothing: {recorded:?}");
}

/// `by=first` is today's mine rule for rule: a file with a pool and `KEEP` of the first law chooses what the file without the
/// pool does.
#[test]
fn extras_by_first_mines_what_the_unpooled_file_mines() {
    let (from, served, clean, strag) = served_and_pool();
    let mine_rules = |tag: &str, laws: &str, env: &[(&str, String)]| {
        let path = std::env::temp_dir().join(format!("extras_laws_{}_{tag}.txt", std::process::id()));
        std::fs::write(&path, laws).unwrap();
        let mut e = vec![("RULEMINER_LAWFILE".to_string(), path.display().to_string()), ("RULEMINER_FAST".to_string(), "1".to_string())];
        e.extend(env.iter().map(|(k, v)| (k.to_string(), v.clone())));
        let chosen = mine(&Setup::with_env(e), &[]).0;
        std::fs::remove_file(&path).ok();
        chosen
    };
    let pooled = mine_rules(
        "pooled",
        &format!("{served}{clean}\n{strag}\n"),
        &[("RULEMINER_EXTRAS_FROM", from.to_string()), ("RULEMINER_EXTRAS_KEEP", "1".to_string()), ("RULEMINER_EXTRAS_BY", "first".to_string())],
    );
    assert_eq!(pooled, mine_rules("plain", &format!("{served}{clean}\n"), &[]));
}

/// The three `RULEMINER_EXTRAS_*` variables become the config the mine keeps by (the `by_first` test above cannot tell
/// whether they were read: a mine that ignored them might choose the same rules), and none of them is no config.
#[test]
fn the_extras_env_becomes_the_config() {
    let cfg = |vars: &[(&str, &str)]| MinerConfig::new(&Setup::with_env(vars.iter().chain(&[("RULEMINER_LAWFILE", "unused")]).map(|(k, v)| (k.to_string(), v.to_string())).collect())).extras;
    assert!(cfg(&[]).is_none());
    let k = cfg(&[("RULEMINER_EXTRAS_FROM", "7"), ("RULEMINER_EXTRAS_KEEP", "3"), ("RULEMINER_EXTRAS_BY", "small")]).expect("set");
    assert_eq!((k.from, k.n, k.by), (7, 3, Keep::Small));
    let k = cfg(&[("RULEMINER_EXTRAS_FROM", "0"), ("RULEMINER_EXTRAS_KEEP", "5"), ("RULEMINER_EXTRAS_BY", "first")]).expect("set");
    assert_eq!((k.from, k.n, k.by), (0, 5, Keep::First));
}

/// `FROM` without `KEEP` and `BY` fails loudly, not as a half-set config.
#[test]
#[should_panic(expected = "RULEMINER_EXTRAS_KEEP")]
fn an_incomplete_extras_env_panics() {
    MinerConfig::new(&Setup::with_env(vec![("RULEMINER_LAWFILE".to_string(), "unused".to_string()), ("RULEMINER_EXTRAS_FROM".to_string(), "2".to_string())]));
}

/// A bad `BY`, `FROM` or `KEEP` value fails loudly and names its variable.
#[test]
fn a_bad_extras_env_value_names_its_variable() {
    let panic_of = |vars: [(&str, &str); 3]| {
        let vars: Vec<(String, String)> = vars.iter().chain(&[("RULEMINER_LAWFILE", "unused")]).map(|(k, v)| (k.to_string(), v.to_string())).collect();
        let Err(err) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| MinerConfig::new(&Setup::with_env(vars)))) else { panic!("a bad value must panic") };
        err.downcast_ref::<String>().cloned().unwrap_or_default()
    };
    assert!(panic_of([("RULEMINER_EXTRAS_FROM", "2"), ("RULEMINER_EXTRAS_KEEP", "3"), ("RULEMINER_EXTRAS_BY", "cheap")]).contains("RULEMINER_EXTRAS_BY"));
    assert!(panic_of([("RULEMINER_EXTRAS_FROM", "x"), ("RULEMINER_EXTRAS_KEEP", "3"), ("RULEMINER_EXTRAS_BY", "small")]).contains("RULEMINER_EXTRAS_FROM=x"));
    assert!(panic_of([("RULEMINER_EXTRAS_FROM", "2"), ("RULEMINER_EXTRAS_KEEP", "-1"), ("RULEMINER_EXTRAS_BY", "small")]).contains("RULEMINER_EXTRAS_KEEP=-1"));
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
