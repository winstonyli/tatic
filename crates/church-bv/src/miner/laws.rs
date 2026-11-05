use super::*;

/// The laws mined for: the stragglers (laws the base rules leave with a machine proof, or do not close) and a guard sample
/// of the machine-free ones, scored with them (`scored`: stragglers first, so `si < stragglers.len()` is a straggler).
pub(super) struct Laws {
    pub(super) stragglers: Vec<Scored>,
    pub(super) scored: Vec<Scored>,
    pub(super) guard_w: i64,
    pub(super) n: usize,
    pub(super) kv: usize,
}

/// The laws of `cfg` and their stragglers under the rules installed on this thread (P1, P2), each rewritten under `budget`
/// steps.
pub(super) fn laws(job: &mut Job, cfg: &MinerConfig, base: &[(Term, Term)], budget: i64, clock: &Clock) -> Laws {
    let named = read_named_laws(&cfg.lawfile);
    clock.phase("law building");
    laws_for(job, named, cfg, base, budget, clock, true)
}

/// `laws_of` over the laws a mine reads: all of `named`, or, with `extras`, its served laws and `extras.n` of the pool after
/// them. `First` cuts the pool before classifying, so it costs and chooses what a file without the pool does; `Small`
/// classifies the pool and keeps its stragglers first, the fewest rewrite steps then the smallest normal form first.
pub(super) fn laws_for(job: &mut Job, mut named: Vec<(String, Term, Term)>, cfg: &MinerConfig, base: &[(Term, Term)], budget: i64, clock: &Clock, loud: bool) -> Laws {
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
pub(super) fn pool_laws(named: &[(String, Term, Term)], outcomes: &[Outcome], from: usize) -> (Vec<crate::ctx_scorer::PoolLaw>, Vec<(Term, Term)>) {
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
pub(super) fn kept_differ(keep: &[usize], other: &[usize], from: usize) -> usize {
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
pub(super) fn laws_of(job: &mut Job, laws: Vec<(String, Term, Term)>, guard_k: usize, fast: bool, budget: i64, clock: &Clock, loud: bool) -> Laws {
    assemble(classify(job, &laws, budget, fast, loud), guard_k, loud, clock)
}

/// What the base rules do to one law: `Skipped` (no law, or over the carry cap), `Clean` (no machine proof needed; it feeds the
/// guard sample) or a `Straggler`, whose flag says the rewriter could not close it at all and whose count is the rewrite steps
/// the classification spent on it (a deterministic cost; `Keep::Small`).
#[derive(Clone)]
pub(super) enum Outcome {
    Skipped,
    Clean(String, Term, Term),
    Straggler(Scored, bool, i64),
}

/// The outcome of each of `laws` under the rules installed on this thread (P1, P2), in order, each rewritten under `budget`
/// steps; `loud` prints a line per straggler. Selecting among laws (`kept_indices`) happens between this and `assemble`.
pub(super) fn classify(job: &mut Job, laws: &[(String, Term, Term)], budget: i64, fast: bool, loud: bool) -> Vec<Outcome> {
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

