//! The rule miner (`search::rule_miner`, search note section 36) in named parts: `config` (`MinerConfig`, `Keep`), the laws
//! and their stragglers (`laws`), the candidates (`candidates`), and the rounds (`rounds`: `Prover`, `Scorer`, `Rounds` and
//! its closing report). This file holds the entry points `run` and `mine` and the cover loop; `tests` holds the tests.
use super::rewrite::Node;
use super::*;

/// A scored law: name, sides, the sides' normal forms under the base rules, its machine proofs there and the time taken.
type Scored = (String, Term, Term, [Term; 2], u64, std::time::Duration);


mod config;
mod laws;
mod candidates;
mod rounds;
#[cfg(test)]
mod tests;

pub use config::*;
pub(crate) use laws::*;
use candidates::*;
use rounds::*;

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
