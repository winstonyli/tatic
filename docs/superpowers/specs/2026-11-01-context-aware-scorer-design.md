---
status: active
---

# v0.6 follow-up: does a law's context in the mine carry a signal that a per-law scorer cannot see? (design)

Milestone: `ROADMAP.md`, goal 3 (the proposer side) and the `PARKED.md` entry "Learned proposer, stage 2 (the cycle) and richer
scorers (v0.6)", whose trigger this spec tests: "a model that sees a law in context (the other laws of the mine) or a different
kind of feature, beating random beyond the redraw spread". Background: `docs/tier-cycle.md`, sections "A learned scorer over the
extras" and "Selecting the extras by straggler verdict" (the "Coverage keys" and "A key under an empty base" bullets are inside
the latter). Prior specs: `2026-10-31-learned-proposer-design.md` (stage 1, done, null), `2026-10-31-context-aware-selector-design.md`
(done; the `small` key is v0.6's answer). Decision of 2026-11-01 (the user's pick, k2): try a context-aware model before stage 2
(the cycle). The user asked to skip the questions, so the choices below are mine, listed in "Calls I made".

Result of stages 0 and 1 (2026-11-01): the Q1 gate as first approved (k in {80, 160}) read FAIL (no room at k = 160); the user
amended it to k in {40, 80} (a2) and it reads PASS. Numbers and the ablation are in `docs/tier-cycle.md`, "A context model over
the extras". Stage 2 (Q2) is planned in `docs/superpowers/plans/2026-11-01-ctx-scorer-q2.md`.

## Why

Three scorers over per-law count features were worse than or equal to random (held-out M +20 to +486 against random, several cells
inside sigma 76; runs `v06-g1` to `g12`), although the offline AUC was real (0.691 against 0.528 for size-only). The only explanation
on record is an inference (`docs/tier-cycle.md`, "A learned scorer over the extras", the reading after the w2 transfer result): a
law's value depends on the other laws of the mine, because the miner is a greedy set cover over the stragglers (`miner.rs`,
`Rounds::pick`: 1000 per newly covered straggler, plus the guard and size terms) and a straggler is a straggler only relative to the
mine's base rules. Nothing measured that claim. It is the cheapest thing to measure and the case for stage 2 rests on it.

Selection by the mine's own verdicts already beats equal-work random at n <= 160 (`cheap`, then `small`; 2 to 4% of about 4800
held-out M). That selection is context-aware in one narrow way (steps under the base rules) and is the bar a new context model must
clear, not random.

## Terms

- **Pool**: the 4n laws the miner classifies (`POOL=4`, n = 319, so 1276) for one mine, in stream order. **Labelled slice**: the first
  n = 319 of the pool, the laws the random (first-n) arm actually mined. Only these have a label.
- **Straggler**: a pool law whose base-rule rewrite verdict is not clean (`classify`). **Label y (w1)**: 1 if the law was credited by
  the greedy cover (`RULEMINER label: 1 <law>`). Labels are printed for stragglers only; every other labelled law (clean or skipped)
  has y = 0 by absence. So y = 1 implies straggler. Consequently every ranker here ranks stragglers by score and puts non-stragglers
  last in stream order (as `small` does); models are fit on stragglers only, so the straggler flag is not a feature.
- **k**: the cutoff of Q1 (below), not the extras budget n of Q2.

## Question and success

Q1 (offline, decides whether to continue): does a model that sees context rank the positive laws of a mine's labelled slice higher
than the same model with per-law features only, and than the `small` key, on salts it was not trained on?

Q2 (only if Q1 passes; the gate): does selecting the mine's extras by that model move the frontier beyond the redraw spread, against
the `small` arm at the same n and against random at equal work?

Success for Q1 is a ranking statistic, not a frontier claim (the stage-1 lesson: AUC 0.691 did not move the frontier, so Q1 can only
stop the work, never prove it pays). Success for Q2 is the pre-registered rule below.

## Non-goals and anti-goals

- Not stage 2 (the refit cycle), not the GPU model, not new definitions or laws beyond 5 nodes, not the belief layer.
- No new label: w1 (credit); w2 (transfer) is a second read only if `transfer_labels` (from `5946c4c`) is cheap to recover.
- Anti-goal: a pass that is per-mine overfit. 42 mines over salts 4 to 10 are few independent contexts; every check is
  leave-one-salt-out.
- Anti-goal: a Q2 win that is only extra CPU. Work and CPU of the context scoring itself (including the marginal feature) are
  counted.

## What "context" means here (the one design choice)

A scorer plugged into `scope_extras` sees only `served`, `held`, `deep` and the filter; it cannot see the mine's base rules or any
rewrite verdict. Those exist inside `miner.rs`, where `laws_for` has `x.from` (so `outcomes[..from]` are the served laws) and the
pool's outcomes. So a context scorer lives in `laws_for` as a ranking function over the pool, replacing the `small` key's
(steps, size) tuple.

Features are computed over the whole 4n pool, for training rows and for Q2 alike, and the count-like ones are percentile ranks
among the pool's stragglers (ties share the average rank), in [0, 1], so a model trained on the labelled slice sees the same
distribution it will rank in Q2. Columns (F = 26 + 3 + 4 + 2 = 35):

- **Per-law arm**: the 26 stage-1 count features, unchanged (`8d9ceaf^:tests/church_bv/scorer.rs`, F = 10 + 2 x 8 operators, to be
  confirmed against `OPS`).
- **Group 1, pool-relative (3)**: percentile of the law's base steps; percentile of its normal-form size; percentile of its fallbacks
  count (all among the pool's stragglers, from `Straggler(s, unproved, steps)`). The pool's straggler share is constant within a mine
  and is not a column.
- **Group 2, served-relative (4)**: with S the multiset union of the operator multisets of the served stragglers' normal forms
  (`Scored.3`): (a) the multiset Jaccard (sum of min over sum of max) between the law's operator multiset (both sides) and S; (b)
  the same using the law's left side only; (c) the fraction of served stragglers whose left-side root operator equals the law's
  left-side root operator; (d) the same for the right side. The coverage keys tried a binary and a graded "reached by a served
  candidate" and both reduced to `cheap` or lost, so this group is a continuous-overlap check and the first cut candidate if the
  ablation shows nothing.
- **Group 3, marginal (2)**: after a greedy cover of the served stragglers alone (the `mine` pipeline's candidates, `Prover::filter`
  and `Rounds::play`, run once per mine on the served set with no extras and the real 400-candidate cap), apply the chosen rules to
  the pool's stragglers (`score_laws(chosen, pool_stragglers)`): (a) 1 if this law's own base verdict is still a straggler under
  the chosen rules; (b) the fraction of pool stragglers with the same left-side root operator that stay uncovered. This is the one
  feature that is a function of the set, not of the law and the base, so it is the real test of the interaction claim. It is
  label-independent (no extras in the served-only mine) but not free: it is a partial mine per mine, counted in CPU. It would need
  `mine` split into a callable pipeline (`mine_served_only(job, laws) -> Vec<(Term, Term)>`); not built (decision c1 drops group 3).

No feature uses the label or any extras-mine result. Standardise each column on the training rows (mean 0, sd 1; a column with
sd = 0 is dropped and noted). Stage 1's fit already standardised (`Scorer`), so the per-law arm is the same fit on the same 26
columns, now with a runtime width so that the same code fits the 35-column and the ablated models. The weights file records the feature layout and a
layout version, so `laws_for` refuses a mismatch; cutting a group means a new layout version.

## Architecture

One mechanism, offline first. Nothing in the kernel changes; no score reaches the kernel (goal 3's belief rule).

- **`tests/church_bv/ctx_scorer.rs`** (new, test-only): `features(law, pool_ctx) -> [f32; 35]`, a logistic `fit`/`score`/`auc`/text I/O
  recovered from `8d9ceaf^:tests/church_bv/scorer.rs` (deterministic, no dependency), and the offline report.
- **Dump.** `classify`, `Outcome`, `Scored` and `kept_indices` are private to `miner.rs`, and `Outcome::Clean` and `Skipped` carry no
  steps or size, so the dump is an env-gated path inside `miner.rs` (`RULEMINER_POOL_DUMP=<file>`), not stderr scraping. A mine's
  base rules include the rules chosen by the earlier mines of its loop, so the pool can only be classified inside a real arm run:
  the dump is a fresh arm run with `POOL=4 EXTRAS_SELECT=first` (the miner mines the first n, so chosen rules and labels are the
  random arm's) whose `First` path, when the dump is on, also classifies the whole pool (1276 laws) and writes, per mine, one TSV
  row per pool law: pool index, law, straggler flag, steps, size, fallbacks (stragglers only; empty otherwise) and the group 2 and
  3 columns. Labels come from that run's own `mine_<m>.log` (`RULEMINER label:`), joined by law text; the labelled slice is the
  first n pool laws. The cached `v06-labels` folders cannot supply labels for the pool: the driver cuts mine j's slice at
  j x POOL x n, so with POOL=4 every mine but the first reads different laws than the cached POOL=1 run. The dump run is therefore
  a new dataset (same salts 4 to 10, same distribution, new law slices) with new counts, recorded when it runs. Assertions at stage
  0: the first n laws of each pool equal that mine's `laws_extra` prefix (the dump's own consistency); no law text repeats across
  salts or across the six mines of a salt (else leave-one-salt-out leaks).
- **Q2 hook** (only if Q1 passes): a new `Keep::Ctx` in `laws_for` ranks the pool's stragglers by score (ties in stream order),
  then its other laws in stream order, and takes the first n (`kept_indices` with the rank from `ctx_scorer::ctx_ranks`, the path
  `Keep::Small` takes). `EXTRAS_SELECT=ctx` plus `CTX_WEIGHTS=<file>` selects it. Runnable check, amended 2026-11-01: the original
  said that with all-zero weights `Keep::Ctx` must equal `Keep::First`, which contradicts "non-stragglers last" (`First` keeps the
  pool's first n, about 63% of them clean); the check is instead that equal scores give the stragglers in stream order, then the
  rest (a unit test of `ctx_ranks`).
- **Q2 feature set, amended 2026-11-01 (decision c1):** Q2 uses the 33 columns without group 3. Group 3 needs a served-only cover
  inside every mine, whose work and CPU count against the 5% work cap, and its direction caveat (it ranks first the laws the
  served rules already cover; `docs/tier-cycle.md`) is untested at Q2. The `mine` refactor above is therefore not built. The choice
  rests on Q1 clearing its bar with these 33 columns (plan `2026-11-01-ctx-scorer-q2.md`, Task 1); a failure there returns the
  decision to the user (the 35-column model).

## Stages

**Stage 0: reproduce, then dump.** Reproduction check before anything else, on the cached `v06-labels` label TSV (recovered
`dump_labels`): 42 mines, 13,398 labelled laws, 3,282 credited as recorded, and the recovered per-law model (26 columns, as stage 1), fit on
salts 4 to 9 and tested on salt 10 (the stage-1 split, `docs/tier-cycle.md`), reproduces test AUC 0.691 and train 0.711 within
0.005, and the size-only baseline (the size-sum feature alone, as stage 1 defined it) 0.528 within 0.005. Else stop and report.
Then build the dump over salts 4 to 10 (7 salts x 6 mines = 42 mines; new counts, recorded). Expected duration: a classify pass
over 1276 laws per mine (4 times the stage-1 one) plus a served-only cover per mine on top of the arm run; probe one salt first and
state the figure before the full dump (run through `run.ps1`, `-MaxMemGB 8`, `-Affinity CFF`).

**Stage 1: Q1, offline, leave-one-salt-out.** For each held-out salt s: fit the per-law and context models (standardised, on
stragglers) on the other six salts. In each of s's six mines, rank the 319 labelled laws by each ranker and count y = 1 in the top k,
k in {40, 80} (about n/8 and n/4; amended 2026-11-01 from {80, 160} by the user, decision a2, after Q1 showed no room at k = 160: a slice holds about 112 stragglers). Rankers: the per-law model, the context model, the `small` key (the order `kept_indices` gives
under `small`, restricted to the 319 labelled laws), and random (mean over 200 seeded shuffles of the 319, seeds 1 to 200). Also
AUC, the number of stragglers and positives per slice, and the ceiling min(k, positives): if `small` is already near the ceiling at
k = 160 there is no room and the report says so.
Gate: let d be the sum over the 42 mines of (context capture minus per-law capture) at a given k, and e the same against `small`.
Pass if, at both k, the 95% interval of d and of e from a paired bootstrap over the 42 mines (2000 resamples, fixed seed) excludes
0 from below, AND d > 0 and e > 0 on at least 5 of the 7 salts. Both baselines are fixed arms, reported separately (not a
per-mine max). Else stop, record a negative with the numbers in `docs/tier-cycle.md`, and update the `PARKED.md` entry. A
feature-group ablation (drop each of groups 1 to 3, and the per-law features) is reported either way, so a negative says which
signal is absent. Limitation, recorded either way: labels exist only for the slice, so Q1 ranks within the slice; Q2 ranks the whole
pool, where 957 laws never had a label.

**Stage 2: Q2, the gate (only if stage 1 passes; plan `docs/superpowers/plans/2026-11-01-ctx-scorer-q2.md`; decisions c1 and d1 of
2026-11-01: 33 columns, `POOL=4`).** Arms at n in {80, 160}: `small`, the context arm, random of equal
walk work (the knee-chart construction), and two further redraws of both the random and the `small` arms (`GEN_DRAW=3`, `4`) so that
sigma is measured at these n and for the arm compared against (sigma 76 rests on two random-arm redraws at n = 319); mines per
salt stay six. The context weights are fit on salts 4 to 10 and evaluated on salts 1 to 3, disjoint from training. Replication:
weights refit on salts 7 to 10 only (24 mines, a thinner fit, stated as such), evaluated on salts 4 to 6. Metrics as `streams_ab.sh`:
held-out M per band, walk and match counts (deterministic), job CPU including the scoring (load noise about
+-10%, a cross-check). Amended 2026-11-01: the work ratio is the summed WORK `walk` count (the knee chart's basis), not
`icount.ps1` instruction counts: the arms run as whole sweeps with their own environments, which `icount.ps1` cannot reproduce.
Pre-registered rule: the context arm passes if
held-out M is below the `small` arm's by more than the larger of sigma and the measured `small` redraw spread (the largest
|redraw - draw 0| over `GEN_DRAW` 3 and 4, as sigma 76 was read) at both n AND the walk work is not larger by more than 5%, on both
the primary and the replication salts; otherwise null (`scripts/q2_verdict.sh`).

*Result (2026-11-04): null.* The primary fails at both n (D +99 at n = 160, -50 at n = 80 against T 76 and 163) and the replication
fails at both n (D +12, +66); record and limits in `docs/tier-cycle.md`, "Q2 primary run". The replication's redraws and equal-work
random arms were not run (D > 0 fails the rule at any T). The unmeasured shifts (fit n = 319 against serve n = 80/160) remain.

## Risks and checks

- **Few contexts.** 42 mines are a small sample; a positive Q1 has to come from within-mine ranking, which is what the statistic
  measures.
- **The label is a path.** Greedy credit depends on candidate order and the 400-candidate cap, so y is noisy for reasons no feature
  sees. A ceiling is unknown. If all rankers sit near the random mean, the label is not predictable by any feature set here.
- **Stage-1 AUC did not predict the frontier.** Q1 can only veto. A pass buys one gate.
- **Thin spread.** Stage 2 measures the spread it needs before reading any difference.
- **No A/A on held-out M** other than the redraw spread; the gate is deterministic, so a rerun reads zero spread. Say so in the result.
- **Cost.** See stage 0; the served-only mine is the expensive part and is also a Q2 CPU cost.

## Checks left behind

- `ctx_scorer` unit tests: `fit` refuses no rows; features are deterministic on a fixed law and pool; percentile columns lie in
  [0, 1] and ties share a rank; the leave-one-salt-out split never puts a salt in both sides; a weights file with a different
  layout version is refused; the zero-weight `Keep::Ctx` check above.
- The stage-0 reproduction check and the Q1 report are kept as ignored tests, with the run ids.
- Docs: the result goes in `docs/tier-cycle.md` (a section beside "A learned scorer over the extras"), the `PARKED.md` entry is updated
  (trigger met or not; it cites the removed scorer as `71cb240`, this spec as `8d9ceaf^`, the same code; unify on `8d9ceaf^`), and
  `docs/TOUR.md` plus `bash scripts/tour_check.sh` in the commit that changes a tour cite (`Keep::Ctx` does; no served-only
  refactor is built, see decision c1).

## Calls I made (not the user's; the user asked to skip the questions)

- Offline veto first (Q1) before any gate: stage 1's offline AUC was real and the gate still failed, and a positives-captured
  statistic within each mine is the closest cheap proxy for what selection does.
- The context scorer lives in `laws_for` (the miner), not in `scope_extras`, because only the miner sees the base rules.
- The bar is the `small` key, not random.
- Fit and rank on stragglers only, since y = 1 implies straggler.
- Logistic regression again, hand-rolled, so a failure is attributable to the features, not the model class; a richer model stays
  parked until a context signal exists.
- The marginal gain (h1b) enters as a feature, not as its own selection arm; its ablation says whether it carries the effect.
- w1 only; w2 only if `transfer_labels` is cheap to recover.
- The Q1 gate uses a paired bootstrap over mines, not the random ranker's sd, because the quantity compared is a paired difference.

## Decisions (the user, 2026-11-01)

Approved as written. m1: the strict Q1 bar (bootstrap interval above 0 at both k against both baselines, and 5 of 7 salts). n1: keep
group 3 (the served-only partial mine and the `mine` refactor). o1: a null is recorded only; the stage-2 `PARKED.md` entry stays.
The first plan covers stage 0 and stage 1 only; stage 2 gets its own plan if Q1 passes.

Amended 2026-11-01 after Q1: a2: the Q1 bar is k in {40, 80} (Q1 passes). c1: Q2 uses the 33 columns without group 3, so n1 is
superseded for Q2 (no served-only cover, no `mine` refactor; group 3 over-credits laws the served rules already cover). d1: pool 4,
n in {80, 160}. The Q2 plan is `docs/superpowers/plans/2026-11-01-ctx-scorer-q2.md`.
