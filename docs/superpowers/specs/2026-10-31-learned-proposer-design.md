---
status: active
---

# v0.6: does a learned proposer push the frontier? (design)

Milestone: `ROADMAP.md`, v0.6 (goals 2 and 3). Background: `docs/tier-cycle.md`, "Idea", "The proposer model's target",
"Count and slicing", "The frontier on the gate". Decisions of 2026-10-31 (the user's picks): scorer first, not the GPU
model; success is a curve shift; the label is miner credit; offline stage before the cycle; Rust, hand-rolled.

## Question and success

Does ordering the laws a mine runs on, by a model trained on the kernel's own verdicts, move the frontier (held-out free
share per band) beyond a random draw of the same laws, at the same mining CPU?

The baseline is today's draw: each mine takes the first n laws the filter keeps from its fresh slice of the stream
sequence (`scope_extras`, `EXTRAS_N` = 319). Redrawn lists move held-out M by a few percent and the frontier by a few
points at n 319 ("Does the choice of extras move the frontier?"), and n costs CPU about linearly (held-out M falls about
770 per e-fold of n; n 688 gives 4622 against 5166 at about twice the job CPU, `PARKED.md`, the mining-budget entry).
So the success measure is a **curve shift**: the scorer arm at a smaller n matches the random arm at a larger n, or beats
it at the same n, by more than the redraw spread (the A/A of a deterministic gate). Nothing below n 319 has been measured, so the random curve at n 80 and
160 is part of the result.

Out of scope: the GPU model (goal 3's end state; it would sit behind the same `score` interface), new definitions,
laws beyond 5 nodes, the belief layer. scratchtape is not a dependency.

## Architecture

One new mechanism: a `Scorer` that orders candidate laws. Nothing else changes in the kernel, the miner or the filter.

- **`tests/church_bv/scorer.rs`** (new): `Scorer { weights }` with `score(&(Term, Term)) -> f32`, `features(&law) -> [f32; F]`,
  `fit(rows) -> Scorer` (logistic regression, fixed-seed full-batch gradient descent), and text load/save of the weights.
  No dependency. Deterministic.
- **`scope_extras`** (`tests/church_bv/driver.rs`): when `SCORER=<weights file>` is set, each mine's slice is 4n
  consecutive kept laws and the mine takes the top n by score (ties keep sequence order). Unset, the code path is today's.
  With all-zero weights the scorer arm equals the baseline: that is the runnable check.
- **Label dump** (the miner's report, `RULEMINER ... covered`): one TSV row per extra law and mine: salt, n, mine, the law,
  y. y = 1 if the law was a straggler (needed a machine proof under the rules in force) and a chosen rule covers it, else 0.
  Free laws are y = 0: the scorer predicts "pays for a rule", not "is hard". Rows go to the run folder (`RUN_DIR`).
- **Features** (about 30 counts, no text): nodes per side, operator histogram, variable count, depth, size difference,
  shared leaves, whether a side is a variable-permutation of the other.
- **Trust.** The scorer only orders candidates. Every law still passes the existing filter and the kernel; no score reaches
  the kernel (goal 3's belief rule).

## Stage 1: signal (this milestone's first build)

1. **Dump** labels from the random arm on salts 4-10 at n 319 (fits the existing sweep; the fresh-slice draw is unchanged).
2. **Fit** the scorer offline on those rows (`fit`), report held-out AUC on a salt it did not see, against a trivial
   baseline (size only). A scorer that cannot beat size-only AUC stops here.
3. **Gate A/B** on salts 1-3 (disjoint from training), n in {80, 160, 319}, arms random and scorer, plus the 4n-pool-first-n
   control (see Risks) and two redraws of the random arm (`GEN_DRAW=1`, `2`) at n 319. The gate is deterministic (the same exe and environment give the same rules and M), so a rerun reads zero spread; the **A/A spread is the redraw spread** (plan, Task 7). Metrics per `streams_ab.sh`: frontier per band, held-out M, job CPU, work counts.
4. **Verdict**: curve shift, or a recorded negative with the AUC and the curves in `docs/tier-cycle.md`; stage 2 is then
   parked in `PARKED.md` with its trigger.

Labels come from the random arm's mines only, so the scorer is not trained on its own picks.

## Stage 2: the cycle (outline; its own spec and plan if stage 1 shows a signal)

Round r: pool, score, mine on the top n, read frontier and labels, refit on the labels of rounds before r, next round.
Tracked: the frontier and the curve shift per round. Open: whether to refit on all rounds or the last, and the label's
in-sample bias (greedy credit rewards laws that are easy to cover whether or not their rule transfers; the held-out
frontier is the check, so a w2 transfer label can replace w1 if the two diverge).

## Risks and checks

- **Sequence length.** 4n per slice needs 4 x loops x mines x n kept laws from the deep sequence; `scope_extras` already
  errors when it is short. The plan's first task measures whether it fits at n 319, and the pool factor drops (2n) if not.
- **A linear model on counts may find nothing.** A null result says "no linear signal in these features", not "no signal".
  Recorded as such; richer features or y3 (a Rust ML crate) are then the parked next step.
- **Leakage.** Training salts 4-10, evaluation salts 1-3; the held-out bands are never in a pool (`filter` already removes them).
- **Selection bias in the pool.** The scorer arm draws from a 4x larger prefix of the sequence than the random arm, so the
  random arm at 4n-pool-and-first-n is not the same draw. The random arm is today's code path; a control arm draws 4n and takes
  the first n, to show the pool size alone moves nothing.

## Checks left behind

- A unit test: all-zero weights leave `scope_extras`' slices equal to the baseline's.
- A unit test: `fit` on a separable toy set reaches AUC 1 and is bit-identical across two runs.
- The stage 1 gate rows in `docs/runs.md`; the finding in `docs/tier-cycle.md` with run ids.

## Architecture check

Adds one selector over the existing extras draw; no per-case branch. If stage 2 lands, the random draw becomes the scorer
with zero weights and the `SCORER` switch is deleted (the baseline stays only while the A/B is pending).
