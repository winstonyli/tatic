---
status: draft
---

# Belief layer, calibration milestone (design)

Goal 3 of `ROADMAP.md` ("the calibrated belief layer"). Background: `docs/tier-cycle.md`, "How much random testing is
worth" (the first calibration point) and `docs/decisions/2026-10-31-learned-target-model.md` (the belief layer is the
substrate both learned-model uses share). Decisions of 2026-10-31 (the user's picks, in order): first consumer g4
(calibration only, a consumer later: g2 filtering a proposer's claims); success h1 (beats the fixed screen); population
and label i1 (key-proposed merges, held-out refutation); estimator j1 (smoothed counts) with j2 (logistic regression) as
the one comparison arm. Revised after an adversarial review (10 findings, 4 blocking; the changes are marked "review").

## Question and success

Does a claim's shape plus the cheap evidence it has passed predict whether the kernel can prove it, better than the
fixed screen's pass/fail?

**Evidence and label are kept apart (review 1, 2).** Evidence, known when a claim is judged, in tiers:
(a) its key; (b) `w4`, passes every width-4 input; (c) `screen`, passes `SCREEN_INPUTS` (204) width-8 inputs;
(d) `extra[n]`, passes the first n of a fixed set S1 of 256 random width-8 triples (nested prefixes, n in {0, 8, 64, 256}).
The label is ground truth and uses none of those as a shortcut: `refuted` if the claim differs on a fixed set S2 of 4096
random width-8 triples, disjoint from S1 (the label tests are a different draw, not a superset), or on any of S1's 256,
or on any width-4 input, or on the screen's inputs (a claim false anywhere is false, so a claim that fails S1 is
refuted whatever n it is scored at); `proved` if the kernel proves it; `unproved` otherwise (round 2, finding 1).
S2 reuses the old probe's 4096-input seed and the claim sample its reservoir seed, so d and the sample match the
2026-10-22 run; S1 is a new fixed seed.

**Each claim is scored at a fixed n, and the AUC set is named (round 2).** The primary is at **n = 0** (key, shape,
`w4`, `screen`; no extra tests): "does shape plus the free evidence predict". n = 8, 64, 256 are reported apart as "more
tests help", each against the plain pass/fail of the same first n of S1 as the fixed-filter comparator (at n = 256 the
screen's 204 inputs are not the fair comparator, since belief would hold 256 more tests than the screen).

Two binary scores, each reported with its negative count (review 6):
- **A_ref:** refuted vs not refuted. The screen cannot see this among claims that pass it, so the comparison that
  matters is the **screen-pass subset** (passes `w4` and `screen`, as in deployment, where the screen runs first). There
  the screen's score is constant (AUC 0.5, ties scored as half) and the question is whether belief ranks the
  remaining refutations (those differing on few of the 4096) below the rest.
- **A_unp:** unproved vs proved among the unrefuted claims. Its negatives were, in the 2026-10-22 run, 19 `lt` claims (10 of them in the
  exhaustive key; to be recomputed on the new dump) and are reported as descriptive, with an exact interval, not as a headline.

Also reported on **all claims** (where `w4` and `screen` are evidence features and the screen's own AUC is inflated
by construction, since, in the 2026-10-22 run, 5, 10 and 21 claims (per key; recomputed on the new dump) were caught only by width 4 or the screen), the strata by d, the share of the
4096 inputs a refuted claim differs on (d = 0 and d ≤ 1%, where the question is not trivial), and `lt` on its own.

Baselines (review 2, 9): the **extra-free** model (kind, key, shape only) and the **size-only** score. A claim of
"beats the screen" needs a margin over both, by the verdict rule of `docs/tier-cycle.md`, "A learned scorer over the
extras" (stage 1: 0.691 against size-only 0.528).

**Primary:** the paired difference of AUCs at n = 0, belief minus the better of {the screen's 0.5, size-only}, on A_ref
over the screen-pass subset, with a 95% bootstrap interval over claims (paired: the same resample scores both). Resamples with no negative are skipped and the
negative count is printed beside the interval. Belief wins if the interval lies above 0.
**Reading n = 0 (round 3).** In the screen-pass subset `w4` and `screen` are constant, so the n = 0 test is a shape-only
test: belief ranks on kind, key, size and vars, and size-only shares most of that. So the win must also hold for the
**no-key arm** (kind, size, vars; key is not a feature a proposer's claim has), which is a required co-primary, and the
report gives a per-feature ablation (kind, key, size, vars, each removed in turn). A win that exists only with the key
is reported as "the key predicts, not the evidence". n = 8 is the first level where a free-standing evidence feature
exists and is reported next to the primary, not behind it. Per-key AUCs are descriptive only (four keys are designs, not a sample; review 4). A tie or a
loss is a recorded negative result ("evidence does not beat the screen"), not a failure of the milestone. The
milestone makes no speed claim; run cost is counted in instructions (`~/.claude/ICOUNT.md`).

## Data

Claims are the merges a key proposes while the class table is enumerated, sampled uniformly per key, as in
`claim_calibration` (patch `docs/runs/2026-10-22/patches/claim_calibration.patch`, script
`docs/runs/2026-10-22/scripts/claim_calibration.sh`; the patch was reverted, so the dump is rebuilt as a new throwaway
probe, not reapplied). One row per claim, in `%LOCALAPPDATA%\claude-runs\tatic\<run>\claims.tsv`:
`key, kind, size, vars, w4, screen, extra8, extra64, extra256, d (of 4096), label, index` (`index` = the claim's
position in its key's sample, which orders the proving deadline).

**Untried claims (review 3).** Proving stops at 10 minutes per key, and the old probe checked refutation on every claim
but proved only until the deadline, so 40-53% of the last three keys' unrefuted claims were untried while every refuted
one was kept. The new dump cuts every claim past a per-key claim-count cap (fixed in advance from the old run's
deadline index, not a wall-clock deadline, so the cut does not depend on the machine), refuted or not (or raises the
budget until all are tried, if the run fits), so the label mix is not biased. It reports the old convention (untried counted
proved) beside it only as the reproduction check below.

**Splits (review 10, round 2).** Claims are grouped into connected components over shared side terms (a claim `u -> r`
joins every claim with the same `u` or the same `r`), and a component's hash picks one of 5 folds, fixed before any fit.
The counts and logistic arms are trained and scored by grouped 5-fold cross-validation, and the paired bootstrap runs
over the pooled out-of-fold scores.

**Stage-1 gate (round 2).** Before any estimator: the dump reports the screen-pass subset's negatives per key and kind
and per fold. If the subset holds fewer than 100 negatives in all or fewer than 10 in any fold, stage 2 does not start; the finding is "too few
hard negatives to compare" and the milestone is recorded as such. By the old table most are `lt` claims in the three
random keys, and the exhaustive key's 10 `lt` negatives are unproved, not refuted, so they are not in A_ref's subset, so the count is expected to be in the hundreds, not computed yet.

## Estimators

- **Counts (j1).** For each cell (kind, key, w4/screen, n) the fraction of the training folds' claims that passed n tests
  with the score's own outcome (refuted, for A_ref; unproved among unrefuted, for A_unp; proved for the reproduction
  check), with a Beta(1, 1) prior: p = (hits + 1) / (tried + 2), and belief = 1 - p for the negative class. In the
  screen-pass subset `w4` and `screen` are constant, so the cell is (kind, key, n) there and the (kind, key) fallback
  is the normal cell. An empty cell falls back to (kind, key), then to the whole
  key, and the fallback is flagged in the report. Evidence that decides outright is not estimated: a pure bitwise term
  on the 8 Boolean tuples is p = 1, and a claim any check refutes is p = 0. Ties are scored as average rank. The 309
  bitwise claims of that key are p = 1 by decision and add no ranking information.
- **Logistic regression (j2).** Features: kind and key (one-hot), `size`, `vars`, `w4`, `screen`, the `extra` bits. Fit
  by hand-rolled Newton steps with L2 on the training folds; no new dependency. Kept as the answer only if its paired
  interval (against the counts arm) lies above 0.

**Reproduction check (review 5).** The 2026-10-22 cells are expectations from d, P = proved / (proved + sum of
(1 − d/4096)^n over the refuted), with untried counted proved; the new cells are empirical and smoothed, so they match
only to a stated tolerance. Test: the unsmoothed old formula on the new dump, with the old label (refuted by the 4096 random inputs, every
width-4 input or the screen; untried counted proved; all claims, not the subset), reproduces the old table's rows to
0.01 for every cell of at least 200 claims (the new label also fails any S1 input, so it differs by construction); then the empirical counts cells are compared with it.

## Interface

`belief(claim, evidence) -> f64` in [0, 1]. It orders and budgets work only. Nothing in the kernel, the miner or the
class table reads it; probabilities never become accepted claims. The open question in `ROADMAP.md` (whether a
high-belief claim may enter the kernel as a tracked postulate) stays open.

Code lands in `tests/church_bv/belief.rs` (counts, logistic fit, AUC with ties, the paired bootstrap, reliability
bins: 10 equal-count bins per kind) with unit tests: the counts reproduce a hand-computed table; the AUC of a perfect
and a constant score are 1 and 0.5, and ties count half; the bootstrap of a constant statistic has zero width; the
logistic fit separates a separable toy set; the input sets S1 and S2 are disjoint (the test compares the sets, not the
seeds). A new module and its place in the data flow get a `docs/TOUR.md` entry in the same commit
(`bash scripts/tour_check.sh`).

## Out of scope

The miner's candidate rules (i2, parked as the transfer check for g2); any proposer; pruning or ordering in the loop; the
postulate question; a GPU model.

## Risks

- **Few negatives.** After the screen, refutations differ on few of the 4096 inputs and are mostly `lt`; the 19
  unproved are too few to rank. The report states which negatives each number rests on.
- **Distribution.** Three variables, size ≤ 9, and `lt` never nested (a second sort no operator consumes) are not a
  proposer's claims; transfer is untested until i2.
- **Key as evidence.** A key is evidence the claim already passed, chosen by us; a proposer's claim has no such key. The
  report gives every number with and without the key feature (the extra-free model is the second case).
- **Claims share subterms across keys,** so claim-level resampling is still slightly optimistic; the grouped folds
  keep the worst of it out of the train/test boundary.
- **Leakage.** S1 and S2 are fixed, disjoint sets, and the folds are fixed before any fit.

## Stages

1. Rebuild the claim dump as a throwaway probe (patch kept under `docs/runs/<date>/patches/`, reverted); pass the stage-1 gate and the
   reproduction check.
2. `belief.rs`: counts, AUC, paired bootstrap, reliability; run the primary comparison for the counts arm, the screen and
   the size-only score.
3. Logistic arm and the comparison; record the finding in `docs/tier-cycle.md` and close the milestone in `ROADMAP.md`.
