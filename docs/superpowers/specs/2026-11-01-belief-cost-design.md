---
status: draft
---

# Belief layer stage 2: predicting the cheap path's misses (design)

Amends `docs/superpowers/specs/2026-10-31-belief-layer-design.md` (done; its stage 1 stopped at the gate, `docs/tier-cycle.md`,
"The belief layer's calibration milestone stops at its first gate"). Decisions of 2026-11-01: f2 (reframe stage 2 as
cost prediction) and h1 (f2 first, on the existing dump with no `verdict` change; g1, an every-input fallback inside
`verdict`, is decided afterwards with f2's result and a timed estimate of the fallback's price).

## Why the question changed

The first spec scored P(refuted). Among claims that pass the screen and the exhaustive width-4 check none was refuted, so
there was nothing to rank. The spike of 2026-11-01 (`docs/tier-cycle.md`, same section) found that every screen-pass claim
`verdict` leaves unproved (2693 of 63384) is true on every width-6 input and is proved by `prove_rule` at width 4, about
0.3 s each. So the label that varies is not truth or provability but **which path proves the claim**: `verdict` (a carry
encoding with each `shr1` a fresh atom, milliseconds) or the every-input proof (0.3 s).

## Question and success

Does a claim's shape, plus the evidence it carries, predict that `verdict` will miss it, better than the cheap baselines?

- **Label.** Negative = `Unproved` in the dump (`verdict` is `None`). Positive = `Proved` (`verdict` is `Some`). `Refuted`
  rows are outside the population (screen-pass excludes them). The dump is the run `2026-11-01-belief-dump-all-2`
  (`claims.tsv`), reused without a rerun; the spike makes the label "needs the slow path", since every negative is
  provable. Truth is not re-checked per claim here.
- **Population.** The screen-pass subset: `in_subset(r, 0)`, which requires only `w4` and `screen`; no row of this dump in it
  is refuted (empirical, not by definition), so it holds 63384 claims, 2693 of them negative. The gate is the first spec's
  (at least 100 negatives in all, 10 per fold, no fold over 40% of the rows) and is checked by code, not by the global count:
  `gate` today counts `Refuted` rows (it would report 0 here), so it takes the negative class as a parameter and counts
  per fold from it.
- **Strata, reported apart.** (a) *All* screen-pass claims; (b) claims containing `shr1`: 14904 claims, 2652 negatives (17.8%),
  12252 proved. The `shr1` stratum is the headline: outside it only 41 negatives (all `lt`) remain, and "contains `shr1`"
  alone already separates 2652 of 2693 negatives from the rest.
- **Features** (all derivable from the stored `u` and `r` text with `parse_term`, so no new dump): kind, key, size, vars,
  and new shape counts: number of `shr1` nodes, whether a `shr1` sits under `add`/`sub`/`lt`, depth of the deepest
  `shr1`, `shl1` count (the depth of a `shr1` is taken through its first argument; the ignored second one does not count). The first spec's evidence flags (`w4`, `screen`, `extra`) are constant in this subset and are
  dropped.
- **Comparators,** all scored out of fold like belief: (c1) size-only, its direction (larger size means likelier negative, or the
  reverse) chosen by AUC on the training folds, since size is not monotone here (in the `shr1` stratum size 20 has 34
  negatives and 0 proved, size 8 has 10 against 42); (c2) the indicator "contains `shr1`"; (c3) the kind-only counts cell;
  (c4) a logistic regression on kind, size and vars only (basic shape, no `shr1` feature), the bar that says whether the
  `shr1` features add anything. Ties score half. In the `shr1` stratum c2 is constant (0.5), so the bar there is the best
  of c1, c3 and c4.
- **Primary.** The paired AUC difference on the `shr1` stratum, belief minus the best comparator (the best by out-of-fold AUC
  on that stratum, named and printed before the interval), with a 95% paired bootstrap interval. The bootstrap resamples
  the `fold_of` components (claims that share a side term move together), not claims, since claims are not independent;
  belief wins if the interval lies above 0. A co-primary on all screen-pass claims uses the same rule (there c2 is a strong
  comparator).
- **Co-primary, no key.** The same with the key feature removed, since a proposer's claim has no key; and a per-feature
  ablation. A win that only exists with the key is reported as "the key predicts".
- **Estimators.** Counts (j1) and logistic regression (j2, `logistic_fit`), with the grouped 5-fold cross-validation and
  reliability bins of the first spec. The counts arm needs a design change the first spec did not: `Cell` holds kind, key,
  `w4`, `screen`, `n`, of which the last three are constant in this subset, so the fallback chain would collapse to a
  kind-by-key table. `Cell` gains a `shape` bucket (0: no `shr1`; 1: one `shr1`, not under `add`/`sub`/`lt`; 2: one `shr1`
  under one of them; 3: two or more `shr1`) with the chain exact cell, (kind, key), (kind, shape), kind, global; the
  `w4`/`screen`/`n` fields stay for the first spec's tests. The orientation changes too: the hit is `Unproved`, and the
  bitwise-on-bool8 shortcut of `belief_counts` does not apply (a new `belief_cost` function carries it). Logistic stays only if its paired interval against counts lies above 0. A tie or loss is a recorded negative
  result.
- **Stop rule.** The AUC is reported with its negative count per stratum and per key; per-key numbers are descriptive.

## What a win would mean, and the risk that decides whether to run it

`verdict`'s outcome is a deterministic function of the claim and costs milliseconds, so a model that predicts it is
predicting something one can compute directly for less than the model costs. A high AUC would show that the cheap path's
misses are a simple function of shape (which the spike already suggests: `shr1` under an operator the carry encoding
cannot see through). It would **not** show a belief layer pays for itself here, and no consumer reads it: no code in the
kernel, miner or class table reads a belief. The milestone is therefore calibration plumbing on a label that happens to
be cheap, kept for the day a claim source has a label that costs more than the model (a proposer's claims, i2, or a
timing-valued target). A high AUC is also predictable before the run: the split 2652 of 14904 `shr1` claims against 41 of
48480 others is already a one-feature rule, and the baselines inside the `shr1` stratum are near chance, so beating them is
easy. Unless a consumer is named, the default is to close the unprovability line (decision f1 of 2026-11-01) and put the
effort into g1 or goal 1; this spec is the plumbing for a future claim source, not a result worth the run by itself.

## Interface and scope

Unchanged from the first spec: `belief(claim, evidence) -> f64` orders and budgets work and never accepts a claim. New code
is two functions in `tests/church_bv/belief.rs` (shape features from the term text; the stratified report) plus unit tests
(feature counts on hand-written terms; a stratum with a known AUC); `docs/TOUR.md` mentions nothing new beyond the report.
Out of scope: g1; a rerun of the dump; any consumer; timing of the slow path (a timed estimate for g1 is a separate step,
under `run.ps1 -Timed`).

## Risks

- **Circularity.** The label is the output of `verdict`; features that mirror its logic (a `shr1` under an operator)
  reproduce it. Reported as such, not as a discovery.
- **Distribution.** Three variables, size at most 9, one enumerator; transfer to a proposer's claims is untested (i2).
- **Shared subterms.** Claims share sides across keys; grouped folds keep the worst of it out of the train/test boundary.
- **The `lt` negatives.** 41 non-`shr1` negatives are all `lt`; too few to rank apart from the `shr1` stratum, so the
  all-claims co-primary is dominated by `shr1`.

## Stages

1. Feature extraction and the stratified report on the dump: gate, comparators, counts arm, bootstrap.
2. Logistic arm and the comparison; record the finding in `docs/tier-cycle.md`, update `PARKED.md` ("Belief layer stage 2")
   and `ROADMAP.md` goal 3, close the milestone.
