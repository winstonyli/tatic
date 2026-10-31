---
status: done
---

# v0.6, second try: select the extras from the kernel's own verdicts (design)

Milestone: `ROADMAP.md`, v0.6 (goals 2 and 3). Follows `2026-10-31-learned-proposer-design.md` (done, negative) and
`docs/tier-cycle.md`, "A learned scorer over the extras". The user's pick of 2026-10-31 was h1: greedy set selection from
the kernel's own verdicts, not a learned per-law score.

## Question and why

Stage 1 found offline signal (AUC 0.69) but no curve shift: a per-law score cannot see the other laws in the mine, and a
law's value depends on them. The kernel can: before a mine chooses rules, `laws_of` rewrites every law under the mine's
base rules and says which are **stragglers** (need a machine proof). Only stragglers can be credited. Measured on the
random arm's mines (`2026-10-31-v06-labels`): of 13398 extras, 4976 (37%) were stragglers and 3282 of those (66%) were
credited. So 63% of the extras a mine reads cannot earn a rule.

Question: does filling the n extras slots with laws the kernel marks as stragglers (from a larger pool) move the frontier
beyond a random draw at the same mining CPU?

## Design

Selection runs **inside the mine** (`rule_miner`), because straggler status depends on that mine's base rules, which the
driver does not have. The driver only supplies a pool.

- **Pool**: with `POOL=p` (exists), the driver appends p×n kept laws per mine instead of n, and tells the miner where the
  extras start (the number of served laws, `RULEMINER_LAWS`; the extras are the lines after them in the lawfile) and
  `EXTRAS_KEEP=n`.
- **h1a, straggler-first (the first build)**: `laws_of` classifies the served laws plus the pool; the miner keeps the
  served laws and the first n pool laws that are stragglers (stable, sequence order), filling any shortfall with the
  first non-stragglers. A law the base rules do not close counts as a straggler, as in `laws_of`. Everything downstream
  (candidates, greedy rule choice, guard sample) sees only the kept laws. No score, no weights, no training.
- **h1b, marginal selection (parked until h1a reads)**: pick pool laws by what they add to the set, using the miner's
  own candidate rules (`candidates`): for example prefer stragglers whose candidate left side no kept law has yet, or
  stragglers still uncovered after a first greedy pass over the served stragglers alone. Which direction pays
  (laws the served rules already cover add evidence for those rules; laws they leave uncovered add new rules) is not
  known, so h1b is two arms, decided after h1a.

Trust is unchanged: selection only decides which laws are read; every rule still passes the kernel.

## Cost

The mine's work is mostly stragglers, so straggler-first fills n slots with about 2.7× the stragglers of a random draw
(1 against 0.37) and may cost more CPU per mine at the same n. So the judgement is at **matched CPU**, over a curve:
arms at n in {80, 160, 319} for random (exists: r80, r160, r319) and h1a, plus the classification cost of the pool
(measured earlier at about 0.1 s per mine for the base rewrite; recheck at POOL 4, it scales with the pool). The pool
costs CPU in the lawfile read and classification and is counted in job CPU.

## Success (set before the data, reuses stage 1's)

Gate A/B on salts 1-3, held-out M summed, σ = 76 (the redraw spread, `GEN_DRAW=1,2`). Win: held(h_n) < held(r_n) − σ at
job CPU ≤ 1.1× the random arm's, or held(h_n) ≤ held(r_2n) at lower job CPU. Control: the in-mine path with
`EXTRAS_KEEP` taking the first n regardless of verdict (selection off) lands within σ of r319. A null result says "the
verdict of the base rules does not choose better extras", recorded with the curves.

## Checks left behind

- Identity: with selection off, the in-mine path reproduces the baseline's lawfile and rules byte for byte (the same
  check stage 1 used for zero weights).
- Unit test of the keep step: stragglers first in sequence order, shortfall filled, extras count always n, served laws
  untouched.
- Determinism: the verdict is a function of the laws and the base rules only (step budget, not a clock); two runs of one
  mine give the same kept set. If the budget is time-based, the plan fixes that first.
- Gate rows in `docs/runs.md`; the finding in `docs/tier-cycle.md` with run ids.

## Out of scope

The GPU model, the cycle (stage 2), the belief layer, new definitions. The per-law linear scorer and its offline
pipeline stay as they are until the user decides their removal (`PARKED.md`, the v0.6 entry).

## Stress test (my own passes, three rounds)

1. Caught: selection cannot run in the driver (base rules are per mine) → moved into the miner. Caught: CPU per mine rises
   with stragglers, so an equal-n comparison would flatter or punish h1a → judged at matched CPU over a curve. Caught:
   classification cost unaccounted → counted in job CPU. Caught: "unproved" laws unclassified → counted as stragglers like
   `laws_of`.
2. Caught: a selection-off control was missing (the pool alone could move M) → in-mine first-n control within σ of r319.
   Caught: non-straggler extras may act as guard laws, so dropping them could cost regressions → the guard sample is
   drawn from the served machine-free laws as today; a regression shows as a worse held-out M and is a recorded outcome,
   not hidden. Caught: h1b's direction is unknown → two arms, after h1a.
3. Found nothing material beyond wording. Not verified yet: that the extras start can be read from the lawfile (plan
   task 1), the verdict's determinism (a check above), and the 0.1 s cost at POOL 4.

## Addendum, 2026-10-31: h1a-cheap (set before data)

Straggler-first gave better held-out M at every n for 1.4-1.9x the job CPU (`docs/tier-cycle.md`, "Selecting the extras by
straggler verdict"). Variant `EXTRAS_SELECT=cheap`: of the pool's stragglers keep the n with the fewest rewrite steps spent
classifying them (`Outcome::Straggler`'s count; a deterministic cost, ties in stream order), then fill as before. One
mechanism with `straggler` (`kept_indices` ranks by a cost key; `straggler` is the constant key). The machine-proof count
cannot rank: every straggler in `v06h-g5`'s logs counts 1 (2710 of 2710).

Gate: salts 1-3, pool 4, n in {160, 319}, against the recorded random arms (r160 5517 at 446 s, r319 5166 at 674 s, r638
4600 at 910 s) and straggler-first (h160 4931 at 841 s, h319 4498 at 1252 s). Win: held(c_n) < held(r_n) - 76 at job CPU
<= 1.1x r_n, or held(c_n) <= held(r_2n) at lower job CPU. Else null; "dominated" if no better than straggler-first at
more CPU. Reading beyond the rule: whether `cheap` sits left of straggler-first on the (CPU, held-out M) curve.

### Follow-up control (set after `v06c-g1` to `g3`, before its data)

`cheap` n 160 reads 4721 held-out M at 700 s; the random arms are n 319 5166 at 674 s, n 345 5023 at 608 s, n 638 4600 at 910 s,
so the pre-registered rule (b) misses by 26 s against r319 and the random curve at 700 s (interpolated) is about 4894. The
match on work counts is random n about 433 (c160's walk count 488 M against r345's 388 M). Control: random n 433 against
`cheap` n 160, salts 1-3 (`v06c-g4`) and fresh salts 4-6 (`v06c-g5`). Win: held(c160) < held(r433) - 76 on both salt sets, with
c160's job CPU <= 1.1x r433's. This is a post-hoc control, not the pre-registered rule; a pass says the n 160 point is on a
better curve, not that the milestone rule was met.

Result (2026-10-31): `v06c-g4` -111 and `v06c-g5` -205 held-out M against random n 433 at 1.05x and 1.03x job CPU: the control
passes on both salt sets. The pre-registered rule (b) missed by 26 s. Details: `docs/tier-cycle.md`, "The cheap variant".
