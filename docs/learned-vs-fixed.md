# Learned vs fixed

Which parts of the reasoning pipeline (rewriter, prover, miner, loop) are learned from data and which are fixed by hand. The goal
(docs/tier-cycle.md) is a kernel that improves itself, so parts move from the right columns to the left over time.

**Keep this current.** Update the row when a part becomes learned, when an experiment measures a fixed part (put the number and a
pointer in "Evidence"), and when a part is added or removed. Experiments' details stay in docs/tier-cycle.md; this page holds the
verdicts. Last updated 2026-10-11.

Columns: *learned in the run*: changes from data while the loop runs. *Learned once*: came from data, then frozen in code.
*Fixed*: written by hand, possibly tuned by experiments (tuning is not learning).

| Part | Learned in the run | Learned once | Fixed | Evidence (M is total over families; lower is better) |
|---|---|---|---|---|
| Trusted checker (`src/kernel.rs`) | | | all, by design (soundness) | |
| Rewrite rules | mined rules (`EXTRA_RULES`): each loop batch mines rules from its stragglers | `PROMOTED` (36 rules), some of the built-in `rules()` | the other built-in rules (shift distribution, `lt` falsity, cancellation) | |
| Which rule fires on a term | preferences (`winner  OVER  loser` lines in `rules.txt`), learned per family on a pooled library (`driver::sweep`); a loop's mines can learn them too (`RULEMINER_PREFS=1`, off by default) | | first match; built-ins before mined rules; mined rules most specific first | order alone moved M by up to 15; specific first beats general first by ~60; preferences learned on a fixed pooled library: serving M 106 to 89 (salt 1), 142 to 137 (salt 2); learned in each loop mine: M down 0-2, mines ~2x slower; learned on the pooled library: pooled loops 67 to 60 and 165 to 129 (tier-cycle.md, "Rule order", "Preferences and rival orientations") |
| Rule orientation | the winner's rival right sides, rescored on its laws (always on) | | `rule_weight` / `rule_order_ok`; the smallest right side is the first candidate; permutative rules ordered on `show()` text | swapping one `sub` chain rule's orientation took an add3 batch from 46 to 27; scoring every orientation was mixed (tier-cycle.md, "Why add3 did better"); rivals: add3 own loops 30 to 14 and 33 to 22; with pooled preferences pooled loops 87 to 60 and 114 to 129; cold salt 1 447 to 472; all loops 1302 to 1289 ("Preferences and rival orientations") |
| Rewrite strategy | | | children first; the steps tried at a node and their order (`rule_step`, `tree_step`, collapse, operand sort by text); built-in `add` steps (constant-carry chains, assoc, comm, with hand-proved lemmas); cycle cut; 200-step budget | outermost first: 106 to 310 ("Rule order"); ablated, pooled library 106: comm 880, assoc 373, tree 318, built-in rules 257, promoted 234, collapse 185; the `x + 0`, `x + ~x` and constant-folding steps were redundant and are deleted; `chain` alone changes nothing but covers for the deleted `x + 0` step (106 to 123 without both) ("Ablating the fixed rewriter and prover parts") |
| Prover after rewriting (`prove_eq`) | | | a fixed cascade: truth table over atoms, per-position prover, `shr_mask_eq`, then the whole-term machine (counted in M); `CARRY_CAP` = 10 | ablated: only the truth table matters on the three-variable families (106 to 110; 828 to 832 with no library); the per-position prover and `shr_mask_eq` are needed for `shr1` laws (unit tests); congruences and generalization changed nothing and are deleted ("Ablating the fixed rewriter and prover parts") |
| Miner | | | candidate shapes (pool terms up to 5 nodes; cross-side pairs); at most 400 candidates; gain = 1000 per fixed law + guard weight + size cut; greedy, one rule per round; stops when nothing gains | the 8-round cap dropped general rules that transfer (removed); a general rule the gain values at 0 cost add3 108 vs 65 when seeded from cmp3d's library (tier-cycle.md) |
| Loop and driver | | | batch size, strides, phases, per-family mine settings (`MINES`), the law pools; pooling concatenates libraries | pooling's hand-picked list of dropped orientations replaced by learned preferences (above) |
| Conjecture proposers | the n-gram proposer, trained on law text | | mutation, pool and stream proposers; the difficulty band | |

## Moving parts to learned: candidates
Ranked by measured effect; each needs the same check as the rules: mine on phase 0, score on phases 1-3, both salts.
1. Operand order (`comm`, sorting by text): the most load-bearing fixed choice (ablated: 106 to 880); the mined rules assume it.
2. Rule orientation's open losses: salt 1's cold loops (447 to 472) and salt 2's pooled add3 (33 to 43) with rivals.
3. Miner gain weights (or a gain that credits transfer).
