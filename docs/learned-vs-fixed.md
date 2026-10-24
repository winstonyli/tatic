# Learned vs fixed

Which parts of the reasoning pipeline (rewriter, prover, miner, loop) are learned from data and which are fixed by hand. The goal
(docs/tier-cycle.md) is a kernel that improves itself, so parts move from the right columns to the left over time.

**Keep this current.** Update the row when a part becomes learned, when an experiment measures a fixed part (put the number and a
pointer in "Evidence"), and when a part is added or removed. Experiments' details stay in docs/tier-cycle.md; this page holds the
verdicts. Last updated 2026-10-23.

Columns: *learned in the run*: changes from data while the loop runs. *Learned once*: came from data, then frozen in code.
*Fixed*: written by hand, possibly tuned by experiments (tuning is not learning).

| Part | Learned in the run | Learned once | Fixed | Evidence (M is total over families; lower is better) |
|---|---|---|---|---|
| Trusted checker (`src/kernel.rs`) | | | all, by design (soundness) | |
| Rewrite rules | mined rules (`set_extra_rules`): each loop batch mines rules from its stragglers | `PROMOTED` (35 rules), some of the built-in `rules()` | the other built-in rules (shift distribution, `lt` falsity, cancellation) | one sweep iteration: best loops 157 to 142 (pooled 58/99 to 57/85, own 55/90); a second adds nothing (tier-cycle.md, "Promotion as an iterated sweep"); iterated from `ABLATE=promoted` the sweep does not recover PROMOTED (pooled 125/160 to 107/140 after three iterations, against 58/99 with it), so it stays; on the streams gate `ABLATE=promoted` raises M on salts 1-2, 176 to 180 and 181 to 192 (tier-cycle.md, "Ablations of the class table"); PROMOTED re-mined by its documented procedure reproduces HEAD's rows ("Operand order") |
| Which rule fires on a term | none now: learned preferences were deleted with the families' preference phase and pooled library (2026-10-23; tier-cycle.md, "Preferences deleted") | | first match; built-ins before mined rules; mined rules most specific first | order alone moved M by up to 15; specific first beats general first by ~60; preferences learned on a fixed pooled library: serving M 106 to 89 (salt 1), 142 to 137 (salt 2); learned in each loop mine: M down 0-2, mines ~2x slower; learned on the pooled library: pooled loops 67 to 60 and 165 to 129 (tier-cycle.md, "Rule order", "Preferences and rival orientations") |
| Rule orientation | the winner's rival right sides, rescored on its laws (always on); a swap holds only if the mine finished that way is worth more | | `rule_weight` / `rule_order_ok`; the smallest right side is the first candidate; permutative rules ordered on `show()` text | swapping one `sub` chain rule's orientation took an add3 batch from 46 to 27; scoring every orientation was mixed (tier-cycle.md, "Why add3 did better"); rivals: add3 own loops 30 to 14 and 33 to 22; with pooled preferences pooled loops 87 to 60 and 114 to 129; cold salt 1 447 to 472, 451 with the lookahead; all loops 1302 to 1266 ("Preferences and rival orientations", "Lookahead on rival swaps") |
| Rewrite strategy | | | children first; the steps tried at a node and their order (`rule_step`, collapse, operand sort by text); built-in `add` steps (assoc, comm, with hand-proved lemmas); cycle cut; 200-step budget | outermost first: 106 to 310 ("Rule order"); ablated, pooled library 106: comm 880, assoc 373, tree 318, built-in rules 257, promoted 234, collapse 185; the `x + 0`, `x + ~x` and constant-folding steps were redundant and are deleted; `chain` alone changes nothing but covers for the deleted `x + 0` step (106 to 123 without both) ("Ablating the fixed rewriter and prover parts"); with the class table, `ABLATE=assoc` still raises M on the streams gate on all 10 salts, 1718 to 1836, and `ABLATE=comm` on 9 of 10, 1718 to 1784 (held-out 8721 to 9000); `tree` (318 without the table) and `chain` change nothing, so their steps are deleted ("Ablations of the class table") |
| Prover after rewriting (`prove_eq`) | | | a fixed cascade: truth table over atoms, per-position prover, `shr_mask_eq`, the bounded join (`join_eq`: the rules in force both ways plus add, and, or, xor associativity and commutativity; terms up to the larger side plus 2 nodes; 1000 reached terms; also on `lt` roots), then the whole-term machine (counted in M); `CARRY_CAP` = 10 | ablated: only the truth table matters on the three-variable families (106 to 110; 828 to 832 with no library); the per-position prover and `shr_mask_eq` are needed for `shr1` laws (unit tests); congruences and generalization changed nothing and are deleted ("Ablating the fixed rewriter and prover parts"); the join, salts 1-10: own M 865 to 13, pooled 757 to 33, cold 4380 to 1568, ref mines 160 to 2, sweep wall +76%; cap 5000 gains a few laws at 2-3x the time ("The bounded join removes the floor") |
| Miner | | | candidate shapes (pool terms up to 5 nodes; cross-side pairs); at most 400 candidates; gain = 1000 per fixed law + guard weight + size cut; greedy, one rule per round; stops when nothing gains | held-out scoring (min of the gains on two halves of the stragglers) changed nothing (tier-cycle.md); the 8-round cap dropped general rules that transfer (removed); a general rule the gain values at 0 cost add3 108 vs 65 when seeded from cmp3d's library (tier-cycle.md) |
| Loop and driver | | | batch size, `STREAM_STRIDE` and the phases, the streams' operator sets | drop units (deleted with the families, 2026-10-23) were: pooling's hand-picked list of dropped orientations replaced by learned preferences (above); drop units: pooled loops 60 to 58 (salt 1), 129 to 99 (salt 2); root-overlap units 60/103; whole-library drops were net zero (tier-cycle.md, "Drop units", "Joinability units") |
| Law source (conjecture proposers) | | the seeds: the class table's representatives, per operator set | the streams (`stream_sequence`): the 56 operator sets, the growth levels and budget, the open-law filter | the hand-written family pools (add3, sbo3, cmp3d, mix3, u3) and the n-gram and mutation proposers were deleted (spec §10, 2026-10-23) |

## Moving parts to learned: candidates
Ranked by measured effect; each needs the same check as the rules: mine on phase 0, score on phases 1-3, both salts.
1. Operand order (`comm`, sorting by text): the most load-bearing fixed choice (ablated: 106 to 880); the mined rules assume it.
   Re-mined under the reversed and size-first orders, the `show()` order wins 13 of 16 pairwise sweep comparisons (own loops
   74/102 against 132/147 and 98/117). Without the promoted rules size first wins 7 of 8 cells, but with them re-learned
   under each order by one procedure `show()` wins 7 of 8 again (own 74/102 against 106/129), so that reversal came from the
   missing rules. Without the built-in comm the miner does not recover it (cold 451/450 to 799/798). Parked: no better global
   order; only sbo3 does better under size first, so what is left is a per-family order learned with that family's promoted
   rules (tier-cycle.md, "Operand order").
2. The miner's greedy search: a larger one-round gain can lead to a worse finished set (salt 1's cold loss with rivals: 38 of 43
   stragglers covered against 42; tier-cycle.md, "The cold loss is a greedy path loss"). Held-out scoring did not help, since
   the loss is not overfitting; finishing the mine both ways at rival swaps fixed that loss. Extending the lookahead to each
   round's runner-up lost (all loops 1266 to 1348; tier-cycle.md, "Lookahead over runners-up too"); choosing among them by
   held-out finished value (2-fold over the stragglers) removes that loss but gains nothing (1234 both ways) at 3.5-4.5x the
   cmp3d mine time ("Runners-up chosen held out"). Dropping the mine's own
   rules afterwards found nothing: none of 642 candidates gains in-sample (tier-cycle.md, "Drops of the mine's own rules").
3. Pooling's drop units (deleted with the families and the pooled library, 2026-10-23; the record stays): where two libraries' normal forms meet (B's rules with a critical pair against A's that does not
   join), learned per family as preference-phase moves; pooled loops 60/129 to 58/99, every salt-2 family at or below its own
   library (tier-cycle.md, "Drop units", "Joinability units"). A drop needs a hand-set gain floor (2000) against one-law
   overfit; held-out gain in its place lost (salt 2 103 to 106). On three salts harmful drops gain 1000-1033 and helpful ones
   3215+, so the floor separates two classes rather than being tuned (salt 3 pooled 74 with it, 80 without; salts 4-5 never
   reach it; "The floor is still needed").
4. The normal form itself: a table of class representatives learned by enumeration (the smallest term of each class of
   equal values, Ruler-style) instead of the rewrite strategy and rules. Wired in as `prove_eq`'s phase 1 (below). Up to size 9 with `lt`
   as a second sort, it makes 189-200 of 200 of each family's held-out laws meet with no rules, and every one of its 3203
   replacements is proved and kernel-checked (tier-cycle.md, "A learned table of representatives: the probe", "The table
   with `lt` as a second sort, its proofs, and smaller keys"). A key of 316 inputs refined by counterexamples does the
   same at 1.5 s per build ("A key refined by counterexamples"). How it enters the rewriter: the spec
   `docs/superpowers/specs/2026-10-22-class-table-normal-form-design.md`. As phase 1 in `prove_eq`
   (`tests/church_bv/classes.rs`) it cuts M 38% (377 to 233 over salts 1-5) at 19% more job CPU (tier-cycle.md, "The
   class table in `prove_eq`: phase 1"). As phase 2, a step in the rewriter, it takes M on the old gate from 233 to 0 at
   a seventeenth of the job CPU, leaving the miner nothing to learn there (tier-cycle.md, "Phase 2 in the rewriter").
