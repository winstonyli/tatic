---
status: "superseded-by: docs/superpowers/specs/2026-10-05-loop-summary.md"
---

# Research state: the rule-proposer line (2026-10-04)

A fresh-session summary of sections 76-88 of `2026-10-02-search-execution-blend-design-part2.md` (cited as §n). The notes are the source of truth; numbers here are copied from them. Part 1 (`2026-10-01-search-execution-blend-design.md`) §0 is the wider current-state table.

## Setting

A law `t1 = t2` over `Term` (add, and, or, xor, sub, lt, shl1, shr1) is proved by the rewriter (built-in, `PROMOTED`, `RULESET`, mined rules), then bitwise provers, `shr_mask_eq`, and last a whole-term machine proof. A **straggler** is a law that still needs the machine. The **rule miner** proposes rewrite rules (each proved and kernel-checked) and scores them by machine proofs removed ("covered" = fewer machine proofs, so a partly fixed law counts). Goal: with lemmas ablated, search finds the missing ones. The kernel is untouched; everything is in `tests/church_bv/`.

## Proposers (deep add3: 64 stragglers, §80-83)

| Proposer | Covers | Note |
|---|---|---|
| `mined` (greedy over equal pairs of a pool) | 51 | the workhorse; mix3: 152 of 174 (§83c) |
| `goal` (abstract subterms of normal forms, smaller equal term) | 27 | §69-70 |
| `midpoint` (bidirectional search for a shared middle term, halves as rules) | 6 alone; 6 of the 16 left after `mined` | paths exist for 12 of 13 (§83a); halves mostly too specific; 9 of 34 on mix3 |
| rule LM (Burn transformer, `tools/rulelm`) | 8 | ceiling set by its training distribution (§79-81) |
| `file`, `transfer`, `random` | not summarized here | §66-67 (`random`, `transfer`, `file`), §77 (transfer between pools) |

Best measured pipeline: `mined`, then `midpoint`, then `goal`. `midpoint` is not general: 0, 0, 1 on shl, lt, shr (§84).

## Rule sets

- Looping sets (§84): `add3_mm` 12 rules, 139 of 150 laws machine-free; `mix3_mm` 7 rules, 1475 of 1500.
- Loop-free `RULEMINER_NOLOOP=1` (§86-87): `add3_nl` 15 rules, 133 of 150; `mix3_nl` 10 rules, 1437 of 1500; left after all three stages: 5 (add3), 63 (mix3).
- `mined` alone with the loop guard: 43 of 64, against 51 without (§86): the loops bought 8 laws through budget-dependent normal forms. Which to prefer depends on whether unique normal forms matter.
- All sets prove and kernel-check at n = 4..64 (§84, §87); 128 was checked for the built-in rules only (§82).

## Why leftovers remain, by family

- **add3 / mix3:** critical pairs and loops. The commutation straggler is a loop between the permutative `add(sub(x,y),z) -> add(sub(z,y),x)` and `sub(add(x,y),z) -> add(sub(x,z),y)`, not a missing rule (§83c, §85). `PERM_ORDER=tie` removes this loop but drops `add3_mm` from 139 to 124 machine-free; not proved terminating (§87).
- **lt:** carry-out comparisons (`lt(add(x,y), x)`), decided by carries, not equalities; expect machine proofs unless hand-written overflow lemmas are added (§85). 17 of 28 left after `mined`.
- **shr:** constant folding took 43 to 24 (§86); root-`shr1` rules provable (§87); `shrnot` plus a `prove_eq` branch took built-in stragglers 24 to 20 (§88). `mined` covers 8, leaving 12: arithmetic laws equal modulo bit 0, which the machine proves and no mined rule removes. Same confluence problem as above.
- **mul:** closed (2 stragglers, both covered). **shl:** 5, none covered.

## Scaling (§82, built-in rules, 40 laws per family)

All proved and kernel-checked at n = 4, 8, 16, 32, 64 (and 128 for 20 laws). Check time grows about 2.5x per doubling for mul and lt, about 2x for shl and shr; machine-proof counts are constant in n. n=128 needed `low_bits(n)` in place of `(1u128 << n) - 1`.

## Not done

- Model proposer beyond the LM pilot; its target is families that hand rules plus 1-3 mined rules already close (§75).
- Laws uniform in the width (goal D): blocked by the missing induction principle for Church encodings (§53-57).
- Search alongside execution (part 1 §6, question 4): unbuilt.
- A termination order covering permutative and regrouping rules; critical-pair completion (§85 options a-c).
- §88's effect on shl, add3 and the other families was not re-measured (it can only reduce stragglers).

## Reproducing

Scripts and raw logs: `scripts/experiments/README.md` (`shrnot.sh`, `pipe.sh`, `noloop.sh`, `mid.sh`, ...). Env switches: `RULEMINER_*` (parsed once in `MinerConfig::from_env`), `ABLATE`, `RULESET`, `PERM_ORDER`. After the refactors of 2026-10-03, deep add3 `mined` re-measured at 51 of 64; `midpoint` 6 and `goal` 27 were measured before them. Long runs: BelowNormal, at most 12 threads; log CPU load and Defender RTP with every timing.

## Update (sections 89-90a)

- `PERM_ORDER=lpo` (a lexicographic path order on weight-tied rules, opt-in): add3 pipeline 125 of 150 machine-free (default loop-free 133, looping 139), mix3 1407 of 1500 (1437, 1475). Equal normal forms on the law sets are no higher than under the default order, so it is not adopted (§89).
- shr leftovers: the add3 rule sets already cut shr machine proofs from 20 stragglers to 10; hand-written bit-0 rules add one law, because the arguments are normalized before they could match (§90).
- Correction to §90: the shr bit-0 laws are reachable by three rules stated over normal forms (`scripts/data/shr_bit0_nf.txt`): 896 of 900 shr laws machine-free under `add3_mm` plus those rules (890 without); 4 plain-sum laws remain (§90a).

## End-to-end loop, first stream (section 91)

Driver and spec: `2026-10-04-end-to-end-loop-design.md` (Results). On deep add3 offset 0 (two batches), total machine proofs M: none 87, loop with the mined proposer 82, ref (mined once on the whole stream, with hindsight) 26, loop with rulelm candidates 87. The loop gains 5 of the 13 proofs available on its second batch; the first batch (64 proofs) is paid in full by construction. The rulelm candidates applied to none of the stragglers. Stride 5 (two batches): none 112, loop-mined 98, ref 29, loop-file 112. Stride 3 (three batches): none 194, loop-mined 125, ref 54, loop-file 194. The loop recovers 38%, 44% and 69% of ref's gain on the later batches (stride 7, 5, 3; upper bounds, because ref is fit on the batches it is scored on; raising its cap to 16 rules changed it by at most 1 proof); the rulelm candidates added nothing on any stream. Details and the criteria check are in the loop spec. Follow-up (A cumulative window, D carried candidates, ADM model added to mined; 12 runs): only A at stride 3 helped, loop-mined 125 to 113 (share of ref16 gain on later batches 68% to 80%); on strides 5 and 7 the configs cannot differ from loop-mined by construction (only mine 0 affects a scored batch), and D and ADM showed no benefit where they could act. One stream, so tentative; the selection rule is untested. Longer stream (stride 2, five batches): none 287, loop-mined 237, A 237, ref16 78; the loop recovers 27% of ref16's later-batch gain and A adds nothing, so the stride-3 gain of A did not generalize. The identity-candidate filter (`RULEMINER_NOIDENT`) changed nothing at stride 3. A generality penalty on the selection (`RULEMINER_GENERAL`, w=100/250) put the general reassociation rules first but left stride 3 at 125; at stride 2, w=100 gave 228 against 237 and w=250 gave 270 (worse), so it is no clear lever.

**Where the loop line stands (2026-10-05).** The loop recovers 27-68% of ref's gain on later batches and ends well above ref (stride 2: 237 against 78; stride 3: 125 against 53). Tried, none a reliable lever: rulelm candidates (applied to nothing), a carried candidate pool, an identity-candidate filter, a cumulative mining window (one gain, at stride 3: 125 to 113; none at stride 2), a generality penalty on selection (stride 2: 228 at w=100, 270 at w=250; none at stride 3). ref reaches its totals because 9 general rules are fitted on all batches at once, while the loop mines each batch on a handful of stragglers and first picks narrow rules; the gap looks evidence-limited. Untested: scoring candidates against laws outside the mining window (b2), rules that only work in combination (b3), larger B. The loop-stream branch is local and unmerged.
 Larger batches (stride 2): the share of ref16's later-batch gain is 27% at B=150, 48% at B=300 and 39% at B=450 (one later batch), but total M stays 237/237/262 because the first batch is paid in full; evidence per mine helps, cold start dominates the total (see the loop spec).
 Warm start from a held-out later slice (stride 2): static 196 against none 199, loop 181 against cold 188; batch 0 unchanged at 47, so rules mined on later laws do not carry to early laws (the slice lacks the xor/-1 shapes); a random split was not tried.
 Warm start from an interleaved split (stride 2 phase 1 mined, phase 0 served, 450 laws): 8 rules mined once on 450 neighbouring laws serve the stream at 50 proofs (none 199, cold loop 188, ref16 54), the loop adds nothing; mined on only 150 neighbours it fixes batch 0 (18) but not later regions (99, 63). Rules transfer to neighbouring laws and not across regions; the interleaved split leaks neighbours, so 50 is an upper bound (a structure-based split was not run).
 Warm start from a structure-based split (halves by erased-variable shape, 450 laws served): 7 rules mined once on 450 laws of the other half give 64 proofs static and 43 with the loop on top, against none 209 and cold loop 95; 150 laws of the other half do not help (213 static, 118 loop). Transfer across shapes is real when the sample is large enough.
 Warm sample-size sweep (structure-based split): 250 laws of the other half behave like 150 (static 213, loop 118, no help); 350 give 71 static / 49 loop (450: 64/43). The threshold lies between 250 and 350 laws and coincides with the miner finding the four general reassociation rules; the smaller samples yield only narrow rules.
 Loop line synthesis: see 2026-10-05-loop-summary.md.
 300-law warm sample gives the same 5 rules and M (71 static, 49 loop) as 350: threshold between 250 and 300 laws.
 Second shape key (salt a): warm threshold moves (200 laws no help, 250 halves M 211 to 111, 450 gives 94); cold loop gets nothing (213 vs 211). See loop spec.
 Loop on a warm start, salt a: no gain at 250 (111 = 111), worse at 450 (108 vs 94 static); on the original split it helped (64 to 43). The loop's value on a warm start is split-dependent.
 WL450 batch-2 regression traced (ablation): one loop-added rule with the same left side as a warm rule (add(sub(x,y),z)) takes batch 2 from 4 to 18; the miner dedups per mine, not against rules already in force.
 RULEMINER_NODUPLHS=1 (no candidate with a left side already in force) restores salt-a warm-450 loop to 94 (= static) and changes none of four other loop configs; the loop still adds nothing on that split.
 Cross-shape selection (RULEMINER_XSHAPE w=1,3): stride 3 125 (unchanged), stride 2 236 (237 before); no lever.
 (RULEMINER_XSHAPE code reverted, not published; the experiment script and logs stay local.)
 Second family mix3 (stride 1, 600 laws, B=150 K=4): none 62, ref 65 (worse than none), loop 40 (batch 3: 0). The loop beats ref there; ref is not an upper bound. Cause of ref's regression found: the miner scores stragglers only, so a rule that fixes 12 stragglers but regresses >=20 of the other laws (add(xor(x,-1),y) rule: 62 none, 44 with rule 1 alone, 65 with both) looks like a gain. No regression guard on non-stragglers.
 Regression guard (RULEMINER_GUARD, unpublished): mix3 ref with all 538 machine-free laws scored picks only rule 1 and serves at 44 (was 65, none 62); a 108-law sample does not help (65). Loop 40 unchanged with the sampled guard; full-guard loop not run.
 Inverse-weighted guard sample (108 of 538, weight 4981 each) gives ref 44 (= full guard) in half the scoring time; loop stays 40. Sample stability untested.
 Regression guard on add3 stride 3 (full guard): ref 51 (53 before), loop 125 (unchanged, identical batches). The add3 conclusions are not an artefact of the straggler-only scoring; stride 2 not rerun.
 Loop summary (2026-10-05-loop-summary.md) updated 2026-10-07 with mix3 and the regression guard.
 mix3 structure split (warm9): stream has 13 proofs in all, no headroom; warm samples 5-10, loop 11; not informative about the add3 warm-start findings. A harder mix3 stream is needed.
 mix3 split on a harder stream (offset 600 half 0, none 136): cold loop 116, warm 450 114, warm 150/300 136 (no gain), loop on warm adds nothing; batch 0 never improves. The warm-start threshold finding is add3-only on this evidence.
 mix3 rule sets: the cold loop mines the same general reassociation rules as add3's four from the served batches; warm samples from the other half find only narrow rules or one variant. The mechanism looks shared; the warm sample is redundant when the served batches carry the evidence.
seed11: mix3 offset600 half0 served with add3's 4 general rules, static: M 9/6/14=29 (none 136, cold loop 116, WS450 114)
