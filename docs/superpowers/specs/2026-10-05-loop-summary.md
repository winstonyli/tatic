---
status: done
---

# The end-to-end loop: what we learned (2026-10-05, updated 2026-10-07)

Synthesis of `2026-10-04-end-to-end-loop-design.md` (details, tables, caveats per experiment). Main family: deep add3 laws (a second family, mix3, near the end); metric M = machine proofs needed to serve a law stream; batch r is served under rules mined from batches 0..r-1 only. `ref` = rules mined on the whole stream in hindsight (ref16: round cap 16, which changes ref by at most 1 proof).

## Question
With lemmas ablated, can rule proposal run together with execution and shrink the machine proofs execution needs?

## Answer in one paragraph
Partly. A batch-by-batch loop does cut M (stride 3: 194 to 125; stride 2: 287 to 237), but it ends far above `ref` (53 and 78) and recovers only 27-68% of ref's gain on the later batches (less on longer streams). Batch 0 is paid in full by construction. The shortfall is **evidence coverage**, not candidate supply, window width or selection: a held-out sample of laws with different shapes, mined once, closes most of the gap once it is large enough (about 350 laws here).

**Two later findings change how to read the numbers** (details below and in the design doc): the miner scores only stragglers, so it cannot see a rule that breaks already machine-free laws (`RULEMINER_GUARD` adds that check), and on a second family (mix3) the loop beat the hindsight `ref` because `ref` picked a regressing rule.

## Results by lever (total M; baselines in the design doc)
| lever | result |
|---|---|
| model proposer (`rulelm` ck_B) alone | no gain; its candidates applied to no stragglers or changed nothing |
| model added to mined (ADM) | no gain beyond A; its samples matched no straggler |
| carried candidate pool (D) | none |
| identity-candidate filter | none (identity candidates harmless) |
| cumulative window (A) | one gain (stride 3: 125 to 113), none at stride 2 (237 = 237): stream-specific |
| generality penalty | stride 3 unchanged (125); stride 2 w=100 228, w=250 270 (vs 237): not a lever |
| cross-shape selection (XSHAPE w=1,3) | stride 3 125, stride 2 236 (vs 125, 237): none |
| competing rules for one left side (`NODUPLHS`) | restores one warm-start loop run (salt a, 450 laws: 108 to 94); changes none of four others |
| larger batches (stride 2) | total 237 / 237 / 262 at B=150/300/450; later-batch share 27% / 48% / 39%: cold start dominates |

## Warm start (served laws 0..450, B=150, K=3)
| warm source | static | loop | note |
|---|---|---|---|
| none (stride 2) | 199 | 188 | baseline |
| later slice (stride 2) | 196 | 181 | no transfer |
| interleaved neighbours, 450 laws | 50 | 50 | leaky upper bound |
| structure split, none | 209 | 95 | stride 1, half 0 |
| 150 / 250 laws of the other half | 213 | 118 | no help, loop worse than cold |
| 300 and 350 laws | 71 | 49 | 5 rules, identical |
| 450 laws | 64 | 43 | 7 rules |

The threshold lies between 250 and 300 laws (300 and 350 give identical rules and M) and coincides with the miner finding four general reassociation rules (`sub(add(x,y),z)`, `add(sub(x,y),z)`, `sub(x,sub(y,z))`, `add(x,sub(y,z))`). Smaller samples yield only narrow rules (`shl1`, `xor(x,-1)`). The rule-set link is observed, not tested.

## Second family: mix3 and the regression guard (stride 1, 600 laws, B=150, K=4)
| config | M | rules | note |
|---|---|---|---|
| none | 62 | 0 | |
| ref (mined on all 600 laws) | 65 | 2 | worse than none |
| ref with the full regression guard | 44 | 1 | the bad rule is rejected |
| loop-mined | 40 | 7 | batch 3 needs no machine proofs |

- `ref` picked `add(xor(x,-1),y) -> add(-1,sub(y,x))`, reported as +12 fixed stragglers, which regresses about 33 machine-free laws (checked by serving the stream under each rule alone: rule 1 alone 44, rule 2 alone 68, both 65). The miner never scores laws that already needed no machine proof, so this was invisible.
- `RULEMINER_GUARD=<k>` scores k of those laws too, each weighted by the inverse sampling fraction. Unweighted, a 108-law sample did not catch the rule; weighted or on all laws it did (44 both ways, the weighted one at half the scoring time).
- On add3 (stride 3) the full guard changes little: ref 53 to 51, loop 125 to 125 (identical batches). The add3 results do not rest on the blind spot; mix3's loop result is unchanged by the guard too (40).
- A structure-based split of mix3: the first stream had 13 proofs in all (no headroom); on a harder one (136 proofs) no warm sample improved batch 0, 150 and 300 laws gave no gain, 450 laws gave 114 against a cold loop's 116, and the loop on a warm start added nothing. So the warm-start threshold finding is add3-specific on this evidence (one extra family, one stream).
- One stream per family and the unguarded default miner still has the blind spot (the option is off by default).

## What this supports
- The loop's gain comes from evidence per mine and shape coverage; cheap levers on the same evidence do nothing.
- Where shapes arrive in runs, a sufficiently large representative sample mined up front beats a pure cold loop, and the loop on top still helps (43 vs 64).

## Limits
- One family, one served stream per experiment, my own shape key for the split. A second key (salt `a`) moved the threshold (200 laws no help, 250 laws halve M; cold loop gets nothing there, and a loop on top of the warm start adds nothing at 250 laws and hurts at 450: 108 against 94 static), so the warm-sample size needed is split-dependent, not a law count.
- Most "none" results are single runs on deterministic mined configs, so there is no noise estimate; only A at stride 3 and the w=100 stride-2 result moved at all, each once.
- ref's rules were fit partly on the batches they are scored on, so shares are not clean out-of-sample figures; on mix3 `ref` is not even an upper bound (see above).
- Untested: other selection rules (a cross-shape score changed nothing), scoring against evidence beyond the mining window, two-process (concurrent) mode, retraining the model on accepted rules, the warm-start and split experiments on mix3, add3 stride 2 with the guard.

## Reproduce
`scripts/loop_stream.sh none|ref|loop OUTDIR` (public repo; env opt-ins in its header); experiment scripts, logs and READMEs under `scripts/experiments/` (local only). Release exe: see the design doc's results sections.

## Shared mechanism, tested (2026-10-07)
Serving the mix3 offset-600 half-0 stream (B=150, K=3, guard 120) with only add3's four general reassociation rules in force (`warm5_WS300` rules 1-4, static, no mining): M = 9 / 6 / 14 = **29**, against 136 with no rules, 116 cold loop, 114 for the best mix3-mined warm start (450 laws). Batch 0 drops 78 to 9, which no mix3-mined warm sample achieved. So the reassociation rules are shared across families, and the mix3 miner did not find them in its warm samples (it did find three of the four in its cold loop). Script: `scripts/experiments/seed11_run.sh`, log `logs/seed11_S.tsv`. One stream, one pair of families; the rules were chosen after seeing them in add3 results, not blind.

## Reverse transfer and new defaults (2026-10-07)
- Defaults: `RULEMINER_GUARD` now 120 and `RULEMINER_NODUPLHS` on (0 turns either off). Checked: mix3 stride 1 with no env overrides gives ref 44 and loop 40, identical to the explicit-guard runs (`mixdef_run.sh`).
- add3 stride 3 (150 x 3 laws; none 194 on the four-batch stream, cold loop 125) served with rules mined on mix3 (`warm10_C`, six rules): static 32/29/40 = **101**; loop starting from them 32/22/28 = **82** (14 rules at the end). Only the three `xor(x,-1)` rules (the non-reassociation ones): 189, no effect. So the transfer is carried by the reassociation rules, in both directions; the family-specific `xor(x,-1)` rules neither help nor hurt the other family.
- Caveats: one stream per family; the mix3 rules came from an offset-600 stream, the add3 stream is offset 0; the 194 baseline is from a K=4 run, add3 K=3 totals for none were not rerun here (batch 0 under no rules is 64, as the cold loop's batch 0). Scripts `seed12_run.sh`, `seed13_run.sh`.
- A miner "starting from another family's rules" needs no code: `WARM_RULES=<file>` (loop) or `RULEMINER_BASE` (miner) already does it.

## Clean add3 baselines under the new defaults, and the shared rule file (2026-10-07)
add3 stride 3, B=150, K=3, guard 120 + NODUPLHS on: none 194, ref 51 (9 rules; mining 4673 s, so ~9 min per round with the guard on), loop 125 (64/21/40). All identical to the pre-default numbers, so the earlier add3 results stand. `scripts/rules/reassoc.txt` (four rules, committed) served statically as `WARM_RULES`: add3 **93** (26/22/45), mix3 offset-600 **29** (9/6/14). On add3 that is better than the cold loop (125) and worse than ref (51). Process note: I edited `scripts/loop_stream.sh` while the ref run was executing it; it broke at the next line (syntax error). The ref mine had completed, so I served under its `rules.txt` instead (same stream, same exe); the loop run started after the revert and is clean. No third family exists in the harness (only shl/shr/add3/mix3; shl/shr have no add/sub, so reassociation cannot apply).

Loop seeded with `scripts/rules/reassoc.txt` on add3 stride 3 (K=3): 26/22/28 = **76** (11 rules at the end), vs static reassoc 93, cold loop 125, mix3-seeded loop 82, ref 51. Batch 1 is the same 22 as cold loop's 21; the gain over static is batch 2 (45 to 28).

## Seeded loops, and a third family (2026-10-07)
- mix3 offset 600 (K=3): loop seeded with `reassoc.txt` 29 (static 29): mining on top neither helps nor hurts there.
- add3 stride 3, K=4: none 200, cold loop 127, seeded loop 77. The stream has only 475 laws, so the fourth batch has 25 laws: this is not a longer stream (a longer one needs stride 2 or less).
- **Third family `sbo3`** (new: add, sub, and, or, depth 2, both operand orders, plus sums/differences of two depth-1 terms; 2655 laws; stride 4, B=150, K=4): none 181, `reassoc.txt` static **72**, cold loop 126 (22 rules), seeded loop **60** (17 rules). Same pattern as add3 and mix3: the four reassociation rules carry most of the gain, and seeding the loop beats the cold loop. The four rules were chosen on add3, so sbo3 is out of sample for them; sbo3 is built from the same ops as add3 minus xor, so it is a related family, not an independent one. No ref run (about 1.5 h at guard 120). Script `sbo3_run.sh`.

## What the loop adds beyond the four rules (2026-10-07, read from rule files by eye, not tested)
Compared the final rule sets of add3 cold loop / ref (base14), mix3-seeded add3 loop (seed13_L6), sbo3 cold (C) and seeded (L) loops. Rules that recur in at least three of those five besides the four in `reassoc.txt`:
- `sub(sub(x,y),z) -> sub(sub(x,z),y)` (add3 ref, seed13, sbo3 C and L): the strongest fifth candidate.
- `sub(xor(x,-1),y) -> sub(-1,add(x,y))` (add3 loop, seed13, sbo3 C and L).
- `sub(sub(x,y),xor(z,-1)) -> add(sub(x,y),sub(z,-1))` (add3 loop and ref, sbo3 C; a variant in seed13).
- `add(sub(x,y),xor(z,-1)) -> add(sub(x,z),xor(y,-1))` (add3 ref, sbo3 C and L).
- `add(sub(sub(x,y),y),z)` rewrites in several right-hand forms (add3 loop, seed13, sbo3 C and L): the same left side gets a different right side per run, so it is a pattern, not one rule.
Family-specific: `sub(x,and(x,y))`, `add(sub(and(x,y),x),z)` and similar (sbo3 only); `shl1` rules (add3/mix3 only). Untested: whether adding the fifth rule to `reassoc.txt` helps on all three streams (cheap: three static serves).

## sbo3 ref (2026-10-07)
ref (14 rules, mined on all 600 laws, guard 120): M = **31** (none 181). Share of ref's gain (181-31 = 150): seeded loop 60 = 81%, static `reassoc.txt` 72 = 73%, cold loop 126 = 37%. (add3 stride 3 for comparison: seeded loop 76 of 194/51 = 83%, cold 125 = 48%.) Whole-stream shares, ref fit partly on the batches it is scored on. Script `sbo3ref_run.sh`.

## Five-rule library, static (2026-10-07)
`reassoc.txt` + `sub(sub(x,y),z) -> sub(sub(x,z),y)`: add3 93 to **78**, mix3 29 to **26**, sbo3 72 to **66** (none 194 / 136 / 181; ref 51 / - / 31). Better on all three, by 6-15 proofs. The fifth rule was picked by looking at the same runs it is now scored on (add3 ref and sbo3 loops contained it), so this is not out of sample. `reassoc.txt` itself is unchanged (README numbers refer to the four rules); the five-rule file is `%TEMP%/reassoc5.txt`. Script `reassoc5_run.sh`.

## Fifth rule, other streams (2026-10-07)
Static serves, none / 4 rules / 5 rules: mix3 offset 0 stride 1 K=4: 62 / 19 / 19; add3 stride 2 K=5: 287 / 143 / 118; sbo3 stride 5 K=3: 135 / 40 / 35. Never worse, better on two of three. Not fully held out: add3 stride 2 shares every 6th law with stride 3, sbo3 stride 5 every 20th with stride 4; the mix3 stream is a different stream whose mined rules never contained the fifth rule. `scripts/rules/reassoc.txt` is now the five-rule file (README numbers for loops refer to the first four rules; stated in the README). Script `oos5_run.sh`.

## Seeded loops with the five-rule file (2026-10-07)
add3 stride 3 K=3: **71** (4-rule loop 76; 13 rules at the end); mix3 offset 600 K=3: **26** (29; 8 rules); sbo3 stride 4 K=4: **55** (60; 17 rules). Shares of ref's gain: add3 (194-71)/(194-51) = 86%, sbo3 (181-55)/(181-31) = 84%. README headline updated to these. Script `seed16_run.sh`.

## mix3 ref and a sixth rule (2026-10-07)
- mix3 offset 600 (SPLIT=0, K=3), ref (7 rules): M = **6** (none 136). Seeded loop 26 is 85% of the gain ((136-26)/(136-6)); static five-rule 26 as well.
- Sixth rule `sub(xor(x,-1),y) -> sub(-1,add(x,y))` on top of `reassoc.txt`, static, five-rule number in brackets: add3 s3 **64** (78), mix3 600 **22** (26), sbo3 s4 **61** (66), mix3 0 **19** (19), add3 s2 **100** (118), sbo3 s5 **32** (35). Never worse, better on five of six. Same caveat as the fifth rule: picked from the same runs (add3 loop, seed13, sbo3 C and L) and the streams overlap partly; the mix3 offset-0 stream is the only one it never appeared in, and it is unchanged. `reassoc.txt` still has five rules; the six-rule file is `%TEMP%/reassoc6.txt`. Script `six_run.sh`.

## Sixth rule on disjoint streams (2026-10-07)
Streams from phase 1 of the stride sequence (disjoint from the phase-0 streams the rule was picked on; new `SPHASE` in `loop_stream.sh`, `RULEMINER_PHASE` now also honoured by mix3/sbo3): add3 stride 3 phase 1 K=3: none 182, 5 rules 77, 6 rules **63**; sbo3 stride 4 phase 1 K=4: none 180, 5 rules 68, 6 rules **65**. `reassoc.txt` is now the six-rule file. Seeded loops with six rules not rerun. Script `oos6_run.sh`.

## Six-rule seeded loops and the seventh rule (2026-10-07)
Seeded loops with the six-rule file: add3 s3 K=3 **62** (five-rule loop 71; 13 rules), mix3 600 K=3 **22** (26), sbo3 s4 K=4 **56** (55; 17 rules). Shares of ref: add3 92%, mix3 88% ((136-22)/(136-6)), sbo3 83%.
Seventh rule on top of six, static (six-rule baselines in brackets: add3 s3 64, sbo3 s4 61, add3 p1 63, sbo3 p1 65, mix3 600 22): (a) `sub(sub(x,y),xor(z,-1)) -> add(sub(x,y),sub(z,-1))`: 63, 61, 62, 64, 22; (b) `add(sub(x,y),xor(z,-1)) -> add(sub(x,z),xor(y,-1))`: 64, 61, 63, 65, 22. At most 1 proof, so the library saturates at six on these streams. Script `lib7_run.sh`.

## Spread over stream samples, and other families (2026-10-08)
Six disjoint samples (phases 0..5 of the stride-6 sequence), static serves; the library is fixed, so this measures how much M varies with the sample, not run-to-run noise (the pipeline is deterministic).
- add3 (B=79, K=3; none / 4 rules / 6 rules, phases 0..5): none 109 103 92 91 86 94 (mean 96); 4 rules 51 53 46 44 46 51 (48.5); 6 rules 32 34 35 34 33 33 (33.5, range 32-35).
- sbo3 (B=110, K=4): none 126 139 134 141 134 122 (133); 4 rules 58 65 57 61 59 54 (59); 6 rules 52 59 51 53 53 48 (52.7).
- Six rules beat four on every sample (add3 by 15-19, sbo3 by 6-8), so the library's effect is much larger than the sample-to-sample spread (about 5-8 proofs for none, 1-4 for six rules). Differences of 1-2 proofs between configs on a single stream remain within that spread.
- Other families (K=1, B=250): shl none 5 / six rules 5; shr 0 / 0; lt 28 / 28. The library neither helps nor hurts where add/sub is not the structure (these families need few machine proofs anyway). Script `noise_run.sh`.

## Loop spread over four samples (2026-10-08)
Phases 0..3 of the stride-6 sequence; loops now mine the residue class they serve (`SPHASE`). add3 (B=79, K=3): none 109 103 92 91; static six rules 32 34 35 34; cold loop 73 72 60 65; seeded loop **31 33 34 33**. sbo3 (B=110, K=4): none 126 139 134 141; static six 52 59 51 53; cold loop 93 103 112 109; seeded loop **46 55 49 48**. Seeded beats cold on every sample (add3 by 27-42, sbo3 by 47-63) and the gap is far larger than the sample spread. Mining on top of the seeded start gains 1 proof on add3 (31-34 vs 32-35) and 3-6 on sbo3 over the static six rules, so the library carries most of it. Script `loopspread_run.sh`.

## Fourth family cmp3: where the library stops (2026-10-08)
`cmp3` = `lt` of two small add/sub/shl1 terms over three variables (308 laws; stride 1, B=100, K=3). First attempt (lt nested under add/sub) failed in the kernel check with a type mismatch: the encoding types an `lt` result differently from a word, so `lt` can only be the outermost operator; the pool was redefined accordingly. Results (M): none 21 (13/8/0), static six rules **21** (no effect), cold loop 19, seeded loop 19, ref **3** (3 rules: `lt(add(x,y),sub(x,z)) -> lt(add(x,y),add(y,z))`, `lt(add(x,y),sub(y,z)) -> lt(add(x,y),add(x,z))`, `lt(sub(x,y),sub(x,z)) -> lt(sub(x,y),sub(z,y))`). The cold loop mines the same three rules after batch 0 (13 proofs paid, then 8 and 0 on the rest, 19 total versus ref's 3), so here the library does nothing and the gain of ref over the loop is pure batch-0 cost. The seeded-loop advantage is therefore specific to families where reassociation of add/sub is the bottleneck. Small stream (21 proofs of headroom), single run. Script `cmp3_run.sh`.

## Libraries compose on a mixed family (2026-10-08)
- `lt` family (2 variables, K=1, B=250): none 28; the three cmp3 `lt` rules 28; six reassoc + lt3 28. Neither library transfers to `lt` (it needs few machine proofs; only 28).
- New family `cmp3d` (lt of an arithmetic term and an arithmetic term that can contain a reassociation redex; 6194 laws; stride 15, B=100, K=4, ~413 laws; cmp3's laws are a subset of cmp3d's and the lt3 rules were mined on cmp3, so not independent): static none 130, six reassoc rules 74, lt3 rules 124, six + lt3 69; ref (8 rules) **39**; cold loop 78 (20 rules); loop seeded with six + lt3 **54** (28 rules). Share of ref's gain (130-39 = 91): cold loop 57%, seeded loop 84%, static six+lt3 67%. So the two libraries are close to additive on a family with both structures (reassoc alone does most; lt3 adds 5), and the seeded loop again beats the cold one. Script `cmpx_run.sh`.

## cmp3d on a disjoint stream (SPHASE=1, stride 15, B=100, K=4; 2026-10-08)
Script `scripts/experiments/cmpx2_run.sh`. M: none 134, six 89, six+cmp 84, cold loop 93, loop seeded with six+cmp 73, ref 46.
Share of ref's gain: seeded 69% (phase 0: 84%), cold 47%, static six+cmp 57%. The comparison rules cut 5 proofs on top of the six, the same as on phase 0 (74 to 69), so the effect replicates on a stream they were not mined near. Seeded beats cold by 20 (phase 0: 24). Single runs; ref 46 vs 39 on phase 0 shows stream-to-stream spread of a few proofs.

## cmp3d phase 2 and mul (2026-10-08; scripts/experiments/lib8_run.sh, lib8b_run.sh)
cmp3d SPHASE=2 (stride 15, B=100, K=4): none 148, six+cmp 88, cold loop 87, seeded loop 65, ref 40. Share of ref's gain: seeded 77%, cold 56%, static 56%. With phases 0 and 1, seeded is 69-84% on three disjoint streams, cold 47-56%; seeded beats cold by 20-24 on all three.
mul (stride 3, K=3, static): none 6, six+cmp 6 (no effect; baseline too low to show one).
lib8_run.sh was killed after p2_c when the session ended; p2_l and p2_r were rerun by lib8b_run.sh (THREADS=2, affinity 0x5000, BelowNormal). Single runs.

## Miner speed: lazy greedy rejected (2026-10-08)
Profile of one ref mine (cmp3d phase 2, 2 threads): laws 66 s, provable filter 93 s, 8 greedy rounds 561-1370 s each (about 97%); each round re-scores every candidate over all laws.
Tried lazy greedy (previous round's gain as an upper bound, stop when the best fresh gain beats all bounds). NEGATIVE: on cmp3d B=40 K=1 ROUNDS=4 (`scripts/experiments/lazy_ab.sh`) it scored 17, 4, 2, 2 of 17 candidates and ran in 57 s vs 81 s, but chose a different second rule (sub(add(x,y),z) -> ... in place of lt(0, sub(sub(x,y),z)) -> ...) and ended at M=6 vs 5. Gains are not decreasing: a rule can become useful only after another rule is in force (the reason the greedy is cumulative), so stale bounds are unsound. Reverted. Exact options left: skip laws a candidate cannot touch (needs a rewrite trace), early abort inside scoring (weak: size term has no cheap bound).

## Miner profile (2026-10-08; samply via a sidecar `<exe>.env`, f2fb283)
60 s cmp3d B=40 mine, debug-info release build. 57% of samples are hash-consing (`hc::intern`, hashbrown, thread-local `Table`); 72% inclusive is `machine::add_tree_law` (proof-term building under `rewrite_law`), kernel nf/whnf only ~7%; the rewriter proper ~2% self; `Term::interp` 7.7% (main thread, `family_laws` setup); allocation ~12%.
`RULEMINER_FAST=1` (existing flag: scoring counts a machine fallback without building its proof) cut CPU time 35% on that mine (39-43 s vs 62-65 s, BelowNormal, pinned) with identical chosen rules (4/4 on two repeats; the same on `lazy_ab.sh`). Caveat: `add_tree_law(...)?` can return None, which FAST skips, so a law whose machine proof fails would count differently; not seen so far. Not yet checked on a full-size mine (cmp3d B=100, 8 rounds; full-run rules in `%TEMP%\lib8_p2_r\rules.txt`).
Warm intern tables across rounds: rejected by measurement. The kernel's hash-cons table is thread-local over `Rc` (a shared table would need `Arc` throughout), and worker tables start cold each round, but `RULEMINER_TRACE` shows the cold cost is the first candidate per thread only: 0.9-1.3 s vs about 0.4 s median, i.e. 0.5-0.8 s per thread per round. At B=100 (186 candidates, rounds of 600-1400 s) that is under 0.2%.

## RULEMINER_FAST=1 at full size (cmp3d phase 2 ref, B=100 K=4, 8 rounds, 2 threads; run 2026-10-08)
Mine time: rounds 3-152 s (first 152 s, rest 3-40 s) vs 561-1370 s for the full-proof run; whole ref run 642 s vs about 6500 s in the mine alone (about 10x). NOT exact: the first five chosen rules agree, rules 6-8 differ (FAST: lt(add(-1,x),add(sub(x,y),z)) -> ..., lt(add(-1,x),add(x,y)) -> ..., plus one common; full: three other lt rules), covered 113 vs 114 of 148 stragglers, M=41 vs 40. Cause not yet traced: the full path's `add_tree_law(..)?` can return None (law unproved, not counted fixed), which FAST never does. (An earlier attempt at this check read the wrong configuration because the `<exe>.env` sidecar overrode the shell env; the loader now only sets unset variables, 6e5d7e6.)

## Making FAST exact: rejected (2026-10-08)
The full path's only extra failure is the encoding search: after `moore_encoding` decides (in `add_tree_law`, up to the `let m = enc.phi...` line) the function always returns Some, so an exact FAST = run that decision, skip the proof terms. Tried splitting it out (`tree_law_encoding`) and calling it from the FAST branch of `prove_eq`: exact by construction, but round times on cmp3d B=100 were 633, 900, 464 s vs 1059, 1011, 755 s full-proof (about 35% saved), against 3-152 s for the inexact FAST. A memo of the decision keyed on (a, b, n, k), shared across threads and rounds, did nothing (711 s, 715 s for rounds 1 and 2): the term pairs differ per candidate. So the 10x of inexact FAST comes from not running the encoding search at all, which is exactly what makes it diverge (rules 6-8, M 41 vs 40). Reverted; `RULEMINER_FAST=1` stays opt-in and approximate.

## RULEMINER_FAST in the loop (2026-10-08)
cmp3d, B=100 K=4 ROUNDS=8, THREADS=2, FAST=1 vs full proofs: total M identical in all six runs
(cold phases 0/1/2: 78/93/87; seeded: 54/73/65). The single-mining-pass divergence (rule 6 onward, M 41 vs 40)
does not show up in loop M at this size. FAST is fine for exploratory loop runs; confirm headline numbers without it.
Single runs, no noise estimate. Logs: scripts/experiments/logs/warm10_summary.txt (fastloop rows).

## Noise check, FAST loops, phases 3/4/5 (2026-10-09)
Cold / seeded M: ph3 74/43, ph4 80/61, ph5 84/67. Gaps (cold - seeded): 31, 19, 17.
Over all six phases (0-5) the gap is 24, 20, 22, 31, 19, 17: mean 22.2, sd about 4.9; seeded beats cold in 6/6.
Cold M ranges 74-93, so compare only within a phase. Script: scripts/experiments/fastnoise_run.sh.

## Where the seeded gap lives, and cmp.txt on the other families (2026-10-09)
Per-batch M (cmp3d, FAST, K=4; cold / seeded): ph0 44 18 10 6 / 24 13 11 6; ph1 52 25 9 7 / 33 26 6 8; ph2 54 16 9 8 / 36 13 9 7;
ph3 49 12 7 6 / 20 10 7 6; ph4 48 18 8 6 / 31 17 8 5; ph5 51 19 9 5 / 38 16 8 5. Almost the whole gap (13-29) is batch 0, the batch served before
the cold loop has mined anything; by batch 1 it is 0-5 and by batches 2-3 it is within 1-3 either way. So the library is a head start,
not a lasting advantage: a longer stream would not widen the gap (cold converges to the seeded rate after about two batches).
Static serves, phase 1 streams (none / reassoc / cmp only / reassoc+cmp): add3 s3 K=3 182/63/182/63; sbo3 s4 K=4 180/65/180/65; mix3 600 K=3 136/22/136/22.
The lt rules never fire outside cmp3d and never hurt there, so adding them to the library is free. Script: scripts/experiments/xlib_run.sh.

## sh3 probe: a shift/bit-trick family has no headroom (2026-10-09)
Tried a new three-variable family `sh3` (and/or/xor/add plus shl1/shr1, depth 2; pool in a reverted edit of search.rs) to test whether the
head-start effect holds for a library mined on a genuinely new structure. Served with no rules (FAMILY=sh3 STRIDE=1): 114 laws, M = 0, i.e. the
kernel's built-in rewriting proves every law and the machine is never needed, so there is nothing to mine (same as the earlier finding for shl/shr/lt).
Families that need the machine all involve add/sub/lt/mul arithmetic: add3, mix3, sbo3, cmp3(d), mul. mul was the only independent op set
(little headroom, M=6 either way). Reverted; the shape-halves partition test passed for it (203 s). Build log: a release build in its own target dir took 21 min.

## Pare/generalization pass (2026-10-09)
Done (commits 120af04, 65acf76): pool3/THREE_VAR_FAMILIES table; removed random/transfer/file/goal/midpoint proposers and the BUNDLE, NOLOOP, GENERAL, STRICT,
TRACE, NOIDENT, SIZE, MIDPOINT, PROPOSALS knobs, mint_corpus, tools/rulelm, scripts/data/rulelm and the candidate scripts, orphan rule files.
Ref mine cmp3d B=40 ROUNDS=4: identical rules before/after (M=5, 4 rules; a thin check). scripts/experiments/matrix.sh is the generic driver (local).
Considered and NOT done: unify the two law-selection schemes. STRIDE/PHASE (index mod stride == phase) and SHAPE (hash of the variable-erased skeleton mod 2 == half;
SHAPE_SALT picks another hash) are both "residue class of a key"; SKIP/LAWS is a window over the selected sequence. One knob `PART=key:mod:res` would cover both and give
N-way structural folds, but SHAPE is used only by SPLIT runs (mix3 offset 600, in the README numbers) and no experiment needs a third fold, so the change would buy nothing
and risk the reproducibility of those numbers. Revisit if a held-out structural fold beyond two is wanted.

## Where the kernel's time goes: rule-covered vs machine-proved laws (2026-10-09)
Test `search::proof_cost_split` (ignored; CHECK_FAMILY, CHECK_RULES, RULEMINER_STRIDE/LAWS as for rule_set_kernel_check), width 4, release, shared machine (2 cores).
"rules" = laws proved with no whole-term machine proof; "machine" = laws that needed one. build = rewrite_law time, check = kernel::check time.
cmp3d, six+lt rules, stride 15, 400 laws: rules n=331 build 6.7 s check 17.5 s (2.13M nodes); machine n=69 build 61.4 s check 47.7 s (1.28M nodes); the 9 rules' own proofs 0.4+0.8 s.
sbo3, six rules, stride 4, 600 laws: rules n=539 build 14.0 s check 61.4 s (2.97M nodes); machine n=61 build 32.0 s check 37.9 s (0.84M nodes); 6 rule proofs 0.3+0.7 s.
Per law: cmp3d rules 20 ms build + 53 ms check vs machine 889 + 691 ms; sbo3 rules 26 + 114 ms vs machine 525 + 621 ms.
Upper bound on what a conversion rule could remove (the rules class's whole time): cmp3d 24 of 134 s (18%), sbo3 75 of 146 s (51%); less in practice since conversion still normalises, and the class includes laws solved by built-in rules without the library.
Rule proofs are about 1 s once: admission is cheap next to the streams. Machine laws are 17% / 10% of laws but 82% / 49% of the time on cmp3d / sbo3.

## What the remaining machine laws on cmp3d have in common (2026-10-09)
Stragglers of the seeded phase-0 loop (parefast_l0 mine logs; six+lt rules in force; 27/16/14 stragglers in rounds 0/1/2, 20 of 24 in round 0 covered by the rules the
miner then chose). Normalised forms in round 0, 24 stragglers: 9 are `lt(0,A) = lt(0,B)` with B = -A (nonzero-ness is negation-invariant: `lt(0,x)=lt(0,sub(0,x))`,
`lt(0,sub(x,z))=lt(0,sub(z,x))`, `lt(0,add(sub(y,x),z))=lt(0,sub(sub(x,y),z))`); 9 are `lt(add(-1,x), .)` laws (x-1 < t, i.e. <= forms, with operand swaps); 6 mix shl1.
Test of the obvious generalisation: add `lt(0, x) -> lt(0, sub(0, x))` to the library (static, cmp3d phases 0/1/2): M 69/84/88 -> 96/106/112, worse on all three (+27, +22, +24).
Reason (not isolated): the rule is unoriented (the rhs is larger), fires on every `lt(0, .)` and hides the redexes other rules need. So the negation family is not expressible
as an oriented rewrite; it needs a canonical-form choice between A and -A (an ordering on terms, as in AC/permutative rewriting), which the rule language only partly has.
Pointer for self-improving mining: rules that choose a representative of an orbit under a symmetry (negation, operand swap) rather than a direction.

### Correction to the section above (2026-10-09)
The "needs a representative-choosing rule" conclusion was too strong. The miner's own loop rules (fastloop_l0/rules.txt) already contain the correctly oriented form,
`lt(0, sub(0, x)) -> lt(0, x)` (rhs smaller; x matches any term, so it is the whole negation family at the top of an lt). My failed test used the reverse direction, which is
unoriented. Static serves with the oriented rule added to the library (lib8_all + rule), cmp3d phases 0/1/2: M 69/84/88 -> 66/83/85 (never worse, 1-3 better). The negation
stragglers also need arithmetic normalisation of `-A` to a canonical form (e.g. `sub(0, sub(x,z)) -> sub(z,x)` style rules), so the full cluster is not removed by this rule alone.
Offset-by-one cluster (`lt(add(-1,x), t)`): no compact general rule exists in the lt/add/sub vocabulary, since x-1 < y  <=>  x != 0 and x <= y (checked by hand on the boundary x=0,
x>0), a conjunction; lt results cannot be combined (lt is never nested), so the miner emits many specific rules instead. Pointer: new defined symbols (le, a nonzero test) would
let a short rule set cover this cluster; adding definitions to the language is the library-learning step, not a new rewrite rule.
Pointer on ordered rewriting: rule_step already has permutative rules (tied weights, instance must go down in the show() or tie/LPO order), so operand-swap symmetries are expressible.

## Defined comparison symbols: scoped, not built (2026-10-09)
`nz(x)` = `lt(0,x)` is already expressible and mined (cmp3_pool has Zero as a leaf; rewrite.rs PROMOTED has `lt(xor(x,-1),-1) -> lt(0,x)`), so a nonzero test needs only display notation.
`le(x,y)` = not lt(y,x): le-vs-le laws are exactly the existing lt-vs-lt laws with arguments swapped, so a le family adds no new rules; only mixed laws `le(a,b) = lt(c,d)`
(complement laws) are new. A real op 8 costs about 6-10 h (OPS/ops_for/interp/parse plumbing, le_u in encoding.rs, four lt special cases in machine.rs, rewrite_law mixed roots, new root rules
leself/lezero/lemax with kernel proofs, soundness re-sweeps). lt returns a one-bit vector (bv_ty(1)), not a Bool0; there is no Bool negation at Term level and lt is root-only.
Caveat found while writing this up: the offset cluster (x-1 < y  <=>  x != 0 and x <= y) is a conjunction of two comparisons, so `le` alone would not give it a short rule; it needs
Boolean combinations of comparison results (and/or/not over lt roots), which the harness forbids (lt never nested, different result width). That, not a new symbol, is the gap.

## Falsification spike: Boolean combinations of comparisons (2026-10-09)
Passed. `lt(add(-1,x),y) = and(lt(0,x), xor(lt(y,x),-1))` is proved by `add_tree_law` and kernel-checked at n=4 (54 ms) after ~120 lines in rewrite.rs (width-aware eval/interp) and machine.rs (`Fin` post function over lt final carries; four final-carry sites). Existing machine tests unaffected. Patch: `docs/superpowers/specs/2026-10-09-boolean-comparisons-spike.patch`; details in the spec. Remaining cost is rule-side (congruence/rule proofs, pools, canonical forms), not the machine.

## Unification pass 2 (2026-10-09, uncommitted at time of writing)
From a survey of per-case code (ranked list kept in this session; unexecuted items: `rewrite` finish-closure for the LT/shift/non-ADD branches ~35 lines, test-driver helpers ~100, lpo-only rule order ~50 and behaviour-changing, `prove_rule` shrnot fall-through).
Done: (3) `OP_INFO` table in rewrite.rs (name, carries, bitwise, shift, prec) replaces `OPS`, `head_prec`, and the op predicates in `has_shift`, `add_free`, `Machine::carries`; (5) `env_or` replaces eleven env closures and bare reads (the injectable `env` parameter of `family_laws`/`pool3` stays: three tests pin knobs through it), and `perm_order()` caches `PERM_ORDER` (was read on every `rule_step`); (1) `depth2_pool`/`depth1`/`leaves3`/`mk` build sbo3, mix3, cmp3 and add3 (pool fingerprints identical before/after for all 5 families).
Checks: 53 tests pass; FAST loop cmp3d B=60 K=4 old exe vs new exe: identical per-batch M, total_M 87, identical rules.txt (18 rules).

Unification pass 2b (2026-10-09, committed locally): (2) `rewrite` has one `rule_step` branch for every non-ADD op (result type from `o == LT`); (4) `parse_rules` replaces 7 rule-file parsers, `check_laws` the shared setup of `rule_set_kernel_check`/`proof_cost_split`. The conjecture_miner/soundness_sweep drivers were left alone (near-duplicates, not identical). Check: 53 tests; cmp3d 300-law check and cost split give identical counts, node and occurrence totals before/after (proof terms unchanged).

## #6 spike: lpo-only rule order (2026-10-09) — NEGATIVE, not adopted
`PERM_ORDER=lpo` already exists (tied rules admitted, oriented per instance by `lpo_greater`), so no code change was needed: FAST loops, B=60 K=4 STRIDE=7, exe at 22f67f9, default vs lpo, total_M (rules): cmp3d phase 0 87 (18) vs 99 (17); phase 1 86 (19) vs 101 (17); phase 2 89 (20) vs 99 (17); add3 phase 0 60 (16) vs 80 (20). lpo is worse by 10-20 M everywhere (single runs, but the sign is consistent across 4/4). Keep the three orders; do not delete `tie_greater`/`rule_permutative`. Open question (not pursued): why lpo costs M (it admits tied rules the default orients by `show()`/`tie_greater`, so the miner may pick different, less general rules).

#6 follow-up (cmp3d phase 0, FAST, cold loop, default vs lpo, rules diffed): per-batch M 34/17/15/21 vs 34/26/16/23. The default run mines the three general sub-reassociation rules (`sub(add(x,y),z) -> add(sub(x,z),y)`, `sub(sub(x,y),z) -> sub(x,add(y,z))`, `sub(x,sub(y,z)) -> add(sub(x,y),z)`) plus two `lt(0, ...)` ones; the lpo run mines none of the three and instead six narrow lt rules. By hand (not run): with prec add 6 > sub 5, `lpo_greater(sub(sub(a,b),c), sub(a,add(b,c)))` is false (the right side is add-headed), so that orientation never fires under lpo, whereas `tie_greater` orients it by operand size. Hypothesis: lpo flips the orientation of reassociation rules relative to what the miner proposes, so they are not selected. Discriminating test (not run): WARM_RULES=reassoc.txt under lpo; if M stays high the rules are inert in that direction, if it drops the miner was the cause.

#6 warm-rules test (cmp3d phase 0, WARM_RULES=reassoc.txt, FAST): default total_M 66 (batch 0: 13) vs lpo 89 (batch 0: 27; cold lpo was 99/34). The reassoc rules are largely inert under lpo, consistent with the orientation hypothesis (they are loaded but lpo orients the sub-chain rules the other way). lpo stays rejected.
Soundness sweep after the rewrite/pool refactors (exe at 22f67f9, RULEMINER_LAWS=300): mul, lt, shl, shr pass (mul: 182 proofs kernel-checked at widths 3,4, 0 unproved, 0 false laws accepted). `soundness_sweep` panics on cmp3d/add3 (rewrite.rs:109, index 2 of len 2) because it hard-codes 2 variables in `family_laws`; pre-existing limitation, so the 3-variable families are covered by `rule_set_kernel_check` (cmp3d 300 laws: 300 checked, 0 unproved) instead.

`soundness_sweep` now takes the variable count from `family_vars` (was hard-coded 2); with RULEMINER_LAWS=200 STRIDE=7 it passes on cmp3d, add3, sbo3, mix3, cmp3 (no kernel rejection, no false law accepted).
#6 orientation test (cmp3d phase 0, FAST, PERM_ORDER=lpo, WARM_RULES): reassoc.txt as-is total_M 89 (batch 0: 27); the first five reassoc rules reversed (+ rule 6 as is) 77 (batch 0: 20); default order with reassoc.txt 66 (batch 0: 13). Orientation explains about half of the lpo gap (89 -> 77); the remaining 11 (77 vs 66) is not explained by rule direction (candidates: the miner's selection under lpo, the built-in ADD branch, tie-break `tie_greater` normal forms that other rules (cmp.txt) assume). Single runs. Mechanism (read in search.rs:801): candidates are `(pat, r)` with `ok_order(pat, r)`; under lpo any tied pair is admissible, scoring decides.

## Unification passes (2026-10-09/10): done and parked

Done (behaviour-neutral, 53 tests pass after each): `OP_INFO` table (name/carries/bitwise/shift/prec/truth/word), `env_or`/`perm_order`, shared pool builders, one `rule_step` branch in `rewrite`, `parse_rules`/`check_laws`, `bits_to_bv`, `binders(n, body)`, `Term::is_law`, `MachineBanner`, `prove_checked`/`Verdict` (lt, shl, mul miners). Commits 5701d97..f09f53e.

Not done, with why:
- `drive` over the remaining drivers (AUDIT, RULES, SWEEP, SCALE, PROBE3): they time/count/compare different things; a common helper would only add parameters.
- `args`/witness idiom helpers (rest of #2): not started; low value.
- #4 (atomize only vars/add/sub/lt, drop the separate shift collapse): PARKED. `abstract_atoms` already atomizes shl1/shr1, so simple shift-over-add cases already work; no law found that #4 would newly prove. A spike needs a corpus run with it on/off (M and proof sizes, ~20 min). Restart there if shifts-over-adds become a goal.
- #5 (delete hand-written x+0 / 0+x / x+~x arms, use `chain_step`): PARKED. Changes proof sizes; the templates double as checker diagnostics.
- #6 (`pos_law` for `bitwise_law_k`, drop `PosTerm`): PARKED. Proof-term/kernel-timing differences, ~25 lines.
- #7 (ADD assoc/comm into `rules()` as permutative rules): PARKED. Ordering within the branch chain and ablation names change; ~35 lines.
- Scripts item (#8: one `need` validator in `loop_stream.sh`): not started, ~10 lines.

## Held-out transfer metric (2026-10-10; computed from the logged figures above, no new runs)
Definition: T = M(seeded) / M(cold) on a stream the library was not mined from (the WARM mine uses a disjoint slice/phase). T < 1 means the library transfers; report T on batch 0 (the head start) and on the whole stream (K batches) separately, since the gap is concentrated in batch 0.
cmp3d, FAST, K=4, phases 0-5 (library = WARM mine on a held-out slice): total T = .69 .79 .75 .58 .76 .80, mean .728, sd .081; batch-0 T = .55 .64 .67 .41 .65 .75, mean .608, sd .117. Seeded beats cold in 6/6.
Cross-family, static serve with reassoc+cmp library vs none (phase 1): add3 .35, sbo3 .36, mix3 .16.
Caveats: the miner is deterministic, so the noise here is stream choice (phase), not seed; T depends on K (it tends to 1 for long streams, since cold converges after about two batches); the cross-family numbers are static serves, not loops. A transfer matrix (mine on family X, loop on family Y, across phases) is the unmeasured extension.

## CHECK_FAST: count-only serving (2026-10-10)
`CHECK_FAST=1` on `rule_set_kernel_check` (and `loop_stream.sh`'s serve step): machine fallbacks are counted without building their proofs (the miner's `SCORE_ONLY`), no kernel check, no NFSAME pass. A/B on the same exe, exact vs fast, identical CHECKED lines (so identical M): cmp3d phase 0, 200 laws, reassoc+cmp library: 157 free / 43 machine, 67 s vs 9 s; cmp3d phase 3, 100 laws from skip 100, empty library: 64 free, 42 s vs 10 s (includes process start and law setup). Two configs, one run each. Headline numbers still need one exact confirmation. Serving threads (not done): the remaining 9-10 s is mostly setup.

## Transfer matrix: plan (2026-10-10, not run; draft 3)
Question: how far does a rule library transfer across law families and held-out streams? Cell (L, Y, p) = static serve (CHECK_FAST=1) of library L on family Y, phase p, 300 laws; T = M(L)/M(none), M = laws - free. Probe: one cell takes 8-10 s (add3, mix3, sbo3, cmp3d alike), so no mining is needed for stage 1.
Stage 1 (about 15 min, no mining): L in {none, reassoc, cmp, reassoc+cmp (lib8_all.txt)}, Y in {add3 (stride 7), sbo3 (stride 4), cmp3d (stride 15), mix3 (stride 1, OFFSET steps of 300, SPLIT=0)}, 5 disjoint streams each: 4 x 4 x 5 = 80 serves. Report per family: mean and sd of T over streams, and the fraction of streams where T < 1.
Stage 2 (only if stage 1 is informative): own-family libraries mined by a FAST ref mine on stream 0 (B=100, K=4; cmp3d took 642 s, the others are unmeasured), served on streams 1-4 of every family; then the real loops (cold vs seeded) on a few cells to see how static T relates to loop T.
Review rounds: (1) Probe showed mix3 stream at skip 600 without SPLIT=0 has M=0 (300 of 300 free) with the empty library, so T = 0/0 there: cells with M(none) < 20 are excluded and counted, not averaged. (2) Phases are bounded by the stride (stride 3 gives 3 residue classes), so disjoint streams use distinct (SPHASE, SKIP) pairs and mix3 uses OFFSET; each cell's slice must not overlap the slice a library was mined on. Provenance of the existing libraries is only partly recorded (cmp3d rules from a cmp3d phase-0 stream; reassoc.txt mined on add3 and mix3, slices not recorded in this file): treat T on those two families as contaminated unless the streams are chosen disjoint from phase 0 and the original offsets. (3) Static T compares a fixed library with no rules at all, not with a cold loop that mines as it goes; the head-start result (loop converges after about two batches) means static T overstates a long-stream benefit. Stage 2's loop cells address this. Stage 1 therefore measures transfer of a fixed library, not self-improvement.
Expected cost: stage 1 about 15 min unattended at BelowNormal, 2 cores. Decision after stage 1: if T < 1 on most streams of at least two families outside the library's origin, stage 2; if T is about 1 away from origin, the libraries are family-specific and stage 2 is the cross-family question.

### Matrix plan: contamination settled (2026-10-10)
Provenance (git log + this file): reassoc.txt rules were picked on add3 (stride 3 and 2), mix3 (offset 600, stride 1; offset 0 for later checks) and sbo3 (stride 4 and 5) streams, phase 0; checks on "other streams" were partly not disjoint. cmp.txt: three rules mined on cmp3, the fourth found by loops on cmp3d phases 0-2.
Pool sizes (full static serve, CHECK_FAST=1, 14-69 s each): add3 1423 laws, mix3 2295, sbo3 2726, cmp3d 6725. The earlier add3 streams (stride 3 x 450, stride 2 x 750) cover most of add3's pool, and sbo3's (stride 4 x 600, stride 5 x 450) most of sbo3's: no law-disjoint stream exists there.
Rule for stage 1: a cell is CLEAN when the library's origin family differs from the served family (cmp.txt on add3/mix3/sbo3; reassoc on cmp3d), or the stream is law-disjoint from every slice used to pick the library: cmp3d phases 3+ of stride 15 for cmp.txt, mix3 offsets 1200/1500/1800 (stride 1, 300 laws, SPLIT=0; slices used so far end below 1200, the warm10_C mining slice is not recorded, so flag these). add3 and sbo3 with reassoc are IN-SAMPLE: report them, labelled, never average with the clean cells.

### Transfer matrix, stage 1 results (2026-10-10; scripts/experiments/transfer_matrix.sh, log logs/transfer_matrix_stage1.tsv)
Static fast serves, 76 cells (19 streams x none/reassoc/cmp/rc), T = M(lib)/M(none), cells with M(none) < 20 excluded (mix3 SPLIT=0 offset 300: M(none)=0; mix3 SPLIT=1 offset 300: 11). One run each (deterministic; spread is across streams).
CLEAN cells (library from another family, or law-disjoint stream):
- reassoc on cmp3d phases 3-7: T mean **.62** (sd .07, .53-.68, 5/5 below 1). A library mined on add3/mix3/sbo3 cuts cmp3d's M by 38% unseen.
- rc (reassoc+cmp) on cmp3d: **.56** (sd .07, .46-.63). cmp alone on cmp3d: **.93** (sd .03): the four lt rules are worth 6 points on top of reassoc's 38.
- cmp on add3 / sbo3 / mix3: T = 1.000 exactly in every cell (the lt rules never fire there; they do not hurt).
IN-SAMPLE cells (reassoc picked on those families; labelled, not averaged with the above): add3 **.34** (sd .02), sbo3 **.24** (sd .04), mix3 SPLIT=1 **.25** (n=2, sd .25; offsets 0/600: T .42 / .07).
Reading: reassoc transfers across families; the in-sample gain is 1.8-2.6x larger than the clean cmp3d gain, so some of the in-sample figure is selection. cmp3d needs its own rules for the rest (rc .56 vs reassoc .62 is small; the loop's remaining M is the comparison stragglers). Static T is a fixed library vs nothing, not vs a cold loop; stage 2 (loops, own-family libraries) is the self-improvement question. Mix3 has too few signal-bearing disjoint streams for more than a few cells.

### Transfer matrix, stage 2a: libraries the system mined itself (2026-10-10; scripts/experiments/transfer_mines.sh, logs/transfer_matrix_stage2_own.tsv)
FAST ref mine per family on its stream 0, 2 threads, 8 rounds: sbo3 (stride 11 ph 0, 200 laws) 524 s, 7 rules; add3 (stride 7 ph 0, 200) 795 s, 8 rules; mix3 (SPLIT=1 offset 0, 200) 280 s, 5 rules; cmp3d (stride 15 ph 0, 400) 1745 s, 8 rules. Then the stage-1 streams (all law-disjoint from stream 0 of the same stride; the one mix3 stream at offset 0 is excluded for own_mix3) served with each library, T = M(lib)/M(none):

| served \ library | own_sbo3 | own_add3 | own_mix3 | own_cmp3d |
|---|---|---|---|---|
| cmp3d (n=5) | .61 | .55 | 1.00 | **.36** (sd .09) |
| add3 (n=5) | .45 | **.30** | .94 | .28 |
| sbo3 (n=5) | **.26** | .35 | .93 | .40 |
| mix3 (n=2 usable) | .28 | .46 | - | .48 |

- The miner rediscovers the reassociation rules without being told: `sub(add(x,y),z) -> add(sub(x,z),y)`, `add(sub(x,y),z) -> add(sub(z,y),x)` and `sub(x,sub(y,z)) -> add(sub(x,y),z)` are in the sbo3, add3 and cmp3d libraries (the mix3 library has none). So reassoc.txt was not a lucky human pick.
- Own-family libraries are the best or near-best on held-out streams of their own family (diagonal .30, .26, .36), and the cmp3d library is better still on add3 (.28) and sbo3 (.40) than the other two non-diagonal ones: breadth of the training family helps.
- The self-mined cmp3d library on held-out cmp3d streams (.36) beats the hand-assembled reassoc+cmp (.56, stage 1) by 20 points; four of its eight rules are lt rules with a different shape from cmp.txt's.
- The mix3 library (shl1-heavy, 5 rules) transfers nowhere (.93-1.00): family-specific. Its own-family cell is untested (no disjoint signal-bearing mix3 stream).
Caveats: single deterministic mines; the mines were FAST (approximate); mix3 rows rest on n=2; diagonal cells are held out from the mine slice but the family pool is small (law overlap across strides is not controlled for add3 and sbo3 beyond the stream-0 slice itself). Still static T, not loops.

### Miner speed: thread scaling and law building (2026-10-10)
Thread scaling, mix3 FAST ref mine (SPLIT=1, 200 laws, 6 pinned cores, other sessions at 29-66% CPU): THREADS 2/4/6 = 140/154/143 s, identical rules. Inconclusive for scoring: mix3 has 18 candidates per round (about 6 s each), so the time is setup. A cmp3d probe (179 candidates/round) is still needed. Phase log: laws 29.4 s, candidate generation 4.9 s, provable filter 1.2 s.
`pool_conjectures`: hoisted the per-input `Vec` allocation and `sort_by_cached_key` (the sort called `show()` per comparison): laws phase 29.4 -> 14.2 s on the same mine, rules identical (md5 101d8d03), 54 tests pass. Not done: bottom-up subterm signatures with a memo, a threaded pool signature pass, a threaded provable filter (93 s on the cmp3d phase-2 mine).
Threaded provable filter (`rule_miner`: candidates proved on `RULEMINER_THREADS` workers, each copying this thread's base rules and step budget). cmp3d phase 0, B=100 K=1, ROUNDS=2, FAST, 2 vs 6 threads, other sessions at 39-56% CPU, identical rules (md5 d5f631e7) and 58 of 68 provable in all three: before (2 threads) total 139 s, provable filter 20.0 s, rounds 35.8/26.7 s; filter threaded, 2 threads: total 102 s, filter 12.5 s, rounds 27.7/24.4 s; 6 threads: total 70 s, filter 5.4 s, rounds 13.6/12.6 s. So scoring scales about 2x at 3x the threads on 58 candidates (the earlier 18-candidate probes could not show it); the laws phase varied 19-38 s between runs of the same code (load). Use THREADS=6 for stage 2b mines when CPU load allows.
`pool_conjectures` bottom-up subterm signatures (each distinct subterm evaluated once as a `Vec<u8>` over all inputs, parents combine children's vectors via `OP_INFO.word`; asserts n <= 8): mix3 FAST ref mine (THREADS=6) "laws and stragglers" 14.2 -> 8.7 s (single run, other sessions loading the CPU), rules identical (md5 101d8d03), 54 tests pass. Not done: threaded pool signature pass.
`SigMemo` (machine.rs) now backs both `pool_conjectures` and the miner's candidate pool index (`sig` closure in `rule_miner`): candidate generation 5.5 -> 0.3 s per mine, rules and M identical (cold cmp3d FAST loop, B=100 K=3, 6 threads: rules md5 02b96b98, M 32/9/33; 54 tests pass). New `phase("law building")` splits the old "laws and stragglers" (7.7 s) into law building 6.2 s + straggler rewrite loop 2.3 s. Consequences: the parallel straggler screen (<= ~1.5 s saving), the cross-side signature prefilter and hash-consing of `show()` keys are not worth doing (candidate generation is 0.3 s); the remaining setup is `family_laws` (6.2 s).
Law building was never slow: instrumented, `family_laws` takes 0.23 s (signature pass 0.2 s, sort 0.015 s). The "law building 6 s" phase was the `MachineBanner` (a `powershell` Get-MpComputerStatus + 2x2 s Get-Counter, about 5 s) that every mine and every serve printed at start and end. `MACHINE_BANNER=0` silences it; `loop_stream.sh` sets it and records one machine-state line at the loop's start and end (new ignored test `machine_state_line`). Cold cmp3d FAST loop (B=100 K=3, 6 threads): 101 -> 44 s wall, rules md5 02b96b98 and M 32/9/33 unchanged. Per mine now: law building 0.2 s, stragglers 1.7 s, candidates 0.2 s, filter 0.3 s, scoring rounds 2.5-3 s each. Scoring rounds now dominate. Other benches (not loop_stream) still print the banner, as intended.
Scoring reuse (`rule_miner`): `rule_step` can record every term it is asked to rewrite (`RULE_TRACE`); the miner records that trace per scored law under the rules chosen so far, and scores a candidate (tried last in the rule list) only on laws whose trace contains a term its left side matches, reusing the other laws' results. Exact by construction (a rule that matches nothing tried cannot change the rewriting or the step budget). Cold cmp3d FAST loop (B=100 K=3, 6 threads): 69% of law evaluations reused in mine 0, 46% in mine 1; rounds 2.5-3.0 -> 1.8-2.4 s; rules md5 02b96b98 and M 32/9/33 unchanged; 54 tests pass. Each round also re-scores the chosen set once with tracing (about one candidate's cost). Not done: a proof-free dry-run rewrite (rewrite_law builds kernel proof terms that scoring discards; profile before attempting).
Scoring profile (samply, single-thread cmp3d mine, 17.9 s, debug-info build; launcher `envrun.exe` in %TEMP%\sgprof sets the miner env because the Samply task passes none, samply follows the child): scoring 81%, `rewrite_law` 72%, `add_tree_law` 57% (via `tree_step` 45%, `k_var_law` 35%), and `hc::intern` (hash-consing while building the machine proofs) 65% inclusive, 54% self. So the cost was repeated machine-proof construction for the same subterm pairs, not the rewriting. `add_tree_law` is now memoized per thread by (n, k, t1, t2) (closed proofs, so mode-independent; None results too): rounds 1.8-2.4 -> 1.1-1.6 s, cold cmp3d FAST loop 46 -> 33 s, rules md5 02b96b98 and M 32/9/33 unchanged; a full kernel-checked serve (CHECK_FAST=0, 100 laws) gives the same CHECKED 100/67/0 and NFSAME 67 on old and new exes; 54 tests pass. Memo is unbounded per thread (fine at these sizes; revisit if a long loop's memory grows).
Re-profile after the `add_tree_law` memo (single-thread mine 17.9 -> 9.4 s): scoring 71% (`rewrite_law` 72% of samples), `hc::intern` still 57% inclusive (47% self: hash-table lookups while building proof terms that scoring discards), `add_tree_law` 29% (cold, first-time builds), `chain_step`/`find_constant_carry` 24%. Negative result: scoring workers without an `InternScope` (plain `Rc::new`, no hash-consing) are slower (rounds 1.8-3.1 s vs 1.1-1.6 s, same rules): sharing saves more than the table costs. Reverted. What is left is the volume of proof terms built per `rewrite_law`; only a proof-free dry-run rewrite (`rewrite`/`rule_step`/`prove_eq`/`tree_step` returning the target term without building Exprs) would remove it. That is a cross-cutting change to the proof-producing rewriter; est. 1-2 days and a second code path to keep in step, for at most ~2x on scoring (about 10 s of a 33 s loop). Parked.
`rewrite` hit-rate measurement (throwaway counters, reverted): cmp3d phase-0 mine, single thread, a seen-set of `t.show()` cleared per `score_laws` call (= one rule set): 5594 misses, 13908 top-level hits, 70952 node visits below hits. Uncached 90454 node visits, cached 19502: 78% of `rewrite` node visits are repeats of a term already rewritten under the same rule set (assumes the standard goods context; counts nodes, not time; `rewrite_law`'s own prove_eq/tree_step calls on the roots are not covered). A per-thread memo of `rewrite` keyed by (rule set, n, term) must replay its side effects on a hit: RULE_BUDGET steps used (do not cache budget-truncated results), MACHINE_FALLBACKS delta, RULE_TRACE terms, RULE_HITS.
`rewrite` memo (`RewriteMemo`, rewrite.rs; enabled by `score_laws` for one rule set per call, only for the standard goods count): cached by (width, `t.show()`); a hit replays the call's side effects (RULE_BUDGET steps, MACHINE_FALLBACKS delta, RULE_TRACE terms) and needs at least that many steps left; calls that ran the budget out are not cached. Exact: cold cmp3d FAST loop rules md5 02b96b98 and M 32/9/33, mix3 FAST ref mine (B=50 K=4 ROUNDS=8) rules md5 101d8d03, both identical to before; 54 tests pass. Scoring rounds 1.1-1.6 -> 0.5-0.8 s; cold cmp3d loop 33 -> 28 s (serves, stragglers and the per-mine setup are now most of it). RULE_HITS (audit counter) is not replayed.
Whole-loop breakdown (cold cmp3d FAST, 28 s): the two machine-state probes were about 12 s (6 s each: powershell + Defender query + 2x2 s CPU samples), mines 7 s, serves 4 s, rest 5 s. `MACHINE_STATE=0` now skips them in `loop_stream.sh`: 19 s, same rules (02b96b98) and M 74. Sweeps set it and record the state once themselves.

## Stage 2b: loops, cold vs seeded with the own-family library (2026-10-10)
`scripts/experiments/loop_pairs.sh` (local), log `scripts/experiments/logs/loop_pairs_stage2b.tsv`. FAST + CHECK_FAST, THREADS=6, ROUNDS=8, B=100 K=3, held-out phases (seed = stage 2a library mined on the family's phase-0 stream), one deterministic run per cell, machine RTP=False, CPU 17% at start / 16% at end. Total M over 3 batches:
| family | cold (5 streams) | seeded | seeded/cold per stream | pooled |
|---|---|---|---|---|
| cmp3d (phases 3-7) | 68 74 79 82 95 | 24 53 54 40 56 | .35 .72 .68 .49 .59 (median .59) | 227/398 = .57 |
| add3 (phases 1-5) | 71 70 67 67 66 | 26 23 23 29 26 | .37 .33 .34 .43 .39 (median .37) | 127/341 = .37 |
| sbo3 (phases 1-5) | 58 52 55 49 46 | 33 29 36 28 29 | .57 .56 .65 .57 .63 (median .57) | 155/260 = .60 |
Seeding helps every one of the 15 streams (ratio .33-.72). Per batch: the first batch carries the gain (cmp3d 48-51 -> 13-27, add3 45-50 -> 16-19, sbo3 21-24 -> 3-7); the cold loop catches up (cmp3d batch 3: cold 7-14, seeded 5-7; add3 batch 3 is 0 for both; sbo3 batch 3 is 17-19 for both, a stubborn 17 that neither the library nor in-loop mining fixes). Seeded runs end with more rules (cmp3d 16-22 vs 12-16, add3 16-19 vs 9-11, sbo3 14-17 vs 12-14). Loops took 100-190 s each (cmp3d), 40-50 s (add3, sbo3), about 40 min for the sweep.
Caveats: single runs; FAST mines are approximate (headline ratio not yet confirmed without FAST); the add3/sbo3 phase streams share the stride sequence with the seed's stream, so law overlap beyond disjoint phases is not ruled out; the library was mined on the same family (transfer across families is stage 1: static, and null off-family).
sbo3 "stubborn 17" investigated (stream 11-1, seeded rules, batch 3 = laws 200-248 of the phase, 48 laws, 17 needing a machine proof): not unfixable. Mining that batch with the seeded library as base covers 17 of 17 stragglers with 7 rules, the first of which, `sub(x, add(y, z)) -> sub(sub(x, y), z)`, fixes 9. Two causes: the loop never mines its last batch (it could not change that batch's M), and the conjecture sequence is sorted by `show()`, so batches are lexicographic ranges (batch 0 `add(...)`-led laws, batch 2 `sub(...)`-led): the later batches are a distribution shift, not exchangeable samples, for cold and seeded alike. Consequence for the metric: per-batch M mixes 'learned' with 'which structural class this batch holds'; a stream shuffled by a fixed hash would separate the two (parked).
Stage 2b exact check (`FAST=0 PHASES=1 ONLY="add3 sbo3"`, log `logs/loop_pairs_stage2b_exact.tsv`; exact mines and exact serves with kernel check and NFSAME; RTP=False, CPU 11% -> 31%): add3 7-1 cold 71 (50,21,0), seeded 26 (18,8,0); sbo3 11-1 cold 58 (24,17,17), seeded 33 (7,9,17); total M, per-batch M and rule counts identical to the FAST rows. Exact loops took 69-123 s vs 36-51 s FAST (2-3x, not 10x, now that scoring is cheap). Not confirmed exactly: cmp3d (where FAST once picked different rules on a ref mine: M 41 vs 40) and the remaining phases.

## RULEMINER_SHUFFLE (2026-10-10)
`RULEMINER_SHUFFLE=<salt>` (exported; 0 = off, default) reorders the three-variable families' sorted law sequence by an FNV-1a hash of `salt|law`, so batches and stride phases are random samples instead of lexicographic ranges (the distribution shift seen in the sbo3 "stubborn 17" investigation). Fixed per salt, differs between salts. Test `shuffle_is_a_fixed_permutation`; suite 55 passed. Sweep scripts take `TAG`/`LIBTAG`/`RUNTAG` to keep shuffled libraries and runs apart from the sorted ones. Shuffled results are a new condition: do not average them with the sorted ones. Not yet run: re-mine seeds on shuffled phase-0 streams, then ~3 streams/family x 2 salts, cold vs seeded.

### Shuffled streams, salt 1 (2026-10-10; FAST, B=100 K=3, single runs, seeds re-mined on the shuffled phase-0 stream)
Total M cold vs seeded (per-batch M in `scripts/experiments/logs/loop_shuf1.tsv`, local):
- cmp3d 15-1/2/3: 62/53/75 vs 27/27/26 (pooled .42; sorted was .57)
- add3 7-1/2/3: 69/62/52 vs 24/19/19 (pooled .34; sorted .37)
- sbo3 11-1/2/3: 42/45/39 vs 14/17/15 (pooled .37; sorted .60)
Seeding helped all 9 streams, and the seeded first batch no longer carries all the gain (batch 2-3 M is small in both modes). Cold per-batch M still falls (e.g. cmp3d 31,20,11), so the loop learns within a stream. sbo3 gained most from shuffling (.60 -> .37): the sorted result partly reflected lexicographic batch structure. Machine: RTP off, CPU 15% at start, 76% at end (load from another job near the end; M unaffected). Salt 2 not yet run.

### Shuffled streams, salt 2, and exact cmp3d (2026-10-10; single runs, RTP off, CPU 9-19%)
Salt 2 (seeds re-mined on its own shuffled phase-0 stream), total M cold vs seeded: cmp3d 62/49/71 vs 37/23/36 (pooled .53); add3 51/51/63 vs 18/16/17 (.31); sbo3 38/36/43 vs 17/14/16 (.40). Seeding helped all 9 streams again. Two salts: cmp3d .42/.53, add3 .34/.31, sbo3 .37/.40, so the ratio is stable to about +-.06 across salts for add3/sbo3 and +-.06 for cmp3d.
Exact (FAST=0) cmp3d, sorted streams 15-3 and 15-4: cold 68, 74; seeded 24, 53; per-batch M 49,12,7 / 48,18,8 cold and 13,4,7 / 23,22,8 seeded. Cold and seeded M equal the FAST values (68/74, 24/53), so FAST mining did not change cmp3d totals here. Exact loops took 202-383 s (1.5-3x FAST).

### Cross-family transfer, shuffled salt 1, phases 1-3 (2026-10-10; FAST, single runs)
Seed = another family's shuffled-phase-0 library. Total M summed over 3 streams (cold / own library / foreign): cmp3d 190 / 80 / add3 118, sbo3 119; add3 183 / 62 / cmp3d 65, sbo3 56; sbo3 126 / 46 / cmp3d 66, add3 52. So foreign libraries recover most of the gain (cmp3d targets: 38% of cold's M removed by foreign vs 58% by own; add3 and sbo3 targets: 65-70% vs 66-64%): rules mined on one three-variable family transfer to the others, nearly fully for add3 targets. cmp3d is the family least served by foreign rules (needs its comparison rules). Logs: `scripts/experiments/logs/loop_cross1.tsv`.

### Library overlap, pooled library, cross-family salt 2 (2026-10-10; FAST, single runs)
Overlap (salt-1 libraries, 8 rules each): cmp3d, add3 and sbo3 share three core rules (`sub(add(x,y),z) -> add(sub(x,z),y)`, `sub(x,sub(y,z)) -> add(sub(x,y),z)`, `add(sub(x,y),z) -> add(sub(z,y),x)`); cmp3d and sbo3 also share `sub(sub(x,y),z) -> sub(x,add(y,z))`, add3 chose the opposite orientation (`sub(x,add(y,z)) -> sub(sub(x,y),z)`, `sub(sub(x,y),z) -> sub(sub(x,z),y)`), so a naive union is cyclic: the pooled library drops those two. The rest is family-specific (lt rules for cmp3d; and/or/xor rules for sbo3 and add3).
Pooled library (14 rules: cmp3d + add3 + sbo3, salt 1; includes the target's own library, so an upper bound for "one shared library"), total M over streams 1-3: cmp3d 82 (own 80, cold 190), add3 51 (own 62, cold 183), sbo3 45 (own 46, cold 126). Pooled matches own within 2 (cmp3d, sbo3) and beats it on add3, so one shared library loses nothing here.
Cross-family salt 2, total M (cold / own / foreign): cmp3d 182 / 96 / add3 126, sbo3 126; add3 165 / 51 / cmp3d 68, sbo3 37; sbo3 117 / 47 / cmp3d 66, add3 55. Same pattern as salt 1: foreign libraries recover most of the gain; sbo3's library beats add3's own library on add3 in both salts (56 vs 62, 37 vs 51); cmp3d is least served (about 31-33% fewer vs 47% own).
Logs: `scripts/experiments/logs/loop_pooled1.tsv`, `loop_cross2.tsv`.

### Mixed-stream library (FAMILY=u3) and held-out mix3 (2026-10-10; salt 1, FAST, single runs)
`u3` = union of the add3, sbo3, cmp3d pools (9140 laws); `pool_conjectures` now never groups a comparison with a non-comparison (one-bit vs n-bit; the union exposed a panic in `bit()`). Library mined on the u3 phase-0 stream (stride 11, B=100 K=4, 215 s, M 49, 8 rules: the three core rules, add3's sub/sub orientation, `sub(sub(x,y),z) -> sub(sub(x,z),y)`, two lt rules; no and/or/xor rules). Total M over streams 1-3: cmp3d 137 (merged pool 82, own 80, cold 190), add3 72 (51, 62, 183), sbo3 54 (45, 46, 126). A library mined directly on the mixed stream is worse than the merged one: 8 rules cannot hold both families' specific rules.
mix3 held out (STRIDE 7, phases 1-3; no mix3 rule in any seed): cold 66 (16,16,34), merged pool 13 (7,3,3), u3-mined 20 (9,4,7). So rules mined on other families transfer to mix3.
README.md (tracked) now has the table.

### u3 library with 16 rules; static shift/lt check (2026-10-10; salt 1, FAST, single runs)
`RULEMINER_ROUNDS=16` on the u3 phase-0 stream (238 s, ref M 24 vs 49 at 8 rules): the 8 extra rules are all `lt` rules (greedy picks the biggest gain), no and/or/xor rules. Total M over streams 1-3: cmp3d 65 (8 rules 137, merged pool 82, own 80, cold 190); add3 72, sbo3 54, mix3 20 (all identical to the 8-rule library). So the mixed-stream gap on cmp3d was the 8-round cap, not the mining; the other families gain nothing from more lt rules.
Static kernel-checked serve (CHECK_FAST, default 250-law windows), none vs merged pooled library: shl 279 laws, 274 machine-free either way; shr 65/65 either way; lt 248 laws, 220 vs 221. So the pooled add/sub/lt rules do not touch the two-variable shift families (and barely the two-variable lt family); mix3, which contains shl1 terms, did transfer (66 -> 13), so the shift gain there came from the add/sub rules around the shifts. Logs: loop_u31_16*.tsv.

### u3 library with the cap lifted (ROUNDS=40; 2026-10-10, salt 1, FAST, single runs)
The greedy miner stopped by itself at 25 rules (490 s, ref M 15; 8 rules 49, 16 rules 24). Rules 17-25: 2 more lt, three `sub(.., xor(z,-1))` rules (the first and/or/xor-flavoured ones), four lt rules with shl1. Total M over streams 1-3: cmp3d 54 (16 rules 65, merged 82, own 80, cold 190); add3 66 (72; merged 51, own 62); sbo3 54 (54; merged 45, own 46); mix3 20 (20). Diminishing returns: the extra 9 rules help cmp3d (-11) and add3 (-6) and nothing else; the add3/sbo3 gap to the merged library (which holds each family's own mined rules) remains.

### Salt 2 repeat of the mixed-stream library, and equal-share stream u3w (2026-10-10; FAST, single runs)
Salt 2 u3 library (cap 40): stopped at 28 rules (481 s, ref M 23). Total M over streams 1-3: full 28 rules cmp3d 60, add3 66, sbo3 72, mix3 39; first 16 rules cmp3d 80, add3 66, sbo3 73 (salt-2 refs: cold 182/165/117, own 96/51/47). Salt 1 (25 rules): 54/66/54, mix3 20. So the cmp3d gain over the family's own library holds on both salts (60, 54 vs 96, 80), add3 stays near own+4..15, sbo3 does not reach own (72 vs 47 salt 2; 54 vs 46 salt 1), mix3 gains but varies (39 vs 20).
`FAMILY=u3w` (add3, sbo3, cmp3d sequences interleaved in equal parts; test `u3w_window_is_an_equal_mix`), salt 1, stride 7, cap 40: stopped at 10 rules (128 s, ref M 23); cmp3d 82, add3 70, sbo3 58, mix3 24. Not better than u3 (54/66/54/20): equal weighting does not close the gap to the merged library, and a smaller, more uniform stream gives fewer rules. The gap is therefore not an artefact of cmp3d's larger share.

### Exact u3 library; sbo3 over four salts (2026-10-10)
Exact (non-FAST) mining of the u3 library, salt 1, cap 40: 1248 s (2.6x the FAST 490 s), 25 rules, ref M 15, and the rule file is byte-identical to the FAST one (same rules, same order), so the loops on it would be identical; the planned exact-library eval was cancelled as redundant. FAST mining is not the cause of any mixed-stream shortfall here.
sbo3 total M over streams 1-3 (cold / own library / u3 library): salt 1 126 / 46 / 54; salt 2 117 / 47 / 72; salt 3 133 / 50 / 52 (u3: 11 rules); salt 4 142 / 54 / 52 (23 rules). So the u3 library is within +-8 of the own library on three of four salts; salt 2 (72) is the outlier. The sbo3 "shortfall" is mostly noise at this sample size, not a systematic gap.
