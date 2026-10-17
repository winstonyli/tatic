---
status: done
---

# End-to-end lemma loop: design (proposal, not started)

Status: **built and run** (loop experiment and follow-up; see the Results sections below).

## Goal

Test the project thesis on one family: with lemmas ablated, can proposal and proof run **together with execution** and shrink the whole-term machine proofs that execution needs? Today the pieces run separately: `rule_miner` proposes, scores and accepts rules in batch `RULEMINER_ROUNDS` rounds (greedy, one process, `EXTRA_RULES`); `rulelm` samples rules into a file that the miner reads once (`RULEMINER_PROPOSER=file`); execution (`rewrite_law`, kernel check) never sees a rule that arrives later.

## What already exists (verified in `tests/church_bv/search.rs`, `scripts/miner_summary.sh`)

- Greedy multi-round acceptance inside `rule_miner` (`rounds`, `trials`, `noloop`, `RULE_BUDGET`, `PERM_ORDER`).
- Proposers: `mined`, `midpoint`, `goal`, `file`, `transfer`, `random`.
- Scoring: machine proofs removed per straggler; checking: `rule_set_kernel_check` prints `CHECKED ... (n machine-free)` and `NFSAME x of y`.
- Every accepted rule is proved (`prove_rule`) and kernel-checked, so soundness does not depend on the proposer.

## What is missing

1. **A request stream.** Execution = laws asked for over time, each proved by `rewrite_law` with the rules accepted so far.
2. **Online acceptance.** A rule accepted mid-stream must help later requests (it does: `rules()` reads `EXTRA_RULES` each call) and must never be applied unproved.
3. **Feedback to the proposer.** Accepted rules become training data or prompt context for the next proposals (§79-81 trained once, offline).
4. **One number.** Cumulative machine proofs (and seconds) over the stream, compared with the same stream under fixed rules.

## Decisions to make (pros and cons)

**Family.** (a) deep add3 (64 stragglers; mined covers 51 of 64 with default order, so the most headroom to show a model adding something the miner lacks), (b) shr (900 laws, already 896 with three normal-form rules, little headroom), (c) mul (2 of 2, saturated). Recommend (a). Con: add3 laws are larger, so each trial costs more.

**Loop shape.** (i) Rounds, sequential: stream a batch, stop, propose, accept, resume. Pro: deterministic, reproducible, reuses `rounds`. Con: not concurrent. (ii) Two processes: the miner writes accepted rules to a file; the executor reloads it between requests. Pro: really concurrent, only a rule-file protocol. Con: nondeterminism and CPU contention on this machine (cap 12 threads, BelowNormal). Recommend (i) first, as the control, then (ii).

**Proposer for the first pass.** Existing `rulelm` checkpoints (no retraining) versus retraining on accepted rules each round. Recommend existing checkpoints first: it isolates "does a model add coverage" from "does feedback help".

## Metric

On a fixed stream S of N laws from the family (seeded order, N around 300, no law repeated):
- **M(S)** = machine proofs needed for S, and **T(S)** = build + check seconds, under (0) built-in rules, (1) the batch miner's final rule set applied from the start (upper reference), (2) the loop (rules arrive during the stream).
- Success: M(2) is within 10% of M(1) and below M(0) by at least the miner's batch gain on this family, **and** adding the model proposer lowers M(2) below the `mined`-only loop on at least one seed. Failure is informative too: it says the miner alone saturates and the model adds nothing here.

## Risks

- The loop, not the model, may dominate cost: each trial is a prove plus rescoring (the 40-law sweeps take minutes at n=64). Score at width 4 as the miner does, prove at the stream width.
- The stream order changes which rules arrive first; run three seeds.
- The `lpo` / loop trade-off (§89): accepted rules must respect `NOLOOP`/`PERM_ORDER` or the stream can stall on a looping rewrite; keep `RULE_BUDGET`.
- Machine load on this shared machine blurs timings; M(S) counts do not depend on it, so decide on counts and report T(S) with load.

## Plan outline (after approval)

1. A driver test `search::loop_stream` (ignored): build S, run it under (0), (1), (2), print M and T. Reuses `family_laws`, `rewrite_law`, the miner's accept step factored into a function.
2. Rounds mode with the `mined` proposer; check M(2) against M(1).
3. Add the `file` proposer fed from `rulelm sample` each round; rerun.
4. Only then the two-process mode.

One small runnable check: with an empty stream the driver reports M = 0 for all three modes.

## Decisions on the open questions (owner, 2026-10-04: "proceed as recommended")

- **Stream:** both. First pass: the family's own laws (`family_laws`, seeded order). Then a held-out stream of corpus-generator laws (§78-80), to tell "the loop learned something" from "it memorised the miner's pool". Unprovable or out-of-family laws in the held-out stream are counted and skipped, not scored.
- **Subsumption:** never remove rules in the first build. After it, prune between rounds only (batch). Per-acceptance removal only if rule-set size shows up in the loop's cost.

Still open: nothing blocking. The build itself still needs the owner's go-ahead.

## Results, stream 1 (deep add3, B=150, K=4, stride 7, offset 0; 2026-10-04)

Logs: `scripts/experiments/logs/loop_0_<cfg>.tsv`, `loop_summary.txt`. The stream has only 204 laws, so it is two batches (150 + 54); rounds 2 and 3 and the offsets 1000 and 2000 streams are empty (M = 0 in every config, as the empty-stream check requires).

| config | M batch 0 (150 laws) | M batch 1 (54 laws) | total M | rules at the end |
|---|---|---|---|---|
| none | 64 | 23 | 87 | 0 |
| loop-mined | 64 | 18 | 82 | 12 |
| ref (mined on the whole stream) | 16 | 10 | 26 | 8 |
| loop-file (rulelm `ck_B`) | 64 | 23 | 87 | 0 |

- **Batch 0 cannot improve in a loop by construction**: it is served before any rule is mined. Of ref's 61-proof gain, 48 are on batch 0. Total M(loop) against M(ref) is therefore a structurally unfair comparison on a two-batch stream.
- **Ruling on the spec's open fraction:** the loop's gain is judged on batches after the first, against ref's gain there: ref saves 13 of 23, loop-mined saves 5 (38% of the achievable). Both stated criteria fail on this stream: M(loop-mined) = 82 is not within 10% of M(ref) = 26, and the loop-mined gain is well under ref's.
- **loop-file got nothing.** The model proposed 43 candidates in round 0 (39 decreasing in the rule order); none applied to any of the 64 stragglers ("0 applicable candidates"), so no rule was mined. So `ck_B` samples do not reach these stragglers; the model proposer did not beat `mined` on this stream.
- The rules mined from batch 0 alone (8 at that point, 12 at the end) overlap with ref's but differ, e.g. ref has the `xor(x, -1)` add rules that the loop did not select before batch 1.
- Not shown by this stream: whether more batches would close the gap. That is what the stride 5 and stride 3 streams (`loop_run2.sh`) test; their results are in the next section.

## Results, streams 2 and 3 (deep add3, B=150, offset 0; `loop_run2.sh`, 2026-10-04)

Logs: `scripts/experiments/logs/loop_s<stride>_<cfg>.tsv`, `loop_summary2.txt`.

| stream | none | loop-mined | ref | loop-file | batches (laws) |
|---|---|---|---|---|---|
| stride 7, K=4 (stream 1) | 87 | 82 | 26 | 87 | 150 + 54 |
| stride 5, K=2 | 112 | 98 (12 rules) | 29 (8 rules) | 112 (0 rules) | 150 + 135 |
| stride 3, K=3 | 194 | 125 (14 rules) | 54 (8 rules) | 194 (1 rule) | 150 + 150 + 150 |

Per batch (stride 3): none 64/75/55; loop-mined 64/21/40 (rules in force 0/5/11); ref 24/14/16; loop-file 64/75/55 (one rule in force on batch 2, covering 2 of 75 stragglers).

- **Share of the hindsight gain, batches after the first** (ref's saving on those batches is the denominator): stride 7, 5 of 13 (38%); stride 5, 14 of 32 (44%); stride 3, 69 of 100 (69%). It is higher on the three-batch stream than on the two-batch ones (stride 7 and 5 differ in batch size, not count), but ref's rules were fit partly on the batches they are scored on, so this is not a clean out-of-sample figure.
- **Criteria.** M(loop-mined) within 10% of M(ref): fails on all three (82 vs 26, 98 vs 29, 125 vs 54). M(loop-file) below M(loop-mined) on at least one stream: fails on all three. The model proposer did not help here: its candidates applied to no stragglers on two streams, and on stride 3 the one rule it contributed changed nothing (batch 2 stayed at 55). Caveat: loop-file uses the model alone, with the mined candidates dropped; "model added to mined" (the spec's criterion as worded) was not run.
- **Reading.** On this family the miner alone carries the loop, and a mined-batch-by-batch loop recovers about 40-70% of the later-batch gain, more as batches accumulate. Batch 0 is unavoidable by construction: under `none` it is 74%, 64% and 33% of the stream's M (strides 7, 5, 3). Whether more batches or a different selection (favoring rules that cover distinct straggler shapes) close the gap is untested.

- **`ref` is capped.** `loop_stream.sh` runs the miner with `RULEMINER_ROUNDS=8`, and `ref` chose exactly 8 rules on every stream, while the loop mines up to 8 per round and ended with 12-14 (of which 8, 8 and 11 were in force on the last batch; the final mine runs after the last batch). So `ref` is a capped reference, and the 38/44/69% shares are upper bounds.

## Step 0 of the follow-up: `ref` with the cap raised to 16 rounds (2026-10-04)

`scripts/experiments/ref_cap.sh`, logs `logs/ref16_s<stride>.tsv`, `ref16_summary.txt`. With `RULEMINER_ROUNDS=16`, ref's total M is 26 / 28 / 53 (strides 7 / 5 / 3) against 26 / 29 / 54 with the cap of 8, with 8 / 9 / 9 rules: the miner stops on its own once no candidate fixes a straggler, so the cap was barely binding. The 38% / 44% / 69% shares stand to within a point; the earlier caveat (ref is capped) can be read as "the cap changes ref by at most 1 proof".

## Results of the follow-up: cumulative window (A), carried pool (D), model added to mined (ADM) (2026-10-04/05)

`scripts/experiments/follow_run.sh` (release exe, THREADS=6, B=150, OFFSET=0, DEEP3=1, ROUNDS=8, mined proposer), logs `logs/follow_s<stride>_<cfg>.tsv`, `follow_summary.txt`; all 12 runs finished (rc=0), 2026-10-04 19:43 to 22:43. Total M (per batch in brackets):

| stride | none | loop-mined | ref16 | A | D | AD | ADM |
|---|---|---|---|---|---|---|---|
| 7, K=4 | 87 | 82 [64,18] | 26 | 82 | 82 | 82 | 82 |
| 5, K=2 | 112 | 98 [72,26] | 28 | 98 | 98 | 98 | 98 |
| 3, K=3 | 194 | 125 [64,21,40] | 53 | **113** [64,21,28] | 125 | **113** | **113** |

Share of ref16's gain on the batches after the first (denominators 13, 32, 101): stride 7 and 5 unchanged at 38% and 44% for every config; stride 3 loop-mined 68%, A/AD/ADM 80%, D 68%.

- **Only one cell is a real test.** Batch r is served under rules from mines 0..r-1 only. On strides 5 and 7 only mine 0 can change a scored batch (stride 7's batches 2 and 3 have no laws), and mine 0 sees the same window and an empty pool under every config, so A and D equal loop-mined there by construction; those cells are vacuous (ADM differs only through its model samples in mine 0, which added nothing). Only stride 3, batch 2 (affected by mine 1) tests A and D, on one stream.
- **Stride 3 result:** A improved batch 2 from 40 to 28 (mine 1 with window 0..2B instead of B..2B); batches 0 and 1 are identical to loop-mined. D alone equals loop-mined; AD and ADM equal A. M is deterministic for the mined configs; ADM's model samples are seeded per round (`scripts/loop_candidates.sh`, seed 100+round) and matched no straggler in any of its 9 mines (applicable-candidate counts equal AD's), so ADM is effectively AD. Caveat: extra candidates skip the rule-order filter that `PROPOSER=file` applies; this changed no result.
- **Does any config beat loop-mined beyond noise?** Only A at stride 3 (125 to 113, 80% against 68% of ref16's later-batch gain); it is a single data point. D and the model samples show no benefit where they could act (stride 3 mine 1; mine 0 of each stream).
- **Reading (tentative).** A wider straggler window may help once earlier batches hold shapes later ones share; that mechanism is untested. Nothing here shows that candidate supply is or is not the bottleneck beyond one batch. The loop still ends well above ref16 at stride 3 (113 against 53). Untested: the selection rule itself, and more or larger batches. Note: the shares above use ref16's gain as denominator (101 at stride 3); the earlier section's 69% used the cap-8 ref (100).

## Identity-candidate filter (`RULEMINER_NOIDENT=1`, stride 3, 2026-10-05)

`scripts/experiments/noident_run.sh`, logs `logs/noident_s3_{N,NA}.tsv`, `noident_summary.txt`. The pool route generates identity candidates (`l -> l`); the filter dropped 10, 13 and 15 of them in the three mines and changed nothing: loop-mined with the filter (N) 125 [64,21,40], with the cumulative window (NA) 113 [64,21,28], identical to the runs without it. So the identity candidates were harmless here (a wasted scoring slot at most); the filter stays opt-in.

## Longer stream: stride 2, K=5 (2026-10-05)

`scripts/experiments/stride2_run.sh` (release exe, THREADS=6, B=150, DEEP3=1; all four configs rc=0, 01:32 to 02:34), logs `logs/stride2_<cfg>.tsv`, `stride2_summary.txt`. Total M (per batch): none 287 [47,100,52,69,19]; loop-mined 237 [47,99,42,42,7]; A 237 [47,99,42,42,7]; ref16 78 [22,21,11,13,11] (9 rules). Share of ref16's gain on the later batches (denominator 240 - 56 = 184): loop-mined 50/184 = 27%, A 27%.

- **The cumulative window gave nothing here**: A equals loop-mined batch for batch, although it mined different rules (24 against 20 at the end). The stride-3 gain (125 to 113) did not generalize; with one gain in four streams it is best read as stream-specific.
- **The loop recovers less on a longer stream** (27%, against 38-68% on the shorter ones), and batch 1 barely improves (99 against 100) because the first mine, on 47 stragglers, found rules that do not transfer to the next 99. Where ref's rules fit all five batches at once (9 rules, 78 total), the loop's rules, mined on one batch at a time, do not carry. This points at the selection rule and the single-batch evidence, not at candidate supply (D, ADM) or window width (A); it still does not test a different selection rule.

## Generality penalty (`RULEMINER_GENERAL=w`, stride 3, 2026-10-05)

Why: at stride 2 the first mine (47 stragglers) chose narrow rules full of constants (`-1`, `shl1(x, 0)`) while ref's 9 rules are general add/sub reassociation laws, and the loop reached the general ones only in the third or fourth mine. The option lowers each candidate's gain by `w * rule_specificity` (left-side size plus 3 per constant leaf on either side); the raw gain must still be positive, `w=0` (default) is unchanged. `scripts/experiments/general_run.sh`, logs `logs/general_s3_w<w>.tsv`, `general_summary.txt`.

Result (loop-mined, stride 3, baseline 125 [64,21,40]): `w=100` 125 [64,21,40] (one different pick, same M), `w=250` 125 [64,21,40] with the general rules (`add(sub(x, y), z) -> add(sub(z, y), x)`, `sub(add(x, y), z) -> ...`, `sub(x, sub(y, z)) -> ...`) now chosen at the top of the list. So selecting general rules first does not lower M here: the first-mine rule shape is not what limits batch 1, at least at stride 3. Stride 2 (baseline 237) was not run with the penalty. What remains untested: scoring against evidence beyond the mining window (b2) and the combination effect (b3).

Stride 2 (K=5, baseline loop-mined 237 [47,99,42,42,7], 27% of ref16's later-batch gain): `w=100` 228 [47,90,42,42,7] (19 rules; later-batch saving 59 of 184, 32%); `w=250` 270 [47,93,60,59,11] (8 rules at the end; worse than loop-mined 237 but still better than none 287; batches 2 and 3 are worse than loop-mined's 42 and 42, cause not investigated). So the penalty gives a small gain at a moderate weight on one stream (-9 proofs, all on batch 1), none at stride 3, and hurts at a large weight; a single weight and stream, not evidence of a lever.

## Larger batches: stride 2 with B=150, 300, 450 (2026-10-05)

`scripts/experiments/largeb_run.sh` (release exe, THREADS=6, DEEP3=1, stride 2; all six runs rc=0, 12:30 to 14:39; machine loaded by other sessions), logs `logs/largeb_B<B>_<cfg>.tsv`, `largeb_summary.txt`; B=150 from `stride2_*`. Per batch:

| B (laws per batch) | none | loop-mined | ref16 | share of ref16's later-batch gain |
|---|---|---|---|---|
| 150 (K=5) | 287 | 237 [47,99,42,42,7] | 78 | 27% (50 of 184) |
| 300 (K=3; 300,300,112) | 287 [147,121,19] | 237 [147,81,9] | 78 [43,24,11] | 48% (50 of 105) |
| 450 (K=2; 450,262) | 287 [199,88] | 262 [199,63] | 78 [54,24] | 39% (25 of 64) |

- **More stragglers per mine help the later batches**: the share rises from 27% (B=150) to 48% (B=300), and batch 1 falls from 121 to 81 at B=300 (at B=150 it fell from 100 to 99). This supports the evidence-limited reading.
- **It does not lower the total**: M(loop) stays 237 at B=300 and gets worse at 450 (262), because the first batch is paid in full and grows with B (batch 0 is 147 and 199 proofs). The share at B=450 rests on a single later batch (63 against none's 88), so it is the weakest number.
- **ref16 is the same 78 at every B** (9 rules): the hindsight rule set does not depend on how the stream is cut.
- **Reading.** Evidence per mine matters (B=300 recovers about half of the later-batch gain), but a loop cannot escape paying for its first batch; in total-M terms the loop is limited by cold start, not by selection. Whether b2 (scoring against laws outside the mining window) helps is still untested; this result makes it more plausible, since more evidence helped. One family, one stream, deterministic counts.

## Warm start from a held-out slice (stride 2, 2026-10-05)

`WARM=<skip>:<laws>` in `loop_stream.sh`, `scripts/experiments/warm_run.sh`, logs `logs/warm_<cfg>.tsv`, `warm_summary.txt`. Served laws 0..450 (B=150, K=3). Rules are mined once on a held-out slice (laws 450..600 = W150; 450..712 = W264), then the loop keeps mining batch by batch (W) or the rules stay fixed (WS). Cold baselines (first three batches of the stride-2 runs, same laws): none 199 [47,100,52], loop-mined 188 [47,99,42].

| config | total M | per batch | rules at batch 0 |
|---|---|---|---|
| WS150 (static) | 196 | 47,100,49 | 6 |
| WS264 (static) | 196 | 47,100,49 | 7 |
| W150 (loop) | 181 | 47,99,35 | 6 |
| W264 (loop) | 181 | 47,99,35 | 7 |

- **The warm rules barely transfer**: batch 0 stays at 47 with 6-7 rules in force, batch 1 at 99-100; only batch 2 gains (52 to 49 static, 42 to 35 loop). Static saves 3 of 199, the loop 7 of 188. W150 and W264 give identical totals.
- **Why (checked)**: the 7 rules mined on laws 450..712 cover 74 of that slice's 88 stragglers in sample, but only two of them are among ref's 9 rules (`sub(x, add(y, z)) -> sub(sub(x, y), z)`, `sub(sub(x, y), z) -> sub(sub(x, z), y)`); ref's `xor(z, -1)` rules (batch 0's stragglers) are absent, so the later slice does not show the shapes of the early batches.
- **Caveat on the design**: the held-out slice is later in the law sequence, so this is a transfer test across sequence position, not across a random split; sequence position may carry a distribution shift (the families that appear change). It tests this: rules mined on later laws do not help early laws. It does not test rules mined on a random half of the laws.

## Warm start from an interleaved split (stride 2 phase 1, 2026-10-05)

`WARM=0:<laws>:1` (`RULEMINER_PHASE`), `scripts/experiments/warm2_run.sh`, logs `logs/warm2_<cfg>.tsv`, `warm2_summary.txt`. Served: stride-2 phase 0, laws 0..450 (B=150, K=3). Rules mined once on phase 1, the laws between the served ones (WP150: its first 150; WP450: its first 450), then the loop continues (WP) or the rules stay (WPS). Baselines (same served laws): none 199 [47,100,52], loop-mined 188 [47,99,42], ref16 54 [22,21,11] (fit on all 714 laws, in sample).

| config | total M | per batch | rules at batch 0 |
|---|---|---|---|
| WPS150 (static) | 180 | 18,99,63 | 8 |
| WP150 (loop) | 85 | 18,32,35 | 8 |
| WPS450 (static) | **50** | 22,25,3 | 8 |
| WP450 (loop) | **50** | 22,25,3 | 8 |

- **Rules mined on interleaved laws transfer strongly**: 8 rules mined on 450 laws between the served ones, never touched again, serve the 450 laws at 50 proofs, against 199 with none, 188 with the cold loop and ref16's 54 (in sample). WP450 and WPS450 are identical: the loop mined three more rounds and changed nothing in force that mattered (11 rules at the end).
- **Locality**: WPS150 (phase-1 laws 0..150, which neighbour only batch 0) gets batch 0 down to 18 (from 47) but leaves batch 1 at 99 and batch 2 at 63 (worse than none's 52); the loop (WP150) then recovers on its own (32, 35). Together with the earlier warm start from later laws (no transfer: batch 0 stayed 47), this says the law sequence is ordered by shape, rules transfer to neighbouring laws and not across regions, and evidence has to span the regions served.
- **Caveat (important)**: adjacent laws in the pool are probably near-variants of each other, so the interleaved split leaks neighbours, and 50 is an upper bound on what a representative sample would give. The two warm starts bracket the answer: later slice 196 (nothing transfers), interleaved 50 (neighbours transfer). A split by law structure rather than by position is the unbiased test and was not run.
- **Reading.** The loop's cold-start cost is an evidence-coverage problem: a sample covering the served regions, mined once, is enough, and a batch-by-batch loop pays for each region as it arrives. In a deployment where laws arrive in shape-ordered runs, the loop cannot avoid that cost without such a sample.

## Warm start from a structure-based split (2026-10-05)

`SPLIT=0` / `RULEMINER_SHAPE` (`0c30f1a`), `scripts/experiments/warm3_run.sh`, logs `logs/warm3_<cfg>.tsv`, `warm3_summary.txt`. The add3 laws (stride 1, 1423 in all) are split in two halves by the shape of both sides with the variables erased (681 + 742), so laws that differ only in variables stay together and no near-variant of a served law is in the warm set. Served: half 0, its laws 0..450 (B=150, K=3). Warm rules mined on half 1 (first 450 or first 150 laws), then static (WS) or with the loop continuing (WL). Cold baselines on the same served laws:

| config | total M | per batch | rules at batch 0 |
|---|---|---|---|
| none (N) | 209 | 50,112,47 | 0 |
| cold loop (C) | 95 | 50,26,19 | 0 |
| WS150 (static) | 213 | 43,114,56 | 8 |
| WL150 (loop) | 118 | 43,53,22 | 8 |
| WS450 (static) | **64** | 21,24,19 | 7 |
| WL450 (loop) | **43** | 21,10,12 | 7 |

- **Rules mined on a half with disjoint shapes transfer**: 7 rules mined once on 450 laws of the other half take batch 0 from 50 to 21 and serve the 450 laws at 64 proofs static, 43 with the loop continuing, against 209 with none and 95 for the cold loop. This is the unbiased version of the interleaved result (50 there, which leaked neighbours): it still halves the cold loop's total.
- **Sample size matters**: 150 laws of the other half give batch 0 a small gain (50 to 43) but no transfer to the later batches (static 213, worse than none; loop 118, worse than the cold loop's 95): rules mined on too narrow a sample misdirect the later mining or leave the stream where it was.
- **Stream density**: on this stride-1 half the cold loop already does well (95 against 209); at stride 2 on the whole sequence it did not (188 against 199). The streams differ (half 0 at stride 1 against every second law of the whole sequence), so the two cold figures are not comparable.
- **Reading.** A held-out sample large enough to cover the shapes, mined once, cuts the stream's cost in half even when no served shape is in it, and a loop on top of it helps further (43 against 64). A small sample does not. One family, one served stream.

### Warm sample-size sweep (2026-10-05)

`scripts/experiments/warm4_run.sh` (ran 19:45-20:55), logs `logs/warm4_<cfg>.tsv`, `warm4_summary.txt`; same setup as the structure-based split, warm samples of 250 and 350 laws of the other half.

| warm laws | static total (rules) | loop total | per batch (static) |
|---|---|---|---|
| 0 (none / cold loop) | 209 (0) | 95 | 50,112,47 |
| 150 | 213 (8) | 118 | 43,114,56 |
| 250 | 213 (8) | 118 | 43,114,56 |
| 350 | 71 (5) | 49 | 21,30,20 |
| 450 | 64 (7) | 43 | 21,24,19 |

- **Threshold between 250 and 350 laws.** 250 behaves like 150 (no help, loop worse than cold loop); 350 nearly matches 450.
- **Why (rule sets).** The 350 and 450 samples both yield the four general reassociation rules (`sub(add(x,y),z)`, `add(sub(x,y),z)`, `sub(x,sub(y,z))`, `add(x,sub(y,z))`) plus `sub(sub(x,y),xor(z,-1))`; the 250 sample yields none of them, only 8 narrow rules with repeated variables (`shl1`, `xor(x,-1)`). Transfer happens exactly when the sample is large enough for the miner to find the general rules. One family, one served stream, one shape key, so the exact threshold is not general.

300-law sample (`warm5_run.sh`, ran 21:19-22:3x, logs `logs/warm5_<cfg>.tsv`): static 71 [21,30,20], loop 49 [21,16,12], with the same 5 rules as the 350 sample (the four general reassociation rules plus `sub(sub(x,y),xor(z,-1))`), identical to 350 batch for batch. The threshold therefore lies between 250 and 300 laws; a finer sweep was not run.

### Second shape key (`RULEMINER_SHAPE_SALT=a`, 2026-10-05/06)

`shape_part` hashes a salt in front of the skeleton string (unset = original halves); salt `a` gives halves of 747 + 676 laws. `scripts/experiments/warm6_run.sh` (ran 22:00-00:2x, `%TEMP%/bv_salt.exe`), logs `logs/warm6_<cfg>.tsv`, `warm6_summary.txt`. Served: half 0, laws 0..450, B=150 K=3; warm samples are the first n laws of half 1; static unless noted.

| config | rules | total M | per batch |
|---|---|---|---|
| none | 0 | 211 | 33,122,56 |
| cold loop | 5 | 213 | 33,124,56 |
| warm 200 | 8 | 191 | 13,122,56 |
| warm 250 | 6 | 111 | 15,75,21 |
| warm 300 | 6 | 111 | 15,75,21 |
| warm 350 | 7 | 106 | 15,75,16 |
| warm 450 | 8 | 94 | 15,75,4 |

- **The threshold depends on the split.** Original key: 250 laws no help, 300 helps. Salt `a`: 200 laws no help (191; the 8 rules are narrow, with `shl1` and `xor(x,-1)`), 250 halves M (111). So the 250-300 figure was not a law count.
- **Same mechanism, observed**: the samples that help contain general reassociation rules (`add(sub(x,y),z)`, `sub(x,sub(y,z))`, `add(x,sub(y,z))`); the 200 sample has none. Not tested causally.
- **Cold loop gets nothing on this split** (213 vs none 211; it was 95 vs 209 on the original), so the loop's cold-start behaviour also varies with the split. Loop-on-warm was not run for salt `a`.
- Batch 1 stays 75 for every helping sample (15 at batch 0, 4-21 at batch 2): later gains come from rule sets that differ only in batch 2.

Loop on top of the warm start, salt `a` (`warm7_run.sh`, 00:51-01:2x, logs `logs/warm7_<cfg>.tsv`; warm rules copied from the static runs with `WARM_RULES`; the loop no longer mines after the last batch, so rule counts are rules in force at the last batch and differ in meaning from earlier summaries). Batch 0 equals the static run's (15), as it must.

| config | total M | per batch | rules at batch 0 / 1 / 2 |
|---|---|---|---|
| warm 250 static (warm6) | 111 | 15,75,21 | 6 |
| warm 250 + loop (WL250) | 111 | 15,75,21 | 6 / 8 / 12 |
| warm 450 static (warm6) | 94 | 15,75,4 | 8 |
| warm 450 + loop (WL450) | 108 | 15,75,18 | 8 / 10 / 14 |

- **The loop adds nothing on this split**: equal at 250, and worse at 450 (batch 2: 18 against 4 static) although the loop only adds rules. Batch 1 stays 75 either way. On the original split the loop on a warm start helped (64 to 43). So the loop's value on top of a warm start also depends on the split.
- Why more rules raise batch 2 from 4 to 18 was not investigated; the added rules include `add(sub(x, y), z) -> sub(add(x, z), y)`, which rewrites in the opposite direction to a warm rule, and the order/priority of rules in force may matter. Hypothesis only.

**Why WL450 batch 2 is 18, not 4 (ablation, salt `a`, served laws 300..450 with `rule_set_kernel_check`; the 8 warm rules alone give 4, all 14 give 18).** Adding each of the 6 loop-added rules alone to the 8 warm rules: only `add(sub(x, y), z) -> sub(add(x, z), y)` raises M (to 18); the other five leave it at 4. That rule has the same left side as the warm rule `add(sub(x, y), z) -> add(sub(z, y), x)`; the miner dedups one rule per left side within a mine, but not against rules already in force, so the loop added a second, competing rewrite for the same pattern and it displaced the better one. Single-rule ablation only (pairs not tried); the conflict-by-left-side mechanism is my reading of why. A fix would be to reject, or replace, a candidate whose left side is already in force; not implemented.

**The fix, `RULEMINER_NODUPLHS=1`** (drops candidates whose left side already has a rule in force; `scripts/experiments/warm8_run.sh`, logs `logs/warm8_<cfg>.tsv`, `warm8_summary.txt`, ran 01:30-01:5x). Loop total M with the option against without:

| config | without | with | per batch (with) |
|---|---|---|---|
| salt a, warm 450 + loop | 108 | **94** (= static 94) | 15,75,4 |
| salt a, warm 250 + loop | 111 | 111 | 15,75,21 |
| original split, cold loop | 95 | 95 | 50,26,19 |
| original split, warm 450 + loop | 43 | 43 | 21,10,12 |
| original split, warm 300 + loop | 49 | 49 | 21,16,12 |

The option restores batch 2 at salt-a warm 450 (18 to 4) and changes nothing in the four other configs, so the ablation's reading holds there. The loop still adds nothing on top of the salt-a warm start (94 = static; 111 = static), so the fix removes a harm, it does not make the loop help on that split. One regression-sized check (five configs); default stays off.

## Cross-shape selection (`RULEMINER_XSHAPE=w`, 2026-10-06)

The mine's stragglers fall in two groups by a shape hash (salt `xgroup`, independent of the split's key; 31 + 33 in the first stride-3 mine); a candidate's gain gets `w * 1000` per straggler by which it raises the *smaller* group's covered count (raw gain must still be positive). `scripts/experiments/xshape_run.sh`, logs `logs/xshape_s<stride>_w<w>.tsv`, `xshape_summary.txt`; loop-mined config, B=150, mined proposer.

| stride | baseline loop | w=1 | w=3 | per batch (both w) |
|---|---|---|---|---|
| 3, K=3 | 125 (A: 113) | 125 | 125 | 64,21,40 |
| 2, K=5 | 237 | 236 | 236 | 47,98,42,42,7 |

- **No effect**: stride 3 identical to the baseline, stride 2 one proof better (batch 1: 98 against 99). w=1 and w=3 are identical, so the bonus rarely changes which rule wins; the straggler groups are probably covered at similar rates by whatever the raw gain picks. Not investigated.
- This is the fifth selection or supply lever with no reliable gain (window, pool, model, generality, cross-shape). Evidence per mine and coverage of served shapes remain the explanation the experiments support; selection among the candidates in one mine does not.

## Second family: mix3 (`FAMILY=mix3`, 2026-10-06)

`scripts/experiments/mix3_run.sh`, `scripts/loop_stream.sh` with `FAMILY=mix3`, logs `logs/mix3_<mode>.tsv`, `mix3_summary.txt`; stream = laws 0..600 of the stride-1 sequence (B=150, K=4, mined proposer, THREADS=6, ROUNDS=16; the none run was made by hand, `%TEMP%/mix3_none`).

| mode | total M | per batch | rules in force at each batch |
|---|---|---|---|
| none | 62 | 8,22,14,18 | 0 |
| ref (mined on all 600 laws) | **65** | 8,23,15,19 | 2 |
| loop-mined | **40** | 8,22,10,0 | 0 / 1 / 5 / 7 |

- **The loop beats the hindsight reference here**: 40 against 65, and batch 3 needs no machine proofs. `ref` chose 2 rules (`add(sub(x,y),z) -> add(x,sub(z,y))`, `add(xor(x,-1),y) -> add(-1,sub(y,x))`) and serves the stream *worse* than no rules (65 against 62), so on mix3 `ref` is not an upper bound and the "share of ref's gain" measure does not apply.
- **Why `ref` serves worse (checked, `%TEMP%/mix3_abl`, `rule_set_kernel_check` on laws 0..600 under each rule set)**: none 62; rule 1 alone (`add(sub(x,y),z) -> add(x,sub(z,y))`) **44** (matches its reported +18); rule 2 alone (`add(xor(x,-1),y) -> add(-1,sub(y,x))`) 68; both 65. Rule 2 was reported as `+12 fixed` on top of rule 1, but it *breaks* laws that were machine-free before: the miner scores only the stragglers (62 of 600), so a candidate that fixes 12 stragglers and regresses 20 or more of the other 538 laws looks like a pure gain. This is a blind spot of the miner's gain function (no regression guard on non-stragglers), not a scoring-width mismatch; the first two guesses (size term, scoring width) were wrong. The loop's mines see the same blind spot, so its mix3 win (40) is partly luck of which rules it picked; whether regressions also exist in add3 results was not checked.
- **Scope**: one stride, one stream, one family; with M at 62 and 8 in the first batch, differences of a few proofs are not meaningful, but 62 to 40 and a zero batch are.

## Regression guard (`RULEMINER_GUARD=<k>`, mix3, 2026-10-06)

About k of the already machine-free laws (all 538 of the 600 here when k is large) are scored with the stragglers: a candidate that breaks one loses the same 1000 as fixing a straggler gains (guard laws do not feed candidate generation or the size term). `scripts/experiments/mix3g_run.sh` (k=120), then `ref` with k=1000 by hand (`%TEMP%/mix3h_ref`, `bv_guard.exe`). Code not published.

| config | total M | rules | per batch |
|---|---|---|---|
| none | 62 | 0 | 8,22,14,18 |
| ref, no guard | 65 | 2 | 8,23,15,19 |
| ref, guard 120 (sample of 108 of 538) | 65 | 2 | same |
| ref, guard all 538 | **44** | 1 | 8,16,8,12 |
| loop, no guard | 40 | 7 | 8,22,10,0 |
| loop, guard 120 | 40 | 6 | 8,22,4,6 |

- **The blind spot is confirmed as the cause**: with every machine-free law scored, `ref` rejects the regressing rule `add(xor(x,-1),y) -> ...` and ends at 44 (rule 1 alone, as the ablation found), against 65.
- **A sample does not fix it**: 108 laws catch about one fifth of the regressions (the rule regresses about 33 laws, gains 12), so the net still looks positive. A sample would have to be weighted by the inverse sampling fraction (not tried); all laws is the unbiased version and costs a full re-proof of the window per trial.
- **The loop total is unchanged at 40** with the sampled guard (different rules, batches 8,22,4,6); the full guard was not run on the loop.

**Inverse-weighted guard sample** (`mix3w_run.sh`, `bv_guardw.exe`): each sampled guard law is weighted `1000 * clean / sampled` (4981 for 108 of 538) instead of 1000, so the sample's net gain estimates the full window's. mix3, k=120:

| config | total M | rules | per batch |
|---|---|---|---|
| ref, guard 120 weighted | **44** | 1 | 8,16,8,12 (same as the full guard) |
| loop, guard 120 weighted | 40 | 6 | 8,22,4,6 (same as the unweighted sample) |

- The weighted sample reproduces the full guard's `ref` (1 rule, 44) at about half the scoring time: the one scoring round took 36.7 s against 72.6 s with all 538 laws (candidate generation about 6-7 s either way; load differed between the runs). One deterministic sample of one window, so how stable the choice is across samples is not shown.
- The loop stays at 40 whether or not the guard is on; the guard changes which rules it picks, not the total on this stream.

## Regression guard on add3 (stride 3, K=3, `scripts/experiments/add3g_run.sh`, 2026-10-06/07)

`RULEMINER_GUARD=1000` (every machine-free law of the window scored; 256 clean laws of 450 in the ref window), B=150, DEEP3, loop-mined and ref (16 rounds). Logs `logs/add3g_s3_<mode>.tsv`, `add3g_summary.txt`. The ref mine took about 4-5 min per scoring round (86 candidates) (9 rounds, about 40 min of scoring; the loop run was much shorter).

| config | without guard | with guard | per batch (with) |
|---|---|---|---|
| ref (16 rounds) | 53 (9 rules) | **51** (9 rules) | 24,13,14 |
| loop-mined | 125 | **125** | 64,21,40 (identical) |

- **The add3 conclusions stand**: the guard leaves the loop at 125 batch for batch and lowers `ref` by 2 (53 to 51). Unlike mix3, no accepted rule on this window regressed enough to change the outcome, so the earlier add3 results are not an artefact of the miner's straggler-only scoring (at this stride and window; stride 2 was not rerun).
- Cost: the full guard makes mining about 2.3x more expensive per trial here, for a 2-proof gain in `ref` only.

## mix3 structure-based split (2026-10-07)

`RULEMINER_SHAPE` now also splits mix3 (1106 + 1142 laws; `family_law_shape_halves_partition` covers both families). `scripts/experiments/warm9_run.sh`, logs `logs/warm9_<cfg>.tsv`, `warm9_summary.txt`: serve half 0 (laws 0..450, B=150, K=3) with the weighted regression guard (k=120); warm samples are the first n laws of half 1; loop configs reuse the static runs' rules (`WARM_RULES`).

| config | total M | per batch | rules at batch 0 |
|---|---|---|---|
| none | 13 | 7,6,0 | 0 |
| cold loop | 11 | 7,4,0 | 0 |
| warm 150 static | 5 | 1,4,0 | 5 |
| warm 300 static | 5 | 1,4,0 | 5 |
| warm 450 static | 10 | 6,4,0 | 1 |
| warm 300 + loop | 11 | 1,10,0 | 5 |
| warm 450 + loop | 10 | 6,4,0 | 1 |

- **Not informative about the add3 findings**: the stream needs 13 proofs in all (batch 2 none), so differences of a few proofs are not meaningful; the add3 split needed 209. The second family at this split has no headroom to test a warm-start threshold or a warm-start-plus-loop effect.
- Observations without a mechanism: 150 and 300 laws give the same 5 rules and the same M (5); 450 laws yields one rule and no gain (10), the opposite of add3's trend; the loop on the 300-law rules raises batch 1 from 4 to 10 (11 against 5), possibly a competing rule for an existing left side (`NODUPLHS` was not on), not checked.
- A harder mix3 stream (another offset or stride) would be needed; not searched for.

### mix3 split on a harder stream (offset 600 of half 0, 2026-10-07)

A serve-only probe (no rules, 150 laws each, `bv_m3s.exe`) found that laws 0..450 of mix3 half 0 are nearly free (13 proofs) while half 0 laws 600..1050 need 78 + 36 + 22 = 136. `scripts/experiments/warm10_run.sh` = `warm9_run.sh` with `OFFSET=600`; logs `logs/warm10_<cfg>.tsv`, `warm10_summary.txt`.

| config | total M | per batch | rules at batch 0 |
|---|---|---|---|
| none | 136 | 78,36,22 | 0 |
| cold loop | 116 | 78,18,20 | 0 |
| warm 150 static | 136 | 78,36,22 | 5 |
| warm 300 static | 136 | 78,36,22 | 5 |
| warm 450 static | 114 | 78,18,18 | 1 |
| warm 300 + loop | 116 | 78,18,20 | 5 |
| warm 450 + loop | 114 | 78,18,18 | 1 |

- **No warm-start transfer to batch 0 at any size** (78 in every config): the first batch's shapes are not covered by the warm sample's rules. This differs from add3, where a large enough sample cut batch 0 by 60%.
- **150 and 300 laws give the same 5 rules and no gain at all** (136); 450 laws gives one rule and 114 (batches 1 and 2 drop from 36/22 to 18/18). The cold loop reaches 116 on its own, so a warm sample does not beat a cold loop here (114 against 116).
- **The loop on top of a warm start adds nothing** (114 = 114; 116 against 136 for the 300-law rules is the loop's own gain, the same as the cold loop's 116). The earlier add3 finding that a loop on a warm start helped on the original split, and not on salt `a`, is not reproduced here either way.
- The warm-start threshold finding is therefore add3-specific on this evidence: one extra family, one stream; the mix3 rule sets differ in kind (five narrow rules vs one general one) and there is no "enough rules found" jump to compare.

**What the mix3 rule sets are (read from `rules.txt`)**: the cold loop (116) mined, from the served stream itself, `add(sub(x,y),z) -> add(sub(z,y),x)`, `sub(add(x,y),z) -> add(sub(x,z),y)`, `sub(x,sub(y,z)) -> add(sub(x,y),z)` (the same general reassociation rules as add3's four) plus three `xor(x,-1)` rules. The 450-law warm sample from the other half found only one reassociation rule (`add(sub(x,y),z) -> add(x,sub(z,y))`, a variant of add3's orientation), and the 150/300-law samples found five narrow rules with repeated variables and `shl1`, the same kind as add3's too-small samples. So the mechanism looks shared (general reassociation rules are what the stream needs; a sample that does not contain enough evidence for them finds only narrow rules), but on mix3 the served batches themselves already supply that evidence, which is why the warm sample brings nothing beyond the cold loop. Observed from rule files, not tested.
