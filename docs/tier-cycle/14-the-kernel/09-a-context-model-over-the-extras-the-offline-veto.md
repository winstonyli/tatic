### A context model over the extras: the offline veto (2026-11-01; v0.6 follow-up, Q1)

Question (`docs/superpowers/specs/2026-11-01-context-aware-scorer-design.md`, stages 0 and 1; plan
`docs/superpowers/plans/2026-11-01-context-aware-scorer.md`): does a model that sees a law in the context of its mine (35
columns: the 26 per-law counts, three percentiles of steps, size and fallbacks among the pool's stragglers, four likenesses to
the served stragglers' normal forms, two marginal-coverage columns after a served-only cover) rank the credited laws of a mine
better than the per-law model and the `small` key? Offline only, nothing reaches the kernel (`crates/church-bv/src/ctx_scorer.rs`,
`scripts/ctx_dump.sh`).

- **Stage 1 reproduced** (`ctx_scorer::reproduce_stage1` on the cached labels of `2026-10-31-v06-labels`): fit on salts 4-9, test
  salt 10: AUC test 0.6913, train 0.7109, size-only 0.5282 (recorded 0.691 / 0.711 / 0.528); 13,398 laws, 3,282 credited, 42 mines.
- **Dump** (`2026-11-01-ctx-dump`, salts 4-10, `POOL=4`, `EXTRAS_SELECT=first`, `POOL_DUMP=1`): 42 mines, 4.9 minutes, peak commit
  5.8 GB (probe `2026-11-01-ctx-dump-s4-2`: 44 s, 6.3 GB). Per mine a pool of 1276 laws with raw per-law facts, the served
  stragglers' normal forms, and `RULEMINER label:` lines. The dump changes no chosen rule, `rules.txt` or `m.tsv`; its own
  classification and quiet served-only cover add to the process's WORK counters (walk 269217 to 371189 in the small smoke loop),
  so a dump arm's WORK is not comparable with another arm's.
- **Labelled slice**: the first 319 pool laws of each mine, 13,398 in all; 5 later copies of a law text dropped (first occurrence
  kept, salts ascending); 4,728 live stragglers, 3,177 credited (about 112 stragglers per slice).
- **Q1** (`ctx_scorer::q1_report`, runs `2026-11-01-ctx-q1-3` and `-4`, identical output; leave-one-salt-out, fit on labelled
  stragglers, 2000-resample paired bootstrap over the 42 mines, seed 1). Held-out AUC (mean over salts): context 0.7344,
  per-law 0.6397. Capture = credited laws in the top k of a slice, summed over the 42 mines:

| k | ceiling | context | per-law | `small` | random (200 shuffles) | d = context - per-law, mean per mine, 95% | e = context - `small`, 95% | salts with d and e > 0 |
|---|---|---|---|---|---|---|---|---|
| 40 | 1680 | 1476 | 1329 | 1281 | 399 | 3.50 [2.74, 4.36] | 4.64 [3.86, 5.43] | 7 of 7 |
| 80 | 2879 | 2481 | 2378 | 2316 | 796 | 2.45 [1.43, 3.62] | 3.93 [2.81, 5.12] | 7 of 7 |
| 160 (first bar, dropped) | 3177 | 3177 | 3177 | 3177 | 1593 | 0 [0, 0] | 0 [0, 0] | 0 of 7 |

- **Verdict: PASS at k in {40, 80}** (runs `2026-11-01-ctx-q1k` and `-q1k-2`, identical output; both intervals above zero at
  both k, 7 of 7 salts). The approved bar was k in {80, 160} (m1) and read FAIL: at k = 160 no ranker can win, because a slice
  holds about 112 stragglers, so every straggler-first ranker, `small` included, already captures all 3,177 credited laws ("no
  room"). The user amended the bar to {40, 80} (decision a2, 2026-11-01) after seeing that result, not before; the k = 80 numbers
  are the same under both bars.
- **Random column caveat**: the `random` column shuffles all live labelled laws, clean ones included, so it is far below the
  straggler-first rankers by construction. A random order of the stragglers only (runs `2026-11-01-ctx-q1s` and `-q1s-2`,
  identical) captures 1130 at k = 40 and 2245 at k = 80, so the real margins over chance are context +31% / +11% and `small`
  +13% / +3%.
- **Group 3 reads which way?** Of the stragglers in the labelled slices (before the 5 duplicates were dropped), those the
  served-only cover already closes (group 3 flag 0) are credited 618 of 651 times (95%); the uncovered ones 2560 of 4078 (63%).
  So group 3 ranks first the laws the served rules would cover anyway, which capture counts as credit but which add no new rule to
  the mine. No leakage (the flag needs no label), but capture over-rewards this, and it may not carry over to held-out M or to
  Q2. The signal is a statement about credit, not marginal value.
- **Ablation** (capture sums, k = 40 / 80; full model 1476 / 2481): drop group 3 (marginal coverage) 1399 / 2429, drop group 1
  (percentiles) 1414 / 2451, drop group 2 (likeness to served) 1485 / 2481, drop the per-law block 1438 / 2457 (the three context
  groups alone beat the per-law model's 1329 / 2378). Groups 3 and 1 carry the signal; group 2 adds nothing.
- **Limits**: labels exist only for the slice, so Q1 ranks within the slice (Q2, "Q2 primary run" below, ranks the whole pool, where 957 laws per mine
  never had a label); capture counts credited laws, not held-out M or CPU, and stage 1's offline AUC was also real while its gate
  failed (above), so this shows no curve shift.
- **Q2 feature set gate** (run `2026-11-04-q2-t1`, `ctx_q1.sh ... no-g3`, 33 columns, no group 3; same dump, folds and bootstrap).
  Verdict **PASS**, gate met at k in {40, 80}. Held-out AUC context 0.6967 (per-law 0.6397). Capture sums, k = 40 / 80: 33-column
  1399 / 2429, per-law 1329 / 2378, `small` 1281 / 2316, random of stragglers only 1130 / 2245. d (33-column - per-law), mean per
  mine: 1.67 [1.07, 2.29] / 1.21 [0.38, 2.14], 7 of 7 salts both k. e (33-column - `small`): 2.81 [2.00, 3.60] / 2.69 [1.67, 3.71],
  7 of 7 salts at k = 40, 6 of 7 at k = 80 (salt 7 has e = 0 at k = 80). The model keeps about half of the full model's lead over
  per-law, and the choice of 33 columns (decision c1) was made after the ablation above was seen.

