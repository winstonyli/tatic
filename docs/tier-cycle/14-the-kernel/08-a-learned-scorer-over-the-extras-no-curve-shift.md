### A learned scorer over the extras: no curve shift (2026-10-31; v0.6 stage 1)

Question (`docs/superpowers/specs/2026-10-31-learned-proposer-design.md`): does ordering each mine's extras by a model
trained on the kernel's own verdicts move the frontier past a random draw at the same mining CPU? The scorer is a
logistic regression on 26 counts of a law's two sides (`tests/church_bv/scorer.rs`); `POOL=4` cuts 4n kept laws per mine
and keeps the best n by score; the label is miner credit (a straggler a chosen rule covers).

- **Signal exists offline.** Run `2026-10-31-v06-labels` (salts 4-10, arm A = arm B, deterministic): 42 mines, 13,398 laws,
  3,282 credited. Fit on salts 4-9, test AUC on salt 10: **0.691**, size-only 0.528 (train 0.711). The verdict rule
  (test AUC >= 0.55 and >= size-only + 0.02) passed, so the gate ran. Final weights fit on salts 4-10.
- **No curve shift.** Gates `2026-10-31-v06-g1` to `g6`, salts 1-3 (disjoint from training), untimed counts, Defender
  real-time protection off, machine about 50% loaded by other apps. Summed over the salts (`curve.sh`):

| arm | held-out M | job CPU | rules | free share, bands 11/13/15/17 |
|---|---|---|---|---|
| random n 80 | 6043 | 333 s | 719 | .939 .827 .810 .750 |
| scorer n 80 | 6337 | 402 s | 866 | .937 .827 .793 .736 |
| random n 160 | 5517 | 417 s | 925 | .943 .838 .829 .775 |
| scorer n 160 | 5603 | 600 s | 1136 | .945 .847 .820 .763 |
| random n 319 | 5166 | 711 s | 1140 | .943 .850 .840 .792 |
| redraw `GEN_DRAW=1` / `2` | 5090 / 5150 | 659 / 677 s | 1210 / 1241 | |
| pool 4, first n (control) | 5168 | 636 s | 1181 | .945 .853 .839 .788 |
| scorer n 319 | 5248 | 770 s | 1327 | .947 .857 .833 .778 |

  Redraw spread sigma = 76 (|5166-5090|, |5166-5150|); the control is within it (the pool alone moves nothing). The scorer
  arm is **worse** than random at every n (+294, +86, +82 held-out M; the last within sigma) and costs more CPU (1.2x, 1.4x,
  1.1x). It reaches no random arm of a larger n: scorer n 80 is 6337 against random n 160 at 5517. The win rule
  (held(s_n) < held(r_n) - sigma at CPU <= 1.1x, or held(s_n) <= held(r_2n) at lower CPU) fails everywhere.
- **Reading (inference).** The labels reward laws that are easy to cover by a rule the mine picks (greedy credit,
  in-sample), and those are the large laws (size feature weight): the scorer prefers them, the mines get more work
  (walk/match/op 1.8x at n 319) and more rules but do not transfer to the held-out bands. What would confirm: refit on a
  held-out-transfer label (w2) and rerun g4-g6 (about 40 min). Not done.
- **Null scope.** "No gain from a linear model on these count features with this label", not "no signal".
- **Size-blind refit (2026-10-31; runs `v06-g7` to `g9`).** The reading above predicts that removing the size features
  helps. Refit with columns 1-4 (sizes, depth) and 10-17 (operator totals, a size proxy) zeroed (`DROP` in `fit_scorer`):
  test AUC 0.650 (train 0.669), so the signal does not come from size alone. Same gate, same salts, pool 4:

| arm | held-out M | job CPU | rules |
|---|---|---|---|
| random n 80 / scorer n 80 | 6043 / 6329 | 333 / 264 s | 719 / 840 |
| random n 160 / scorer n 160 | 5517 / 5783 | 417 / 420 s | 925 / 1142 |
| random n 319 / scorer n 319 | 5166 / 5186 | 711 / 687 s | 1140 / 1322 |

  Still no shift: worse at n 80 and 160 (+286, +266, beyond sigma 76) and equal at 319 (+20, inside sigma); the n 80 CPU is
  noise from other load (the arm ran 264 s against 333 s for 1.3x the rules). So the "large laws" reading is not
  what fails; the label's in-sample credit does not transfer by whatever features. The full w2 transfer label (credit
  by a rule that also covers held-out stragglers) was then built (below).
- **Held-out transfer label w2 (2026-10-31; runs `v06-labels2`, `v06-g10` to `g12`).** `RULEMINER_TRANSFER=1` makes each mine
  also print `RULEMINER label2:` (`transfer_labels` in `miner.rs`): a straggler is 1 if it is covered and a chosen rule that
  could act in its evaluation (`Trace::touched_by`) earns its keep on the held-out bands: some held-out straggler (base
  rules, bands 11-17, 4000 laws, 917-1542 stragglers per mine) is covered under the chosen rules but not under the chosen
  rules without that rule. The print changes nothing the mine chooses (probe `v06-tx-probe`: rules, M and held-out M equal
  to the plain exe; about 1 s per mine). Over salts 4-10: 2949 positives against 3282 for the credit label (90%: most credit
  transfers by this test, 28-54% of chosen rules earn their keep). Fit on salts 4-9, test AUC on salt 10: 0.686 (size-only 0.543).
  Gate, salts 1-3, pool 4:

| arm | held-out M | job CPU | rules |
|---|---|---|---|
| random n 80 / w2 scorer n 80 | 6043 / 6529 | 333 / 307 s | 719 / 866 |
| random n 160 / w2 scorer n 160 | 5517 / 5832 | 417 / 634 s | 925 / 1118 |
| random n 319 / w2 scorer n 319 | 5166 / 5409 | 711 / 1075 s | 1140 / 1232 |

  Worse than random at every n (+486, +315, +243, all beyond sigma 76) and worse than the credit-label scorer. So the
  label's in-sample bias was not the cause: three scorers (credit, size-blind, transfer) over count features all fail.
  What is left is that count features of a law do not predict which laws help a mine (an inference: a law's value depends
  on the other laws in the mine, which a per-law score cannot see).

