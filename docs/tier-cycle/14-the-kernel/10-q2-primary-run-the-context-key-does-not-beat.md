### Q2 primary run: the context key does not beat `small` (2026-11-04; v0.6 follow-up)

Question (plan `docs/superpowers/plans/2026-11-01-ctx-scorer-q2.md`): with `EXTRAS_SELECT=ctx` (the 33-column model, weights
fit on salts 4-10, `docs/runs/2026-11-01/ctx-weights/ctx33-v1-s4-10.txt`) ranking the 4n-law pool, is held-out M on salts 1-3
lower than with `small` by more than the draw spread, at no more than 1.05 times the walk? Rule (fixed before the runs): S = max
over draws 3 and 4 of |`small` redraw - `small` draw 0|, T = max(76, S); PASS iff D = (ctx - `small`) < -T at both n and R <= 1.05.
Gates `q2-p-c160`, `q2-p-c80` (0 of 6 arms failed each); redraws `q2-p-d{3,4}-{c,r}{160,80}` (`q2-p-d4-c80` lost one arm to the
8 GB watchdog at 8.8 GB against a 5.5 GB peak elsewhere; the rerun `-rerun` peaked at 5.4 GB and is the one used).

- **Verdict: FAIL at both n** (`scripts/q2_verdict.sh`). n = 160: `small` 4690, walk 489.5 M; ctx 4789, walk 471.5 M; S 57, T 76,
  D +99 (worse), R 0.963. n = 80: `small` 5356, walk 213.4 M; ctx 5306, walk 188.4 M; S 163, T 163, D -50 (inside the noise), R 0.883.
  The n = 160 `small` arm reproduces held 4690 and walk 489.5 M of the recorded run; its match (2.72 G) and op (0.98 G) counts differ
  from the recorded 3.12 G / 1.60 G, taken to be the build profile (ledger ruling), not a change to `small`.
- **Equal-work random** (arms `r419`, `r181`, built to the ctx arm's walk; not part of the verdict): n = 160: ctx 4789 against
  random 4880, -91 at +3.4% walk; n = 80: ctx 5306 against 5566, -260 at -3% walk. The ctx key beats random at equal work, as
  `small` does (knee chart); it does not beat `small`.
- **Redraws** (draws 3 and 4 of the generator; held-out M): `small` 4645 / 4747 at n = 160 and 5193 / 5370 at n = 80. ctx minus
  `small`, robustness read only: n = 160 -145 / +30; n = 80 +69 / +33; the sign is not stable. Random against `small` at the redraws
  (r160 5028 / 4941, r80 5544 / 5635) stays above `small`.
- **Overlap** (fit-slice laws among eval laws, before the verdict; runs `q2-overlap-160`, `q2-overlap-80`): 3 of 11518 (0.026%)
  and 1 of 5760 (0.017%), against the stop rule of 1% and the 0.04% base rate among the train folders themselves.
- **Surplus and cost**: stragglers exceed n in 16 of 18 mines at n = 160 (fewest 145) and 17 of 18 at n = 80 (fewest 72), so the
  ranker chooses among stragglers and the ctx key keeps 30.5 of 160 (18.6 of 80) laws different from `small` per mine. Extras
  selection takes 0.172 s per mine for ctx against 0.183 s for `small` at n = 160 and 0.072 s for both at n = 80 (the scoring is
  free next to the walk). Job CPU: n = 160 653 s against 648 s; n = 80 352 s against 385 s.
- **Reading**: no effect of at least T detected; the offline gain (Q1, 2.7 captured laws per mine over `small`) does not reach
  held-out M. Limits: the model is fit on n = 319 labelled laws per mine and served on pools of 320 and 640 with different base
  rules; draw 0 is one draw; c1 was chosen after the Q1 numbers were seen.
- **Replication** (salts 4-6, weights fit on salts 7-10, `ctx33-v1-s7-10.txt`; gates `q2-r-c160`, `q2-r-c80`, 0 of 6 arms failed
  each): n = 160: `small` 4591, walk 532.9 M (reproduces the recorded run); ctx 4603, walk 473.1 M; D +12, R 0.888. n = 80: `small`
  5422, walk 243.0 M; ctx 5488, walk 214.7 M; D +66, R 0.884. D is positive at both n, so the rule (D < -T, T >= 76) fails at
  both whatever the redraw spread; the redraws and the equal-work random arms were not run for these salts (ledger ruling).
  Overlap, eval salts 4-6 against the fit set of salts 7-10: 1 of 11519 (0.009%) at n = 160, 1 of 5760 (0.017%) at n = 80. Against
  the salts 4-10 set that the primary weights saw: 25.2% and 33.2%, as expected since salts 4-6 are in it; this is why the
  replication is not independent of the primary (its fit set shares salts 7-10).
- **Reading: Q2 FAILS.** Primary FAIL at both n, replication FAIL at both n (four of four lines). The 33-column context key picks
  different laws from `small` (30 of 160, 19 of 80 per mine) that are no better in held-out M. A null means no effect of at least
  T detected; the Q1 capture gain does not carry to held-out M.

