### Kernel cost calibrated against time (2026-10-10)
`law_work_report` now writes each counted slot separately for building (`b_`) and checking (`c_`), plus the terms built while
checking, and also runs in the normal build (counts zero, uninstrumented times). Per-law time (normal build, pinned to two cores,
the smaller of two runs; the machine was not quiet, 16-58% load from other programs) was fitted against the per-law counts (feature
build) by non-negative least squares on half of the 1,200 rows (sbo3 and cmp3d, own library and none), and tested on the other
half. Held-out error (sum of absolute errors over total time): 18% for the fit, 55% for raw visits with one weight. The weights
are collinear and not individually meaningful; building's `shift` visits got weight 0, as the `bool0` timing found.

| family, library | M | time s | fitted s | total visits (M) |
|---|---|---|---|---|
| sbo3, none | 92 | 10.9 | 13.5 | 10.6 |
| sbo3, own | 17 | 4.8 | 7.0 | 6.1 |
| cmp3d, none | 118 | 50.8 | 51.7 | 37.7 |
| cmp3d, own | 31 | 46.2 | 48.9 | 55.1 |

- **By time the own library is cheaper on both families** (sbo3 2.3x, cmp3d 1.1x), the direction M gives; raw visits ranked
  cmp3d's library the other way. cmp3d gains little because of the cycle above.
- **Decision: M stays the miner's objective.** It agrees in direction with time on both families, is deterministic, and can be
  counted without building proofs (`RULEMINER_FAST`), which a fitted cost cannot (it needs the feature build, about 4x slower, and
  weights tied to this machine). The fitted cost is a check to report beside M, not an objective. The cmp3d gap between M's cut
  (3.8x) and time's (1.1x) is a defect in the library (the cycle), not in M.

The cmp3d gap is now smaller (time 1.37×, see "Per-side rule budget" above), and the cycles that cost each exhausted law 200 steps
are cut (see "Cycle cut" below).

