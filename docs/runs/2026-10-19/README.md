# Runs of 2026-10-19

Rows behind `docs/tier-cycle.md`, "The three levers, tried". Each run is recorded in `docs/runs.md` with its raw folder
under `%LOCALAPPDATA%\claude-runs\tatic\<run id>`. Builds were `cargo test --profile sweep --test church_bv --no-run`,
copied to `$TEMP/bv_<name>.exe`: `bv_riv` (2280c01, the same code as db442d8), `bv_spine` (eabd8d5, the spine deferral),
`bv_back` (07e3416, with the undoing step skipped) and `bv_room` (bce3407, the size need in the index), `bv_shape` (fcef618, the index down to the grandchildren), `bv_fits` (7e4f037, the operands' needs alone, branchless), `bv_pairs` (75d4b99, the depth-2 pairs), `bv_lazy` (cadb700, the pairs compared only once the shapes fit). The scripts are 2026-10-18's (`quiet_ab.sh`), except `scripts/order_fx.py` (the order within a round, from the rows).

- `patches/undo_skip.patch`: commit 07e3416, dropped from the branch; it applies on eabd8d5.
- `patches/match_fail.patch`: the counters of `-match-fail`; it applies on bce3407.
- `patches/rep_var.patch`: the counters of `-rep-var`, `match_fail.patch`'s and five more; it applies on 7e4f037.
- `patches/shallow_eq.patch`: the counters of `-shallow-eq`, `match_fail.patch`'s and five more; it applies on 7ad582e.
- `patches/op_callers.patch`: the counters of `-op-callers` (`match_fail.patch`'s plumbing, `Term::op` calls by origin and outcome); it applies on 3f2265b.
- `patches/walk_repeat.patch`: `op_callers.patch` plus the counters of `-walk-repeat` (subterms walked again in a search); it applies on d1599dd.

| Run | Build | Script | Result |
|---|---|---|---|
| `2026-10-19-spine-quiet` | `bv_riv`, `bv_spine`, `bv_back` | `quiet_ab.sh 1 2` | files the same; job CPU 290.6+312.3 / 274.0+252.4 / 270.1+289.3 s under others' 10-20% |
| `2026-10-19-spine-main-quiet` | `bv_riv`, `bv_spine` | `quiet_ab.sh 1 4` | files the same; job CPU won 4/4, at 3-5% others 249.5/229.5 and 232.6/212.8 s (-8%) |
| `2026-10-19-spine-back-quiet` | `bv_spine`, `bv_back` | `quiet_ab.sh 1 4` (4 clean of 5) | files the same; at 5-6% others 227.2/239.1, 232.6/228.5, 226.9/238.3 s |
| `2026-10-19-spineprof` | `bv_spineprof` (cc5650e + 2026-10-18's `lazy_prof.patch`) | `lazy_prof.sh` | 249.5 k busy samples; the visit 30.7%, `Spine::make` 5.6%, `Term::op` 11.4%, `match_pat` 17.7% |
| `2026-10-19-mainprof3` | `bv_mainprof` | `lazy_prof.sh`, back to back with `-spineprof` | 241.1 k busy samples; the visit 40.2%, `place` 12.7%, `Term::op` 17.9% |
| `2026-10-19-match-fail` | `bv_mprobe2` (bce3407 + `patches/match_fail.patch`) | 2026-10-18's `match_count.sh` salt 1 | 3.17 G `match_pat` calls, 31% match; failures 969 M at grandchildren, 934 M a repeated variable, 270 M leaf roots, 19 M deeper |
| `2026-10-19-room-quiet` | `bv_spine`, `bv_room` (bce3407) | `quiet_ab.sh 1 4` (4 clean of 5) | files the same; job CPU median 250.5/258.0 s, won 2/4: no gain |
| `2026-10-19-match-fail-shape` | `bv_mprobe3` (fcef618 + `patches/match_fail.patch`) | 2026-10-18's `match_count.sh` salt 1 | files the same as `-match-fail`; `match_pat` calls 3.17 G to 1.93 G, the same 977 M matches |
| `2026-10-19-shape-quiet` | `bv_room`, `bv_shape` (fcef618) | `quiet_ab.sh 1 8` (8 clean of 11) | files the same; job CPU median 242.5/223.1 s (-8.2%), won 8/8 |
| `2026-10-19-shapeprof` | `bv_shapeprof` (fcef618 + 2026-10-18's `lazy_prof.patch`) | `lazy_prof.sh` | 234.2 k busy samples; `match_pat` 14.9% self, the index filter 5.6%, `Term::op` 13.0% inclusive |
| `2026-10-19-rep-var` | `bv_rprobe` (7e4f037 + `patches/rep_var.patch`) | 2026-10-18's `match_count.sh` salt 1 | files the same as `-match-fail`; 987 M calls of repeating patterns, 934 M fail on the binding, visiting 4.15 G of 7.96 G pattern nodes; a pre-check walks 2.92 G |
| `2026-10-19-fits-quiet` | `bv_shape`, `bv_fits` (7e4f037) | `quiet_ab.sh 1 8` (8 clean of 9) | files the same; job CPU median 206.8/207.3 s, won 3/8: no gain |
| `2026-10-19-shallow-eq` | `bv_xprobe` (7ad582e + `patches/shallow_eq.patch`) | 2026-10-18's `match_count.sh` salt 1 | files the same as `-match-fail`; depth-2 same-variable pairs reject 917 M of 934 M binding failures; `op(x, x)` roots 311 M |
| `2026-10-19-fitsprof` | `bv_fitsprof` (7ad582e + 2026-10-18's `lazy_prof.patch`) | `lazy_prof.sh` | loaded machine (CPU 60% at start), shares only: `match_pat` 13.9% self, the filter 4.7% |
| `2026-10-19-pairs-quiet` | `bv_fits`, `bv_pairs` (75d4b99) | `quiet_ab.sh 1 8` (8 clean of 8) | files the same; job CPU median 210.9/203.6 s, won 5/8 (all 4 run first); the mean over the two orders -5.7 s (-2.7%), the second arm +6.7 s |
| `2026-10-19-match-fail-pairs` | `bv_pprobe` (75d4b99 + `patches/match_fail.patch`) | 2026-10-18's `match_count.sh` salt 1 | files the same as `-match-fail`; `match_pat` calls 1.93 G to 1.01 G, binding failures 934 M to 16 M, the same 977 M matches |
| `2026-10-19-pairsprof` | `bv_pairsprof` (75d4b99 + 2026-10-18's `lazy_prof.patch`) | `lazy_prof.sh` | loaded again during the run (searches 67.2 s against 55.4 s), shares only: `match_pat` 8.0% inclusive (14.9%), `PatIndex::get` 6.8% (2.2%) |
| `2026-10-19-lazy-quiet` | `bv_pairs`, `bv_lazy` (cadb700) | `quiet_ab.sh 1 8` (8 clean of 8) | files the same; job CPU median 202.0/195.6 s, won 4/8; the mean over the two orders -5.0 s (-2.5%), running second +7.6 s |
| `2026-10-19-op-callers` | `bv_oprobe` (3f2265b + `patches/op_callers.patch`) | 2026-10-18's `match_count.sh` salt 1 | files the same as `-match-fail`; 787 M `Term::op` calls in the join: 532 M new steps' `subst_pat` (92.5% cache hits), 201 M spines (66.4%), 54 M other; 0.2% insert |
| `2026-10-19-lazyprof` | `bv_lazyprof` (cadb700 + 2026-10-18's `lazy_prof.patch`) | `lazy_prof.sh` | taken under load without waiting (CPU 28% at start), shares only: the index's self 8.4% (8.8%), mostly the filter closure now; `match_pat` 8.1% self, `Term::op` 13.4% inclusive |
| `2026-10-19-lazy-aa-together` | `bv_lazy` twice | `QUIET_AB_FLAGS=--together quiet_ab.sh 1 8` (8 clean of 8) | files the same; A/A job CPU median 281.3/281.0 s, over the two parts -0.8 s, part 2 +1.0 s; sd 3.2 s (1.1%) within a part order against `-lazy-quiet`'s 1.6 s (0.8%): noisier, and each run +44% job CPU |
| `2026-10-19-lazy-aa-q10` | `bv_lazy` twice | `QUIET_AB_FLAGS="--quiet-secs 10" quiet_ab.sh 1 8`, stopped after 9 rounds | files the same; 1 clean of 9 in 36 min, others at 12-45% within the runs: inconclusive against 60 s |
| `2026-10-19-walk-repeat` | `bv_wprobe` (d1599dd + `patches/op_callers.patch` + `patches/walk_repeat.patch`) | 2026-10-18's `match_count.sh` salt 1 | 1436 M subterm visits in the join, 82.3% already walked in the same search; 59.3% of 1006 M `match_pat` calls at those |
