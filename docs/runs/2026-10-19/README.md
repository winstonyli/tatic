# Runs of 2026-10-19

Rows behind `docs/tier-cycle.md`, "The three levers, tried". Each run is recorded in `docs/runs.md` with its raw folder
under `%LOCALAPPDATA%\claude-runs\tatic\<run id>`. Builds were `cargo test --profile sweep --test church_bv --no-run`,
copied to `$TEMP/bv_<name>.exe`: `bv_riv` (2280c01, the same code as db442d8), `bv_spine` (eabd8d5, the spine deferral)
and `bv_back` (07e3416, with the undoing step skipped). The scripts are 2026-10-18's (`quiet_ab.sh`).

- `patches/undo_skip.patch`: commit 07e3416, dropped from the branch; it applies on eabd8d5.

| Run | Build | Script | Result |
|---|---|---|---|
| `2026-10-19-spine-quiet` | `bv_riv`, `bv_spine`, `bv_back` | `quiet_ab.sh 1 2` | files the same; job CPU 290.6+312.3 / 274.0+252.4 / 270.1+289.3 s under others' 10-20% |
| `2026-10-19-spine-main-quiet` | `bv_riv`, `bv_spine` | `quiet_ab.sh 1 4` | files the same; job CPU won 4/4, at 3-5% others 249.5/229.5 and 232.6/212.8 s (-8%) |
| `2026-10-19-spine-back-quiet` | `bv_spine`, `bv_back` | `quiet_ab.sh 1 4` (4 clean of 5) | files the same; at 5-6% others 227.2/239.1, 232.6/228.5, 226.9/238.3 s |
| `2026-10-19-spineprof` | `bv_spineprof` (cc5650e + 2026-10-18's `lazy_prof.patch`) | `lazy_prof.sh` | 249.5 k busy samples; the visit 30.7%, `Spine::make` 5.6%, `Term::op` 11.4%, `match_pat` 17.7% |
| `2026-10-19-mainprof3` | `bv_mainprof` | `lazy_prof.sh`, back to back with `-spineprof` | 241.1 k busy samples; the visit 40.2%, `place` 12.7%, `Term::op` 17.9% |
