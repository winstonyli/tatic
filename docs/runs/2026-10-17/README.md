# Runs of 2026-10-17

Rows behind `docs/tier-cycle.md`, "The bounded join removes the floor". Each run is recorded in `docs/runs.md` with its raw
folder under `%LOCALAPPDATA%\claude-runs\tatic\<run id>`. Builds were `cargo test --profile sweep --test church_bv
--no-run`, copied to `$TEMP/bv_join*.exe`. Each script writes into `$RUN_DIR` (or `kk.sh`'s directory).

- `scripts/join_cold.sh <exe> <salt>...`: sweeps of one build with the join on and with `ABLATE=join`, the two arms of a
  salt side by side. Stages come from `$STAGES` (default `cold`). Prints M per stage file, the exit code and the wall
  seconds per arm.
- `scripts/join_cap.sh <exe> <salt>...`: full sweeps at `JOIN_VISIT` 5000, 1000, 300 and with the join off, two at a time.
- `patches/join_trace.patch`: the throwaway `JOIN_TRACE=<path>` line per search (found, reached terms, microseconds, the
  pair). It applies to 8d5b29d. The probes made the same two edits by hand on 43c6d8f and cad853e.
- `rows/<run id>.txt`: each run's `out.log`. `rows/join-final_<arm>_<stage>.tsv`: that run's stage files, salt first, then
  the sweep's columns (`mines`: family, seconds, M, rules, exhausted; the loop stages: family, stride-phase, source, M,
  M per batch, rules, seconds, exhausted).

| Run | Build | Script | Result |
|---|---|---|---|
| `2026-10-17-join-cold` | 43c6d8f (cap 5000, no index) | `join_cold.sh`, cold only, salts 1-10 | cold M 1530 against 4380 |
| `2026-10-17-join-full` | 43c6d8f | `join_cold.sh` with `STAGES="mines own cold pooled"`, salts 1-2 | own 0/0 against 74/102, pooled 2/0 against 58/99 |
| `2026-10-17-join-trace` | 43c6d8f, cad853e + `join_trace.patch` | by hand: `SWEEP="mines:cmp3d cold:cmp3d"`, salt 1 | 6.1 to 2.9 µs per reached term |
| `2026-10-17-join-cap` | cad853e | `join_cap.sh`, salts 1-2 | cap 1000 chosen |
| `2026-10-17-join-final` | 8d5b29d (cap 1000) | `join_cold.sh` with `STAGES="mines own cold pooled"`, salts 1-10 | the section's table |

Later the same day, on the miner's view of the join (`docs/tier-cycle.md`, "The miner sees the join", and
`docs/decisions/2026-10-17-monotone-join.md`). Builds were copied to `$TEMP/bv_jtrace3.exe`, `bv_jmemo.exe`,
`bv_jdepth.exe` and `bv_jsticky.exe`; the baseline is `bv_join3.exe` (8d5b29d).

- `scripts/join_trace.sh <exe> <salt>`: one full sweep with `JOIN_TRACE` from `patches/join_trace2.patch` (the line adds
  the rule set's fingerprint, n and k).
- `scripts/join_ab.sh <exe_a> <exe_b> <salt>...`: full sweeps of two builds side by side per salt, `$ENV_B` for b only.
- `scripts/join_depth.sh <exe> <salt> <depth>...`: full sweeps with `JOIN_DEPTH=<d>` (0 = the visit cap) and the trace,
  from `patches/join_depth.patch` (against 0c383d6, with the exact miner).
- `patches/join_check.patch`: `JOIN_CHECK`, re-running the search on every memo hit of a met plan and counting flips.

| Run | Build | Script | Result |
|---|---|---|---|
| `2026-10-17-join-trace2` | 0c383d6 + `join_trace2.patch` | `join_trace.sh`, salt 1 | 40214 searches, 90% met; 23419 distinct (rule set, pair), 3624 distinct pairs |
| `2026-10-17-join-memo` | 8d5b29d against the exact miner | `join_ab.sh`, salts 1-10 | mines 2 to 0, own 13 to 26, cold 1568 to 1563, pooled 33 to 36 |
| `2026-10-17-join-depth` | the exact miner + `join_depth.patch` | `join_depth.sh`, salt 1, depths 0 2 3 4 | the decision file's probe table |
| `2026-10-17-join-sticky` | 8d5b29d against option 1 (+ `join_check.patch`, off) | `join_ab.sh`, salts 1-10 | M and rules those of the exact miner on every salt; mine 33 s blind, 46 s option 1 |
| `2026-10-17-join-sticky-ablate` | the same two | `join_ab.sh` with `ABLATE=join` | identical rows |
| `2026-10-17-join-sticky-flips` | option 1 against itself, `ENV_B=JOIN_CHECK=1` | `join_ab.sh`, salts 1-10 | no flips in at least 230000 met-plan hits; rows identical |

The join's cost (`docs/tier-cycle.md`, "The miner sees the join", its last bullets). Build `$TEMP/bv_jtime.exe`: the
search time in `JoinCost`, plus `patches/no_bound.patch` (`RULEMINER_NO_BOUND`, scoring every candidate; reverted).

- `scripts/join_cost.sh <exe> <sweep dir> <salt>...`: `proof_cost_split` on every served cmp3d batch of a sweep's
  loops, join on and off, into `cost.tsv`.
- `scripts/join_time.sh <exe> <salt> <reps>`: the cmp3d ref mine with the gain bound on and off, alternated.

| Run | Build | Script | Result |
|---|---|---|---|
| `2026-10-17-join-proof-cost` | `bv_jtime.exe` | `join_cost.sh` on `2026-10-17-join-sticky`, salts 1-5 | per joined law: build 7.7 against 21.5 ms for the machine proof, check 0.49 against 0.47 ms |
| `2026-10-17-join-time` | `bv_jtime.exe` | `join_time.sh`, salt 6, 4 reps; then by hand two `runs run` (job CPU, `job.txt`) and two PowerShell runs (`cpu.txt`, process CPU 0: the mine runs in a child) | same rules either way; join searches 84% of the stage's CPU, failed ones 26% |
