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
