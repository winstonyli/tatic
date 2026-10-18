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
- `patches/score_pool_join.patch`: the `score-pool` spike (96b6e7e) ported onto c87573b: scoring workers alive for the
  whole search, their memo carried across rounds (reverted).
- `scripts/join_prof.sh <exe>` with `patches/join_prof.patch` (`driver::sweep_prof`, a throwaway test setting SALT=6
  SWEEP=mines:cmp3d, since `profile.ps1` passes no environment): a samply profile of that mine, built with
  `CARGO_PROFILE_SWEEP_DEBUG=true`.
- `scripts/gen_src.sh <exe> <salt>...`: cold sweeps plain and with `MINE_EXTRA` from each `MINE_SOURCE` (stream, grammar),
  one after another; prints mined-batch M per family.
- `scripts/gen_cost.sh <exe> <salt>...`: the same per arm of `$ARMS` (default `half quarter pad nopad`; also `plain`,
  `stream`, `grammar`): grammar at half and a quarter of the counts, and `GEN_PAD=pad|nopad` at full counts. Prints M per
  family, rules and summed loop seconds.
- `scripts/pad_strip.py <run dir>`: strips the padding from each `pad_*` loop's extras and counts how many are twins of a
  served law (`tier-cycle.md`, "Why padding laws pay"). `scripts/pad_files.py <run dir> <out>` writes the probe's extras
  files from the same: `full`, `untwin` and `control` (the inputs are kept in
  `%LOCALAPPDATA%\claude-runs\tatic\2026-10-17-gen-twin-inputs`). Run each as `python -P <script> ... < /dev/null`.
- `scripts/gen_twin.sh <exe> <inputs> <salt>...` with `patches/extra_file.patch` (`MINE_SOURCE=file`, reverted): cold
  sweeps per arm reading the extras from those files.
- `scripts/twin_wide.py <run root> <arm prefix>...`: counts each arm's extras that twin a served law under three
  normalizations (the strip on the extras, the strip on both sides, two-leaf value classes on both sides) and the laws
  trivial after normalizing (`tier-cycle.md`, "One filter for every source"). `scripts/wide_files.py <out>
  <run root>/<prefix>...` writes `gen_twin.sh` inputs from the class normalization: `<prefix>_full`, `<prefix>_class`,
  and for pad `pad_notriv` and `pad_ctl` (kept in `%LOCALAPPDATA%\claude-runs\tatic\2026-10-17-gen-wide-inputs`).
- `scripts/gen_prof.sh <exe>` with `patches/gen_prof.patch` (on `extra_file.patch`; `driver::sweep_prof`, a throwaway test
  setting salt 6, `cold:cmp3d` and the nopad_class extras files): a samply profile of that loop, built with
  `CARGO_PROFILE_SWEEP_DEBUG=true`. `scripts/prof_incl.py <run dir>`: inclusive frames and the callers of `Term::op`.
- `scripts/op_cache.sh <exe>` with `patches/op_cache.patch` (the probe build: `OP_CACHE_BITS`, 0 for off, and an
  `OPPROBE` line counting `Term::op` calls, new nodes and the join's share): `runs time` over 5 cache sizes.

| Run | Build | Script | Result |
|---|---|---|---|
| `2026-10-17-join-proof-cost` | `bv_jtime.exe` | `join_cost.sh` on `2026-10-17-join-sticky`, salts 1-5 | per joined law: build 7.7 against 21.5 ms for the machine proof, check 0.49 against 0.47 ms |
| `2026-10-17-join-pool` | `bv_jtime.exe` against it + `patches/score_pool_join.patch` (`bv_jpool.exe`) | `join_ab.sh`, salts 1-10 | M and rules equal; mine join searches -3.4%, mine time 52 s both |
| `2026-10-17-join-prof` | c87573b + `join_prof.patch`, debug info | `join_prof.sh` | nothing: `-File` passed the test args as one string, 0 tests ran |
| `2026-10-17-join-prof2` | the same | `join_prof.sh` (`-Command`) | `Term::op` 43% self + 11% shard lock; callers `join_steps` 37%, `subst_pat` 21% |
| `2026-10-17-op-cache` | c87573b + `op_cache.patch` (`bv_opcache.exe`) | `op_cache.sh`, salt 6 cmp3d, 3 clean rounds | job CPU 25.8 s off, 16.9 s at 2^16 slots; rules equal in all 25 runs |
| `2026-10-17-op-cache-ab` | `bv_jtime.exe` against the cache (`bv_opc.exe`) | `join_ab.sh`, salts 1-10 | all 2430 stage, rules and law files equal (time columns aside); wall 86 to 77 s summed, mines 35 to 30 s |
| `2026-10-17-gen-src` | da775e7 + `grammar_laws`, `extra_laws` (`bv_gen.exe`) | `gen_src.sh`, salts 1-10 | mined-batch M plain 120, stream 29, grammar 12; batch 0 1443 in every arm; rules 640 / 1163 / 1889 |
| `2026-10-17-gen-cost` | 4346cda + `GEN_PAD`, `GEN_LAWS` (`bv_gen2.exe`) | `gen_cost.sh`, salts 1-10 | M half 33, quarter 64, pad 16, nopad 9; rules 1352 / 1012 / 1220 / 2483; loop s 229 / 67 / 166 / 1373 |
| `2026-10-17-gen-salts` | the same | `gen_cost.sh` with `ARMS="plain stream grammar pad"`, salts 11-20 | M plain 101, stream 15, grammar 16, pad 11; batch 0 1408 in every arm; loop s 2 / 110 / 673 / 204 |
| `2026-10-17-gen-twin` | b492165 + `extra_file.patch` (`bv_padfile.exe`) | `gen_twin.sh`, salts 1-10 | M full 16 (all 90 rule files equal `-gen-cost` pad's), untwin 30, control 14 |
| `2026-10-17-gen-wide` | the same | `gen_twin.sh` with `ARMS="pad_class pad_notriv pad_ctl stream_full stream_class grammar_full grammar_class"`, salts 1-10 | M pad_class 40, pad_notriv 42, pad_ctl 83, stream 31 / class 29, grammar 12 / class 21; loop s 51 / 49 / 5 / 86 / 40 / 413 / 359 |
| `2026-10-17-gen-nopad` | the same | `gen_twin.sh` with `ARMS=nopad_class`, salts 1-10 | M 10 (cmp3d 9, sbo3 1), rules 2478, loop s 1043; against stream_class better 6, equal 4 |
| `2026-10-17-gen-prof` | a5ade34 + `extra_file.patch` + `gen_prof.patch`, debug info | `gen_prof.sh` | join 89.5% inclusive; `Term::op` 43.8% self (from `join_steps` 29.8%, `subst_pat` 13.7%); frames in `rows/2026-10-17-gen-prof.txt` |
| `2026-10-17-join-time` | `bv_jtime.exe` | `join_time.sh`, salt 6, 4 reps; then by hand two `runs run` (job CPU, `job.txt`) and two PowerShell runs (`cpu.txt`, process CPU 0: the mine runs in a child) | same rules either way; join searches 84% of the stage's CPU, failed ones 26% |
