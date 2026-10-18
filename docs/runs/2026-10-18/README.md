# Runs of 2026-10-18

Rows behind `docs/tier-cycle.md`, "Lazy join steps, and sweeps in lanes". Each run is recorded in `docs/runs.md` with its
raw folder under `%LOCALAPPDATA%\claude-runs\tatic\<run id>`. Builds were `cargo test --profile sweep --test church_bv
--no-run`, copied to `$TEMP/bv_<name>.exe`: `bv_jprobe` (6e621ca + `patches/join_count.patch`), `bv_lanes` (397dcf2's
tree: lanes, eager join), `bv_lazy` (7ee55b3's tree before its last refactor) and `bv_lazy2` (7ee55b3). The rows of the
morning's generator rounds are in `docs/runs/2026-10-17/README.md`.

- `patches/join_count.patch`: the probe's counters (neighbours built, new and already reached; spine rebuilds; the
  operator-invariant cut) and their `RULEMINER join` print line. It applies to 6e621ca.
- `scripts/lanes_check.sh <exe> <salt>`: one sweep per lane count in `LANES` (default `1 2`) per arm in `ARMS` (default
  `all cold`: the default SWEEP with `ABLATE=gen`, and `SWEEP=cold` with extras), wall seconds, and whether the arm's
  first two sweeps agree (`../2026-10-17/scripts/same_arms.sh`). Runs with a single sweep per arm print a verdict line
  against a sweep they did not make; their rows compare by hand.
- `scripts/history_check.sh <exe> <salt>`: `SWEEP=cold:cmp3d` at 1 lane, 3 lanes and 1 lane with `LEMMA_RECHECK=1`, and
  which loops' rules agree with the 3-lane run.
- `rows/<run id>.txt`: each run's `out.log`. `rows/lanes-check_cold_l{1,2}_cmp3d_2_mine_0.log`: the first mine of the
  loop that differed between `-lanes-check`'s sweeps.

| Run | Build | Script | Result |
|---|---|---|---|
| `2026-10-18-join-count` | `bv_jprobe` | by hand: `SWEEP=cold:cmp3d`, salt 6 | 58% of neighbours already reached; invariant cut 0 |
| `2026-10-18-lanes-check` | `bv_lanes` | `lanes_check.sh` (its first version), salt 1 | cold 386 s at 1 lane, 236 s at 2, one loop differs |
| `2026-10-18-cold-repeat` | `bv_lanes` | `ARMS=cold LANES=1` | 366 s, as the 1-lane sweep |
| `2026-10-18-loop-history` | `bv_lanes` | `history_check.sh` | no history through worker or lemma file |
| `2026-10-18-cold-l2-repeat` | `bv_lanes` | `ARMS=cold LANES="2 2"` | 223 and 199 s, both as the 1-lane sweep |
| `2026-10-18-lazy-join` | `bv_lazy` | `LANES=1` | cold 154 s, every file as the eager join's |
| `2026-10-18-eager-join-ab` | `bv_lanes` | `ARMS=cold LANES=1` | cold 331 s, the A/B for `-lazy-join` |
| `2026-10-18-lazy-lanes2` | `bv_lazy2` | `LANES=2` | cold 99 s, every file as the eager join's |
