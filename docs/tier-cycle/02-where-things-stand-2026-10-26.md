## Where things stand (2026-10-26)
- **The loop** (`driver::sweep`, `driver::run_loop`, `search::rule_miner`): a loop mines rewrite rules on a batch of laws,
  then serves the next batch under them, and M (laws still needing a whole-term machine proof) falls as rules arrive.
- **The laws** come from operator-set streams over three variables (`stream_laws`, `stream_sequence`; the class-table
  spec's decisions 8 and 11) since 2026-10-23, when the hand-built three-variable families (add3, sbo3, cmp3d, mix3, u3)
  were deleted ("The families deleted"); the last families' code (mul, shl, shr, lt) went on 2026-10-26 (00a21d9).
  Results dated before 2026-10-23 are on families; "Metrics" below keeps their terms.
- **Serving** rewrites each node bottom-up, taking the learned class table's step where the table knows the node
  ("Phase 2 in the rewriter") and the mined rules elsewhere; then the fixed prover steps and a bounded join of the two
  sides run ("The bounded join removes the floor"), and what is left takes a whole-term machine proof.
- **The gate** (`scripts/streams_ab.sh`) runs two builds' loops per salt and compares their rules, M, held-out M per band
  and work counts ("The gate on the streams and its A/A baseline", "Work counts as the gate's cost",
  "The frontier on the gate").
- **The explorer is not learned.** Each loop mines on its batches plus extras (`scope_extras`), through the miner's
  greedy candidate pool: each mine its own `EXTRAS_N` (319) laws from the stream sequence grown to the held-out sizes,
  minus served laws and held-out laws and their twins (since 2026-10-28, "Count and slicing"). Mining on more laws
  beats ranking candidates ("More laws beat any ranking"; "Fresh laws of the held-out sizes do as well";
  the `v0.5.0` tag message).
- **Raw rows**, run scripts and the patches of reverted switches are kept per day under `docs/runs/<date>/` (from
  2026-10-12); runs from 2026-10-17 on have a row each in `docs/runs.md`. A `scripts/` path cited below that no longer
  exists is in that day's `docs/runs/<date>/scripts/`, or in git history (`git log --all --oneline -- <path>`), except
  `cpu_ab.ps1` and `cpu_arms.ps1`, never committed; `tools/runs` replaced them.

