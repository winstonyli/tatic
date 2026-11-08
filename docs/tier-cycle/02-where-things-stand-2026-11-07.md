## Where things stand (2026-11-07)
- **The loop** (`driver::sweep`, `driver::run_loop`, `search::rule_miner`): a loop mines rewrite rules on a batch of laws,
  then serves the next batch under them, and M (laws still needing a whole-term machine proof) falls as rules arrive.
- **The laws** come from operator-set streams over three variables (`stream_laws`, `stream_sequence`; the class-table
  spec's decisions 8 and 11) since 2026-10-23, when the hand-built three-variable families were deleted ("The families
  deleted"). Results dated before 2026-10-23 are on families; "Metrics" below keeps their terms.
- **Serving** rewrites each node bottom-up, taking the learned class table's step where the table knows the node
  ("Phase 2 in the rewriter") and the mined rules elsewhere; then the fixed prover steps and a bounded join of the two
  sides run ("The bounded join removes the floor"), and what is left takes a whole-term machine proof.
- **The gate** (`scripts/gate/streams_ab.sh`, run through `scripts/gate/gate.sh`) runs two builds' loops per salt and
  compares their rules, M, held-out M per band and work counts ("The gate on the streams and its A/A baseline", "Work
  counts as the gate's cost", "The frontier on the gate"). Its `peakproc` moves in arena-sized steps between runs of one
  exe ("The streams and the gate", the `peakproc` bullet).
- **The explorer is not learned.** Each mine takes its own `EXTRAS_N` (319) laws from the stream sequence grown to the
  held-out sizes, minus served and held-out laws and their twins ("Count and slicing"). Mining on more laws beats ranking
  them ("More laws beat any ranking"). v0.6 (tagged 2026-10-31) tried learned selection and found none that beats random:
  a count-feature scorer ("A learned scorer over the extras") and a context model ("A context model over the extras";
  its primary run, "Q2 primary run", was null). Its answer was a fixed rule, selection by the mine's own verdicts
  (`EXTRAS_SELECT=small`), which helps at n 80-160 only, below the default 319, so the default draw is unchanged.
- **The belief layer is not built.** Its calibration milestone stopped at its first gate: no screen-passing claim was
  refuted, so there was nothing to rank ("The belief layer's calibration milestone stops at its first gate"). Its
  reframing as cost prediction was not run (`PARKED.md`, "Belief layer stage 2"). No GPU model exists (goal 3,
  `ROADMAP.md`). In this domain the kernel's cheap checks decide almost every claim in milliseconds, which leaves a model
  little to save (inference from these results, under survey since 2026-11-07).
- **Laws uniform in the width** (goal D): `wfold.rs` proves stream laws (no `shr1` or `mul`, `lt` only at the root) at
  every width with no per-law code, built as kernel terms since the w1 port ("One generator proves stream laws at all
  widths"). Nothing consumes a uniform law yet (`PARKED.md`, "Search alongside execution, and laws uniform in the width").
- **The JIT** (goal 1) compiles a fragment of higher-order terms once their compiled form is kernel-proved equal ("The JIT
  and the target machine"); the mined rules find no work in its programs ("Other ways to join the JIT and the loop").
- **The workspace** has four crates since 2026-11-04: `tatic-kernel` (the trusted kernel, which cannot import `tatic`),
  `church-bv` (the loop, the miner and the provers), `tatic` (the JIT) and `tatic-rng` (the seeded generator); `docs/TOUR.md` maps them.
- **Counting work:** a retired-instruction count replaces timing where a verdict only needs "does less work"; with large
  OS pages it wanders, for reasons traced in "Why a retired-instruction count wanders".
- **Raw rows**, run scripts and the patches of reverted switches are kept per day under `docs/runs/<date>/` (from
  2026-10-12); runs from 2026-10-17 on have a row each in `docs/runs.md`. A `scripts/` path cited below that no longer
  exists is in that day's `docs/runs/<date>/scripts/`, or in git history (`git log --all --oneline -- <path>`), except
  `cpu_ab.ps1` and `cpu_arms.ps1`, never committed; `tools/runs` replaced them.
