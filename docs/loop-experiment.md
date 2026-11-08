# The end-to-end loop experiment

An experiment on whether rule mining can run alongside execution: laws are
served in batches, rules are mined from each served batch, and the next batch
is served under the rules mined so far. The metric M is the number of laws that
still need a whole-term machine proof. The measured results are in
`docs/tier-cycle/README.md`, with raw rows and the scripts that produced them under
`docs/runs/`.

- The laws come from the streams: `streams::stream_sequence(salt)`, the operator-set
  streams round-robin, built once per process and salt; a phase is a residue class
  mod `STREAM_STRIDE`. Held-out laws are in `crates/church-bv/data/held_*.txt`. The
  design is in the spec
  [`2026-10-22-class-table-normal-form-design.md`](superpowers/specs/2026-10-22-class-table-normal-form-design.md),
  §9.
- The driver is `church-bv loop-stream` (`crates/church-bv/src/driver.rs`; also the ignored test `driver::loop_stream`):
  `LOOP_MODE=none|ref|loop LOOP_OUT=<dir> church-bv loop-stream` (build with `cargo build -p church-bv [--profile sweep]`).
  `none` only serves, `ref` mines once on the whole stream, `loop` mines after
  each batch. It writes `<dir>/m.tsv` (one row per batch: M, laws, rules in
  force, seconds and the join's counts). The module comment documents all
  options (`B`, `K`, `OFFSET`, `SPHASE`, `WARM_RULES=<file>`, ...).
  `church-bv sweep` runs three cold
  loops on phases 1-3 into `SWEEP_OUT=<dir>`; `scripts/gate/streams_ab.sh` is the gate
  built on it (A/B per salt, plus held-out M under each loop's rules).
- The miner (`search::rule_miner` in `crates/church-bv/src/search.rs`) takes its
  settings from `RULEMINER_*` environment variables; the driver passes its laws
  as a file (`RULEMINER_LAWFILE`). Two options: `NODUPLHS` (no candidate whose left side
  already has a rule in force; on by default, `0` turns it off) and `GUARD=<k>`
  (also score k laws that are already machine-free, so a rule that fixes
  stragglers but breaks those is not chosen; default 120, `0` turns it off).
- Which parts of the rewriter, prover, miner and loop are learned and which are
  fixed by hand, with the evidence per part: `docs/learned-vs-fixed.md`.

Results on the streams, with their A/A baseline, are in `docs/tier-cycle/`
("The gate on the streams and its A/A baseline"). The earlier results on the
hand-built three-variable families (`add3`, `sbo3`, `cmp3d`, `mix3`, the pooled
and cross-family libraries) were in `docs/loop-result.md`, deleted on 2026-10-26
(`git show 00a21d9:docs/loop-result.md`); the code that ran them was deleted
with the families (tag `v0.2.0` has it).

The planning notes are in `docs/superpowers/` and the dated run scripts in
`docs/runs/`; only `scripts/experiments/`, with its logs, is not part of the
repository (`README.md`, "License and development notes").

