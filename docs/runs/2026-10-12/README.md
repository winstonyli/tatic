# Runs of 2026-10-12

Raw rows behind the 2026-10-12 sections of `docs/tier-cycle.md`, with the scripts that ran them and the patches of the switches
that were reverted. The sweeps are deterministic, so a row can be regenerated from its commit, patch and environment; the logs
and libraries (43 MB) were not kept.

- `rows/<run>/*.tsv`: the stage files of `driver::sweep` (`mines.tsv`: family, seconds, M; `own`/`cold`/`pooled.tsv`: column 4
  is M) or `m.tsv` of `driver::loop_stream`. Total a run with `bash scripts/sumrows.sh rows/<run>...`.
- `scripts/`: as run, from Git Bash. They expect builds at `$TEMP/bv_<name>.exe` (copies of the `church_bv` test binary,
  `cargo test --release --test church_bv --no-run`) and write to `$TEMP/kk`.
- `patches/`: `probe_promo.patch` (the temporary `ORDER=show|rev|size` switch over the three operand-order sites and
  `PROMOTED_FILE`, which replaces `PROMOTED` with a rule file), `heldout_lookahead.patch` (runners-up chosen by held-out
  finished value). Apply to the commit named below; both still apply cleanly to b7fde44.
- `promo/`: the re-promoted rule sets (round 1, and both rounds) under the `show()` and size-first orders.

| Runs | Build | Script | Result (tier-cycle.md) |
|---|---|---|---|
| `sm0*`, `sm1*` | 930c345 with and without the state memo | `sm_job.sh` | "Rule-set evaluations reuse the last one's memo" |
| `sweep_h_*`, `sweep_sm_*`, `sweep_f1_*`, `sweep_w2_*` | sweeps around 930c345-8979a3f; `sweep_f1_*` is the library the `du*` runs pool | `sm_sweep.sh` (`sweep_h_*`); the others' commands were not recorded | |
| `du_*`, `dufloor_*`, `duheld_*`, `duroot_*`, `dujoin_*`, `duonce_*`, `dunofloor_*` | drop-unit variants, 8979a3f-d19c654 (pooled stage on `sweep_f1_*`) | `du_job.sh` with `TAG` | "Drop units", "Joinability units" |
| `pair_head_*`, `pair_base_*` | HEAD of 5dbf48f against 6ca89b3, same load | `pair_sweep.sh` | 5dbf48f |
| `s3_*`, `s4_*`, `s5_*` | head, and the 2000 drop floor set to 0 (`nofloor`, reverted, no patch kept) | `salt3.sh`, `order_probe.sh`, `nofloor45.sh` | "The floor is still needed" |
| `ord_*` | 465ed76 + `probe_promo.patch`'s `ORDER` part (`ord_def_1`: default order, sanity) | `order_probe.sh` | "Operand order" |
| `np_*` | the same, `ABLATE=promoted` | `order_np.sh` | "Operand order" |
| `do_*` | 740dcd0's parent + own-rule drop units (reverted, no patch kept) | `dropown.sh` | "Drops of the mine's own rules" |
| `fix_*` | 87a2e8e (rivals scored by counting only) | `fixrepro.sh` | "Rivals scored by counting only" |
| `ps_*` | 87a2e8e + `probe_promo.patch`, `PROMOTED_FILE=promo/<order>.rules ORDER=<order>` | `repromote.sh`, `promosweep.sh` | "Operand order" |
| `ho_*` | 87a2e8e + `heldout_lookahead.patch` | `hosweep.sh` | "Runners-up chosen held out" |
| `it0_*`, `it1_*`, `it2_*` | the commit adding `MINES_WARM` (iteration 0 = HEAD; k+1 seeded from k's pooled libraries) | `iterate.sh`, `iterate2.sh` | "Promotion as an iterated sweep" |
| `npit0_*`-`npit3_*` | the same, `ABLATE=promoted` | `iterate_np.sh` | "From `ABLATE=promoted`" |
| `sq_head_*`, `sq_streq_*` | 22b9280 against structural term equality (before the drop-matching fix), same load | `streq_pair.sh` | "Structural term equality" |
| `pl_head_*`, `pl_plain_*` | 2bf9c7a against e49535f (decisions by plain Booleans), same load | `plain_pair.sh` | "Decisions that read kernel terms" |
| `pp_plain_*`, `pp_plans_*` | e49535f against proof plans, same load | `plans_pair.sh` | "Proof plans" |
| `gc_head_*`, `gc_gates_*` | e1d28d9 against the gate constants built once per interning generation, same load | `gates_pair.sh` | "Gate constants built once per generation" |
