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
| `lemma_keys/*.tsv` | 374299b + a temporary `LKEY` line per lemma built (reverted): key hash, exclusive build ns, check ns, kind; cmp3d ref loop, `RULEMINER_FAST=1`, salt 1 | `loop_stream` as in the profile | "Which lemmas repeat" |
| `gc_head_*`, `gc_gates_*` | e1d28d9 against the gate constants built once per interning generation, same load | `gates_pair.sh` | "Gate constants built once per generation" |
| `lcp_head_*`, `lcp_cache_*` | 639cdcd against the trusted lemma cache, same load | `lc_pair.sh` | "A trusted lemma cache per loop" |
| `lfp_head_*`, `lfp_lf_*` | 3ac4e20 against law files from the driver, same load | `lf_pair.sh` | "Law files from the driver" |
| `spp_head_*`, `spp_sp_*` | 99475ac against the two-variable candidate index plus the law sequence kept per salt, same load | `sp_pair.sh` | "The candidate index over two variables" |
| `slp_head_*`, `slp_sl_*` | ed00b7a against one lemma file per sweep, same load | `sl_pair.sh` | "One lemma file per sweep" |
| `bpp_head_*`, `bpp_bp_*` | 514b7a2 against winners proved in the background, same load (rollback check: `spec_rollback.sh`, rows not kept) | `bp_pair.sh` | "Winners proved in the background" |
| `qp_head_*`, `qp_q_*` | 5c4618f against one shared queue for the scoring workers, same load | `q_pair.sh` | "One queue for the scoring workers" |
| `lap_head_*`, `lap_la_*` | 8f348b9 against the ref mines on 6 scoring threads plus lookahead's winners proved in the background, same load | `la_pair.sh` | "Six scoring threads, and lookahead's proofs in the background" |
| `las_head_*`, `las_la_*` | the same two builds one run at a time (la, head on salt 1; head, la on salt 2) | `la_seq.sh` | "Why six threads gave little" |
| `o3s_head_*`, `o3s_o3_*` | e9a8be1 against three rounds kept open, one run at a time (o3, head on salt 1; head, o3 on salt 2) | `o3_seq.sh` | "Three rounds kept open" |
| `vcs_head_*`, `vcs_vc_*` | 84242e0 against winner verdicts kept in the sweep's lemma file (reverted, no patch kept), one run at a time | `vc_seq.sh` | "Winner verdicts kept across the sweep" |
| `dds_head_*`, `dds_dd_*` | 84242e0 against case trees at nv = 9 (`DDMIN` default 10), one run at a time | `dd_seq.sh` | "Case trees at nv = 9" |
| `mos_head_*`, `mos_new_*` | 50ba04f (as the prototype with `OLDMOTIVE=1`) against one shared motive per case tree, one run at a time | `mot_seq.sh` | "One motive for a case tree" |
| `nds_head_*`, `nds_new_*` | 5f65267 (as `bv_wide.exe`: HEAD plus an appended ignored probe test) against the decision-diagram path deleted, one run at a time | `nodd_seq.sh` | "Decision diagrams deleted" |
| `tbs_head_*`, `tbs_new_*` | 51cd960 (as the prototype with `NOTABMEMO=1`) against truth tables built once per generation, one run at a time | `tab_seq.sh` | "Truth tables built once" |
| `sts_head_*`, `sts_new_*` | 4da7e02 against the `gen_memo` helper plus each step once per leaf, one run at a time | `step_seq.sh` | "One builder memo, and each step once per leaf" |
| `ais_head_*`, `ais_new_*` | 01018d6 against `args_id` taking canonical arguments' own addresses, one run at a time | `aid_seq.sh` | "Canonical arguments are not interned again" |
| `bss_head_*`, `bss_new_*` | a1ad219 against `beta_spine` reducing the spine's own head plus `args_id`'s stack buffer, one run at a time | `bsp_seq.sh` | "The spine's head reduced as its own node" |
| `lws_head_*`, `lws_new_*` | 8cd8dfa against the instantiation memo skipping nodes of height ≤ 2, one run at a time | `low_seq.sh` | "Small nodes skip the instantiation memo" |
| `pss_head_*`, `pss_new_*` | 6cd8948 against the node table as a set of node pointers with their hashes, one run at a time | `pset_seq.sh` | "The node table holds node pointers with their hashes" |
| `sls_head_*`, `sls_new_*` | 9fab09a against the memos storing only their results, one run at a time | `slim_seq.sh` | "The memos store only their results" |
| `uss_head_*`, `uss_new_*` | 7fe880f against the last `uses` answer kept in the node header (the per-scope `uses` table deleted), one run at a time | `uslot_seq.sh` | "Per-node facts in the node header" |
| `sms_head_*`, `sms_new_*` | ff3eb86 against one shift memo (`ShiftMemo` deleted; the `cong` builders open their own scope), one run at a time | `smemo_seq.sh` | "One shift memo" |
| `whs_head_*`, `whs_new_*` | 3892f3d against weak head normal forms kept per interning scope in hc's table, one run at a time | `whnf_seq.sh` | "Weak head normal forms kept for the scope" |
| (no rows) | `proof_cost_split` CPU-time A/B of f77238e against a per-scope `conv` pair memo, and against `conv_rc` skipping `==` on canonical pairs (both reverted, no patch kept) | `cpu_ab.ps1` | "`conv` repeats pairs across `def_eq` calls" |
| (no rows) | `proof_cost_split` at 7643319 with a node-header flag for who reads `inst_rec`'s new nodes, plus `inst_get` counters (reverted, no patch kept); and a CPU-time A/B with the instantiation memo off | `cpu_ab.ps1`'s environment, `HCPROBE_FILE`; `cpu_ab.ps1` | "How much of what `instantiate_n` builds is read", "The instantiation memo still pays" |
| (no rows) | `proof_cost_split` CPU-time A/B of 136bbe5 against the instantiation memo keyed by the argument suffix a child uses, and a run of it with lookup and hit counters (both reverted, no patch kept) | `cpu_ab.ps1`; `HCPROBE_FILE` | "The instantiation memo keyed by the arguments a child uses" |
| (no rows) | `proof_cost_split` at a73c6a1 with counters for the pairs `conv` reduces (by side reduced, same head, arguments convertible) and the `App` rule's substitutions (reverted, no patch kept); callers in the 8334948 profile | `cpu_ab.ps1`'s environment, `HCPROBE_FILE`; `prof_callers.py` | "What `conv` reduces, and the type checker's own substitution" |
| (no rows) | `proof_cost_split` at 4bad241 with counters for pairs where `whnf` changed both sides (reverted, no patch kept); samply profile at 4bad241 (profile not kept) | `cpu_ab.ps1`'s environment, `HCPROBE_FILE`; `prof_self.py`, `prof_callers.py` | "The pairs where both sides reduce", "Profile at 4bad241" |
| `cts_head_*`, `cts_new_*` | 8334948 against a `const`-initialized `TABLE` plus interning without moving the node through the table's closure, one run at a time | `ctab_seq.sh` | "Profile at 8334948" (both built) |
| (no rows) | samply profile of `proof_cost_split` at 8334948 (profile not kept), self times, key `instantiate_n(`, `hc::intern(`, `whnf_rc(`, and the node-table lookup's sampled instructions | `prof_self.py`, `prof_callers.py`, `prof_addr.py` | "Profile at 8334948" |
| (no rows) | samply profile of `proof_cost_split` at 0fdd223 (profile not kept), key `hc::intern(`, and self times | `prof_callers.py`, `prof_self.py` | "Profile after the two table changes" |
| (no rows) | `proof_cost_split` at ec49e4c with node-table interns and hits counted per builder call site (`#[track_caller]`, reverted, no patch kept) | `cpu_ab.ps1`'s environment, `HCPROBE_FILE` | "How many builder inputs the caller already holds" |
| `cap/*.txt` | `mul_conjecture_miner` (`MULMINER_MAX=7`) on 5f65267 (old) against 0cb4e6c (head), one run at a time | `cap_ab.sh` | "Decision diagrams deleted" |
| (no rows) | samply profile of `proof_cost_split` at af20655 (profile not kept), scopes `tree_proof` and `lemma_n` | `prof_cases.py` | "The builder side is about 8%" |
| (no rows) | samply profile of `proof_cost_split` at 1f4db8b (profile not kept), key `hc::intern(` and `reserve_rehash` (`raw`) | `prof_callers.py` | "Where the node table's time goes" |
| (no rows) | the same at 849bf22, also key `Scope*)` | `prof_callers.py` | "Profile after the two table changes" |
| (no rows) | samply profile of `proof_cost_split` at 0cb4e6c (profile not kept) | `prof_cases.py` | "Where the case lemmas' time goes" |
| (no rows) | `proof_cost_split` CPU-time A/B with the `LEAFV` leaf prototype (reverted, no patch kept) | `cpu_ab.ps1` | "Leaves that state the computed bit" |
| `lsp_A`, `lsp_B` | 84072cd + a temporary `LEMMA_SWEEP` switch (reverted, no patch kept), with (A) and without (B) it; `own pooled` on one set of salt-1 libraries | `lemma_sweep_probe.sh` | "A lemma file shared by a whole sweep" |
| `rsp_head_*`, `rsp_rs_*` | 34ea646 against the rule list built once, same load | `rs_pair.sh` | "The rule list built once" |
| `mx_head_*`, `mx_mux_*` | 9f1d23e against `mux` and `not` as one gate each, same load | `mux_pair.sh` | "`mux` and `not` as one gate each" |
