---
status: active
---

# Codebase cleanup (survey of 2026-10-21)

A read-only survey of the whole tree (three Sonnet agents, spot-checked) found the items below. The user approved all
of them on 2026-10-21. Items with a design decision (marked **D**) wait for a ruling before they are built. The others
are mechanical. Anything that touches the miner's path is gated (`docs/runs/2026-10-18/scripts/salts_ab.sh` salts 1-5,
rules byte-equal) and thread-checked (`threads_check.sh`). Leftovers go to `PARKED.md` before this plan is marked done.

Status per item: `todo`, `ruling`, `done <commit>`, `decided against`, `parked`.

## Architecture

- **C1 (D): one rewrite context for the 14 thread-locals in `tests/church_bv/rewrite.rs`.** `SCORE_ONLY`, `RULE_TABLE`,
  `RULE_TRACE`, `RULE_PREFS`, `RULE_BUDGET`, `PROVING`, `REWRITE_MEMO`, `REWRITE_PATH`, `CYCLE_CUTS`, `CUT_LOW`,
  `REWROTE`, `MACHINE_FALLBACKS`, `JOIN_COST` and `JOIN_STORE`. `proving` (rewrite.rs:1856) and `check_replay`
  (rewrite.rs:2424) save and restore 6-8 of them by hand; one job-state swap replaces both. Also folds in the
  `PerTask` statics against `thread_local!` split (`task.rs:126-160`). Status: ruling.
- **C2: one `measured(steps, f)` helper** for "set the budget to 200, read the fallback delta" (about 16 sites in
  search.rs and rewrite.rs; `law_cost` at search.rs:2550 already does it). The `200` and `i64::MAX / 2` literals get
  names. Status: todo (after C1).
- **C3 (D): split `rule_miner`** (search.rs:445, 831 lines, about 60 closures) into a `Miner` struct with methods for
  candidates, scoring, rounds, finish and the preference phase. After C1. Status: ruling.
- **C4: finish `MinerConfig`.** Its doc says it holds every `RULEMINER_*` switch, but about 9 are read inline. Flag parsing
  disagrees (`==1`, `!=0`, `is_some()`, so `NF_TRACE=0` turns tracing on): one `env_flag`. Status: done 30d5a3a (gate 2026-10-21-c4-gate: M 362 = 362, rules same in 15 loops and across threads).
- **C5 (D): one denote walker in `src/proof/`.** `denote_with_placeholders` (hardening.rs:201) mirrors
  `denote_closure_typed` (hardening.rs:437) except for the `SelfCall` arm; the three literal collectors
  (`proof.rs:335`, `closures.rs:2300`, `closures.rs:1813`) are one walk with different accept tables. Status: ruling.
- **C6 (D): bundle the parameters that travel together.** proof/: `store` beside `combinators` (which holds it) in about 20
  functions, and the `(params, concrete, facts)` triple; kernel: `Spaces, Globals, InferCache, CtxScope` in 7
  signatures. Removes 9 `too_many_arguments` allows. Status: ruling.
- **C7 (D): a typed handoff from the miner to the driver.** The driver parses `RULEMINER drop`, `chosen` and `prefer`
  lines from the miner's stdout (driver.rs:721-728). Status: ruling.
- **C8 (D): the ablation switches.** `ablated("...")` is checked at 11 hard-coded sites; 7 names appear in no script.
  Status: ruling.
- **C9: one builder-bug mechanism in `src/compile.rs`** (three counters with the same count, debug-panic, reject shape,
  compile.rs:352-493) and a `decline` helper for the 7 repeated decline sequences in `jit::compile_verify_and_apply`
  (jit.rs:225-326). Status: done 0119ddf.

## Deletions

- **C10: delete `src/kernel_lazy.rs`** (591 lines, an untrusted prototype, closed at 64-100 times slower:
  docs/tier-cycle.md:1869, 1926), its lib.rs gate, the replay test in `tests/church_bv/encoding.rs:853-895` and the
  kernel.rs:37 doc line, once the fuzz tests are confirmed to cover its differential check. Status: todo.
- **C11 (D): the `record-defeq` probes in the trusted kernel** (34 cfg sites in kernel.rs, hand-numbered `WALKS`
  slots), read only by ignored experiments. Status: ruling.
- **C12: hot-path diagnostics read only by ignored tests.** `RULE_HITS` (a mutex and a linear find on every rule firing,
  rewrite.rs:2181), `TRACE_RULES`/`NF_TRACE`, and `PROF`/`LEMMA_HITS` in `tree_proof` (machine.rs:236). Status: done e2bb64f.
- **C13 (D): unreferenced ignored tests.** Ten ignored tests no doc, script or PARKED entry names, the five
  `*_conjecture_miner` tests (machine.rs, about 650 lines), `RULEMINER_PERM=2` and env knobs used nowhere. Status: ruling.
- **C14: test-only public API.** `NatPostulates` (kernel/postulates.rs:395-595) moves into the tests; `args_id`
  (kernel.rs:962) returns `Aid`, not an always-`Some` `Option`. Status: done 5419183.

## Smaller

- **C15: shared code.** One splitmix64 PRNG instead of 9 copies; one `SharedMemo<K, V>` for the global caches
  (`SCREENS`, `TREE_CANDS`, `TREE_ENCS`), which also removes `task.rs`'s hand-kept list. Status: done ba28d56 (gate 2026-10-21-c15-gate: M 362 = 362, rules same in 15 loops and across threads).
- **C16 (D): `docs/runs/2026-10-12/scripts`** (14 `*_pair.sh`, 18 `*_seq.sh` near-copies). Status: ruling.
- **C17: nits.** Stale comments at rewrite.rs:2129 (`PERM_ORDER`) and rewrite.rs:1209 (`SCORE_ONLY`); tier-cycle.md:666
  names functions that are gone; lib.rs's allocator list misses `tests/proof_scope.rs`; `compile::tests` (60% of
  compile.rs) moves to `src/compile/tests.rs`. Status: done 4bff6e4.
- **C18 (D): the jit's sample-based provers** feed only reporting above arity 0 (jit.rs:381-423). Status: ruling.

## Not covered by the survey

The scan for public items with no outside users timed out; `tests/rule_match_census.rs`, `tests/proof_scope.rs`,
`tests/church_lemmas.rs` and `tests/church_encoding.rs` were not read for dead helpers.
