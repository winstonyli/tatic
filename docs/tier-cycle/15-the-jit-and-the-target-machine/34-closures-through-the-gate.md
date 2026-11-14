### Closures through the gate (2026-11-14)

The question: with the closure word as rows (`shl`, `shr_u`, `or`, `wrap`, `extend`, `i32.const`), `call_indirect` as a
machine instruction (`Ins::CallIndirect`) and the source reading taking closure values and closure calls
(`docs/superpowers/specs/2026-11-13-closures-through-the-gate-design.md`), which census rows does the gate cover, do
the closure convention's mutants fail, and what does it cost? Branch `closures-gate` (`210debc` to `53915a8`), plan
`docs/superpowers/plans/2026-11-13-closures-through-the-gate.md`. The census it moves is the one in "What blocks the
NotCovered rows: a census".

- **Verdicts.** Eight rows of `proof/tests/baseline.rs#VERDICTS` go from `NotCovered` to `Accepted`, and no other row
  moves: `twice`, `iterate`, `iterate_creating_a_closure_over_g`, `closure_typed_loop_carried_parameter_loop`,
  `non_tail_closure_carrying_recursion`, `branching_non_tail_closure_carrying_recursion`,
  `tail_recursive_loop_with_if_between_closures_self_call_arg` and `inconsistent_arity_saturating_instance`. Now 27 of
  the 40 rows are `Accepted` (19 before), 13 `NotCovered` (21), none `Rejected`. The census counted 9 rows
  covered by its steps 1 and 2 (the closure word, then `call_indirect` and the table); the ninth,
  `oversized_source_with_a_shrinking_step`, is over the tree budget, so it stays `NotCovered`. The 13 that stay are the census's rows with scratch locals or the heap,
  `open_redex_probe` (no fragment) and `oversized_source_with_a_shrinking_step` (over the tree budget).
- **The empty-set rows.** `twice`, `iterate` and `iterate_creating_a_closure_over_g` have an empty dynamic set for every
  arity (checked on their gated fragments: `dynamic_sets` is `[[], [], []]`, `[[], [], [], []]` and
  `[[], [], [], []]`; no record is reached through `$env`), so on both sides every closure call answers `z`. Their
  `Accepted` says only that each closure call traps on both sides. The other five rows have a non-empty set for the
  arity they call (`non_tail_closure_carrying_recursion`: `[1]` at arity 1). That is why the mutants below are on the
  carrying recursion, and why one of the `twice` mutants is refused by the walk alone.
- **Mutants** (`proof/tests/gate_mutants.rs`, `closure_convention_mutants_are_rejected_on_the_carrying_recursion` and
  `a_twice_with_one_closure_call_is_rejected`; each edit asserts the slice it replaces, and a test that ignores its
  replacement fails at the first mutant). Layers observed:

| mutant | edit | layer | `forged_rejected` |
|---|---|---|---|
| the index off by one | the entry's packed index `1` becomes `2` | `Rejected(Walk)` | passes (the kernel refuses the positive proof against the mutant's statement) |
| the halves swapped | env and index exchange places in the packing | `Rejected(Walk)` | passes |
| the closure's body | `$c1`'s `konst 1` becomes `2` | `Rejected(Walk)` | passes |
| the argument replaced | `get 2` becomes `get 0` in `$c0`'s else branch | `Rejected(Walk)` | passes |
| the closure call dropped | `get 1; wrap; call_indirect 1` becomes `add` | `Rejected(Pairing)` | n/a (no statement is built) |
| `twice` with one closure call | the inner call becomes `add` | `Rejected(Walk)` ("the machine branches but the source is stuck") | not applicable, below |

- **A closure-call count on an empty set is unobservable in the closed module.** The sixth mutant's statement is
  `def_eq` to the positive one (asserted in `a_twice_with_one_closure_call_is_rejected`; the first version of that test
  asserted a `forged_rejected` that does not hold, and the Task 5 review found why): on an empty dynamic set every
  closure call answers `z` on both sides, so one call or two give the same statement. No hole follows, because the walk is
  lockstep and refuses the mismatch, which is the layer that decides, but the kernel alone would not. The pairing check
  cannot see it either: equal callee sets on an empty set say nothing about how many times the head is called.
- **The reading refuses what it cannot yet model**, each pinned by a test in `proof/tests/gate.rs`: a closure call
  beside a table slot with no record (`a_closure_call_beside_a_pap_slot_is_not_covered`), curried dispatch
  (`a_curried_closure_call_is_not_covered`; 6 census fragments are curried, all call a closure, all `NotCovered`), and a
  module whose calls, widened by the dynamic sets, form a cycle (`a_closure_cycle_is_not_covered`, a `NotCovered` from
  `call_cycle` before any statement is built). Decision y1: a direct call into a `Pointer` record stays refused (`PARKED.md`,
  "Direct calls into `Pointer` records").
- **Cost.** The probe (`docs/runs/2026-11-13/patches/q2-cost.patch`, test `q2_probe`, run once at `15ad793` and at
  `53915a8` and removed; runs `2026-11-14-t6-q2-base` and `2026-11-14-t6-q2-head`) prints the kernel's work counts for the
  build and the check by the method of section 32's `p1_probe`. The base run, in a separate worktree, reproduces section
  32's table exactly for the six rows it shares (`capturing_closure_loop` 9288/7275 ... `doubling(12)`
  1346914/1074514), so the head numbers compare against the same instrument. Check/build work:

| row | at `15ad793` | at `53915a8` | ratio (check, build) | gate cost at `15ad793` -> `53915a8` |
|---|---|---|---|---|
| `capturing_closure_loop` | 9288 / 7275 | 9825 / 7911 | 1.058, 1.087 | 245 -> 245 |
| `straight_line` | 29241 / 4530 | 29606 / 4860 | 1.012, 1.073 | 12 -> 12 |
| `held_out_b` | 31449 / 7568 | 31986 / 8204 | 1.017, 1.084 | 247 -> 247 |
| `doubling(6)` | 26170 / 19762 | 26528 / 20092 | 1.014, 1.017 | 128 -> 128 |
| `gcd` | 61609 / 7037 | 62146 / 7673 | 1.009, 1.090 | 243 -> 243 |
| `doubling(12)` | 1346914 / 1074514 | 1347272 / 1074844 | 1.0003, 1.0003 | 8192 -> 8192 |
| `twice` | n/a (`NotCovered`) | 7262 / 4980 | n/a | 7 -> 463 |
| `iterate` | n/a | 9917 / 8968 | n/a | 248 -> 476 |
| `iterate_creating_a_closure_over_g` | n/a | 11040 / 9575 | n/a | 254 -> 710 |
| `closure_typed_loop_carried_parameter_loop` | n/a | 62701 / 92496 | n/a | 485 -> 713 |
| `non_tail_closure_carrying_recursion` | n/a | 62336 / 91169 | n/a | 487 -> 715 |
| `branching_non_tail_closure_carrying_recursion` | n/a | 63161 / 96402 | n/a | 716 -> 944 |
| `tail_recursive_loop_with_if_between_closures_self_call_arg` | n/a | 58045 / 111843 | n/a | 483 -> 939 |
| `inconsistent_arity_saturating_instance` | n/a | 8867 / 7216 | n/a | 11 -> 11 |

  - **The two new `Prog` constructors cost a constant.** Every statement grows by a fixed amount, not a share: the
    check by 537 (`capturing_closure_loop`, `held_out_b`, `gcd`), 365 (`straight_line`) or 358 (`doubling(6)`,
    `doubling(12)`); the build by 636 (the same three) or 330 (`straight_line`, `doubling(6)`, `doubling(12)`). That is
    at most 6% of the check and 9% of the build on the small rows, and 0.03% on `doubling(12)`.
  - **`doubling(12)` stays at the cap and is accepted**: its gate cost is 8192, equal to `MAX_GATE_TREE` (a term over it
    is `NotCovered`), and its work is up 358 and 330. `doubling(13)` stays the over-budget pin.
  - **The new rows are cheap against the cap.** Their gate cost is 11 to 944, and their check plus build work 12 thousand
    to 170 thousand, against 2.42 million for `doubling(12)`. A closure call site is counted by `module_cost` at
    `CALL_WEIGHT` times its width (the head twice, and the dynamic set's size), which is the rise in the cost column
    (+228 per site, +456 for two).
  - **`CALL_WEIGHT` (228) was not refitted.** Work per cost unit, check plus build: `doubling(12)` 296 and `gcd` 287;
    the new rows with a cost over 400 do 169 to 218 (`closure_typed_loop_carried_parameter_loop` 218,
    `non_tail_closure_carrying_recursion` 215, `tail_recursive_loop_with_if_between_closures_self_call_arg` 181,
    `branching_non_tail_closure_carrying_recursion` 169). The rows under 100 are dominated by a fixed part, as the static
    ones are (`straight_line`, cost 12, does 34 thousand), so their rate says nothing. So a closure call site is not
    dearer per unit of cost than the term at the cap, and the budget is not loosened by them. This compares whole-row
    rates, not one site against another: the rows mix both kinds of site, and a probe that isolates a closure site (a
    chain of `k` closure calls against `k` static calls, as section 32's `%` chains do) was not run. The counts are
    deterministic, so the comparison needs no timing.
- **The suites** (all through `run.ps1 -Affinity CFF`, at `53915a8` with only documents changed since): run
  `2026-11-14-t6-q2-suite` (`cargo test -j 10 -p tatic-wasm && -p tatic && -p church-bv`), exit 0: `tatic-wasm` lib 59
  passed, 4 ignored; `tatic` lib 331 passed, 12 ignored, its other test binaries (`repl` 5, `compile_fuzz` 7,
  `golden_wat` 4, `syntax_fuzz` 1 passed); `church-bv` lib 318 passed, 43 ignored, its integration test 3; no failure.
  Run `2026-11-14-t6-q2-optable` (`cargo test -j 10 -p tatic --lib op_table -- --ignored`), exit 0:
  `op_table_agrees_at_n8_exhaustive` and `op_table_agrees_at_n64_on_all_edges` pass. The other ignored suites of section
  32 (where its three older failures are) were not rerun, so those three stay as that section recorded them.

What it leaves: the 13 rows above. Each needs scratch locals, the heap, or a different bound; `PARKED.md` holds the scratch-locals
and heap entries with their counts restated, and the direct-calls entry (y1).
