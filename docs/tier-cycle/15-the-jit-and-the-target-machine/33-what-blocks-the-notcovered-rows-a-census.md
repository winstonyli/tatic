### What blocks the NotCovered rows: a census (2026-11-13)

The question: of the census rows the gate does not cover (`proof/tests/baseline.rs#VERDICTS`), what does each need, so
that the next goal-1 step can be sized by counts? Read-only, on `3ba6a15`: the probe
(`docs/runs/2026-11-13/patches/notcovered-census.patch`, test `p5_census`, run `2026-11-13-p5-notcovered-census`)
prints, per row, the distinct `Raw` lines of its fragment, its records with a pointer-reached environment
(`EnvAccess::Pointer`) and the gate's message.

21 of the 40 rows are `NotCovered` (19 `Accepted`, none `Rejected`). One, `open_redex_probe`, has no fragment: the
compiler declines it, so the gate never sees it. Every other row is refused at the first step, the source reading
(`proof/gate.rs#build`: "position N is outside what the source reading takes"), before the shape check would refuse its
`Raw` lines. So for each of the 20, both sides need work: the source reading has to take closure values, and the
machine has to model the lines below.

| term | packs a closure word | `call_indirect` | heap | scratch locals | pointer-env records | gate's message |
|---|---|---|---|---|---|---|
| `closure_typed_loop_carried_parameter_loop` | y | y |  |  | 1 | source position 0 |
| `inconsistent_arity_loop_carried_parameter_loop` | y | y |  | y | 1 | source position 0 |
| `twice` | y | y |  |  | 0 | source position 0 |
| `iterate` | y | y |  |  | 0 | source position 0 |
| `non_tail_closure_carrying_recursion` | y | y |  |  | 1 | source position 0 |
| `branching_non_tail_closure_carrying_recursion` | y | y |  |  | 1 | source position 0 |
| `over_application_if_between_closures` | y | y | y | y | 2 | source position 0 |
| `tail_recursive_loop_with_if_between_closures_self_call_arg` | y | y |  |  | 1 | source position 0 |
| `open_redex_probe` | - | - | - | - | - | no fragment |
| `oversized_source_with_a_shrinking_step` | y |  |  |  | 1 | source position 0 |
| `inconsistent_arity_parameter` | y | y |  | y | 0 | source position 0 |
| `inconsistent_arity_saturating_instance` | y |  |  |  | 1 | source position 1 |
| `inconsistent_arity_under_applying_instance` | y | y |  | y | 1 | source position 0 |
| `inconsistent_arity_capturing_instance` | y | y | y | y | 1 | source position 0 |
| `inconsistent_arity_runtime_chosen_instance` | y | y |  | y | 2 | source position 0 |
| `inconsistent_arity_iterate` | y | y |  | y | 0 | source position 0 |
| `iterate_creating_a_closure_over_g` | y | y |  |  | 0 | source position 0 |
| `calls_a_capturing_closure_picked_by_if` | y | y | y | y | 2 | source position 0 |
| `a_pap_of_a_self_recursive_combinator` | y | y | y | y | 1 | source position 0 |
| `a_pap_of_a_capturing_self_recursive_combinator` | y | y | y | y | 1 | source position 0 |
| `over_application_if_between_closures_of_params` | y | y | y | y | 2 | source position 0 |

"Packs a closure word" is the 32-bit split of the closure word (`i64.shl`, `i64.or`, `i64.extend_i32_u` to build it;
`i64.shr_u`, `i32.wrap_i64` to take it apart); "heap" is `call $alloc`, `i64.store` or `i64.load`; "scratch locals" is
`$envtmp`, `$papenv` or `local.tee`.

- **Totals over the 20 with a fragment:** 20 split or build a closure word, 18 call through `call_indirect`, 11 write
  scratch locals, 6 touch the heap, 15 have a pointer-env record.
- **Nested needs:** every heap row also needs scratch locals and `call_indirect`, and every row needs the closure word.
  So the steps stack: (1) the closure word (Bit rows `wrap`, `extend`, `shl`, `or`, `shr_u`) plus the source reading of
  closure values; (2) `call_indirect` and the table; (3) scratch locals; (4) the heap. What each step would cover,
  counting rows whose lines are all covered by then: step 1 covers 2 (`oversized_source_with_a_shrinking_step`,
  `inconsistent_arity_saturating_instance`), step 2 adds 7 (the rows with neither scratch locals nor heap), step 3 adds
  5, step 4 the last 6. These are upper bounds from the lines alone: a row's pointer-env record or its source shape can
  still need more (the closure convention against its source, `docs/tier-cycle/`, "Calling a closure parameter: the
  closure convention against its source, a spike").
- **Against the v0.8 census** (`docs/decisions/2026-11-10-v08-shape-and-any-backend.md`, "Where the code stands",
  run `2026-11-08-b1-census`, over a different row set): it counted 11 table-call rows with no memory and 7 with closure
  records in memory; here 12 rows call through the table without the heap and 6 use the heap. The Bit rows it tied to
  terms 25 and 28 are the closure word's split, needed by every row here.
