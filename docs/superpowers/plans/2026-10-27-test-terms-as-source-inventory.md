# Hand-built term inventory (eval.rs, jit.rs, compile/tests.rs, proof/tests.rs)

Appendix to `2026-10-27-test-terms-as-source.md`. A read-only survey (Sonnet) wrote this on 2026-10-27 at
commit 9a81523. Its `source` column is a transcription of the code. The plan's hash check proves each one at
conversion, and the check outranks this file wherever they disagree. Line numbers are as of 9a81523. The shape ids
S1-S22 below are this file's own; the plan maps each to the function or sample that replaces it. Loop rows write
placeholders as `{a}`. In source they must be parenthesised, `({a})`, since `f -5` parses as a subtraction (plan,
Review Focus).

Conventions
- `source` is derived from the code (De Bruijn indices checked against the parser's scope rules: `rec f p1..pk = body` puts `f` at `Var(k)`, the last parameter at `Var(0)`; `a > b` parses to `Lt(b, a)`, so `Lt(0, x)` is written `0 < x`).
- Class A = closed, can become source. Class B = cannot (free variable / deliberately unbound / exponential doubled DAG / RNG-generated).
- A "loop" row is ONE row for a `for` loop that builds N terms differing only in literals; the source uses `{lit}` placeholders and the variants are listed in notes. Such a row's `shape` is given only if the same shape is built somewhere else.
- `twin` = a `samples.rs` function with an alpha-equivalent term (identical De Bruijn structure). "contains" = the sample is only a sub-term.
- "from samples" = the test gets part of the term from `samples::{factorial,twice,inc,iterate}` and hand-wraps it.
- Line numbers: eval.rs and jit.rs are absolute file lines; proof and compile tables are lines of their `tests.rs`.
- Shape ids are listed in section 1. `~` = near-duplicate (differs in literal(s) or noted otherwise).

## eval.rs (test module, lines 176-282)

| test | lines | source | class | twin | shape | keeps | notes |
|---|---|---|---|---|---|---|---|
| `countdown` helper (called by `deep_tail_recursion_does_not_overflow_the_native_stack`, 1 caller) | 192-208 | `rec f n = if n <= 0 then 0 else f (n - 1)` | A | none | - | no | Helper; test uses the hash only via `apply_term(&s, h, &[2_000_000])`. Distinct from proof's countdown (`if 0 < n then f (n - 1) else n`). Comment matches code. |
| `deep_tail_recursion_creating_and_calling_a_fresh_closure_each_iteration_does_not_overflow` | 230-248 | `rec f n acc = if n <= 0 then acc else f (n - 1) ((\y. acc + y) n)` | A | `capturing_closure_loop` | S2 | no | Comment matches code (the comment says `f(n-1, ...)` in call style). |
| `higher_order_terms_still_work` | 256-270 | `(\f x. f (f x)) (\y. y + 1) 5` | A | `twice_inc_5` | S1 | `twice`, `inc` built separately, but only `applied` is used | Comment `(twice inc) 5` matches `app2(twice, inc, five)`. |
| `div_by_zero_errors_instead_of_panicking` | 277-279 | `1 / 0` | A | none | - | no | Closed, arity 0. |

## jit.rs (test module, lines 460-1565)

| test | lines | source | class | twin | shape | keeps | notes |
|---|---|---|---|---|---|---|---|
| `a_closure_of_the_wrong_arity_off_the_samples_is_not_installed` | 480-497 | `\n. (\g. if n == 777 then (\k. k n) (g 1) + (\k. k n) (g 2) else n) (\x y. x + y + n)` | A | none | - | no (only `h`; `c`/`raw` derive from it) | Comment matches code. Uses `typing::well_typed(&s, h, 1)`. |
| `an_ill_typed_branch_off_the_samples_is_not_miscompiled` | 539-549 | `\n. (\g. if n == 777 then g 1 + g else n) (\x. x + n)` | A | none | - | no | Comment matches code. |
| `a_closure_argument_of_the_wrong_arity_gets_no_proof` | 560-569 | `\n. (\g. g 1) (\x y. x + y) n` | A | none | - | no (`h` only) | Comment matches code. |
| `invoke_agrees_with_the_interpreter_past_the_stack_buffer_threshold` | 655-663 | `\a b c d e f g h i j. j + i + h + g + f + e + d + c + b + a` | A | none | - | no | Built by loops (`Var(0)` then `+ Var(i)` for i in 1..10, left-assoc; 10 `Abs`), but fixed size, so it can be written as literal text (or generated with `format!`). |
| `a_term_too_big_as_a_tree_is_interpreted` | 713-718 | `\x. t_16` with `t_0 = x`, `t_{i+1} = t_i + t_i` | B (exponential doubled DAG: 18 nodes, 2^17 as a tree) | none | S10 (d = 16) | no | Same builder as compile's `doubling(s, d)`; jit repeats it inline instead of sharing the helper. |
| `division_agrees_with_the_interpreter_at_i64_min_over_negative_one` | 751-756 | `\a b. a / b` | A | none | - | no | Comment matches code. |
| `non_capturing_higher_order_terms_now_compile` | 818-830 | `(\f x. f (f x)) (\y. y + 1) 5` | A | `twice_inc_5` | S1 | no | |
| `a_let_bound_self_recursive_function_compiles_and_is_kernel_verified` | 852-868 | `let fact = rec f n = if n <= 1 then 1 else n * f (n - 1) in fact 10` (same term as `(\g. g 10) (rec f n = ...)`) | A | contains `factorial` | S9 | no | `let` desugars to `App(Abs(body), value)`, so the `let` form is the identical term. |
| `a_returned_closure_now_compiles_via_over_application` | 895-912 | `(\x. if 0 < x then (\y. x + y) else (\y. x - y)) 3 4` | A | none | - | no | Contains the "picker" sub-term (SS1). Comment says `x > 0`, which parses to the same `Lt(0, x)`. |
| `a_closure_typed_loop_carried_parameter_compiles_and_is_kernel_verified` - `it` | 1006-1021 | `rec f n g x = if n <= 0 then x else f (n - 1) g (g x)` | A | `iterate` | - | YES: `it` is reused by `proof::prove_tail_recursive_universal(&s, it)` after the run | Sub-term of the next row. |
| (same test) - `top` | 1023-1031 | `(rec f n g x = if n <= 0 then x else f (n - 1) g (g x)) 10 (\y. y + 1) 0` | A | `closure_typed_loop_carried_parameter_loop(10)` | S17 | no (`inc`, `partial` local only) | Comment matches code. |
| `a_tail_recursive_loop_compiles_and_is_kernel_verified_once_its_own_closure_parameter_turns_inconsistent` - `it` | 1063-1089 | `rec f n g x = if 1 < 0 then g x 999 else if n <= 0 then x else f (n - 1) g (g x)` | A | none for the bare loop (`inconsistent_arity_loop_carried_parameter_loop` is the applied form) | S13 | YES: `it` goes to `compile::try_compile(&s, it)` and the WAT is asserted on | |
| (same test) - `top` | 1091-1099 | `(rec f n g x = if 1 < 0 then g x 999 else if n <= 0 then x else f (n - 1) g (g x)) 10 (\y. y + 1) 0` | A | `inconsistent_arity_loop_carried_parameter_loop(10)` | S14 (N = 10) | no | |
| `a_closure_created_in_a_self_call_argument_capturing_a_closure_typed_loop_parameter_compiles_and_gets_a_universal_proof` - `it` | 1130-1157 | `rec f n g x = if n <= 0 then x else f (n - 1) g (g x + (\y. g y + 1) x)` | A | none | S15 | YES: `proof::prove_tail_recursive_universal(&s, it)` asserted after the run | |
| (same test) - `top` | 1159-1167 | `(rec f n g x = if n <= 0 then x else f (n - 1) g (g x + (\y. g y + 1) x)) 5 (\y. y + 1) 0` | A | none | S16 | no | |
| `partial_application_of_a_non_capturing_root_compiles_and_is_kernel_verified` | 1191-1206 | `(\g. g 4) ((\x y. x + y) 3)` | A | `a_pap_non_capturing` | S7 | no | |
| `partial_application_of_a_capturing_root_compiles_and_is_kernel_verified` | 1227-1245 | `\z. (\g2. g2 4) ((\x y. x + y + z) 3)` | A | `a_pap_capturing` | S8 | no | |
| `partial_application_of_a_self_recursive_root_compiles_and_is_kernel_verified` | 1265-1288 | `(\g. g 1) ((rec f n acc = if n <= 0 then acc else f (n - 1) (n * acc)) 3)` | A | none | S19 | no | |
| `partial_application_of_a_capturing_self_recursive_root_compiles_and_is_kernel_verified` | 1306-1332 | `\z. (\g. g 1) ((rec f n acc = if n <= 0 then acc else f (n - 1) (n * acc + z)) 3)` | A | none | S20 | no | |
| `an_over_applied_literal_lambda_returning_a_closure_compiles_and_is_kernel_verified` | 1355-1385 | `\p q r. (\a b. if 0 < a then (\c. a + b + c) else (\c. a - b + c)) p q r` | A | none (the sample `over_application_if_between_closures` is the same `f` applied to literals 10 3 100) | S21 | no | Comment `f(a,b,c)` matches code. |
| `an_inconsistently_called_parameters_saturating_instance_is_kernel_verified` | 1406-1425 | `(\f. if 0 < 1 then f 1 2 else f 1) (\a b. a + b)` | A | none | S3 | no | |
| `an_inconsistently_called_parameters_under_applying_instance_is_kernel_verified` | 1436-1454 | `(\f. if 1 < 0 then f 1 2 else f 1) (\a. a + 100)` | A | none | S4 | no | |
| `a_captured_value_through_an_inconsistently_called_parameter_is_declined_for_want_of_a_universal_proof` | 1465-1487 | `\k. (\f. if 0 < 1 then f 1 2 else f 1) (\a b. k + a + b)` | A | none | S5 | no | |
| `a_runtime_chosen_literals_own_instance_is_declined_for_want_of_a_universal_proof` | 1508-1539 | `\pick. (\f. if 0 < 1 then f 1 2 else f 1) (if 0 < pick then (\a b. a + b) else (\a b. a - b))` | A | none | S6 | no | |

jit tests that use no in-file hand-built term: `the_verify_battery_*`, `a_parameter_that_is_only_called_*` (parse), `an_open_redex_is_not_contracted_away_by_the_jit` (calls `test_corpus::open_redex_probe`, a free-variable term built in `src/test_corpus.rs`, class B by design, outside the four files), `the_installation_proof_*` (parse), `sample_arg_vectors_*` x2, `a_mismatched_arg_count_*`, `first_call_*`, `kernel_proof_recorded_*`, `branching_recursion_*`, `content_addressing_*`, `repeated_calls_*`, `a_self_recursive_closure_created_and_called_*`, `a_known_partial_application_*` (corpus lookup).

## compile/tests.rs (lines 1-1166)

| test | lines | source | class | twin | shape | keeps | notes |
|---|---|---|---|---|---|---|---|
| `applying_twice_to_a_literal_inc_compiles_and_matches_interpreter` | 76-79 | `(\f x. f (f x)) (\y. y + 1) 5` | A | `twice_inc_5` | S1 | no (`t`, `i` are samples; only `applied` used) | From samples `twice`, `inc` + hand `lit(5)`/`app2`. |
| `a_capturing_closure_compiles_and_matches_interpreter` (+ helper `calls_its_closure_arg_with_5`, 93-98) | 111-130 | `\x. (\g. g 5) ((\x. if 0 < x then (\y. x + y) else (\y. x - y)) x)` | A | none | S18 | no | **Code/comment disagree**: the comment (102) writes `\x. (\g. g 5) (if 0 < x then ... )`, but the code wraps the `if` in a `picker` lambda and applies it to `x` (an extra redex `picker x`). Contains the picker sub-term SS1. |
| `self_recursion_creating_a_fresh_capturing_closure_every_iteration_compiles` | 156-174 | `rec f n acc = if n <= 0 then acc else f (n - 1) ((\y. acc + y) n)` | A | `capturing_closure_loop` | S2 | no | Comment matches code. |
| `resetting_hp_between_calls_keeps_memory_bounded_across_many_calls` | 206-228 | `rec f n acc = if n <= 0 then acc else f (n - 1) ((\g. g n) (\y. acc + y))` | A | none | - | no | Escaping-closure sibling of the row above. Comment matches code. |
| `a_self_recursive_combinator_can_also_capture_from_an_enclosing_scope` | 285-305 | `\z. (\h. h 5) (rec f n = if n <= 0 then z else n + f (n - 1))` | A | none | - | no | Comment matches code. |
| `calling_a_closure_reached_through_a_captured_free_variable_compiles` | 328-348 | `(\cb x. (\y. cb y) x) (\z. z + 1) 5` | A | none (contains `inc` alpha-equivalently) | - | no | Comment matches code. |
| `inconsistent_call_arity_for_a_parameter_now_compiles_via_curried_dispatch` | 377-385 | `\f. f 1 + f 1 2` | A | none | S12 | no | Ill-typed but parses. |
| `a_combinator_never_reached_as_a_bare_value_gets_no_stage_chain_even_when_the_fragment_needs_generic_dispatch` | 410-442 | `(\f. (if 0 < 1 then f 1 2 else f 1) + (\x y. x * y) 3 4) (\a b. a + b)` | A | none | - | no | Test then parses the WAT for `i64.mul`, unrelated to hashes. |
| `an_inconsistently_called_parameter_matching_its_own_saturating_arity_agrees_with_the_interpreter` | 497-516 | `(\f. if 0 < 1 then f 1 2 else f 1) (\a b. a + b)` | A | none | S3 | no | |
| `an_inconsistently_called_parameter_matching_its_own_under_applying_arity_agrees_with_the_interpreter` | 534-552 | `(\f. if 1 < 0 then f 1 2 else f 1) (\a. a + 100)` | A | none | S4 | no | |
| `a_capturing_closure_reached_through_an_inconsistently_called_parameter_agrees_with_the_interpreter` | 571-593 | `\k. (\f. if 0 < 1 then f 1 2 else f 1) (\a b. k + a + b)` | A | none | S5 | no | |
| `a_parameters_own_value_arriving_via_an_if_between_two_literals_still_agrees_once_dispatched_generically` | 617-648 | `\pick. (\f. if 0 < 1 then f 1 2 else f 1) (if 0 < pick then (\a b. a + b) else (\a b. a - b))` | A | none | S6 | no | |
| `partial_application_of_a_literal_lambda_compiles` | 677-692 | `(\g. g 4) ((\x y. x + y) 3)` | A | `a_pap_non_capturing` | S7 | no | |
| `partial_application_of_a_capturing_literal_lambda_compiles` | 715-733 | `\z. (\g2. g2 4) ((\x y. x + y + z) 3)` | A | `a_pap_capturing` | S8 | no | |
| `a_pap_wrappers_own_supplied_argument_creating_more_closures_does_not_corrupt_its_environment` | 862-879 (generator helpers 779-857) | `rec f n acc = if n <= 0 then acc else f (n - 1) (acc <OP> <PAYLOAD>)` with `OP`, `PAYLOAD` drawn from SplitMix64 seed `0xC0FFEE1E55 ^ 2117` (`gen_expr(rng, s, 2, 3)`) | B (generated by an RNG) | none | - | no | Skeleton: `n = Var(1)`, `base = acc = Var(0)`, `f = Var(2)`. Not transcribed beyond the skeleton (section 4). Known facts: `apply_term(h, [10, -20]) == -370`; payload is a closure block under-applying a literal lambda whose supplied argument is another closure block (comment 772-777). |
| `curried_application_is_indistinguishable_from_multi_arg_calls` | 906-912 | `\f x. f x x` | A | none | - | no | |
| `an_over_applied_literal_lambda_returning_a_closure_compiles_and_matches_interpreter` (loop) | f: 936-956; applied: 959-964 | `(\a b. if 0 < a then (\c. a + b + c) else (\c. a - b + c)) {a} {b} {c}` | A | `over_application_if_between_closures` for (10, 3, 100) | S22 | `f` reused across loop iterations | Loop variants: (10,3,100) = the sample; (-5,3,100) = S22~ (literal a). Comment matches code. |
| `classify_recognizes_only_a_saturated_self_call_and_only_a_peelable_callee` - `saturated` | 988-989 | `f a b` with `a = Var(1)`, `b = Var(0)`, `f = Var(2)` | B (free variables by design: the body of `rec f a b`, `classify` is given arity 2 and self index 2) | none | - | YES: `a`, `b` hashes asserted (`*args == vec![a, b]`) | |
| (same) - `partial` | 990 | `f a` (same free vars) | B (free) | none | - | no | |
| (same) - `over` | 991 | `f a b b` (same free vars) | B (free) | none | - | no | |
| (same) - `bad_call` | 1000-1002 | `(rec f = 5) a`, `a = Var(1)` | B (free `a`; the `rec f = 5` part parses: zero-parameter `Rec`) | none | - | no | |
| (same) - `good_call` | 1004-1006 | `(\x. x) a`, `a = Var(1)` | B (free `a`) | none | - | no | |
| `an_unbound_variable_is_rejected_not_a_panic` | 1015-1017 | `\x. y` with `y = Var(3)` | B (deliberately unbound; the parser rejects unbound names) | none | - | no | Comment matches code. |
| `a_let_bound_self_recursive_function_compiles_and_matches_interpreter` | 1032-1038 | `let fact = rec f n = if n <= 1 then 1 else n * f (n - 1) in fact 10` | A | contains `factorial` | S9 | no | From samples `factorial` + hand wrapper. |
| `a_trace_the_checker_rejects_panics_in_debug` / `..._falls_back_to_h_and_is_counted_in_release` via helper `a_rejected_candidate` (2 callers) | 1108 (helper 1104-1110) | `0` (written with `sp.store.lit(0)` into the specialiser's own store) | A (trivial; but it replaces the `term` field of a `Specialised`, so it stays as a one-line store call or `parse(&mut sp.store, "0")`) | none | - | no | `h` itself comes from `corpus("partial_application_loop")`. |
| `a_term_is_compiled_only_up_to_a_tree_size` - `doubling(13)` | 1147 (helper 1134-1140) | `\x. t_13`, `t_0 = x`, `t_{i+1} = t_i + t_i` | B (exponential doubled DAG, 2^14 tree nodes) | none | S10 (d = 13) | YES: `at_the_cap`, `over`, `huge` hashes passed to `tree_size` | `tree_size == MAX_TREE_NODES` asserted. |
| (same) - `doubling(14)` | 1150 | `\x. t_14` | B | none | S10~ (d = 14) | yes (`over`) | |
| (same) - `doubling(200)` | 1153 | `\x. t_200` | B | none | S10~ (d = 200) | yes (`huge`) | 2^201 nodes as a tree. |

compile tests that use no hand-built term: `factorial_*`, `gcd_*`, `twice_alone_*` (samples), `build_produces_the_hand_built_ir_for_each_fixture` (`ir::fixtures` already use `samples::{factorial, twice, twice_inc_5}`; the hand-built part is the IR, not terms), `compile_specialised_compiles_the_checked_specialisation`, `a_term_with_nothing_to_specialise_*`, `a_checked_specialisation_that_does_not_compile_*` (all `corpus(name)`), `an_oversized_source_compiles_without_consulting_the_checker` (`test_corpus::oversized_source_with_a_shrinking_step`, class B by construction, outside the four files).

## proof/tests.rs (lines 1-2717)

| test | lines | source | class | twin | shape | keeps | notes |
|---|---|---|---|---|---|---|---|
| `a_shared_subterm_is_denoted_once` | 30-32 | `x * x + x * x`, `x = Var(0)` free (the body of an arity-1 function) | B (free variable by design; passed as `setup(&s, body, 1, None)`, not wrapped in `Abs`) | none | - | YES: `a = x*x` is the shared subterm; the test is about hash-consed sharing | A converted version `\x. x * x + x * x` would change the `setup` call (arity peeled from the term), not just the construction. |
| `straight_line_term_gets_a_kernel_checked_proof` | 45-55 | `\a b. if a < b then a * 2 else b + 1` | A | `straight_line` | - | no (`f` only) | |
| `recursive_term_is_out_of_scope` | 167-177 | `rec f n = if n <= 1 then 1 else n * f (n - 1)` | A | `factorial` | S11 | no | |
| `genuinely_higher_order_term_is_out_of_scope` | 184-190 | `\f x. f (f x)` | A | `twice` | - | no | |
| `a_capturing_partial_application_created_inside_a_self_call_argument_gets_a_universal_proof` | 271-302 | `rec f n acc = if n <= 0 then acc else f (n - 1) ((\g. g 4) ((\x y. x + y + acc) n))` | A | none | - | no | Comment matches code. |
| `a_closure_created_in_a_leafs_own_top_level_expression_gets_a_universal_proof` | 322-339 | `rec f n = if n <= 0 then 0 else (\y. n + y) 5 + f (n - 1)` | A | none | - | no | Comment matches code. |
| `a_closure_typed_loop_carried_parameter_compiles_and_is_kernel_verified` | 372-377 | `(rec f n g x = if n <= 0 then x else f (n - 1) g (g x)) 3 (\y. y + 1) 5` | A | none (near-twin: `closure_typed_loop_carried_parameter_loop(3)` with the final `0` replaced by `5`) | S17~ (jit's S17 = `10 ... 0`; two literals differ) | no | From samples `iterate`, `inc` + hand `lit`/`app2`/`app`. |
| `one_functions_theorem_proof_is_rejected_against_anothers_type` | 399-409 | `rec f n = if n <= 1 then 1 else n * f (n - 1)` (built into a second store `s2`) | A | `factorial` | S11 | no | The test uses two stores deliberately; the gcd half is `samples::gcd`. |
| `tail_recursive_countdown_gets_a_universal_proof_with_base_in_the_else_branch` | 428-438 | `rec f n = if 0 < n then f (n - 1) else n` | A | none | - | no | Comment writes `if n > 0` which parses to the same term. |
| `tail_recursive_gcd_with_two_base_cases_gets_a_universal_proof` | 456-469 | `rec f a b = if a == 0 then b else if b == 0 then a else f b (a % b)` | A | `gcd_with_two_base_cases` | - | no | |
| `non_tail_recursion_gets_a_universal_proof_now` | 485-495 | `rec f n = if n <= 1 then 1 else n * f (n - 1)` | A | `factorial` | S11 | no | |
| `fibonacci_two_self_calls_gets_a_universal_proof` | 510-523 | `rec f n = if n < 2 then n else f (n - 1) + f (n - 2)` | A | `fib` | - | no | |
| `an_if_nested_inside_an_arithmetic_leaf_gets_a_universal_proof` | 540-554 | `rec f n = if n <= 0 then n + (if n == 0 then 1 else 2) else f (n - 1)` | A | none | - | no | |
| `a_self_call_inside_a_nested_if_branch_gets_a_universal_proof_and_a_correct_instance` | 573-589 | `rec f n = if n <= 0 then 0 else n + (if n % 2 == 0 then f (n - 1) else f (n - 1) + 1)` | A | none | - | no | Comment says `n mod 2`; code is `Mod`. |
| `a_clo_typed_nested_if_as_a_direct_self_call_argument_gets_a_universal_proof` | 618-646 | `rec f n g h = if n <= 0 then 0 else f (n - 1) (if n % 2 == 0 then g else h) h + g n + h n` | A | none | - | no | |
| `a_clo_typed_nested_if_as_an_ad_hoc_closures_own_argument_gets_a_universal_proof` | 673-716 | `rec f n g g2 x = if n <= 0 then x else g 0 + g2 0 + (\h. h x) (if n % 2 == 0 then g else g2) + f (n - 1) g g2 x` | A | none | - | no | |
| `a_long_running_trace_declines_instead_of_overflowing_the_stack` | 743-756 | `rec f n x = if n <= 0 then x else f (n - 1) (x + 1)` | A | none | - | no | |
| `twice_inc_5_gets_a_kernel_checked_closure_proof` | 832-836 | `(\f x. f (f x)) (\y. y + 1) 5` | A | `twice_inc_5` | S1 | no | From samples `twice`, `inc` + hand `lit(5)`/`app2`. |
| `a_directly_called_self_recursive_combinator_gets_a_closure_proof` | 878-881 | `(rec f n = if n <= 1 then 1 else n * f (n - 1)) 10` | A | contains `factorial` | - | no | From samples `factorial` + `app(f, 10)`. |
| `a_self_recursive_combinator_used_as_a_value_gets_a_closure_proof` | 906-912 | `let fact = rec f n = if n <= 1 then 1 else n * f (n - 1) in fact 10` | A | contains `factorial` | S9 | no | From samples `factorial` + hand wrapper. |
| `a_partially_applied_self_recursive_combinator_used_as_a_value_gets_a_closure_proof` | 942-965 | `(\g. g 1) ((rec f n acc = if n <= 0 then acc else f (n - 1) (n * acc)) 3)` | A | none | S19 | no | |
| `partial_application_of_a_capturing_self_recursive_combinator_gets_a_closure_proof` | 991-1017 | `\z. (\g. g 1) ((rec f n acc = if n <= 0 then acc else f (n - 1) (n * acc + z)) 3)` | A | none | S20 | no | |
| `recursion_combined_with_closures_is_out_of_scope` | 1046-1052 | `rec f n = (\g x. g (g x)) (\y. y + 1) n` | A | none | - | no | The `Var(0)` that looks free is the `Rec`'s `Abs` parameter (`Rec(Abs(twice inc Var(0)))`). From samples `twice`, `inc`. |
| `inconsistent_call_arity_for_a_parameter_is_still_out_of_scope_for_the_closure_proof` | 1083-1091 | `\f. f 1 + f 1 2` | A | none | S12 | no | |
| `a_partially_applied_literal_lambda_used_as_a_value_gets_a_closure_proof` | 1104-1119 | `(\g. g 4) ((\x y. x + y) 3)` | A | `a_pap_non_capturing` | S7 | no | |
| `a_partially_applied_literal_lambda_with_mixed_parameter_types_gets_a_closure_proof` | 1147-1157 | `(\h. h 5) ((\f x. f (f x)) (\y. y + 1))` | A | none | - | no | From samples `twice`, `inc`. |
| `a_partially_applied_capturing_literal_lambda_used_as_a_value_gets_a_closure_proof` | 1184-1202 | `\z. (\g2. g2 4) ((\x y. x + y + z) 3)` | A | `a_pap_capturing` | S8 | no | |
| `if_branches_with_different_pap_extra_arity_are_not_conflated_into_a_false_proof` | 1237-1267 | `\x. (\g. g 5) (if x == 0 then (\p a. if a == 0 then (\b. b) else (\b. a + b)) x else (\y. y + 1))` | A | none | - | no | Comment matches code; `inc` from samples. |
| `over_application_of_a_literal_lambda_is_still_out_of_scope_for_the_closure_proof` | 1287-1298 | `(\x y. x + y) 1 2 3` | A | none | - | no | |
| `calling_a_literal_lambda_whose_own_body_picks_between_two_closures_gets_a_closure_proof` | 1319-1342 | `\x. (\g. g 5) ((\x. if 0 < x then (\y. x + y) else (\y. x - y)) x)` | A | none | S18 | no | Here the comment (1308-1310) correctly describes `picker` being applied to `x2`; its first line `\x. (\g. g 5) (if 0 < x ...)` omits that redex, same as compile's. |
| `a_literal_lambda_picking_between_two_different_arity_closures_is_out_of_scope` | 1372-1398 | `\x. (\g. g 5) ((\x. if 0 < x then (\y. x + y) else (\y z. x - y - z)) x)` | A | none | S18~ (else arm is a 2-ary lambda; not a literal difference) | no | |
| `an_over_applied_literal_lambda_returning_a_closure_gets_a_closure_proof` | 1419-1449 | `\p q r. (\a b. if 0 < a then (\c. a + b + c) else (\c. a - b + c)) p q r` | A | none | S21 | no | Same as jit's. |
| `a_capturing_closure_used_as_a_value_gets_a_closure_proof` | 1468-1480 | `\x. (\h. h 5) (\y. x + y)` | A | none | - | no | |
| `a_directly_called_capturing_closure_gets_a_closure_proof` | 1504-1511 | `\x. (\y. x + y) 5` | A | `a_capturing_closure_call` | - | no | |
| `a_capture_of_a_closure_typed_value_gets_a_closure_proof` | 1550-1565 | `\cb. cb 1 + (\h. h 5) (\y. cb)` | A | none | - | no | Ill-typed at runtime by design (returns `TypeError`). |
| `a_closure_created_in_a_self_call_argument_capturing_a_closure_typed_loop_parameter_gets_a_universal_proof` - `it` | 1602-1630 | `rec f n g x = if n <= 0 then x else f (n - 1) g (g x + (\y. g y + 1) x)` | A | none | S15 | YES: `proof::prove_tail_recursive_universal(&s, it)` before `top` is built | |
| (same) - `top` | 1643-1650 | `(rec f n g x = if n <= 0 then x else f (n - 1) g (g x + (\y. g y + 1) x)) 5 (\y. y + 1) 0` | A | none | S16 | no | |
| `a_whole_functions_result_being_a_closure_now_gets_a_closure_proof` | 1670-1677 | `\x. if 0 < x then (\y. y + 1) else (\y. y + 1)` | A | none | - | no | From sample `inc` twice (same hash). Comment says `x > 0`, same term. |
| `a_bare_closure_typed_parameter_read_gets_a_closure_proof` | 1695-1700 | `\f. if f 0 then f else f` | A | none | - | no | |
| `a_closure_typed_ifs_own_result_used_as_a_value_gets_a_closure_proof` (+ helper `dec`, 1709-1714) | 1726-1741 | `\w. (\g x. g x) (if 0 < w then (\y. y + 1) else (\z. z - 1)) 5` | A | none | - | no | `inc` from samples; `dec` helper has 1 caller. |
| `an_if_mismatching_int_and_clo_branches_is_out_of_scope` | 1762-1777 | `\w. (\g x. g x) (if 0 < w then (\y. y + 1) else 5) 5` | A | none | - | no | Near-duplicate of the row above (else arm `5` instead of `dec`); not a shared shape (not one literal). |
| `one_closure_terms_proof_is_rejected_against_anothers_type` | 1786-1795 | `(\f x. f (f x)) (\y. y + 1) 5` (store `s`), and `\f x. f (f x)` in a second store `s2` (from `samples::twice`, not hand-built) | A | `twice_inc_5` | S1 | no | From samples `twice`, `inc` + hand `lit(5)`/`app2`. |
| `prove_closure_expr_declines_where_the_instance_proof_picks_up` | 1826-1845 | `(\f. if 0 < 1 then f 1 2 else f 1) (\a b. a + b)` | A | none | S3 | no | |
| `an_under_applying_instance_gets_a_per_instance_proof_too` | 1857-1875 | `(\f. if 1 < 0 then f 1 2 else f 1) (\a. a + 100)` | A | none | S4 | no | |
| `a_captured_value_reached_through_an_inlined_call_gets_a_per_instance_proof` | 1889-1911 | `\k. (\f. if 0 < 1 then f 1 2 else f 1) (\a b. k + a + b)` | A | none | S5 | no | |
| `a_runtime_chosen_literal_gets_a_per_instance_proof` | 1928-1959 | `\pick. (\f. if 0 < 1 then f 1 2 else f 1) (if 0 < pick then (\a b. a + b) else (\a b. a - b))` | A | none | S6 | no | |
| `a_tail_recursive_loop_carrying_an_inconsistently_classified_closure_parameter_gets_a_per_instance_proof` - `it` | 1983-2010 | `rec f n g x = if 1 < 0 then g x 999 else if n <= 0 then x else f (n - 1) g (g x)` | A | none for the bare loop | S13 | YES: `it` passed to `param_types_for` and `prove_closure_expr`; `inc` (2012-2015) is reused | |
| (same) - `top` (loop) | 2021-2024 | `(rec f n g x = if 1 < 0 then g x 999 else if n <= 0 then x else f (n - 1) g (g x)) {n} (\y. y + 1) 0` | A | `inconsistent_arity_loop_carried_parameter_loop({n})` | S14 (n = 10), S14~ (n = 0, 1) | no | Loop variants n = 0, 1, 10. Comment matches code. |
| `a_loop_carried_call_result_that_itself_gates_termination_gets_a_per_instance_proof` - `it` | 2049-2070 | `rec f g x = if 1 < 0 then g x 999 else if x <= 0 then x else f g (g x)` | A | none | - | YES: `it` passed to `param_types_for` | |
| (same) - `top` (loop) | 2072-2081 | `(rec f g x = ...as above...) (\y. y - 1) {x}` | A | none | - | `dec` reused across the loop | Loop variants x = 0, 1, 5; every run evaluates to 0. |
| `a_closure_argument_arriving_via_a_separate_saturated_call_that_itself_returns_a_clo_gets_a_per_instance_proof` - `f`, `pick` | 2105-2134 | `f = \k. if 0 < 1 then k 1 2 else k 1`; `pick = \s. if 0 < s then (\a b. a + b) else (\a b. a - b)` | A | none | - | YES: `f` goes to `param_types_for`, `pick` to `combinator_return_type`, standalone; then both feed the loop | Two separate sub-terms the test inspects individually. |
| (same) - `top` (loop) | 2138-2141 | `(\k. if 0 < 1 then k 1 2 else k 1) ((\s. if 0 < s then (\a b. a + b) else (\a b. a - b)) {s})` | A | none | - | no | Loop variants s = 3, -3. |
| `a_non_tail_self_call_carrying_an_inconsistently_classified_closure_parameter_gets_a_per_instance_proof` - `it` | 2165-2193 | `rec f n g x = if 1 < 0 then g x 999 else if n <= 0 then x else 1 + f (n - 1) g (g x)` | A | **none** (`non_tail_closure_carrying_recursion` is the same loop WITHOUT the dead `if 1 < 0 then g x 999 else`) | - | YES: `it` passed to `param_types_for`; `inc` reused | **Sample/test disagreement**: `samples::non_tail_closure_carrying_recursion` is documented as "the same shape as" this test but has no dead call, so `g` is not `Inconsistent` there. |
| (same) - `top` (loop + deep) | 2204-2206 and 2224-2227 | `(rec f n g x = if 1 < 0 then g x 999 else if n <= 0 then x else 1 + f (n - 1) g (g x)) {n} (\y. y + 1) 0` | A | none (see above) | - | no | Loop variants n = 0, 1, 3, 10, 100, plus 1_000_000 built separately. |
| `a_self_application_reached_only_through_a_captured_closure_is_bounded_by_the_step_budget` - `step` | 2256-2278 | `\g n. if 1 < 0 then g 999 else if n <= 0 then n else g g (n - 1)` | A | none | - | YES: `step` goes to `param_types_for` standalone and is both function and argument of `top` | |
| (same) - `top` (loop + deep) | 2286-2287 and 2301-2302 | `(\g n. ...step...) (\g n. ...step...) {n}` | A | none | - | no | Textually duplicates `step` (hash-consed to the same node). Variants n = 0, 1, 3, 10, 100, plus 1_000_000. |
| `a_capturing_clo_returning_root_declines_without_evaluating_its_own_argument` - `pick_a` | 2350-2372 | `\s. if 0 < s then (\a b. a + b + cap) else (\a b. a - b + cap)` with `cap = Var(3)` free | B (open on purpose: it "captures" `cap` from outside; used standalone) | none | - | YES: `pick_a` goes to `combinator_return_type`, `compile::peel` and `compile::free_vars` | |
| (same) - `top` | 2382-2414 | `(\g. if 1 < 0 then g 999 888 else g (1 + 1 + ... + 1)) ((\cap. if 0 < 1 then P else P) 7)` where `P` = the `pick_a` text and the sum has 301 ones (`lit(1)` then 300 x `+ 1`) | A | none | - | YES: `let_wrapper` goes to `param_types_for`; `mega` unused otherwise | The whole `top` is closed (`cap` is bound by `mega`). Long but linear. Comment says "300-deep"; code is 301 ones. |
| `branching_non_tail_self_calls_carrying_an_inconsistently_classified_closure_parameter_get_a_per_instance_proof` - `it` | 2438-2475 | `rec f n g = if 1 < 0 then g 0 999 else if n <= 1 then g n else f (n - 1) g + f (n - 2) g` | A | **none** (`branching_non_tail_closure_carrying_recursion` is the same loop WITHOUT the dead `if 1 < 0 then g 0 999 else`) | - | YES: `it` passed to `param_types_for`; `inc` reused | Same sample/test disagreement as the non-tail row. |
| (same) - `top` (loop) | 2485-2486 | `(rec f n g = ...above...) {n} (\y. y + 1)` | A | none (see above) | - | no | Loop variants n = 0, 1, 2, 3, 4. |
| `an_over_applied_if_between_two_non_symmetric_closures_gets_a_closure_proof` (loop) | f: 2521-2533; applied: 2536-2539 | `(\a. if 0 < a then (\c d. c - d) else (\c d. d - c)) {a} {c} {d}` | A | none | - | `f` reused across the loop | Variants (a,c,d) = (5,10,3), (-5,10,3). |
| `an_inner_closures_captures_resolve_against_its_roots_own_frame_in_a_closure_proof` (loop) | f: 2548-2560; h: 2563-2566 | `\w. (\a. if 0 < a then (\c. a + w + c) else (\c. a - w - c)) {a} {c}` | A | none | - | `f` reused | `f` alone is open (`w` free); only the `\w.`-wrapped `h` is built into a checked term. Variants (a,c) = (10,5), (-10,5); `w` only appears as the call argument `[100]`. |
| `an_over_applied_partial_application_root_gets_a_closure_proof` - first term | 2575-2585 | `(\a. (\x y. x * 10 + y) a) 5 3` | A | `over_application_pap_producing_root` | - | no | |
| (same) - second term | 2590-2605 | `(\r. (\o. (\m. (\p q. p - q) m) o) r) 11 4` | A | none | - | no | Three nested one-parameter wrappers around `\p q. p - q`. |
| `an_over_applied_partial_application_root_with_two_supplied_args_and_a_capture_gets_a_closure_proof` | 2613-2630 | `(\x y. (\p q r. p * 100 + q * 10 + r + y) x y) 5 7 3` | A | none | - | no | The inner lambda alone is open (`y` captured) but is only built inside the wrapper. |
| `a_closure_reached_only_through_a_further_saturated_call_gets_a_closure_proof` (loop) | root: 2638-2656; applied: 2659-2662 | `(\a b. if 0 < a then (\x. (\p q. p * 10 + q) x) b else (\y. y - 1)) {a} {b} {c}` | A | none | - | `root` reused | Variants (a,b,c) = (5,3,7), (-5,3,7). |
| `a_self_recursive_root_whose_body_never_self_calls_gets_a_closure_proof` (loop) | helper: 2671-2681; applied: 2684-2686 | `(rec helper a = if 0 < a then (\c. c + a) else (\c. c - a)) {a} {c}` | A | none | - | `helper` reused | Variants (a,c) = (5,3), (-5,10). |
| `a_nested_if_choosing_among_three_closures_gets_a_closure_proof` (loop) | f: 2695-2709; applied: 2712-2714 | `(\a. if 0 < a then (if 10 < a then (\c. c) else (\c. c + 1)) else (\c. c - 1)) {a} {c}` | A | none | - | `f` reused | Variants (a,c) = (5,3), (20,3), (-5,3). |

proof tests that use no hand-built term: `every_arith_postulates_*`, `a_curried_int_arrow_*` (kernel exprs only), `tail_recursive_call_gets_a_per_execution_proof` (gcd), `tail_recursive_gcd_gets_a_universal_proof`, `a_closure_typed_loop_carried_parameter_gets_a_universal_proof` (iterate), `a_closure_created_and_called_inside_a_self_call_argument_*` (capturing_closure_loop), `an_instance_whose_branch_divides_by_zero_*` (parse), `non_tail_recursion_gets_a_per_instance_proof`, `fibonacci_branching_leaves_*`, `one_functions_instance_proof_*` (samples), `twice_alone_*` (sample).

# Sections

## 1. Shared shapes

All sites are listed as `file:test`. J = jit.rs, C = compile/tests.rs, P = proof/tests.rs, E = eval.rs.

| id | source | sites | literal differences |
|---|---|---|---|
| S1 | `(\f x. f (f x)) (\y. y + 1) 5` (= `twice_inc_5`) | E:higher_order_terms_still_work; J:non_capturing_higher_order_terms_now_compile; C:applying_twice_to_a_literal_inc_compiles_and_matches_interpreter; P:twice_inc_5_gets_a_kernel_checked_closure_proof; P:one_closure_terms_proof_is_rejected_against_anothers_type (5 sites) | none |
| S2 | `rec f n acc = if n <= 0 then acc else f (n - 1) ((\y. acc + y) n)` (= `capturing_closure_loop`) | E:deep_tail_recursion_creating_and_calling_a_fresh_closure_each_iteration_does_not_overflow; C:self_recursion_creating_a_fresh_capturing_closure_every_iteration_compiles (2 hand-built; J and P use the sample) | none |
| S3 | `(\f. if 0 < 1 then f 1 2 else f 1) (\a b. a + b)` | J:an_inconsistently_called_parameters_saturating_instance_is_kernel_verified; C:an_inconsistently_called_parameter_matching_its_own_saturating_arity_agrees_with_the_interpreter; P:prove_closure_expr_declines_where_the_instance_proof_picks_up (3) | none |
| S4 | `(\f. if 1 < 0 then f 1 2 else f 1) (\a. a + 100)` | J:..._under_applying_instance_is_kernel_verified; C:..._matching_its_own_under_applying_arity_agrees_with_the_interpreter; P:an_under_applying_instance_gets_a_per_instance_proof_too (3) | none |
| S5 | `\k. (\f. if 0 < 1 then f 1 2 else f 1) (\a b. k + a + b)` | J:a_captured_value_through_an_inconsistently_called_parameter_is_declined_for_want_of_a_universal_proof; C:a_capturing_closure_reached_through_an_inconsistently_called_parameter_agrees_with_the_interpreter; P:a_captured_value_reached_through_an_inlined_call_gets_a_per_instance_proof (3) | none |
| S6 | `\pick. (\f. if 0 < 1 then f 1 2 else f 1) (if 0 < pick then (\a b. a + b) else (\a b. a - b))` | J:a_runtime_chosen_literals_own_instance_is_declined_for_want_of_a_universal_proof; C:a_parameters_own_value_arriving_via_an_if_between_two_literals_still_agrees_once_dispatched_generically; P:a_runtime_chosen_literal_gets_a_per_instance_proof (3) | none |
| S7 | `(\g. g 4) ((\x y. x + y) 3)` (= `a_pap_non_capturing`) | J:partial_application_of_a_non_capturing_root_compiles_and_is_kernel_verified; C:partial_application_of_a_literal_lambda_compiles; P:a_partially_applied_literal_lambda_used_as_a_value_gets_a_closure_proof (3) | none |
| S8 | `\z. (\g2. g2 4) ((\x y. x + y + z) 3)` (= `a_pap_capturing`) | J:partial_application_of_a_capturing_root_compiles_and_is_kernel_verified; C:partial_application_of_a_capturing_literal_lambda_compiles; P:a_partially_applied_capturing_literal_lambda_used_as_a_value_gets_a_closure_proof (3) | none |
| S9 | `let fact = rec f n = if n <= 1 then 1 else n * f (n - 1) in fact 10` | J:a_let_bound_self_recursive_function_compiles_and_is_kernel_verified; C:a_let_bound_self_recursive_function_compiles_and_matches_interpreter; P:a_self_recursive_combinator_used_as_a_value_gets_a_closure_proof (3; C and P get `fact` from `samples::factorial`) | none |
| S10 | `\x. t_d`, `t_0 = x`, `t_{i+1} = t_i + t_i` (class B) | J:a_term_too_big_as_a_tree_is_interpreted (d = 16); C:a_term_is_compiled_only_up_to_a_tree_size (d = 13, 14, 200) via helper `doubling` | d differs: S10 = 16 (jit), S10~ = 13/14/200 (compile). One generator would serve both (jit has no helper). |
| S11 | `rec f n = if n <= 1 then 1 else n * f (n - 1)` (= `factorial`, hand-built) | P:recursive_term_is_out_of_scope; P:non_tail_recursion_gets_a_universal_proof_now; P:one_functions_theorem_proof_is_rejected_against_anothers_type (3) | none |
| S12 | `\f. f 1 + f 1 2` | C:inconsistent_call_arity_for_a_parameter_now_compiles_via_curried_dispatch; P:inconsistent_call_arity_for_a_parameter_is_still_out_of_scope_for_the_closure_proof (2) | none |
| S13 | `rec f n g x = if 1 < 0 then g x 999 else if n <= 0 then x else f (n - 1) g (g x)` (bare `it`) | J:a_tail_recursive_loop_compiles_and_is_kernel_verified_once_...; P:a_tail_recursive_loop_carrying_an_inconsistently_classified_closure_parameter_gets_a_per_instance_proof (2) | none |
| S14 | `S13 N (\y. y + 1) 0` (= `inconsistent_arity_loop_carried_parameter_loop(N)`) | J (N = 10); P (loop N = 0, 1, 10) | S14 = N 10; S14~ = N 0 and 1 (one literal) |
| S15 | `rec f n g x = if n <= 0 then x else f (n - 1) g (g x + (\y. g y + 1) x)` (bare `it`) | J:a_closure_created_in_a_self_call_argument_capturing_a_closure_typed_loop_parameter_compiles_and_gets_a_universal_proof; P:a_closure_created_in_a_self_call_argument_capturing_a_closure_typed_loop_parameter_gets_a_universal_proof (2) | none |
| S16 | `S15 5 (\y. y + 1) 0` | same two tests as S15 (2) | none |
| S17 | `iterate N (\y. y + 1) X` (= `closure_typed_loop_carried_parameter_loop(N)` when X = 0) | J:a_closure_typed_loop_carried_parameter_compiles_and_is_kernel_verified (N = 10, X = 0); P:a_closure_typed_loop_carried_parameter_compiles_and_is_kernel_verified (N = 3, X = 5) | S17 = (10, 0); S17~ = (3, 5): two literals differ |
| S18 | `\x. (\g. g 5) ((\x. if 0 < x then (\y. x + y) else (\y. x - y)) x)` | C:a_capturing_closure_compiles_and_matches_interpreter; P:calling_a_literal_lambda_whose_own_body_picks_between_two_closures_gets_a_closure_proof (2) | S18~ (P:a_literal_lambda_picking_between_two_different_arity_closures_is_out_of_scope): else arm is `\y z. x - y - z`, a structural difference, not a literal |
| S19 | `(\g. g 1) ((rec f n acc = if n <= 0 then acc else f (n - 1) (n * acc)) 3)` | J:partial_application_of_a_self_recursive_root_compiles_and_is_kernel_verified; P:a_partially_applied_self_recursive_combinator_used_as_a_value_gets_a_closure_proof (2) | none |
| S20 | `\z. (\g. g 1) ((rec f n acc = if n <= 0 then acc else f (n - 1) (n * acc + z)) 3)` | J:partial_application_of_a_capturing_self_recursive_root_compiles_and_is_kernel_verified; P:partial_application_of_a_capturing_self_recursive_combinator_gets_a_closure_proof (2) | none |
| S21 | `\p q r. (\a b. if 0 < a then (\c. a + b + c) else (\c. a - b + c)) p q r` | J:an_over_applied_literal_lambda_returning_a_closure_compiles_and_is_kernel_verified; P:an_over_applied_literal_lambda_returning_a_closure_gets_a_closure_proof (2) | none |
| S22 | `(\a b. if 0 < a then (\c. a + b + c) else (\c. a - b + c)) {a} {b} {c}` (= `over_application_if_between_closures` at (10, 3, 100)) | C:an_over_applied_literal_lambda_returning_a_closure_compiles_and_matches_interpreter (1 loop row, 2 variants) | S22 = (10, 3, 100); S22~ = (-5, 3, 100) (literal a). Sibling of S21: S21 abstracts the three arguments. |

Sub-shape (not a whole term, appears inside several): SS1 "picker" `\x. if 0 < x then (\y. x + y) else (\y. x - y)` inside J:a_returned_closure_now_compiles_via_over_application, S18 (C, P) and S18~ (else arm differs). SS2 `\a b. a + b` / `\y. y + 1` appear in a dozen terms.

Loop families (one test builds N variants differing only in literals): C:an_over_applied_literal_lambda_* (S22), P:a_tail_recursive_loop_carrying_* (S14), P:a_loop_carried_call_result_* (x in 0,1,5), P:..._separate_saturated_call_... (s in 3,-3), P:a_non_tail_self_call_* (n in 0,1,3,10,100,1_000_000), P:a_self_application_* (n in 0,1,3,10,100,1_000_000), P:branching_non_tail_* (n in 0..4), P:an_over_applied_if_between_two_non_symmetric_closures (a in 5,-5), P:an_inner_closures_captures_* (a in 10,-10), P:a_closure_reached_only_through_a_further_saturated_call (a in 5,-5), P:a_self_recursive_root_whose_body_never_self_calls (a,c in (5,3),(-5,10)), P:a_nested_if_choosing_among_three_closures (a in 5,20,-5).

Samples/test disagreement worth knowing: `samples::non_tail_closure_carrying_recursion` and `samples::branching_non_tail_closure_carrying_recursion` are documented as "the same shape as" proof::tests terms, but both samples omit the dead `if 1 < 0 then g ... else` call site that the proof tests have. They are not alpha-equivalent to the proof-test terms (no twin recorded).

## 2. Per-file counts (tallied by awk over the tables above)

| file | #[test] total | tests with any hand-built term | rows | rows A | rows B |
|---|---|---|---|---|---|
| src/eval.rs | 5 | 4 | 4 | 4 | 0 |
| src/jit.rs | 35 | 21 (a 22nd, `an_open_redex_*`, gets its class-B term from `test_corpus`, outside the four files) | 24 (3 tests have an `it` row and a `top` row) | 23 | 1 (exponential DAG) |
| src/compile/tests.rs | 31 | 23 (22 with their own rows; `a_rejected_candidate` serves 2 tests) | 28 | 18 | 10 (5 free-variable `classify` terms, 1 deliberately unbound, 3 doubling rows, 1 RNG term) |
| src/proof/tests.rs | 70 | 59 | 68 (9 tests have 2 rows) | 66 | 2 (`a_shared_subterm_is_denoted_once` free `x`; `pick_a` open on `cap`) |

Totals: 141 tests, 124 rows, 111 class A, 13 class B.

## 3. Local helper functions that build terms

| helper | file:line | callers | disposition |
|---|---|---|---|
| `countdown` | eval.rs:192 | 1 (`deep_tail_recursion_does_not_overflow_the_native_stack`) | vanishes (source `rec f n = if n <= 0 then 0 else f (n - 1)`); a new sample only if reused |
| `calls_its_closure_arg_with_5` | compile/tests.rs:93 | 1 (`a_capturing_closure_compiles_and_matches_interpreter`) | vanishes (`\g. g 5` inlined as text) |
| `a_rejected_candidate` | compile/tests.rs:1104 | 2 (`a_trace_the_checker_rejects_panics_in_debug`, `..._falls_back_to_h_and_is_counted_in_release`) | stays (it mutates a `Specialised`); the `sp.store.lit(0)` line could be `parse(&mut sp.store, "0")` |
| `doubling(s, d)` | compile/tests.rs:1134 | 1 test, 3 calls (d = 13, 14, 200) | stays (class B); jit repeats the same builder inline for d = 16, so one shared helper (e.g. in `test_corpus.rs`) would serve both |
| `random_arith_op`, `random_cmp_op`, `gen_leaf`, `gen_cond`, `gen_expr`, `gen_closure_block` (nested fns inside one test) | compile/tests.rs:781-857 | 1 test each (`a_pap_wrappers_own_supplied_argument_...`) | vanish if the seed-2117 term is dumped once to source (e.g. via `syntax::print`); otherwise stay |
| `dec` | proof/tests.rs:1709 | 1 (`a_closure_typed_ifs_own_result_used_as_a_value_gets_a_closure_proof`) | vanishes (`\z. z - 1` inlined) |
| `curried_arrow` | proof/tests.rs:95 | 1 | builds kernel types, not terms; unaffected |
| `check_instance_proof`, `check_closed_closure_proof`, `corpus(name)`, `instantiate` | proof/tests.rs:1813, 2510; compile/tests.rs:1059, 6 | many | take a hash or a name, build nothing; stay |
| (outside the four files) `test_corpus::open_redex_probe`, `oversized_source_with_a_shrinking_step` | src/test_corpus.rs:10, 29 | jit.rs (1 test), specialise.rs (1 test); compile/tests.rs (1 test) | already named class-B helpers (free variable; programmatic oversize); unaffected |

## 4. Terms I could not transcribe confidently

1. `compile/tests.rs` `a_pap_wrappers_own_supplied_argument_creating_more_closures_does_not_corrupt_its_environment` (lines 862-879): only the skeleton `rec f n acc = if n <= 0 then acc else f (n - 1) (acc <OP> <PAYLOAD>)` is known from the code. `OP` (Add/Sub/Mul) and `PAYLOAD` come from `gen_expr` driven by `SplitMix64::new(0x00C0_FFEE_1E55 ^ 2117)`; I did not run the generator (no cargo, and I did not hand-simulate SplitMix64). To get the source, run that code once and print the result with `syntax::print`; check it against the pinned result `apply_term(h, [10, -20]) == -370`.
2. Everything else in the four files is either transcribed as above or deliberately class B with its reason given (free variables in the `classify` terms, `a_shared_subterm_is_denoted_once`, `pick_a`, `\x. y`; doubled DAGs; the RNG term). The 301-term sum in `a_capturing_clo_returning_root_declines_*` is transcribable but I wrote it with `1 + 1 + ... + 1` instead of spelling out all 301 ones.
