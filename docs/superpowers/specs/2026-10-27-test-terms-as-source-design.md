---
status: draft
---

# Test terms as source

Convert the terms that unit tests build by hand (`s.var`, `s.lit`, `s.abs`, `s.prim`, `s.if_`, `s.app`, `s.rec`) to
source text parsed by `syntax::parse`. Taken up from the cleanup plan's CU5 leftover
(`docs/superpowers/plans/2026-10-26-cleanup.md`, CU5 "Not done"); decisions approved in chat 2026-10-27.

## Why

A hand-built term is hard to read, and a wrong index can't be spotted by reading the code. Two cases already show
this: comments that don't describe the term the code builds (D6), and the same 15-line builder copied into three
files. Source text can be read, and when a term is shared, one function holds it.

## Scope

**Files:** `src/proof/tests.rs`, `src/compile/tests.rs`, the test module of `src/jit.rs`, the test module of
`src/eval.rs`; also `src/samples.rs` and `src/test_corpus.rs`, which gain functions.

**Out of scope:**
- `samples::corpus()`, which must not change because `tests/golden_wat.rs`, `tests/rule_match_census.rs` (its
  pinned node counts) and the corpus-wide tests in `decompile.rs`, `specialise.rs` and `spec_check.rs` read it;
- `benches/`, `main.rs`, `tests/golden_wat.rs`;
- the builder tests in `syntax.rs` and `term.rs`, which test the builders themselves.

**Inventory (2026-10-27, commit 9a81523):**

| File | Tests | Tests with a hand-built term | Terms | Can be source (A) | Can't (B) |
|---|---|---|---|---|---|
| `proof/tests.rs` | 70 | 59 | 68 | 66 | 2 |
| `compile/tests.rs` | 31 | 23 | 28 | 18 | 10 |
| `jit.rs` | 35 | 21 | 24 | 23 | 1 |
| `eval.rs` | 5 | 4 | 4 | 4 | 0 |
| Total | 141 | 107 | 124 | 111 | 13 |

- A test that builds two separate terms counts twice in the "Terms" column.
- The RNG term in `compile/tests.rs` is counted in B, but it converts (D4).
- So 112 terms become source, and 12 stay hand-built across 6 tests (D5).
- The earlier survey counted tests rather than terms: 98 of 105 hand-building tests convertible. The plan carries the
  per-test inventory.

## Decisions

**D1. `samples::source`.** The private `samples::parse(s, src) -> Hash` becomes `pub fn source`, unchanged. Every
test-local source term is parsed through it: one panic message ("sample `{src}` should parse: {e}") and no per-file
wrapper.

**D2. Shared shapes are pub functions in `samples.rs`, after `corpus()`.**
- A header comment says they are deliberately not in the corpus.
- Each is named for what it is.
- Each has the same signature as the other samples, `fn(&mut TermStore) -> Hash`.
- A shape gets a parameter only where its copies differ in one literal. None of the twelve below does.

Where a test needs a shape at another literal, it either builds that variant with `format!` in the test or applies
the bare shape through glue (D3). For example, proof's `iterate 3 (\y. y + 1) 5` is `samples::iterate` plus two
`s.app` calls. The twelve new shapes:

| Function | Source | Sites |
|---|---|---|
| `inconsistent_arity_parameter` | `\f. f 1 + f 1 2` | compile, proof |
| `inconsistent_arity_saturating_instance` | `(\f. if 0 < 1 then f 1 2 else f 1) (\a b. a + b)` | jit, compile, proof |
| `inconsistent_arity_under_applying_instance` | `(\f. if 1 < 0 then f 1 2 else f 1) (\a. a + 100)` | jit, compile, proof |
| `inconsistent_arity_capturing_instance` | `\k. (\f. if 0 < 1 then f 1 2 else f 1) (\a b. k + a + b)` | jit, compile, proof |
| `inconsistent_arity_runtime_chosen_instance` | `\pick. (\f. if 0 < 1 then f 1 2 else f 1) (if 0 < pick then (\a b. a + b) else (\a b. a - b))` | jit, compile, proof |
| `inconsistent_arity_iterate` | `rec f n g x = if 1 < 0 then g x 999 else if n <= 0 then x else f (n - 1) g (g x)` | jit, proof |
| `iterate_creating_a_closure_over_g` | `rec f n g x = if n <= 0 then x else f (n - 1) g (g x + (\y. g y + 1) x)` | jit, proof |
| `let_bound_factorial_10` | `let fact = rec f n = if n <= 1 then 1 else n * f (n - 1) in fact 10` | jit, compile, proof |
| `calls_a_capturing_closure_picked_by_if` | `\x. (\g. g 5) ((\x. if 0 < x then (\y. x + y) else (\y. x - y)) x)` | compile, proof |
| `a_pap_of_a_self_recursive_combinator` | `(\g. g 1) ((rec f n acc = if n <= 0 then acc else f (n - 1) (n * acc)) 3)` | jit, proof |
| `a_pap_of_a_capturing_self_recursive_combinator` | `\z. (\g. g 1) ((rec f n acc = if n <= 0 then acc else f (n - 1) (n * acc + z)) 3)` | jit, proof |
| `over_application_if_between_closures_of_params` | `\p q r. (\a b. if 0 < a then (\c. a + b + c) else (\c. a - b + c)) p q r` | jit, proof |

The source text above was transcribed from the code by a survey. The hash check in "Method" is what proves each
transcription. If a site's term turns out to differ from its shape, that site does not use the shape, and the
finding is reported.

**Sample twins:** about 20 tests rebuild an existing sample by hand. These call the sample:
- `twice_inc_5`, at 5 sites;
- `factorial` (proof's `recursive_term_is_out_of_scope` and two more);
- `capturing_closure_loop`, `a_pap_non_capturing`, `a_pap_capturing`, `iterate`,
  `closure_typed_loop_carried_parameter_loop(n)`, `inconsistent_arity_loop_carried_parameter_loop(n)`, `inc`.

`compile/tests.rs`'s `an_over_applied_literal_lambda_returning_a_closure_compiles_and_matches_interpreter` builds
`over_application_if_between_closures` at `a = 10` and at `a = -5`, in one loop. It keeps a test-local `format!`
over `a` rather than adding a parameter to a corpus sample.

**D3. Glue for sub-hashes stays; its terms become source.** About 20 tests keep a subterm's hash for a later call: an
`it` they apply in a loop, or a lambda they pass to `param_types_for`. Each piece becomes source, and the joining
`s.app`/`s.app2` calls stay. Parsing the same text twice in one store gives the same hash, so a piece can be parsed
alone or inside the whole term.

**D4. The seed-2117 regression term is frozen as source.**
- The test is `compile/tests.rs`'s `a_pap_wrappers_own_supplied_argument_creating_more_closures_does_not_corrupt_its_environment`.
- It runs its copy of `tests/compile_fuzz.rs`'s generator once, then prints the term with `syntax::print`.
- That text replaces the generator copy, which is deleted (`random_arith_op`, `random_cmp_op`, the `gen_*` functions).
- The test's pinned result `apply_term(h, [10, -20]) == -370` must still hold.
- A comment names the seed and the fuzz test the term came from.

**D5. These stay hand-built, each with a one-line comment saying why:**

| Test | Term | Why |
|---|---|---|
| `proof/tests.rs` `a_shared_subterm_is_denoted_once` | `x * x + x * x`, `x` free | the test is about an open body passed to `setup` with arity 1 |
| `proof/tests.rs` `a_capturing_clo_returning_root_declines_without_evaluating_its_own_argument` | `pick_a`, open on `cap` | used alone, so it can't be closed; the test's closed `top` becomes source and contains `pick_a` with the same hash |
| `compile/tests.rs` `classify_recognizes_only_a_saturated_self_call_and_only_a_peelable_callee` | 5 terms over free `f a b` | `classify` is given a body, not a closed term |
| `compile/tests.rs` `an_unbound_variable_is_rejected_not_a_panic` | `\x. y` | deliberately unbound; the parser rejects it |
| `compile/tests.rs` `a_term_is_compiled_only_up_to_a_tree_size` | `doubling(13, 14, 200)` | a doubled DAG; its text is exponentially long |
| `jit.rs` `a_term_too_big_as_a_tree_is_interpreted` | `\x. t_16` | the same doubled DAG |

**D6. Comments.**
- A comment that restates the term (`// \x. (\g. g 5) ...`, `// f(n-1, g, g(x))`) is deleted, because the source
  text now says it.
- A comment that explains why a term has its shape (a dead branch, the reason for a depth) stays.
- Two known comments disagree with their code:
  - `compile/tests.rs`'s `a_capturing_closure_compiles_and_matches_interpreter` leaves out the picker redex its code
    builds. The code is the reference, so this comment goes.
  - `proof/tests.rs`'s `a_capturing_clo_returning_root_declines_*` says "300-deep" for a sum of 301 ones. Its source
    builds the same 301, with `format!`, and the comment says 301.
- Two doc comments in `samples.rs` are wrong:
  - `non_tail_closure_carrying_recursion` and `branching_non_tail_closure_carrying_recursion` say they are "the same
    shape as" two `proof/tests.rs` tests.
  - Both samples lack the tests' dead call site, `if 1 < 0 then g x 999 else`.
  - Their docs are corrected to say so. Their terms stay as they are, because they are in `corpus()`.

**D7. `doubling` moves to `test_corpus.rs`.** `test_corpus.rs` already holds the terms the parser can't express, so
it becomes `pub(crate) fn doubling(s, d)`. `jit.rs` calls it at `d = 16` instead of its inline copy. This removes the
one duplicated class-B builder.

## Method

Every converted term is checked against the builder it replaces, by hash. This is the method CU5 used.

1. Convert. Keep the old builder beside the new source, with a temporary `assert_eq!(new, old)`.
2. In each stage, plant two wrong source strings, for example a swapped operand and a changed literal. Watch the
   assert fail, then remove them.
3. Run the lib suite with the temporary asserts in place.
4. Delete the old builders and the temporary asserts. Run the full suite, and commit only that state.

The temporary state is never committed. The commit message records the number of comparisons, the mutations caught,
the test counts, and the lines removed.

**Stages, one commit each (step 4's state):**

| Stage | Contents |
|---|---|
| T1 | `samples::source` (D1), the twelve shapes (D2), and every site of a shape or a sample twin, across all four files |
| T2 | the rest of `proof/tests.rs` |
| T3 | the rest of `jit.rs`, and `doubling` to `test_corpus.rs` (D7) |
| T4 | the rest of `compile/tests.rs`, including the frozen seed-2117 term (D4) |
| T5 | the rest of `eval.rs`, and the `samples.rs` doc fixes (D6) |

**Checks for every stage:**
- The lib suite's test count is unchanged against a baseline taken before T1 (358 passed at the CU5 close; the
  ignored count is recorded at the baseline). A count that moves is a stop.
- Every golden in `tests/golden_wat.rs` stays byte-identical. It reads `corpus()`, two samples by name and its own
  `rejects_*` terms, and none of these change. A moved golden means an edit escaped the scope. The same holds for
  `rule_match_census.rs`'s pinned counts.
- Lines removed are recorded per stage. The survey estimated about 1,300 in total.
- If a term doesn't parse, or the hash check fails and fixing the transcription doesn't settle it, that is a
  finding. Stop and report it with options.

## Docs

- **`PARKED.md`:** the entry "One-off hand-built terms inside single tests" is deleted in this spec's commit.
- **Cleanup plan:** CU5's "Not done" points to this spec in place of `PARKED.md`.
- **`samples.rs` module doc:** says it also holds shapes shared by tests outside the corpus. `README.md`'s
  `samples.rs` row says the same in T1.
- **`test_corpus.rs` module doc:** says it holds three terms (D7).
- **Other docs:** `tier-cycle.md`, `ROADMAP.md` and `RELATED_WORK.md` record no finding or milestone this changes.
  T5 greps them for every renamed or deleted helper name.
- **Status:** `active` when T1 starts; `done` when T5 lands.
