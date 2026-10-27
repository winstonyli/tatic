---
status: done
---

# Test terms as source: implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Every term the unit tests build by hand becomes source text. The exceptions are the 12 terms in D5 of the
spec. No test's meaning changes, and each conversion is proved by hash against the builder it replaces.

**Architecture:**
- `samples::source` parses a closed term and panics on failure.
- Twelve shapes that two or three test files share become pub functions in `src/samples.rs`, after `corpus()`.
- A test that rebuilds an existing sample calls the sample instead.
- Every other term becomes a source string in its own test.
- Glue that keeps a subterm's hash stays (`s.app`/`s.app2` over parsed pieces).
- Five stages, one commit each.

**Tech stack:** Rust, `cargo test`; `syntax::parse` and `syntax::print` (`src/syntax.rs`).

**Spec:** `docs/superpowers/specs/2026-10-27-test-terms-as-source-design.md`

**Inventory (appendix):** `docs/superpowers/plans/2026-10-27-test-terms-as-source-inventory.md` has one row per
hand-built term: its test, lines (at 9a81523), the source as transcribed, its class, twin and shape id. Each task
below names the rows it converts.

## Global Constraints

- `samples::corpus()` and the 23 samples' terms do not change. The goldens in `tests/golden_wat.rs` stay
  byte-identical, and `tests/rule_match_census.rs`'s pinned counts stay as they are.
- Out of scope: `benches/`, `main.rs`, `tests/golden_wat.rs`, and the builder tests in `syntax.rs` and `term.rs`.
- Test count: a stage neither adds nor removes a test. Any test count that moves is a stop.
- The temporary state (old builder plus `assert_eq!`) is never committed.
- Each stage's commit message records:
  - the number of hash comparisons;
  - the mutations caught;
  - the lib test count;
  - the line counts (`git diff --shortstat` against the stage's BASE).
- Run cargo as `cmd //c start "" //b //wait //belownormal //affinity CFF cargo test --release -j 4 <args>`, from bash.
  This means BelowNormal priority, affinity off CPUs 8 and 9, and 4 jobs.
- Never let python read stdin. If python is needed: script file plus `python -P f.py < /dev/null`.
- Make edits with the Edit tool. Commit messages go in `$TEMP/msg.txt` and end with
  `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.
- If a term doesn't parse, or its hash check fails and fixing the transcription doesn't settle it, stop and report
  with options. Do not change the test's term to make the check pass.
- Comments (spec D6):
  - Delete comments that restate the term: `// \x. ...`, `// f(n-1, g, g(x))`, and per-line `// always false`
    notes that the source now shows.
  - Keep comments that say why a term has its shape.
  - Rewrite a kept comment's call-style notation (`f(n-1, g)`) into the source's notation only where the comment
    would otherwise mislead.

## Review Focus

- **A shape function used at a site whose term differs.** Every converted site must keep its temporary
  `assert_eq!(new, old)` through the stage's suite run. The commit message's comparison count has to match the
  number of converted terms in the task's row list.
- **A test that keeps `it` and builds `top` with glue.** Both hashes are asserted against the old builder. A kept
  hash that silently changes would still pass a test that only checks `top`.
- **A comment left describing the old term or another term.** The final review reads every comment within 5 lines of
  a converted site.
- **`corpus()` touched by accident** (renaming `parse` to `source` inside a sample body is the risky edit). Each stage
  runs `golden_wat` and `rule_match_census`.
- **A loop test whose variants use `format!`.** Every interpolated literal is parenthesised, `({a})`, as the samples
  write `({iters})`. A bare `f {a}` with `a = -5` gives `f -5`, which parses as the subtraction `f - 5`.
  `(-5)` parses as `Lit(-5)`, which matches `s.lit(-5)`. The hash check catches a mistake here only if every variant
  goes through the assert, so the assert sits inside the loop.

## Method (every task)

For each converted term:
1. Rename the old builder's result, for example `let old_h = ...;`, and keep its code.
2. Write the new line, for example `let h = source(&mut s, r"...");` or `let h = samples::x(&mut s);`.
3. Add `assert_eq!(h, old_h, "<test>: source differs from the builder");` straight after.

Both are built in the same store, so their hashes are equal exactly when the terms are equal. A test with several
terms, or with kept sub-hashes, gets one assert per term or sub-hash. Then:

- **Mutate.** Change one character of one new source string, then of another, picked so the term changes, for
  example `+` to `-` or `1` to `2`. Run that test each time and confirm the assert fails, then undo each mutation.
- **Gate.** Run the lib suite and the two corpus readers with the asserts in place:
  `cmd //c start "" //b //wait //belownormal //affinity CFF cargo test --release -j 4 --lib --test golden_wat --test rule_match_census > "$TEMP/stage.log" 2>&1; tail -30 "$TEMP/stage.log"`.
  Expected: all pass, and the lib count equals the baseline.
- **Strip.** Delete every `old_*` builder, every temporary assert, and every helper only they used. Re-run the gate,
  with the same expected result.
- **Commit** the stripped state.

Each task also adds `source` and any sample it calls to the module's `use crate::samples::{...}` line, and drops
imports that no code uses any more; warnings show which.

Count the asserts before stripping with `git diff | grep -c '^+.*assert_eq!(.*old_'`; that number goes in the commit
message.

---

### Task 0: Branch and baseline

**Files:** none changed.

- [ ] **Step 1:** Create a worktree on a new branch `test-terms` from main (superpowers:using-git-worktrees), and work
  there for every later task.
- [ ] **Step 2:** Run the gate on the untouched tree:
  `cmd //c start "" //b //wait //belownormal //affinity CFF cargo test --release -j 4 --lib --test golden_wat --test rule_match_census > "$TEMP/base.log" 2>&1; grep "test result" "$TEMP/base.log"`.
  Expected: three `ok` lines. Record the lib line's passed and ignored counts in the ledger (lib was 358 passed at the
  CU5 close). Every later stage compares against these counts.
- [ ] **Step 3:** Record the line counts of the four test files and `samples.rs` (`wc -l`), and the warning count
  (`grep -c "^warning" "$TEMP/base.log"`; expected 0, since `cargo check --all-targets` was clean at the CU close). A
  stage ends with the same warning count.
- [ ] **Step 4:** Set the front matter of this plan and of the spec to `status: active` and commit
  (`plan: test terms as source, active`).

### Task 1 (T1): `source`, the twelve shapes, and every shape or twin site

**Files:**
- Modify: `src/samples.rs` (rename `parse` to `source`, make it pub, add the shapes after `corpus()`, update the
  module doc)
- Modify: `src/proof/tests.rs`, `src/compile/tests.rs`, `src/jit.rs` (test module), `src/eval.rs` (test module)
- Modify: `README.md` (the `samples.rs` row)

**Interfaces:**
- Produces: `pub fn source(s: &mut TermStore, src: &str) -> Hash`, and twelve `pub fn <name>(s: &mut TermStore) -> Hash`
  with the names below. T2 to T5 use `source`.

- [ ] **Step 1: `source`.** In `src/samples.rs`, replace the private parser function with:

```rust
/// Parses `src`, a closed term, into `s`. Panics naming `src` if it doesn't parse: a sample or a test's term that
/// doesn't parse is a bug in that term.
pub fn source(s: &mut TermStore, src: &str) -> Hash {
    syntax::parse(s, src).unwrap_or_else(|e| panic!("sample `{src}` should parse: {e}"))
}
```

Rename every `parse(` call inside `samples.rs` to `source(`. That is a call rename only: the string arguments
stay byte for byte as they are.

- [ ] **Step 2: Module doc.** Replace the module doc of `src/samples.rs` with:

```rust
//! Sample terms, written as source (`syntax`): the benchmarks' terms, the
//! demo's, and the corpus that unit tests and `tests/golden_wat.rs` run
//! over. One copy, so a bench, a test and the demo that name the same term
//! build the same hash. After `corpus()`, the shapes that unit tests in
//! several files share, outside the corpus.
```

- [ ] **Step 3: The shapes.** Append after `corpus()`:

```rust
// Shapes that unit tests in two or three files share. Deliberately not in
// `corpus()`: the goldens, the rule census and the corpus-wide tests read
// the corpus, and these terms are only test inputs.

/// `f` called at two arities, and nothing more: no single type fits it.
pub fn inconsistent_arity_parameter(s: &mut TermStore) -> Hash {
    source(s, r"\f. f 1 + f 1 2")
}

/// A parameter called at two arities, given a 2-ary literal; the live call
/// (`f 1 2`) saturates it.
pub fn inconsistent_arity_saturating_instance(s: &mut TermStore) -> Hash {
    source(s, r"(\f. if 0 < 1 then f 1 2 else f 1) (\a b. a + b)")
}

/// As `inconsistent_arity_saturating_instance`, but the live call is `f 1`
/// and the literal is 1-ary.
pub fn inconsistent_arity_under_applying_instance(s: &mut TermStore) -> Hash {
    source(s, r"(\f. if 1 < 0 then f 1 2 else f 1) (\a. a + 100)")
}

/// As `inconsistent_arity_saturating_instance`, with the literal capturing
/// the outer parameter `k`.
pub fn inconsistent_arity_capturing_instance(s: &mut TermStore) -> Hash {
    source(s, r"\k. (\f. if 0 < 1 then f 1 2 else f 1) (\a b. k + a + b)")
}

/// As `inconsistent_arity_saturating_instance`, with the literal chosen at
/// run time by an `if` on the outer parameter.
pub fn inconsistent_arity_runtime_chosen_instance(s: &mut TermStore) -> Hash {
    source(s, r"\pick. (\f. if 0 < 1 then f 1 2 else f 1) (if 0 < pick then (\a b. a + b) else (\a b. a - b))")
}

/// `iterate` with one dead call site (`g x 999`, behind `1 < 0`) that
/// makes `g` inconsistently classified. Bare; applied, it is
/// `inconsistent_arity_loop_carried_parameter_loop`.
pub fn inconsistent_arity_iterate(s: &mut TermStore) -> Hash {
    source(s, "rec f n g x = if 1 < 0 then g x 999 else if n <= 0 then x else f (n - 1) g (g x)")
}

/// A loop that creates, in its self-call argument, a closure capturing its
/// closure-typed loop parameter `g`.
pub fn iterate_creating_a_closure_over_g(s: &mut TermStore) -> Hash {
    source(s, r"rec f n g x = if n <= 0 then x else f (n - 1) g (g x + (\y. g y + 1) x)")
}

/// `factorial` bound by `let` and called at 10: a self-recursive
/// combinator used as a value.
pub fn let_bound_factorial_10(s: &mut TermStore) -> Hash {
    source(s, "let fact = rec f n = if n <= 1 then 1 else n * f (n - 1) in fact 10")
}

/// A literal lambda whose body picks between two closures over `x`, applied
/// to `x`, its result passed to `\g. g 5`.
pub fn calls_a_capturing_closure_picked_by_if(s: &mut TermStore) -> Hash {
    source(s, r"\x. (\g. g 5) ((\x. if 0 < x then (\y. x + y) else (\y. x - y)) x)")
}

/// A self-recursive combinator partially applied (one argument of two) and
/// completed through `\g. g 1`.
pub fn a_pap_of_a_self_recursive_combinator(s: &mut TermStore) -> Hash {
    source(s, r"(\g. g 1) ((rec f n acc = if n <= 0 then acc else f (n - 1) (n * acc)) 3)")
}

/// As `a_pap_of_a_self_recursive_combinator`, with the combinator capturing
/// the outer parameter `z`.
pub fn a_pap_of_a_capturing_self_recursive_combinator(s: &mut TermStore) -> Hash {
    source(s, r"\z. (\g. g 1) ((rec f n acc = if n <= 0 then acc else f (n - 1) (n * acc + z)) 3)")
}

/// `over_application_if_between_closures` with its three arguments as
/// parameters.
pub fn over_application_if_between_closures_of_params(s: &mut TermStore) -> Hash {
    source(s, r"\p q r. (\a b. if 0 < a then (\c. a + b + c) else (\c. a - b + c)) p q r")
}
```

- [ ] **Step 4: Convert the sites** by the Method, with a temporary assert at each. Rows are named by inventory
  shape id; every row with that id in the inventory is a site.

| Inventory id | Replacement | Sites (inventory rows) |
|---|---|---|
| S1 | `samples::twice_inc_5` | eval `higher_order_terms_still_work`; jit `non_capturing_higher_order_terms_now_compile`; compile `applying_twice_to_a_literal_inc_*`; proof `twice_inc_5_gets_*`, `one_closure_terms_proof_is_rejected_against_anothers_type` (store `s` only) |
| S2 | `samples::capturing_closure_loop` | eval `deep_tail_recursion_creating_and_calling_a_fresh_closure_*`; compile `self_recursion_creating_a_fresh_capturing_closure_*` |
| S3-S6 | the four `inconsistent_arity_*_instance` functions | three sites each (jit, compile, proof) |
| S7, S8 | `samples::a_pap_non_capturing`, `samples::a_pap_capturing` | three sites each |
| S9 | `let_bound_factorial_10` | jit, compile, proof |
| S11 | `samples::factorial` | proof `recursive_term_is_out_of_scope`, `one_functions_theorem_proof_is_rejected_against_anothers_type` (into `s2`), `non_tail_recursion_gets_a_universal_proof_now` |
| S12 | `inconsistent_arity_parameter` | compile, proof |
| S13 + S14 | `it` = `inconsistent_arity_iterate`; `top` = `samples::inconsistent_arity_loop_carried_parameter_loop(&mut s, n)` | jit `a_tail_recursive_loop_compiles_*` (n = 10); proof `a_tail_recursive_loop_carrying_*` (loop over n = 0, 1, 10, with the assert inside the loop) |
| S15 + S16 | `it` = `iterate_creating_a_closure_over_g`; `top` = glue over `it` (see Step 5) | jit and proof `a_closure_created_in_a_self_call_argument_capturing_*` |
| S17 | jit: `it` = `samples::iterate`, `top` = `samples::closure_typed_loop_carried_parameter_loop(&mut s, 10)`; proof (S17~): `samples::iterate` plus glue for `3 (\y. y + 1) 5` | jit and proof `a_closure_typed_loop_carried_parameter_compiles_and_is_kernel_verified` |
| S18 | `calls_a_capturing_closure_picked_by_if` | compile `a_capturing_closure_compiles_*` (delete helper `calls_its_closure_arg_with_5` and the comment that leaves out the picker redex); proof `calling_a_literal_lambda_whose_own_body_picks_*` |
| S19, S20 | `a_pap_of_a_self_recursive_combinator`, `a_pap_of_a_capturing_self_recursive_combinator` | jit, proof |
| S21 | `over_application_if_between_closures_of_params` | jit, proof |
| twins without an S id | the sample in the inventory's `twin` column | proof `straight_line_term_*` (`straight_line`), `genuinely_higher_order_term_is_out_of_scope` (`twice`), `tail_recursive_gcd_with_two_base_cases_*` (`gcd_with_two_base_cases`), `fibonacci_two_self_calls_*` (`fib`), `a_directly_called_capturing_closure_*` (`a_capturing_closure_call`), `an_over_applied_partial_application_root_gets_a_closure_proof` first term (`over_application_pap_producing_root`) |

Not in T1: S10 (T3), S18~ (T2), S22 (T4), and every row with no twin or S id.

- [ ] **Step 5: Glue.** Where a test keeps `it` and applies it, keep the joining calls and parse only the leaves. For
  S16, for example:

```rust
let it = samples::iterate_creating_a_closure_over_g(&mut s);
let inc = samples::inc(&mut s);
let (five, zero) = (source(&mut s, "5"), source(&mut s, "0"));
let partial = s.app2(it, five, inc);
let top = s.app(partial, zero);
```

`s.lit(5)` is also acceptable for a lone literal leaf; prefer whichever the surrounding test already uses. Assert
both `it` and `top` against the old builder.

- [ ] **Step 6: Imports.** Add `source` and the new names to each test module's `use crate::samples::{...}` line.
  Drop names, and `PrimOp` imports, that no code uses any more; `cargo test` warnings show which.
- [ ] **Step 7: Mutate, then gate.** Plant two mutations as in the Method (one in a new shape function's body, one
  in a test's glue leaf), see each fail, then undo them. Run the gate. Expected: all pass, and the lib count equals
  the baseline.
- [ ] **Step 8: Strip, then gate.** Delete the old builders, the asserts and the helper. Re-run the gate; expected as
  in Step 7, with no warnings (`grep -c "^warning" "$TEMP/stage.log"` gives 0).
- [ ] **Step 9: README.** In `README.md`, change the `samples.rs` row to:

```markdown
| `samples.rs` | The sample terms, written as source: the benchmarks', the demo's, the corpus unit tests and `tests/golden_wat.rs` run over, and (outside the corpus) shapes that tests in several files share. |
```
- [ ] **Step 10: Commit** (`T1: samples::source and twelve shared test shapes replace their hand-built copies`), with
  the counts in the body.

### Task 2 (T2): the rest of `proof/tests.rs`

**Files:** Modify `src/proof/tests.rs`.

**Interfaces:** Consumes `samples::source`, `samples::inc`, `samples::iterate`, `samples::twice`.

- [ ] **Step 1: Convert** every proof row in the inventory that is class A with no twin and no S id (S18~ included).
  Use the row's `source` column as the starting text, and keep the old builder with its assert. Special cases:
  - **Loop rows** (`{n}`, `{a}`, `{x}`, `{s}`, `(a, c)` placeholders): one `format!` in the loop body, for example
    `source(&mut s, &format!(r"(\a. if 0 < a then (\c d. c - d) else (\c d. d - c)) ({a}) ({c}) ({d})"))`, with every
    placeholder parenthesised (Review Focus). Where the row
    says `f`, `root` or `helper` is "reused", parse that piece once before the loop, keep it, and join with glue
    inside the loop. The assert goes inside the loop.
  - **`a_capturing_clo_returning_root_declines_without_evaluating_its_own_argument`:**
    - `pick_a` stays hand-built (spec D5). Add one line above it: `// Open on `cap`, used alone: the parser rejects it.`
    - `top` becomes source built with `format!`, with the sum written as
      `std::iter::repeat("1").take(301).collect::<Vec<_>>().join(" + ")`.
    - The comment's "300-deep" becomes 301.
    - `let_wrapper`, which goes to `param_types_for`, gets its own `source` call; parsing it again in the same store
      gives the same hash.
  - **`a_shared_subterm_is_denoted_once`:** stays as it is, with one line above the build:
    `// Hand-built: an open body (\`x\` free), passed to \`setup\` with arity 1.`
  - **`a_closure_typed_ifs_own_result_used_as_a_value_gets_a_closure_proof`:** the helper `dec` goes, as `\z. z - 1`
    inside the source.
  - **Rows "from samples ... + hand wrapper"** (`a_directly_called_self_recursive_combinator_*`,
    `recursion_combined_with_closures_is_out_of_scope`,
    `a_partially_applied_literal_lambda_with_mixed_parameter_types_*`, `a_whole_functions_result_being_a_closure_*`):
    the whole term becomes one source string, unless the test also uses the sample's hash on its own, in which case
    use glue.
- [ ] **Step 2: Mutate, then gate** as in the Method.
- [ ] **Step 3: Strip, then gate.** Check that every remaining `s.var(` in `src/proof/tests.rs` lies inside the two D5 builders
  (`grep -n "s\.var(" src/proof/tests.rs`).
- [ ] **Step 4: Commit** (`T2: proof tests' remaining terms as source`), with the counts.

### Task 3 (T3): the rest of `jit.rs`, and `doubling` to `test_corpus.rs`

**Files:** Modify `src/jit.rs` (test module), `src/test_corpus.rs`, `src/compile/tests.rs` (the `doubling` call
sites only).

**Interfaces:** Produces `pub(crate) fn doubling(s: &mut TermStore, d: u32) -> Hash` in `crate::test_corpus`. T4 does
not touch it again.

- [ ] **Step 1: Move `doubling`.** Add to `src/test_corpus.rs`:

```rust
/// `\x. t_d`, `t_0 = x`, `t_{i+1} = t_i + t_i`: d + 2 distinct nodes, 2^(d+1)
/// as a tree, so its source text is exponentially long.
pub(crate) fn doubling(s: &mut TermStore, d: u32) -> Hash {
    let mut t = s.var(0);
    for _ in 0..d {
        t = s.prim(crate::term::PrimOp::Add, t, t);
    }
    s.abs(t)
}
```

  Replace its three-line module doc with: `//! Three test terms `samples` can't hold: one with a free variable (the
  parser rejects unbound names), one built programmatically past `spec_check::MAX_NODES`, and a doubled DAG whose text
  is exponentially long.`, wrapped at 80 columns like the old one. Delete `fn doubling` from `src/compile/tests.rs` and call
  `crate::test_corpus::doubling` at its three call sites. In `jit.rs`'s `a_term_too_big_as_a_tree_is_interpreted`,
  replace the inline loop with `let h = crate::test_corpus::doubling(&mut s, 16);`, keeping the old loop and an assert
  until the strip. Drop the restating comment `t_{i+1} = t_i + t_i`, which the helper's doc now holds, and keep its
  "past `MAX_TREE_NODES`" reason.
- [ ] **Step 2: Convert** every other jit row that is class A with no twin and no S id:
  - `a_closure_of_the_wrong_arity_off_the_samples_*`, `an_ill_typed_branch_*`, `a_closure_argument_of_the_wrong_arity_*`;
  - `invoke_agrees_with_the_interpreter_past_the_stack_buffer_threshold`, as one literal string
    `r"\a b c d e f g h i j. j + i + h + g + f + e + d + c + b + a"`;
  - `division_agrees_with_the_interpreter_at_i64_min_over_negative_one`;
  - `a_returned_closure_now_compiles_via_over_application`.
- [ ] **Step 3: Mutate, gate, strip, gate** as in the Method.
- [ ] **Step 4: Commit** (`T3: jit tests' remaining terms as source; doubling moves to test_corpus`), with the counts.

### Task 4 (T4): the rest of `compile/tests.rs`, and the frozen seed-2117 term

**Files:** Modify `src/compile/tests.rs`.

- [ ] **Step 1: Dump the seed-2117 term.**
  - Add a temporary line `eprintln!("SEED2117 {}", crate::syntax::print(&s, h));` after the term is built in
    `a_pap_wrappers_own_supplied_argument_creating_more_closures_does_not_corrupt_its_environment`.
  - Run `cmd //c start "" //b //wait //belownormal //affinity CFF cargo test --release -j 4 --lib a_pap_wrappers_own_supplied_argument -- --nocapture > "$TEMP/seed.log" 2>&1; grep SEED2117 "$TEMP/seed.log"`.
  - Expected: one line of source.
- [ ] **Step 2: Freeze it.**
  - Replace the generator copy (the nested `Rng` use, `random_arith_op`, `random_cmp_op` and the `gen_*` functions)
    and the build with `let h = source(&mut s, r"<printed text>");`.
  - Keep the old build beside it with an assert until the strip.
  - Above it, add: `// Frozen from tests/compile_fuzz.rs's generator at seed 0x00C0_FFEE_1E55 ^ 2117 (printed with
    syntax::print).`
  - Keep the comment that explains why this term (a wrapper's own argument creating closures); drop the one about
    how it is generated.
  - The pinned `apply_term(h, [10, -20]) == -370` stays.
  - Rename the printer's names only if the result still matches by hash.
- [ ] **Step 3: Convert** every other compile row that is class A with no twin and no S id:
  - `resetting_hp_between_calls_*`, `a_self_recursive_combinator_can_also_capture_*`,
    `calling_a_closure_reached_through_a_captured_free_variable_*`;
  - `a_combinator_never_reached_as_a_bare_value_*`;
  - `curried_application_is_indistinguishable_*`;
  - the S22 loop `an_over_applied_literal_lambda_returning_a_closure_compiles_and_matches_interpreter`: one
    test-local `format!` over `({a})` (parenthesised: `a` is -5 in one variant), parsing `f` once before the loop if
    the test reuses it; assert inside the loop;
  - `a_rejected_candidate`'s `sp.store.lit(0)`, which becomes `source(&mut sp.store, "0")`.
- [ ] **Step 4: Mark the exceptions.**
  - `classify_recognizes_only_a_saturated_self_call_and_only_a_peelable_callee`: add one line above its builds,
    `// Hand-built: classify takes an open body (f, a, b free); the parser accepts only closed terms.`
  - `an_unbound_variable_is_rejected_not_a_panic`: add `// Hand-built: the parser rejects an unbound name.`
  - `a_term_is_compiled_only_up_to_a_tree_size` already calls `test_corpus::doubling`, whose doc gives the reason.
- [ ] **Step 5: Mutate, gate, strip, gate** as in the Method. The strip also deletes the generator helpers and any
  import only they used (the `Rng`/SplitMix64 code).
- [ ] **Step 6: Commit** (`T4: compile tests' remaining terms as source; the seed-2117 term frozen`), with the counts.

### Task 5 (T5): the rest of `eval.rs`, the samples doc fixes, docs

**Files:** Modify `src/eval.rs` (test module), `src/samples.rs` (two doc comments), this plan, the spec.

- [ ] **Step 1: Convert** eval's remaining rows:
  - `countdown`: delete the helper; its one caller gets `source(&mut s, "rec f n = if n <= 0 then 0 else f (n - 1)")`;
  - `div_by_zero_errors_instead_of_panicking`: `source(&mut s, "1 / 0")`.
  
  Then mutate, gate, strip, gate as in the Method.
- [ ] **Step 2: Sample docs (spec D6).** In `src/samples.rs`:
  - On `non_tail_closure_carrying_recursion`, replace the first two doc lines ("The same shape as `proof::tests`' ...")
    with: `/// The loop of `proof::tests`' `a_non_tail_self_call_carrying_an_inconsistently_classified_closure_parameter_gets_a_per_instance_proof`
    /// without its dead call site (`if 1 < 0 then g x 999 else`), so `g` is consistently classified here;`. Keep
    the sentences that follow, from "fully saturated" on.
  - On `branching_non_tail_closure_carrying_recursion`, do the same with that test's name and its dead call site
    `if 1 < 0 then g 0 999 else`.
  - Terms unchanged. Run `--test golden_wat --test rule_match_census` to confirm.
- [ ] **Step 3: Docs grep.** Run `git grep -n "calls_its_closure_arg_with_5\|fn countdown\|fn dec\b\|gen_closure_block\|samples::parse\|fn doubling" -- '*.md' '*.rs'`.
  Expected: only `test_corpus.rs`'s `doubling`, and this plan or the spec. Fix any other hit. Also grep
  `docs/tier-cycle.md`, `ROADMAP.md` and `RELATED_WORK.md` for each converted test name that changed; no test is
  renamed, so expect none.
- [ ] **Step 4: Full suite.**
  - Run `cmd //c start "" //b //wait //belownormal //affinity CFF cargo test --release -j 4 > "$TEMP/full.log" 2>&1; grep "test result" "$TEMP/full.log"`.
  - Expected: every line `ok`, and the lib count equals the baseline.
  - Check `Get-Process python, cargo, rustc -EA 0` for leftovers.
- [ ] **Step 5: Close.**
  - Plan front matter: `status: done`, with a closing note giving per-stage line counts against the estimated
    ~1,300, total comparisons and mutations, and any rulings.
  - Spec front matter: `status: done`.
  - Commit (`T5: eval tests' terms as source; samples docs no longer claim twins; plan done`).

### Final review

One whole-branch review of `main..test-terms`:
- Opus, since the branch is over 300 changed lines.
- It is given the spec, this plan, the inventory and the Review Focus above.
- It reads every comment within 5 lines of a converted site, and checks each D5 exception's comment.

After that come the fixes, the full suite, and then finishing-a-development-branch (merge is the user's call).

## Outcome (2026-10-27)

T1 to T5 landed on `test-terms`: 17af427, 9cae3dd, 757ecc7, 0076365, fd8c29f, then the final review's comment
fixes in the next commit. Each stage was gated
with the temporary asserts in place and again after the strip: lib 358 passed / 2 ignored, golden_wat 2,
rule_match_census 2, 0 warnings. The full suite passed at T5.

| Stage | Hash comparisons | Mutations caught | Lines (+/-) |
|---|---|---|---|
| T1 | 57 | 3 | +264 / -1104 |
| T2 | 43 | 3 | +135 / -752 |
| T3 | 7 | 3 | +31 / -97 |
| T4 | 8 (9 at run time) | 3 | +70 / -289 |
| T5 | 2 | 2 | +13 / -30 (code only) |
| Total | 117 | 14 | +513 / -2272, net -1759 against the survey's ~1,300 |

There are more comparisons than the spec's 112 converted terms, because kept sub-hashes and the `doubling` call
were also checked. One mutation per stage was planted by the reviewer, not the implementer.

Hand-built terms left: the six D5 tests. Four carry a one-line comment. The two that call `test_corpus::doubling`
rely on that function's doc (T4 Step 4). After the strip, the test modules of `jit.rs` and
`eval.rs` build no term by hand. None of the test modules of `compile`, `jit.rs` or `eval.rs` imports `PrimOp` any
more.

Rulings:
- **T2.** A loop that keeps a sub-hash (`it`, `step`, `pick`, `f`) parses it from a local `*_src` string, and
  embeds that string in each iteration's `format!` rather than joining with `s.app`. D3 allows a piece to be parsed
  alone or inside the whole term, and the embedded form reads as one term.
- **T4.**
  - The S22 loop keeps no separate `f` hash, since nothing uses it alone.
  - The test's assert on the RNG's first draw (`choice == 1`) was deleted with the generator. It checked the
    generator, not the term.
  - The frozen seed-2117 text keeps `syntax::print`'s `v0..v5` names.
- **Comments.** When a comment's first line was deleted as a restatement, the rest was re-wrapped. Comment stubs
  that predate the branch (`jit.rs`: "have missed", "Same shape as") were left alone.
- **Final review** (Opus, no Critical findings).
  - The one Important finding was fixed: a comment in
    `a_literal_lambda_picking_between_two_different_arity_closures_is_out_of_scope` restated a term without its
    picker redex.
  - Its minor findings were fixed too: comments that named builder locals the conversion removed (`it`, `inner`,
    `closure1`, `f_lit`, `f_abs`, `add_lit`, `mega`, `HUGE_S`, `f x y z`), a restated term in jit's
    closure-typed-loop test, and one over-long line.
  - Left as they are:
    - the cleanup plan's "keeps two terms": a dated outcome, true when written, and `test_corpus.rs`'s module doc
      holds the current count;
    - one local `let inc = inc(&mut s)` that shadows the shape function.
