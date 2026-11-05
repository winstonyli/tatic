## 33. One classifier for the compiler and every proof walker

§28 proposed unifying `denote` and `compile_node` as "one traversal
with two backends". Reading the code showed that shape doesn't exist.
There are five denoters -- `denote`, `denote_with_placeholders`,
`denote_closure_typed`, `denote_closure`, and the `eval_dyn` family --
and they are different proof methods (symbolic, induction with
placeholders, per-execution trace), each covering a different slice of
what `compile_node` accepts. They are not one walk that could share a
backend. What they, `compile_node`, and the scope-gating walkers
(`collect_literals*`, `find_self_calls`, `return_type_of`,
`prime_closure_postulates`, `classify_step`, `scan_for_closure_calls`,
...) do share is a case analysis. Each did it by hand, some from
`compile.rs`'s `match_self_call`/`unwind_app_spine`, some through
`proof.rs`'s own `classify_app_node`.

**The change.** `compile::classify` returns a `Shape` -- `If`,
`SelfCall`, `VarCall`, `CombinatorCall` (a literal callee that peels to
`arity > 0`), `OtherCall`, `Var`, `Lit`, `Prim`, `Combinator { is_rec }`
-- and all 16 of those functions now dispatch on it. `compile_node` and
every denoter start with the same `match`. `classify_app_node` became
`app_shape`, which only *refines* an application-shaped `Shape` with the
closures fragment's parameter types. The rules it fixes in one place:
- a saturated self-call is recognised before any other application,
  and only when saturated -- under- or over-applied, it is a `VarCall`;
- a callee counts as a combinator only if it peels to a function;
- `If` conditions: `compile::is_comparison` is defined by `cmp_instr`
  itself, and `classify_tree`'s soundness check (a condition must only
  ever denote `0` or `1`, §28) now uses it instead of a hand-copied
  `Lt | Le | Eq`.

Each consumer still decides which shapes it supports and what they
mean. Behaviour-preserving with one deliberate exception:
`scan_for_closure_calls` used to accept any `Abs`/`Rec` callee and rely
on `register` rejecting a non-function `Rec` at codegen. It now declines
at the scan. Both paths end in the same decline.

**Verify-teeth.** Making `classify` treat over-application as
`OtherCall` -- a one-line change in one function -- fails 16 tests
across `compile::tests` (1), `jit::tests` (2) and `proof::tests` (13).
Both sides really do read the same classification. A new
`compile::tests::classify_recognizes_only_a_saturated_self_call_and_only_a_peelable_callee`
pins the two non-obvious rules above.

**What this does not do.** It makes *classification* drift impossible.
It does nothing about *meaning* drift: `compile_node`'s `i64.div_s` and
`proof.rs`'s postulated `op_ref(Div)` are still hand-kept twins, as is
every other per-case translation. §28's correction says why no refactor
reaches that.

