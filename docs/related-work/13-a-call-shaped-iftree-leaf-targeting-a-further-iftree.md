## 13. A `Call`-shaped `IfTree` leaf targeting a further `IfTree` — already worked, confirmed rather than built

Section 10 above added `Call`-shaped leaf support to
`clo_eq_ref_if_tree`/`resolve_closure_if_tree`, for a leaf whose own
target is itself resolved via a further, recursive `build_clo_call_bridge`/
`resolve_closure_shape_to_leaf` pass. That recursive pass dispatches
generically on `ClosureRhsShape` (`IfTree`/`Pap`/`Call`), so the natural
follow-up question is whether a `Call`-shaped leaf's *own target* can
itself be an `IfTree` (as opposed to a bare `Abs`/`Pap`) — i.e., whether
the two mechanisms compose two levels deep, not just one.

They do, with zero additional code. `resolve_closure_shape_to_leaf`'s
`IfTree` arm was already written to walk an arbitrary `DecisionTree` down
to whichever `Leaf` the concrete literals select, and `resolve_closure_if_tree`
already returns `IfTreeLeafResolution::Indirect` for a `Call`-shaped leaf,
carrying the fully-resolved concrete value up through the same recursion
used for a root-level `Call`. Nothing in that path assumes the *target*
of a `Call`-shaped leaf is any particular shape — it just recurses through
`resolve_closure_shape_to_leaf` again, which handles `IfTree` exactly as
it would at the root.

Confirmed empirically, not just by re-reading the dispatch: a term of the
shape `root = \a b. if 0<a then g(b) else (\c. b*2+c)`, where `g` is
itself `\b. if 0<b then (\c. b+c) else (\c. b-c)` (so the `Call`-shaped
leaf's own target `g` has a further `If`-shaped body, selecting between
two different concrete closures depending on `g`'s own argument) —
hand-verified against `eval::apply_term` across three literal cases
distinguishing every branch (`root`'s own `If`, `g`'s own `If`, and the
final called closure), then run through `eval_and_prove_call_over` and
kernel-checked — passed on the first attempt, added as
`a_call_shaped_if_tree_leaf_whose_own_target_is_itself_a_further_if_tree_gets_a_concrete_instance`
in `proof.rs`. Verify-teeth here took a different shape than usual:
since the new test exercises existing, already-verified machinery in a
new combination rather than new code, there's no production-code
mutation to make fail-then-revert. Instead, corrupting one of the test's
own hardcoded `expected` values and re-running confirmed the test's
assertions are genuinely live (not vacuously true) — same discipline,
applied to the test harness rather than to `proof.rs` itself.

**Takeaway:** `resolve_closure_shape_to_leaf`'s generic, shape-dispatched
design (built for section 10's single level of `Call`-leaf indirection)
already generalizes to arbitrary depth for free, because it recurses
through its own dispatch rather than hardcoding what a `Call` target's
own shape must be. No further work item follows from this — it's a
confirmation, not a capability gap.

