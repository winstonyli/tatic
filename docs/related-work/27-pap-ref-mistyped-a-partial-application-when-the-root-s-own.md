## 27. pap_ref mistyped a partial application when the root's own saturated call itself returns a closure -- found and fixed

A fresh, from-scratch audit (independent of the prior 26-section punch
list) surfaced a genuine soundness bug in how `proof.rs` types a partial
application. `pap_ref` builds the postulated Pi type for `mk_pap_h_k`,
the wrapper standing in for a combinator `h` (arity `arity`) called with
only `k` of its arguments supplied. Every call site computing this
wrapper's "remaining shape" -- `pap_ref` itself, `return_type_of`'s
`Ordering::Less` (partial-application) arm, three `debug_assert_has_type`
sites in the three parallel closure-denotation pipelines
(`denote_with_placeholders`, `denote_closure_typed`, `denote_closure`),
and the PAP-shape classifiers `clo_eq_ref_pap`/
`classify_closure_if_tree_leaf` -- hardcoded that remaining shape as
`Clo_{arity-k}`, silently assuming `h`'s own saturated call always
denotes `Int`.

That assumption is false whenever `h`'s body itself returns a further
closure. For example `root = \p a. if a == 0 then (\b. b) else (\b. a +
b)`: `root`'s saturated call (both `p` and `a` supplied) denotes `Clo_1`,
not `Int`. So `root x` -- a 1-of-2 partial application, `p` supplied, `a`
still missing -- has genuine remaining shape `Clo_2` (`a`, then `b`), not
the `Clo_1` every one of the sites above assumed. Since `Clo_k` is a
*literal* kernel Pi type (`ClosurePostulates::clo_ty`), not an opaque
postulate, the kernel has no way to catch this on its own: a wrong-but-
internally-consistent arity still typechecks. Concretely: put that PAP
value in one arm of an `If` whose other arm is a genuine, unrelated
`Clo_1`, then call the result with a single argument as if both arms
agreed on arity. `prove_closure_expr` built and the kernel happily
accepted a `refl`-based proof claiming this was *universally* valid; the
compiled form was marked `is_kernel_verified`; and at a concrete
adversarial input reaching the mismatched arm, the compiled code --
genuinely dispatching one argument short -- returned whatever raw bits
its own extra `call_indirect` produced (garbage, not a trap), silently
disagreeing with the interpreter.

Fixed with one new shared helper:

```rust
fn pap_extra_arity(store: &TermStore, root: Hash) -> usize {
    combinator_return_type(store, root).flatten().unwrap_or(0)
}
```

and folding it into every site above: the remaining shape is
`Clo_{(arity-k) + pap_extra_arity(h)}`, not `Clo_{arity-k}`. This fold is
*exact*, not approximate: `Clo_j`/`Clo_m` are both literal, associative
Pi-type chains, so `Int^(arity-k) -> Clo_m` is definitionally the same
term, arrow for arrow, as `Clo_{(arity-k)+m}` -- not merely isomorphic to
it -- whenever the remaining `arity-k` parameters are themselves plain
`Int` (every call site already independently restricts to that case, the
same restriction `combinator_return_type`'s own callers already default
to: "undetermined" conservatively means "assume no widening," consistent
with this classifier's use everywhere else in the file).

Verified with a permanent regression test,
`if_branches_with_different_pap_extra_arity_are_not_conflated_into_a_false_proof`,
built from exactly the `root`/`If`-between-mismatched-arities shape
above, asserting `prove_closure_expr` returns `None`. Verify-teeth:
temporarily made `pap_extra_arity` return `0` unconditionally (reproducing
the pre-fix behavior at its single defining site rather than reverting
seven call sites by hand) and confirmed the new test fails exactly as
expected (the false universal proof reappears), then restored the real
definition and confirmed it passes again. Full validation green
afterward: `cargo build --all-targets`, `cargo clippy --all-targets`,
`cargo test --lib --bins` (190/190, including the new test), all four
fuzzers at release, and the release demo.

A distinct, deeper issue surfaced while investigating this one and is
**not** fixed here: even after this fix declines the false universal
proof, `jit.rs`'s `compile_verify_and_apply` still gates whether a
compiled form is *cached and trusted* purely on `verify()` -- a fixed,
finite sample battery -- with `kernel_verify` running only afterward and
purely informationally (it never un-installs an already-cached form).
A term whose compiled behavior only diverges from the interpreter at an
adversarially-chosen input outside that sample set can still reach a
caller silently wrong, with or without a kernel proof ever being
attempted. This is a structurally separate concern from the arity-typing
bug above (it's about `verify()`'s completeness, not about any specific
postulate's type) and needs its own scope discussion before further work
proceeds into it.

