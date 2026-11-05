## 24. proof.rs's closures-section doc comment still described the pre-migration opaque-Clo/apply_k design -- found and swept

The doc block opening `proof.rs`'s closures section (and roughly a dozen
smaller echoes scattered through the file) still described an earlier
design: a closure value postulated fully opaque (`Clo : Sort(0)`, the
same pattern `Int` itself uses) with a separate axiom, `apply_k : Clo ->
Int^k -> Int`, postulated once per arity to let a `call_indirect` site
apply one. That design was superseded in two steps this project's own
history already covers (`docs/related-work/` section 11, and the
`apply_ref`-removal writeup later in `proof.rs` itself): `Clo` was first
made arity-aware (`apply_k` renamed/reworked into a per-arity
`apply_ref(k)`), then `apply_ref` itself was removed entirely once
`Clo_k` became a *literal* kernel Pi type (`Int -> .. -> Int`, `k`
copies, built from ordinary `Pi` nodes via `ClosurePostulates::clo_ty`)
rather than an opaque `Sort(0)` postulate -- calling one through a
closure-typed parameter is now just ordinary `App`, checked by
`kernel::infer`'s own Pi-application rule, no per-arity axiom needed at
all. The `apply_ref`-era writeup (`proof.rs`, the "Caught a real bug
while building this" section) was correctly kept as history when
`apply_ref` was swept in an earlier pass; the older `apply_k` mentions,
predating even that, were simply never touched at either migration and
were still describing the axiom-based design in the present tense as if
it were current.

Swept every present-tense `apply_k`/`Clo : Sort(0)` mention (the main
closures-section header block, `build_universal`'s own doc, `denote_closure`'s
doc, `combinator_return_type`'s doc, `return_type_of`'s inline comment,
`ClosureCombinators::env_ty`'s doc, `call_ref`'s doc, and a test's own
doc comment) to describe the actual, current mechanism: `Clo_k` as a
real Pi type, ordinary `App` for the generic closure-typed-parameter
case, and `ite_clo_ref` as the one genuine remaining axiom (needed only
for an `If` choosing between two same-arity closures, since `Int` has no
case-eliminator in this kernel). Left untouched the handful of `apply_k`/
`apply_ref` mentions that are explicitly narrating history ("used to
be", "was removed", a bug-fix writeup describing the mechanism as it
existed *at the time*) -- those are accurate as written and rewriting
them to the present tense would make the history they're recording
harder to follow, not easier.

No code changed (comment-only), so verification here is `cargo build
--all-targets`, `cargo clippy --all-targets`, and `cargo doc --no-deps`
(to confirm no new broken intra-doc links -- the 9 pre-existing warnings,
all an unrelated `Hash` type-alias/derive-macro ambiguity, are
unchanged) staying clean, plus the full existing test/fuzz suite and the
release demo confirming the change is what it claims to be: purely
textual.

