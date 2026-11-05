use super::*;

#[test]
fn twice_inc_5_gets_a_kernel_checked_closure_proof() {
    // The higher-order demo term main.rs uses: a
    // closed (arity 0), non-recursive expression combining two
    // non-capturing combinators.
    let mut s = TermStore::new();
    let applied = twice_inc_5(&mut s);

    let proof = prove_closure_expr(&s, applied).expect("(twice inc) 5 should get a closure proof");
    assert_eq!(proof.arity, 0);
    kernel::check_in(
        &proof.globals,
        &Ctx::new(),
        &proof.proof,
        &kernel::id(proof.result_ty, proof.denotation, proof.denotation),
    )
    .expect("the recorded proof should independently re-typecheck");

    // Also actually compiles -- the proof and the compiler agree on
    // this term being in scope.
    assert!(compile::try_compile(&s, applied).is_some());
}

#[test]
fn twice_alone_gets_a_kernel_checked_closure_proof() {
    // twice itself, standalone: f is a closure-typed parameter (always
    // called with 1 argument), x a plain Int parameter.
    let mut s = TermStore::new();
    let t = twice(&mut s);

    let proof = prove_closure_expr(&s, t).expect("twice alone should get a closure proof");
    assert_eq!(proof.arity, 2);
    kernel::check_in(
        &proof.globals,
        &Ctx::new(),
        &proof.proof,
        &kernel::id(proof.result_ty, proof.denotation, proof.denotation),
    )
    .expect("the recorded proof should independently re-typecheck");
}

#[test]
fn a_directly_called_self_recursive_combinator_gets_a_closure_proof() {
    // A direct static call to a self-recursive combinator,
    // the App-root `Term::Rec` branch (mirroring the `Term::Abs`
    // direct-call path `twice_inc_5` already exercises): the call is
    // postulated opaque either way, so widening the pattern needed no
    // new proof machinery.
    let mut s = TermStore::new();
    let applied = source(&mut s, "(rec f n = if n <= 1 then 1 else n * f (n - 1)) 10");

    let proof = prove_closure_expr(&s, applied).expect("fact(10) should get a closure proof");
    assert_eq!(proof.arity, 0);
    kernel::check_in(
        &proof.globals,
        &Ctx::new(),
        &proof.proof,
        &kernel::id(proof.result_ty, proof.denotation, proof.denotation),
    )
    .expect("the recorded proof should independently re-typecheck");

    assert!(compile::try_compile(&s, applied).is_some());
}

#[test]
fn a_self_recursive_combinator_used_as_a_value_gets_a_closure_proof() {
    // `let fact = rec f n = .. in fact 10` desugars to `(\g. g 10) fact`
    // (found via the REPL -- see syntax.rs/repl.rs, and
    // jit::tests::a_let_bound_self_recursive_function_compiles_and_is_kernel_verified
    // for the same shape checked directly against jit.rs): `fact`
    // itself, a bare `Term::Rec` value, gets registered
    // (`ClosureCombinators::register`) the same way a non-recursive
    // literal does, then called through the closure-typed
    // parameter of `\g. g 10` via call_indirect.
    let mut s = TermStore::new();
    let applied = let_bound_factorial_10(&mut s);

    let proof = prove_closure_expr(&s, applied).expect("(\\g. g 10) fact should get a closure proof");
    assert_eq!(proof.arity, 0);
    kernel::check_in(
        &proof.globals,
        &Ctx::new(),
        &proof.proof,
        &kernel::id(proof.result_ty, proof.denotation, proof.denotation),
    )
    .expect("the recorded proof should independently re-typecheck");

    assert!(compile::try_compile(&s, applied).is_some());
}

#[test]
fn a_partially_applied_self_recursive_combinator_used_as_a_value_gets_a_closure_proof() {
    // fact(1) supplied as a 1-of-1 partial application isn't a
    // meaningful example on its own (fact's arity is already 1), so
    // use a 2-ary self-recursive combinator instead, applied to 3
    // (under-applied by one arg) and passed to `\g. g 1`.
    // pap_ref no longer rejects a recursive root -- shape::peel/
    // shape::free_vars/param_types_for were already generic over
    // is_rec (a call is always postulated opaque regardless), and
    // compile.rs's register_partial_app/lower_wat.rs's emit_pap_wrapper
    // never special-cased it either (a PAP wrapper only ever forwards a
    // static call to its root, indifferent to whether that root's own
    // codegen happens to loop), so the only thing standing in the way
    // was pap_ref's own extra is_rec check.
    let mut s = TermStore::new();
    let top = a_pap_of_a_self_recursive_combinator(&mut s);

    let proof = prove_closure_expr(&s, top)
        .expect("a partially applied self-recursive combinator used as a value should get a closure proof");
    assert_eq!(proof.arity, 0);
    kernel::check_in(
        &proof.globals,
        &Ctx::new(),
        &proof.proof,
        &kernel::id(proof.result_ty, proof.denotation, proof.denotation),
    )
    .expect("the recorded proof should independently re-typecheck");

    assert!(compile::try_compile(&s, top).is_some());
}

#[test]
fn partial_application_of_a_capturing_self_recursive_combinator_gets_a_closure_proof() {
    // The two pap_ref restrictions lifted independently this session
    // (a capturing root, then a self-recursive root) combined in one
    // term, to confirm they actually compose rather than each having
    // only been checked in isolation: the combinator captures z from
    // the *enclosing* scope (not one of its own parameters), and is
    // itself partially applied (one arg short) -- passed to `\g. g 1`
    // as before.
    let mut s = TermStore::new();
    let top = a_pap_of_a_capturing_self_recursive_combinator(&mut s);

    let proof = prove_closure_expr(&s, top).expect(
        "a partially applied self-recursive combinator that also captures an outer variable should get a closure proof",
    );
    assert_eq!(proof.arity, 1);
    kernel::check_in(
        &proof.globals,
        &Ctx::new(),
        &proof.proof,
        &kernel::id(proof.result_ty, proof.denotation, proof.denotation),
    )
    .expect("the recorded proof should independently re-typecheck");

    assert!(compile::try_compile(&s, top).is_some());
}

#[test]
fn inconsistent_call_arity_for_a_parameter_is_still_out_of_scope_for_the_closure_proof() {
    // `f`, a *parameter*, called with
    // inconsistent arities (1 then 2) at different call sites.
    // Unrelated to partial application of a *literal lambda* (see
    // a_partially_applied_literal_lambda_used_as_a_value_gets_a_closure_proof
    // below for that, now-covered, case): param_types_for declines to
    // classify an inconsistently-called parameter as `Clo`-typed at
    // all (mapping `ArityUse::Inconsistent` to `None`, exactly like
    // an absent entry), so `denote_closure`'s own purely-structural
    // classification -- which has no way to reason about a call
    // whose outcome depends on which concrete value `f` turns out to
    // be at runtime, not on term shape alone -- still can't make
    // sense of either call site here.
    //
    // `compile::try_compile` no longer agrees this is out of scope,
    // though: it now compiles this exact shape via a curried,
    // one-argument-at-a-time dispatch mechanism (see
    // `compile::tests::inconsistent_call_arity_for_a_parameter_now_compiles_via_curried_dispatch`
    // and the runnable capability tests alongside it). That's an
    // intentional, expected gap, not a regression -- extending
    // kernel-checked proof coverage to this new capability is
    // separately scoped future work (see `docs/related-work/`'s own
    // notes on why it doesn't fit this file's existing, purely
    // structural methodology), not a byproduct of compile.rs alone
    // accepting more terms.
    let mut s = TermStore::new();
    let g = inconsistent_arity_parameter(&mut s);

    assert!(prove_closure_expr(&s, g).is_none());
}

#[test]
fn a_partially_applied_literal_lambda_used_as_a_value_gets_a_closure_proof() {
    // `(\x y. x + y) 3` is under-applied by one argument, then passed to
    // `\g. g 4`. It is denoted via pap_ref's new `Less`-arity branch (a
    // Clo-typed value), then completed through the caller's own
    // call_indirect the same way any other Clo-typed argument would be.
    let mut s = TermStore::new();
    let top = a_pap_non_capturing(&mut s);

    let proof = prove_closure_expr(&s, top).expect("a partially applied literal lambda used as a value should get a closure proof");
    assert_eq!(proof.arity, 0);
    kernel::check_in(
        &proof.globals,
        &Ctx::new(),
        &proof.proof,
        &kernel::id(proof.result_ty, proof.denotation, proof.denotation),
    )
    .expect("the recorded proof should independently re-typecheck");

    // Also actually compiles, and the two readings agree on scope.
    assert!(compile::try_compile(&s, top).is_some());
}

#[test]
fn a_partially_applied_literal_lambda_with_mixed_parameter_types_gets_a_closure_proof() {
    // `twice`'s own param_types are
    // [None(x), Some(1)(f)] (mixed: x plain Int, f closure-typed),
    // unlike the add-based test above where both parameters happen to
    // be Int and so can't distinguish a correct `pap_ref` type slice
    // from an incorrectly-shifted one. Supplying only `f` (`inc`) is a
    // 1-of-2 partial application, so pap_ref's type must be built from
    // param_types[arity-k..] = param_types[1..2] = [Some(1)] (f's own
    // Clo type) -- not param_types[..k] = param_types[0..1] (x's Int
    // type, wrong parameter entirely). `\h. h 5` then
    // completes the wrapper with the missing `x` argument.
    let mut s = TermStore::new();
    let top = source(&mut s, r"(\h. h 5) ((\f x. f (f x)) (\y. y + 1))");

    let proof = prove_closure_expr(&s, top).expect("a partially applied combinator with mixed parameter types should get a closure proof");
    assert_eq!(proof.arity, 0);
    kernel::check_in(
        &proof.globals,
        &Ctx::new(),
        &proof.proof,
        &kernel::id(proof.result_ty, proof.denotation, proof.denotation),
    )
    .expect("the recorded proof should independently re-typecheck");

    assert!(compile::try_compile(&s, top).is_some());
}

#[test]
fn a_partially_applied_capturing_literal_lambda_used_as_a_value_gets_a_closure_proof() {
    // The same shape as
    // compile::tests::partial_application_of_a_capturing_literal_lambda_compiles,
    // which compiles via Lowering::pap_env composing the wrapper's own
    // environment with a copy of the (capturing) root's own
    // environment. pap_ref now mirrors that: when the root captures,
    // its postulated type takes the root's own Env as a leading
    // parameter (the same convention call_ref already uses), and every
    // PAP call site builds that environment via build_env_expr and
    // prepends it to the wrapper's own arguments -- so this now gets a
    // kernel-checked proof too, not just empirical sample verification.
    let mut s = TermStore::new();
    let g = a_pap_capturing(&mut s);

    let proof = prove_closure_expr(&s, g).expect("a partially applied capturing literal lambda used as a value should get a closure proof");
    assert_eq!(proof.arity, 1);
    kernel::check_in(
        &proof.globals,
        &Ctx::new(),
        &proof.proof,
        &kernel::id(proof.result_ty, proof.denotation, proof.denotation),
    )
    .expect("the recorded proof should independently re-typecheck");

    assert!(compile::try_compile(&s, g).is_some());
}

#[test]
fn if_branches_with_different_pap_extra_arity_are_not_conflated_into_a_false_proof() {
    // `root`, the two-parameter literal `\p a. ..`, has its
    // own saturated call (both p and a supplied) denoting a further
    // Clo_1, not Int, so `root`'s 1-of-2 partial application `root x`
    // (p supplied, a still missing) genuinely has remaining shape
    // Clo_2 (`a`, then `b`) -- not Clo_1, which is what every call
    // site of `combinator_return_type` assumed before `pap_extra_arity`
    // was folded in (see the doc comment on `pap_extra_arity` itself).
    //
    // The top term puts that genuinely-Clo_2 value in one arm of an `If` whose other
    // arm, `\y. y + 1`, is a genuine, unrelated Clo_1 -- and then calls
    // the result with a single argument, as if it were uniformly
    // Clo_1. Before the fix this compiled to a claimed *universal*
    // (`refl`-based) kernel proof despite the two branches genuinely
    // disagreeing in arity; the kernel itself can't catch this,
    // because `Clo_k` is a literal Pi type family, so a wrong-but-
    // internally-consistent arity still typechecks on its own. The fix
    // must make this decline instead.
    let mut s = TermStore::new();
    let top = source(
        &mut s,
        r"\x. (\g. g 5) (if x == 0 then (\p a. if a == 0 then (\b. b) else (\b. a + b)) x else (\y. y + 1))",
    );

    assert!(
        prove_closure_expr(&s, top).is_none(),
        "the two If branches genuinely differ in arity (Clo_2 vs Clo_1); \
         claiming a universal proof here would be unsound"
    );
}

#[test]
fn over_application_of_a_literal_lambda_is_still_out_of_scope_for_the_closure_proof() {
    // A two-parameter literal lambda called with three arguments -- rejected by
    // denote_closure's own args.len() > arity check (proof.rs has no
    // fragment for over-application at all, unlike compile.rs, which
    // now compiles the shape -- see lower_wat.rs's module docs and
    // compile::tests::an_over_applied_literal_lambda_returning_a_closure_compiles_and_matches_interpreter
    // -- though not *this* term specifically: the lambda's body is a plain
    // `Int`, never a further closure, so this one is genuinely
    // ill-typed and would only ever be trusted via jit.rs's own
    // sample verification, never a kernel-checked proof).
    let mut s = TermStore::new();
    let over_applied = source(&mut s, r"(\x y. x + y) 1 2 3");

    assert!(prove_closure_expr(&s, over_applied).is_none());
}

#[test]
fn calling_a_literal_lambda_whose_own_body_picks_between_two_closures_gets_a_closure_proof() {
    // The same term compile.rs's own
    // a_capturing_closure_compiles_and_matches_interpreter test uses.
    // The picker (the literal lambda whose own body is the If) is
    // *directly called* (a fully-saturated application of a
    // literal lambda) -- `call_ref`'s own postulated type used to
    // always assume a directly-called combinator returns `Int`,
    // causing the call's claimed `Int` type to fail `\g. g 5`'s own
    // `.clo()?` check where it's used as `g`. `call_ref` now consults
    // `combinator_return_type` for its own return type instead of
    // universally assuming `Int` -- correctly classifying the picker's
    // body (an `If` between two closures) as `Clo`-typed, without
    // `call_ref` itself ever denoting the picker's own body -- so this
    // now gets a genuine kernel-checked proof.
    let mut s = TermStore::new();
    let f = calls_a_capturing_closure_picked_by_if(&mut s);

    assert!(compile::try_compile(&s, f).is_some(), "compile.rs should compile this via closure conversion");
    let proof = prove_closure_expr(&s, f).expect("picker's own Clo-typed body should now be reachable through call_ref");
    assert_eq!(proof.arity, 1);
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.proof, &kernel::id(proof.result_ty, proof.denotation, proof.denotation))
        .expect("the recorded proof should independently re-typecheck");
}

#[test]
fn a_literal_lambda_picking_between_two_different_arity_closures_is_out_of_scope() {
    // Same shape as the test above, except the picker's own `else`
    // branch now has arity *2*, not 1: `Clo`, before the
    // arity-indexed `Clo_k` refactor (`docs/types.md` section 7), was a
    // single, arity-blind kernel type, so this exact shape would have
    // kernel-*typechecked* under the old scheme (`ite_clo : Int -> Clo
    // -> Clo -> Clo` accepts any two `Clo`-typed branches, whatever
    // their underlying arity) while being genuinely unsound --
    // `\g. g 5`'s own `g 5` call commits to arity 1, silently wrong
    // whenever `picker` actually took the `else` branch. Both
    // `return_type_of`'s own arity-consistency check (in
    // `combinator_return_type`'s classification of `picker`'s body)
    // and, independently, `kernel::check`'s definitional-inequality
    // between `Clo_1` and `Clo_2` now reject this -- `call_ref` falls
    // back to assuming `picker`'s call is plain `Int`-typed (the
    // classifier can't determine a single consistent arity), which
    // then fails `\g. g 5`'s own `.clo()?` check on `g`, so
    // `prove_closure_expr` returns `None` rather than a
    // kernel-"verified" but unsound proof.
    let mut s = TermStore::new();
    let f = source(&mut s, r"\x. (\g. g 5) ((\x. if 0 < x then (\y. x + y) else (\y z. x - y - z)) x)");

    assert!(
        prove_closure_expr(&s, f).is_none(),
        "an If between two different-arity closures should be rejected, not accepted as a single blind Clo"
    );
}

#[test]
fn an_over_applied_literal_lambda_returning_a_closure_gets_a_closure_proof() {
    // Same shape as compile::tests::
    // an_over_applied_literal_lambda_returning_a_closure_compiles_and_matches_interpreter/
    // jit::tests::an_over_applied_literal_lambda_returning_a_closure_compiles_and_is_kernel_verified.
    // Unlike the test above (a directly-called combinator's own
    // Clo-typed result used as a *value*), this is genuine
    // over-application: `f`'s own saturated call (`f a b`) is
    // denoted first via `call_ref` (now correctly `Clo`-typed, same
    // classifier), then dispatched on the extra argument `c`
    // directly, exactly the way calling a closure-typed variable
    // already denotes.
    let mut s = TermStore::new();
    let top = over_application_if_between_closures_of_params(&mut s);

    assert_eq!(eval::apply_term(&s, top, &[10, 3, 100]).unwrap(), 113, "interpreter sanity check");
    assert_eq!(eval::apply_term(&s, top, &[-5, 3, 100]).unwrap(), 92, "interpreter sanity check");

    let proof = prove_closure_expr(&s, top).expect("an over-applied literal lambda returning a closure should get a proof");
    assert_eq!(proof.arity, 3);
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.proof, &kernel::id(proof.result_ty, proof.denotation, proof.denotation))
        .expect("the recorded proof should independently re-typecheck");
}

#[test]
fn a_capturing_closure_used_as_a_value_gets_a_closure_proof() {
    // `\y. x + y` captures `x`, g's
    // own parameter, and is used as a plain *value* (an argument to
    // `\h. h 5`), not directly called -- exercises
    // ClosureCombinators::register's mk_clo_ref path and
    // build_env_expr together with the pre-existing
    // call-through-a-parameter path, unmodified.
    let mut s = TermStore::new();
    let g = source(&mut s, r"\x. (\h. h 5) (\y. x + y)");

    let proof = prove_closure_expr(&s, g).expect("a capturing closure used as a value should get a proof now");
    assert_eq!(proof.arity, 1);
    kernel::check_in(
        &proof.globals,
        &Ctx::new(),
        &proof.proof,
        &kernel::id(proof.result_ty, proof.denotation, proof.denotation),
    )
    .expect("the recorded proof should independently re-typecheck");

    for x_val in [-5, 0, 1, 42] {
        let interpreted = eval::apply_term(&s, g, &[x_val]).unwrap();
        assert_eq!(interpreted, x_val + 5, "sanity check on the term itself, not the proof");
    }
}

#[test]
fn a_directly_called_capturing_closure_gets_a_closure_proof() {
    // `\y. x + y` captures the enclosing function's own `x`, and
    // is called *directly* (a literal lambda in function position),
    // exercising call_ref's new Env-prefixed signature and
    // build_env_expr in the direct-call branch of denote_closure.
    let mut s = TermStore::new();
    let g = a_capturing_closure_call(&mut s);

    let proof = prove_closure_expr(&s, g).expect("a directly called capturing closure should get a proof now");
    assert_eq!(proof.arity, 1);
    kernel::check_in(
        &proof.globals,
        &Ctx::new(),
        &proof.proof,
        &kernel::id(proof.result_ty, proof.denotation, proof.denotation),
    )
    .expect("the recorded proof should independently re-typecheck");
}

#[test]
fn a_capture_of_a_closure_typed_value_gets_a_closure_proof() {
    // `cb 1` makes g's own
    // scan recognize `cb` as closure-typed (Some(1)); `\y. cb`
    // separately captures that same `cb`. `build_env_expr`'s own
    // capture signature (`capture_sig`) now lets `Env`/`mk_env` hold
    // a `Clo`-typed slot honestly, rather than assuming every capture
    // is `Int` -- so this gets a proof.
    //
    // Note what this proof is (and isn't) claiming: `h`'s own call
    // (`h 5`, through `call_ref`, which -- like every opaque call in
    // this fragment -- always postulates an `Int` return) is used as
    // the `Prim::Add`'s own second operand, denoted `Int` accordingly.
    // The concrete closure actually bound to `h` here (`\y. cb`)
    // returns a `Clo`, not an `Int`, so this particular term always
    // errors at runtime on both readings (confirmed: interpreted and
    // compiled both return `Err(TypeError)`) -- but the proof was
    // never a runtime-correctness certificate to begin with: it's a
    // `refl` argument that both readings compose the *same* postulated
    // symbols identically, which holds regardless of what those
    // symbols are later found to compute. `jit.rs`'s own sample-based
    // `verify()` independently agrees this term is "verified" too,
    // in exactly the same weak sense (`Err == Err`) -- consistent,
    // not contradictory, and the same honest limitation `call_ref`'s
    // own always-`Int`-return assumption already has everywhere else
    // in this fragment.
    let mut s = TermStore::new();
    let g = source(&mut s, r"\cb. cb 1 + (\h. h 5) (\y. cb)");

    let proof =
        prove_closure_expr(&s, g).expect("a capture of a closure-typed value should get a closure proof");
    assert_eq!(proof.arity, 1);
    kernel::check_in(
        &proof.globals,
        &Ctx::new(),
        &proof.proof,
        &kernel::id(proof.result_ty, proof.denotation, proof.denotation),
    )
    .expect("the recorded proof should independently re-typecheck");

    assert!(compile::try_compile(&s, g).is_some());
}

#[test]
fn a_whole_functions_result_being_a_closure_now_gets_a_closure_proof() {
    // An `If` choosing between two
    // closures was already covered (denote_closure's own `Term::If`
    // via `ite_clo` -- see
    // a_closure_typed_ifs_own_result_used_as_a_value_gets_a_closure_proof
    // below), but `prove_closure_expr`'s own *top-level* call still
    // hardcoded `.int()?`, rejecting this term for an orthogonal
    // reason: `f`'s own body (the whole function's result) denotes as
    // `Clo`, not `Int`. Now that `Clo` is arity-indexed (`Clo_k`),
    // `prove_closure_expr` picks `result_ty` from `denote_closure`'s
    // own `Denoted` tag instead of assuming `Int` -- `Clo_1` here,
    // both `inc`s sharing arity 1 -- so this is now proven, not
    // rejected.
    let mut s = TermStore::new();
    let f = source(&mut s, r"\x. if 0 < x then (\y. y + 1) else (\y. y + 1)");

    let proof = prove_closure_expr(&s, f).expect("a Clo-typed top-level result should now get a closure proof");
    assert_eq!(proof.arity, 1);
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.proof, &kernel::id(proof.result_ty, proof.denotation, proof.denotation))
        .expect("the recorded proof should independently re-typecheck");
}

#[test]
fn a_bare_closure_typed_parameter_read_gets_a_closure_proof() {
    // `f`'s own arity is inferred as 1
    // only because `infer_closure_arities` needs *some* use-site call
    // to assign it one at all (see `docs/types.md` section 3.1's own
    // "Default" rule), supplied here by the condition `f 0` (its own
    // value otherwise unused); both branches then read `f` itself as
    // a bare value, exercising `Term::Var(i)`'s own `Denoted::Clo`
    // case as `prove_closure_expr`'s own top-level result -- the
    // simplest possible instance of the new capability.
    let mut s = TermStore::new();
    let h = source(&mut s, r"\f. if f 0 then f else f");

    let proof = prove_closure_expr(&s, h).expect("a bare Clo-typed parameter read should get a closure proof");
    assert_eq!(proof.arity, 1);
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.proof, &kernel::id(proof.result_ty, proof.denotation, proof.denotation))
        .expect("the recorded proof should independently re-typecheck");
}

#[test]
fn a_closure_typed_ifs_own_result_used_as_a_value_gets_a_closure_proof() {
    // The If's own result (Denoted::Clo, via
    // the new `ite_clo` postulate) is used as the *argument* of `\g x. g x`
    // (matching its own closure-typed parameter `g`), not as a
    // directly-called combinator's implicit return -- exactly the
    // shape `ite_clo` actually needs to be reachable (see
    // calling_a_literal_lambda_whose_own_body_picks_between_two_closures_is_still_out_of_scope
    // above for the shape that still isn't).
    let mut s = TermStore::new();
    let f = source(&mut s, r"\w. (\g x. g x) (if 0 < w then (\y. y + 1) else (\z. z - 1)) 5");

    let proof = prove_closure_expr(&s, f).expect("an If between two closures used as a value should get a closure proof");
    assert_eq!(proof.arity, 1);
    kernel::check_in(
        &proof.globals,
        &Ctx::new(),
        &proof.proof,
        &kernel::id(proof.result_ty, proof.denotation, proof.denotation),
    )
    .expect("the recorded proof should independently re-typecheck");

    assert!(compile::try_compile(&s, f).is_some());
}

#[test]
fn an_if_mismatching_int_and_clo_branches_is_out_of_scope() {
    // One branch Clo (`inc`), the other Int (`5`) -- neither ite_ref nor ite_clo
    // applies; rejected as a genuine type mismatch, not silently
    // accepted as either.
    let mut s = TermStore::new();
    let f = source(&mut s, r"\w. (\g x. g x) (if 0 < w then (\y. y + 1) else 5) 5");

    assert!(prove_closure_expr(&s, f).is_none());
}

#[test]
fn one_closure_terms_proof_is_rejected_against_anothers_type() {
    // Adversarial: twice_inc_5's proof, checked in its own ctx, against
    // twice-alone's type -- must be rejected, not somehow typecheck.
    let mut s = TermStore::new();
    let applied = twice_inc_5(&mut s);
    let applied_proof = prove_closure_expr(&s, applied).expect("(twice inc) 5 should get a closure proof");

    let mut s2 = TermStore::new();
    let t2 = twice(&mut s2);
    let alone_proof = prove_closure_expr(&s2, t2).expect("twice alone should get a closure proof");

    assert!(
        kernel::check_in(
            &applied_proof.globals,
            &Ctx::new(),
            &applied_proof.proof,
            &kernel::id(alone_proof.result_ty, alone_proof.denotation, alone_proof.denotation),
        )
        .is_err(),
        "(twice inc) 5's proof should be rejected against twice-alone's type"
    );
}

// --- over-applied closures, applied to literal arguments -----------------------
//
// Calls whose saturated result is itself a closure (chosen by an `If`, a partial application, or a further call) and is
// then applied to more arguments, with every argument a literal. These are the shapes the deleted per-call witness
// engine (`eval_and_prove`, 2026-10-26 "CU3") had a special case for; `prove_closure_expr` covers each one with no
// shape-specific code, and `prove_closure_expr_instance` declines them (its trace-following inliner handles closures
// reached through a parameter, not a closed over-application). The arithmetic is asymmetric so an argument-order
// mix-up changes the value the interpreter check pins.

/// `h(args)` evaluates to `expected` in the interpreter, and `prove_closure_expr` proves `h` for every input, with a
/// proof that re-checks from scratch.
fn check_closed_closure_proof(s: &TermStore, h: Hash, args: &[i64], expected: i64) {
    assert_eq!(eval::apply_term(s, h, args).unwrap(), expected, "{args:?}: interpreter sanity check");
    let proof = prove_closure_expr(s, h).unwrap_or_else(|| panic!("{args:?}: should get a closure proof"));
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.proof, &kernel::id(proof.result_ty, proof.denotation, proof.denotation))
        .expect("the recorded proof should independently re-typecheck");
}

#[test]
fn an_over_applied_if_between_two_non_symmetric_closures_gets_a_closure_proof() {
    let mut s = TermStore::new();
    for (a_val, c_val, d_val, expected) in [(5, 10, 3, 7), (-5, 10, 3, -7)] {
        let h = source(
            &mut s,
            &format!(r"(\a. if 0 < a then (\c d. c - d) else (\c d. d - c)) ({a_val}) ({c_val}) ({d_val})"),
        );
        check_closed_closure_proof(&s, h, &[], expected);
    }
}

#[test]
fn an_inner_closures_captures_resolve_against_its_roots_own_frame_in_a_closure_proof() {
    // The closures capture `w` from the frame of the `\w.` around the call.
    let mut s = TermStore::new();
    for (w_val, a_val, c_val, expected) in [(100, 10, 5, 115), (100, -10, 5, -115)] {
        let h = source(
            &mut s,
            &format!(r"\w. (\a. if 0 < a then (\c. a + w + c) else (\c. a - w - c)) ({a_val}) ({c_val})"),
        );
        check_closed_closure_proof(&s, h, &[w_val], expected);
    }
}

#[test]
fn an_over_applied_partial_application_root_gets_a_closure_proof() {
    let mut s = TermStore::new();
    let h = over_application_pap_producing_root(&mut s);
    check_closed_closure_proof(&s, h, &[], 53);

    // The same through two more levels of saturated calls that each return a closure.
    let h_term = source(&mut s, r"(\r. (\o. (\m. (\p q. p - q) m) o) r) 11 4");
    check_closed_closure_proof(&s, h_term, &[], 7);
}

#[test]
fn an_over_applied_partial_application_root_with_two_supplied_args_and_a_capture_gets_a_closure_proof() {
    // The inner lambda captures `y` from the wrapper, so it is only ever built inside it.
    let mut s = TermStore::new();
    let h = source(&mut s, r"(\x y. (\p q r. p * 100 + q * 10 + r + y) x y) 5 7 3");
    check_closed_closure_proof(&s, h, &[], 580);
}

#[test]
fn a_closure_reached_only_through_a_further_saturated_call_gets_a_closure_proof() {
    let mut s = TermStore::new();
    for (a_val, b_val, c_val, expected) in [(5, 3, 7, 37), (-5, 3, 7, 6)] {
        let h = source(
            &mut s,
            &format!(
                r"(\a b. if 0 < a then (\x. (\p q. p * 10 + q) x) b else (\y. y - 1)) ({a_val}) ({b_val}) ({c_val})"
            ),
        );
        check_closed_closure_proof(&s, h, &[], expected);
    }
}

#[test]
fn a_self_recursive_root_whose_body_never_self_calls_gets_a_closure_proof() {
    // A `Rec`-wrapped root that never self-calls.
    let mut s = TermStore::new();
    for (a_val, c_val, expected) in [(5, 3, 8), (-5, 10, 15)] {
        let h = source(
            &mut s,
            &format!(r"(rec helper a = if 0 < a then (\c. c + a) else (\c. c - a)) ({a_val}) ({c_val})"),
        );
        check_closed_closure_proof(&s, h, &[], expected);
    }
}

#[test]
fn a_nested_if_choosing_among_three_closures_gets_a_closure_proof() {
    let mut s = TermStore::new();
    for (a_val, c_val, expected) in [(5, 3, 4), (20, 3, 3), (-5, 3, 2)] {
        let h = source(
            &mut s,
            &format!(
                r"(\a. if 0 < a then (if 10 < a then (\c. c) else (\c. c + 1)) else (\c. c - 1)) ({a_val}) ({c_val})"
            ),
        );
        check_closed_closure_proof(&s, h, &[], expected);
    }
}
