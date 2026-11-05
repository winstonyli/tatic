use super::*;

#[test]
fn tail_recursive_gcd_gets_a_universal_proof() {
    let mut s = TermStore::new();
    let g = gcd(&mut s);

    let proof = prove_tail_recursive_universal(&s, g).expect("gcd should get a universal proof");
    assert_eq!(proof.arity, 2);
    // Independently re-typecheck from scratch.
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.theorem_proof, &proof.theorem_ty)
        .expect("the recorded theorem should independently re-typecheck");
}

#[test]
fn a_closure_typed_loop_carried_parameter_gets_a_universal_proof() {
    let mut s = TermStore::new();
    let it = iterate(&mut s);

    let proof = prove_tail_recursive_universal(&s, it).expect("iterate should get a universal proof");
    assert_eq!(proof.arity, 3);
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.theorem_proof, &proof.theorem_ty)
        .expect("the recorded theorem should independently re-typecheck");
}

#[test]
fn a_capturing_partial_application_created_inside_a_self_call_argument_gets_a_universal_proof() {
    // Same shape as capturing_closure_loop above, but the self-call argument
    // partially applies a *capturing* literal lambda (one argument
    // short) and completes it through `\g. g 4`, rather than creating and
    // immediately calling a fully-applied closure. This is exactly the
    // shape that exposed a real staleness bug, caught by compile_fuzz's
    // random-term fuzzing before this dedicated regression test existed:
    // a missed `mk_env_ref` push under scope-time priming (`docs/related-work/`
    // §70); kept as a regression test.
    let mut s = TermStore::new();
    let h = source(
        &mut s,
        r"rec f n acc = if n <= 0 then acc else f (n - 1) ((\g. g 4) ((\x y. x + y + acc) n))",
    );

    let proof = prove_tail_recursive_universal(&s, h)
        .expect("a self-recursive loop partially applying a fresh capturing literal each iteration should get a universal proof");
    assert_eq!(proof.arity, 2);
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.theorem_proof, &proof.theorem_ty)
        .expect("the recorded theorem should independently re-typecheck");

    assert!(compile::try_compile(&s, h).is_some());
}

#[test]
fn a_closure_created_in_a_leafs_own_top_level_expression_gets_a_universal_proof() {
    // The closure creation+call sits in the leaf's own top-level
    // expression (combined arithmetically with the recursive call),
    // not nested inside a self-call's own argument list --
    // find_self_calls/denote_closure now cover this too
    // (mirroring denote_closure's own Term::Abs | Term::Rec
    // handling), not just a self-call argument's own closure creation.
    let mut s = TermStore::new();
    let h = source(&mut s, r"rec f n = if n <= 0 then 0 else (\y. n + y) 5 + f (n - 1)");

    let proof = prove_tail_recursive_universal(&s, h)
        .expect("a closure created in a leaf's own top-level expression should get a universal proof");
    assert_eq!(proof.arity, 1);
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.theorem_proof, &proof.theorem_ty)
        .expect("the recorded theorem should independently re-typecheck");

    assert!(compile::try_compile(&s, h).is_some());
}

#[test]
fn a_closure_typed_loop_carried_parameter_compiles_and_is_kernel_verified() {
    // Cross-check against compile.rs/jit.rs directly, with an actual
    // closure argument (`inc`) baked into the term the same way
    // `twice_inc_5_gets_a_kernel_checked_closure_proof` does (there's
    // no way to pass a `Clo` value as a top-level runtime `i64`
    // argument -- see `jit.rs`'s own calling convention): this shape
    // already compiled before this proof extension existed
    // (`infer_closure_arities`/`build_node`'s Var-callee branch
    // already handled a Clo-typed loop-carried parameter generically),
    // it just had no proof strategy covering it -- now two do: this
    // *particular* term also happens to get `is_kernel_verified` via
    // `prove_closure_expr` directly (`applied` itself is a direct,
    // fully-saturated call to the self-recursive combinator `rec f ...`,
    // which `prove_closure_expr`'s own `Term::Rec` widening covers --
    // see a_directly_called_self_recursive_combinator_gets_a_closure_proof
    // below for the same shape without a closure-typed parameter
    // involved), independently of `prove_tail_recursive_universal`'s
    // own new coverage that
    // `a_closure_typed_loop_carried_parameter_gets_a_universal_proof`
    // above exercises directly against that combinator itself.
    let mut s = TermStore::new();
    let applied = source(&mut s, r"(rec f n g x = if n <= 0 then x else f (n - 1) g (g x)) 3 (\y. y + 1) 5"); // = 8

    let mut jit = crate::jit::JitEngine::new();
    let result = jit.apply(&s, applied, &[]).unwrap();
    assert_eq!(result, 8);
    let interpreted = eval::apply_term(&s, applied, &[]).unwrap();
    assert_eq!(result, interpreted);
    assert!(jit.is_kernel_verified(applied));
}

#[test]
fn one_functions_theorem_proof_is_rejected_against_anothers_type() {
    // Adversarial: does the kernel actually discriminate between two
    // different functions' universal proofs, or would it accept
    // anything with roughly the right shape? gcd's theorem_proof
    // (arity 2) checked against factorial's theorem_ty (arity 1, a
    // completely different Ev/combine/postulate layout) should be
    // rejected outright, not somehow typecheck by coincidence.
    let mut s = TermStore::new();
    let g = gcd(&mut s);
    let gcd_proof = prove_tail_recursive_universal(&s, g).expect("gcd should get a universal proof");

    let mut s2 = TermStore::new();
    let fact = factorial(&mut s2);
    let fact_proof = prove_tail_recursive_universal(&s2, fact).expect("factorial should get a universal proof");

    // gcd's proof, checked in gcd's own ctx (a proof is only
    // meaningful relative to the ctx it was built in), against
    // factorial's theorem_ty.
    assert!(
        kernel::check_in(&gcd_proof.globals, &Ctx::new(), &gcd_proof.theorem_proof, &fact_proof.theorem_ty).is_err(),
        "gcd's proof should be rejected against factorial's theorem type"
    );
}

#[test]
fn tail_recursive_countdown_gets_a_universal_proof_with_base_in_the_else_branch() {
    // Unlike `gcd` above, the tail call is the *then*-branch and the base case is the *else*-
    // branch, exercising the other `cond`-gating polarity
    // (`prove_tail_recursive_universal`'s `base_lit = 0` arm, vs gcd's
    // `base_lit = 1`) that gcd alone never touches.
    let mut s = TermStore::new();
    let countdown = source(&mut s, "rec f n = if 0 < n then f (n - 1) else n");

    let proof = prove_tail_recursive_universal(&s, countdown)
        .expect("countdown should get a universal proof");
    assert_eq!(proof.arity, 1);
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.theorem_proof, &proof.theorem_ty)
        .expect("the recorded theorem should independently re-typecheck");
}

#[test]
fn tail_recursive_gcd_with_two_base_cases_gets_a_universal_proof() {
    // Deeper than a single `If`: two base leaves (`b` at path
    // [a==0], `a` at path [a!=0, b==0]) and one tail leaf (`f b (a % b)`
    // at path [a!=0, b!=0]), exercising the widened
    // `prove_tail_recursive_universal` (one `Ev` constructor per leaf,
    // each gated by its own *conjunction* of path premises, not a
    // single top-level condition).
    let mut s = TermStore::new();
    let g = gcd_with_two_base_cases(&mut s);

    let proof =
        prove_tail_recursive_universal(&s, g).expect("gcd with two base cases should get a universal proof");
    assert_eq!(proof.arity, 2);
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.theorem_proof, &proof.theorem_ty)
        .expect("the recorded theorem should independently re-typecheck");
}

#[test]
fn non_tail_recursion_gets_a_universal_proof_now() {
    // Factorial: the self-call is nested inside a multiplication, not
    // tail position.
    // Generalizing Ev/ev_rec/loop_val to leaves with an arbitrary
    // self-call count, recombined via kernel::cong_n, covers this too
    // (this was the whole point of widening past tail recursion).
    let mut s = TermStore::new();
    let fact = factorial(&mut s);

    let proof =
        prove_tail_recursive_universal(&s, fact).expect("factorial should now get a universal proof");
    assert_eq!(proof.arity, 1);
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.theorem_proof, &proof.theorem_ty)
        .expect("the recorded theorem should independently re-typecheck");
}

#[test]
fn fibonacci_two_self_calls_gets_a_universal_proof() {
    // Naive Fibonacci: two self-calls combined by one Prim, exercising
    // combine_i for k=2 and kernel::cong_n's actual n>1 case
    // (factorial above only needs k=1, where cong_n's loop runs once).
    let mut s = TermStore::new();
    let fib = fib(&mut s);

    let proof = prove_tail_recursive_universal(&s, fib).expect("fibonacci should get a universal proof");
    assert_eq!(proof.arity, 1);
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.theorem_proof, &proof.theorem_ty)
        .expect("the recorded theorem should independently re-typecheck");
}

#[test]
fn an_if_nested_inside_an_arithmetic_leaf_gets_a_universal_proof() {
    // The base leaf has an `If` embedded as a *sub-expression* of a
    // `Prim`, not as the whole body of some branch, so `classify_tree`
    // doesn't extract it into the DecisionTree itself; it stays part
    // of the leaf's own expression instead, and (with no self-call
    // inside it here) `find_self_calls`/placeholder-mode `denote_closure`
    // just walk through it the same way they already walk a `Prim`.
    let mut s = TermStore::new();
    let g = source(&mut s, "rec f n = if n <= 0 then n + (if n == 0 then 1 else 2) else f (n - 1)");

    let proof = prove_tail_recursive_universal(&s, g).expect("a purely-arithmetic nested If should get a universal proof");
    assert_eq!(proof.arity, 1);
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.theorem_proof, &proof.theorem_ty)
        .expect("the recorded theorem should independently re-typecheck");
}

#[test]
fn a_clo_typed_nested_if_as_a_direct_self_call_argument_gets_a_universal_proof() {
    // `chosen = if n % 2 == 0 then g else h` is a self-call's own
    // argument (threaded into the next iteration's `g` slot), and both
    // branches are `Clo`-typed parameters, not `Int`s -- exercises
    // `denote_closure`'s widened `Term::If` arm (mirroring
    // `denote_closure`'s three-way Int/Int-or-Clo/Clo match via
    // `ite_clo_ref`), which builds each self-call argument's own
    // denotation for the leaf's `Ev` constructor. `g`/`h` are each
    // called directly (`g(n)`/`h(n)`) so `infer_closure_arities`
    // classifies both as `Clo`-typed arity-1 parameters in the first
    // place.
    let mut s = TermStore::new();
    let top = source(
        &mut s,
        "rec f n g h = if n <= 0 then 0 else f (n - 1) (if n % 2 == 0 then g else h) h + g n + h n",
    );

    let proof = prove_tail_recursive_universal(&s, top)
        .expect("a Clo-typed nested If as a direct self-call argument should get a universal proof");
    assert_eq!(proof.arity, 3);
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.theorem_proof, &proof.theorem_ty)
        .expect("the recorded theorem should independently re-typecheck");
}

#[test]
fn a_clo_typed_nested_if_as_an_ad_hoc_closures_own_argument_gets_a_universal_proof() {
    // Unlike the test above, the nested If here isn't a self-call's
    // own argument (find_self_calls's early self-call match would
    // consume the whole call node before ever walking into it); it's
    // the argument to an ad-hoc closure (`\h. h(x)`, itself capturing
    // `x` and calling its own `h` parameter, so `h` is itself
    // Clo-typed) created and called within the leaf, *alongside* a
    // separate, visible self-call in the same leaf's `Prim` tree. This
    // exercises placeholder-mode `denote_closure`'s own widened `Term::If`
    // arm -- the leaf-specific walker that builds the leaf's `combine`
    // function body -- rather than `denote_closure`'s. `g`/`g2`
    // are each called directly (`g(0)`/`g2(0)`) purely so
    // `infer_closure_arities` classifies both as `Clo`-typed.
    let mut s = TermStore::new();
    let top = source(
        &mut s,
        r"rec f n g g2 x = if n <= 0 then x else g 0 + g2 0 + (\h. h x) (if n % 2 == 0 then g else g2) + f (n - 1) g g2 x",
    );

    let proof = prove_tail_recursive_universal(&s, top).expect(
        "a Clo-typed nested If used as an ad-hoc closure's own argument, alongside a separate self-call in the same leaf, should get a universal proof",
    );
    assert_eq!(proof.arity, 4);
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.theorem_proof, &proof.theorem_ty)
        .expect("the recorded theorem should independently re-typecheck");
}

#[test]
fn recursion_combined_with_closures_is_out_of_scope() {
    // Even a trivial Rec wrapper puts a closures term out of scope for
    // prove_closure_expr when it's the *top-level* term itself that's
    // Rec-wrapped (unlike a self-recursive combinator called or used
    // as a value *inside* an otherwise non-recursive top-level term --
    // see a_self_recursive_combinator_used_as_a_value_gets_a_closure_proof
    // and a_directly_called_self_recursive_combinator_gets_a_closure_proof
    // below for that, now-covered, case): prove_closure_expr's own
    // top-level check still requires `h` itself to be non-recursive,
    // since it's `prove_tail_recursive_universal`'s job, not this fragment's, to
    // prove what a self-recursive function's *own* body computes.
    let mut s = TermStore::new();
    let wrapped = source(&mut s, r"rec f n = (\g x. g (g x)) (\y. y + 1) n");

    assert!(prove_closure_expr(&s, wrapped).is_none());
}

#[test]
fn a_closure_created_in_a_self_call_argument_capturing_a_closure_typed_loop_parameter_gets_a_universal_proof() {
    // Same closure-typed loop-carried parameter as `iterate`, but
    // each iteration *also* creates a fresh closure (`\y. g y + 1`)
    // that captures `g` itself (a `Clo`-typed value, not an `Int`).
    // The direct call `g x` is still needed here, unrelated to the
    // capture itself: `infer_closure_arities` never looks inside a
    // nested `Abs`'s own body (a lambda used as a plain value is
    // opaque to it, matching `denote_closure`'s own "a call is never
    // denoted by looking inside a body" discipline one level up), so
    // without *some* direct call to `g` at `it`'s own top level, `g`
    // would never be classified `Clo`-typed at all and this wouldn't
    // exercise the capture-typing question -- it would just be
    // rejected (or silently misclassified) for an unrelated reason.
    //
    // Exercises `denote_closure`'s own value-leaf registration
    // with a `Clo`-typed capture, inside `prove_tail_recursive_universal`'s full
    // induction pipeline (not just the non-recursive `prove_closure_expr`
    // fragment `a_capture_of_a_closure_typed_value_gets_a_closure_proof`
    // above checks).
    let mut s = TermStore::new();
    let it = iterate_creating_a_closure_over_g(&mut s);
    let inc = inc(&mut s);
    let (five, zero) = (source(&mut s, "5"), source(&mut s, "0"));
    let partial = s.app2(it, five, inc);
    let top = s.app(partial, zero);

    let proof = prove_tail_recursive_universal(&s, it)
        .expect("a closure created in a self-call argument capturing a closure-typed loop parameter should get a universal proof");
    assert_eq!(proof.arity, 3);
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.theorem_proof, &proof.theorem_ty)
        .expect("the recorded theorem should independently re-typecheck");

    // `inc` baked in as the initial g, run for real: each
    // iteration computes new_x = g(x) + (g(x)+1) = 2*inc(x) + 1 =
    // 2x + 3. Starting from x=0: 3, 9, 21, 45, 93 after 1..5
    // iterations (hand-derived and cross-checked against eval::apply_term
    // directly while building this test).
    assert_eq!(eval::apply_term(&s, top, &[]).unwrap(), 93);
    assert!(compile::try_compile(&s, top).is_some());
}

