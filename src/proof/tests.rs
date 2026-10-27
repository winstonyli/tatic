use super::*;
use crate::eval;
use crate::kernel::Ctx;
use crate::samples::{
    a_capturing_closure_call, a_pap_capturing, a_pap_non_capturing, capturing_closure_loop, factorial, fib, gcd,
    gcd_with_two_base_cases, inc, inconsistent_arity_loop_carried_parameter_loop, iterate,
    over_application_pap_producing_root, source, straight_line, twice, twice_inc_5,
};
use crate::test_corpus::{
    a_pap_of_a_capturing_self_recursive_combinator, a_pap_of_a_self_recursive_combinator,
    calls_a_capturing_closure_picked_by_if, inconsistent_arity_capturing_instance, inconsistent_arity_iterate,
    inconsistent_arity_parameter, inconsistent_arity_runtime_chosen_instance, inconsistent_arity_saturating_instance,
    inconsistent_arity_under_applying_instance, iterate_creating_a_closure_over_g, let_bound_factorial_10,
    over_application_if_between_closures_of_params,
};
use crate::term::TermStore;

#[test]
fn every_arith_postulates_starts_from_one_checked_prelude() {
    // `push` type-checks each entry (RELATED_WORK §69), so building the
    // 10-entry prelude per proof cost ~5 µs, half of a small proof.
    // Each `new` must reuse one checked copy: same nodes, not rebuilt.
    let a = ArithPostulates::new();
    let mut b = ArithPostulates::new();
    assert_eq!(a.p.globals.len(), 10);
    let (ga, gb) = (a.p.globals[1].get(), b.p.globals[1].get());
    let (kernel::Node::Pi(x, _), kernel::Node::Pi(y, _)) = (ga.node(), gb.node()) else { panic!("a binop's type is an arrow") };
    assert!(kernel::node_key(&x) == kernel::node_key(&y), "the prelude was rebuilt");
    // A proof's own pushes stay its own.
    b.lit(7);
    assert_eq!((a.p.globals.len(), b.p.globals.len()), (10, 11));
    assert_eq!(ArithPostulates::new().p.globals.len(), 10);
}

/// `a + a`, for a shared `a`, denotes `a` once: both operands of the
/// denotation share their children, so the kernel's pointer-keyed
/// caches see one subterm, not two copies (`RELATED_WORK.md` §48).
#[test]
fn a_shared_subterm_is_denoted_once() {
    // Hand-built: an open body (`x` free), passed to `setup` with arity 1.
    let mut s = TermStore::new();
    let x = s.var(0);
    let a = s.prim(PrimOp::Mul, x, x);
    let body = s.prim(PrimOp::Add, a, a);
    let (arith, params) = setup(&s, body, 1, None).unwrap();
    let d = denote(&s, body, &arith, &params).unwrap();
    // `d` is `App(App(+, da), da')`; `da`, `da'` are `App(App(*, x), x)`.
    let kernel::Node::App(plus_da, da2) = d.node() else { panic!() };
    let kernel::Node::App(_, da1) = plus_da.node() else { panic!() };
    let (kernel::Node::App(f1, _), kernel::Node::App(f2, _)) = (da1.node(), da2.node()) else { panic!() };
    assert!(kernel::node_key(&f1) == kernel::node_key(&f2), "the two operands were denoted separately");
}

#[test]
fn straight_line_term_gets_a_kernel_checked_proof() {
    let mut s = TermStore::new();
    let f = straight_line(&mut s);

    let proof = prove_pure_expr(&s, f).expect("straight-line term should be provable");
    assert_eq!(proof.arity, 2);
    // Independently re-typecheck from scratch (not just trusting the
    // `.ok()?` inside `prove_pure_expr`).
    kernel::check_in(
        &proof.globals,
        &Ctx::new(),
        &proof.proof,
        &kernel::id(proof.result_ty, proof.denotation, proof.denotation),
    )
    .expect("the recorded proof should independently re-typecheck");

    // This term is also handled by the interpreter and the WASM
    // compiler -- all three paths agree on which terms are in scope.
    assert!(compile::try_compile(&s, f).is_some());
}

/// Confirms a `Clo_k`-shaped value can be built as the literal curried
/// `Int -> .. -> Int` arrow type, reusing `Int` (already postulated by
/// `ArithPostulates`) instead of an opaque `Sort(0)` postulate family
/// (`RELATED_WORK.md` section 11):
///
/// 1. Such a value can be called directly via ordinary `kernel::app`,
///    typechecking as `Int` with no separate "how to call this" axiom
///    needed at all.
/// 2. `bool_rec` instantiated at a *constant* motive (`\_:Bool. A`) is a
///    real `ite : Bool -> A -> A -> A` for any `A`, with its
///    computation-rule axioms (`bool_rec_true_eq`/`bool_rec_false_eq`)
///    already proving `ite`'s own -- but this does *not* extend to
///    `ite_clo_ref`, whose condition is `Int`-typed rather than
///    `Bool`-typed and so has no bridge to `bool_rec`'s own motive.
/// 3. Two different arities are still genuinely distinct types --
///    `kernel::check` rejects a `Clo_3`-shaped value where a `Clo_2` is
///    expected, for free, from ordinary Pi-type structural inequality --
///    so this doesn't reopen the arity-blind-`Clo` unsoundness
///    `TYPES.md` section 6.2 documents.
#[test]
fn a_curried_int_arrow_can_stand_in_for_clo_k_with_zero_new_postulates() {
    fn curried_arrow(int_ty: &Expr, k: usize) -> Expr {
        let mut ty = *int_ty;
        for _ in 0..k {
            ty = kernel::arrow(*int_ty, ty);
        }
        ty
    }

    let mut arith = ArithPostulates::new();
    let nat = kernel::NatPostulates::new(&mut arith.p);

    // Push every postulate this prototype needs first -- two opaque
    // arity-2 closure values (f, g, exactly like
    // `ClosureCombinators::combinator_value`'s own postulated
    // constant), two opaque Ints to call the chosen one with, and one
    // opaque arity-3 closure value (h, for the arity-mismatch check) --
    // then resolve every reference in a final pass.
    let f_pos = arith.p.push(curried_arrow(&arith.int_ty(), 2));
    let g_pos = arith.p.push(curried_arrow(&arith.int_ty(), 2));
    let a_pos = arith.p.push(arith.int_ty());
    let b_pos = arith.p.push(arith.int_ty());
    let h_pos = arith.p.push(curried_arrow(&arith.int_ty(), 3));

    let int_ty = arith.int_ty();
    let clo2_ty = curried_arrow(&int_ty, 2);
    let clo3_ty = curried_arrow(&int_ty, 3);
    assert_ne!(clo2_ty, clo3_ty, "different arities must stay genuinely distinct types");

    let f = arith.p.get(f_pos);
    let g = arith.p.get(g_pos);
    let a = arith.p.get(a_pos);
    let b = arith.p.get(b_pos);
    let h = arith.p.get(h_pos);

    // A generic `ite`, derived (not postulated) from `bool_rec`
    // instantiated at the constant motive `\_:Bool. Clo2`.
    let bool_ty = nat.bool_ty(&arith.p);
    let const_motive = kernel::lam(bool_ty, kernel::shift(&clo2_ty, 0, 1));
    let cond = nat.true_(&arith.p);
    let chosen = kernel::app(
        kernel::app3(nat.bool_rec(&arith.p), const_motive, f, g),
        cond,
    );
    arith.p.check(&chosen, &clo2_ty).expect("ite(Clo2, true, f, g) should typecheck at Clo2");

    // Calling it directly through ordinary `App` -- no `apply_ref`
    // postulate anywhere in this construction at all.
    let called = kernel::app2(chosen, a, b);
    arith.p.check(&called, &int_ty)
        .expect("calling a Clo2-shaped value with 2 Ints should typecheck as Int, with no apply_ref axiom");

    // The computation rule (`ite(true) = f`) is already derivable from
    // `bool_rec_true_eq` at this instantiation -- no new `ite_true_eq`
    // postulate needed either.
    let true_eq_generic = nat.bool_rec_true_eq(&arith.p);
    let instantiated = kernel::app3(true_eq_generic, const_motive, f, g);
    let expected_ty = kernel::id(clo2_ty, chosen, f);
    arith.p.check(&instantiated, &expected_ty)
        .expect("bool_rec_true_eq, instantiated at Clo2, should already prove ite(Clo2,true,f,g) = f");

    // Arity mismatch is still rejected: a Clo3-shaped value can't stand
    // in where a Clo2 is expected -- the soundness gain `TYPES.md`
    // section 6.2/7 documents survives this representation change.
    assert!(
        arith.p.check(&h, &clo2_ty).is_err(),
        "a Clo3-shaped value must still be rejected where a Clo2 is expected"
    );
}

#[test]
fn recursive_term_is_out_of_scope() {
    let mut s = TermStore::new();
    let fact = factorial(&mut s);
    assert!(prove_pure_expr(&s, fact).is_none());
}

#[test]
fn genuinely_higher_order_term_is_out_of_scope() {
    let mut s = TermStore::new();
    let twice = twice(&mut s);
    assert!(prove_pure_expr(&s, twice).is_none());
}

#[test]
fn tail_recursive_call_gets_a_per_execution_proof() {
    let mut s = TermStore::new();
    let g = gcd(&mut s);

    for (a, b) in [(48, 18), (270, 192), (17, 5), (0, 7)] {
        let proof = prove_closure_expr_instance(&s, g, &[a, b])
            .unwrap_or_else(|| panic!("gcd({a},{b}) should get a per-execution proof"));
        assert_eq!(proof.arity, 2);
        kernel::check_in(
            &proof.globals,
            &Ctx::new(),
            &proof.proof,
            &kernel::id(proof.result_ty, proof.denotation, proof.denotation),
        )
        .expect("the recorded proof should independently re-typecheck");
    }
}

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
fn a_closure_created_and_called_inside_a_self_call_argument_gets_a_universal_proof() {
    let mut s = TermStore::new();
    let h = capturing_closure_loop(&mut s);

    let proof = prove_tail_recursive_universal(&s, h)
        .expect("a self-recursive loop creating a fresh capturing closure each iteration should get a universal proof");
    assert_eq!(proof.arity, 2);
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.theorem_proof, &proof.theorem_ty)
        .expect("the recorded theorem should independently re-typecheck");

    // The per-execution proof (`kernel_verified` never depended on it, see `jit.rs`'s own docs)
    // covers this shape too: a self-call argument that creates and calls a *capturing* literal
    // lambda (`root`'s own single capture, `acc`) whose body is a single `Prim` node.
    assert_eq!(eval::apply_term(&s, h, &[5, 0]).unwrap(), 15, "interpreter sanity check: 5+4+3+2+1");
    let instance = prove_closure_expr_instance(&s, h, &[5, 0])
        .expect("a self-call argument creating and calling a capturing closure should get a concrete instance");
    check_instance_proof(&instance);

    assert!(compile::try_compile(&s, h).is_some());
}

#[test]
fn a_capturing_partial_application_created_inside_a_self_call_argument_gets_a_universal_proof() {
    // Same shape as capturing_closure_loop above, but the self-call argument
    // partially applies a *capturing* literal lambda (one argument
    // short) and completes it through `\g. g 4`, rather than creating and
    // immediately calling a fully-applied closure. This is exactly the
    // shape that exposed a real staleness bug, caught by compile_fuzz's
    // random-term fuzzing before this dedicated regression test existed:
    // a missed `mk_env_ref` push under scope-time priming (`RELATED_WORK.md`
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
fn a_self_call_inside_a_nested_if_branch_gets_a_universal_proof_and_a_correct_instance() {
    // The recursive leaf's own `If` isn't the whole branch body
    // either (it's the right-hand operand of the outer `+`), and this
    // time each of its two branches contains its own self-call
    // occurrence: `find_self_calls` must find both (in the same
    // left-to-right order placeholder-mode `denote_closure` substitutes them
    // in), each becoming its own placeholder of the leaf's `combine`
    // function.
    let mut s = TermStore::new();
    let g = source(
        &mut s,
        "rec f n = if n <= 0 then 0 else n + (if n % 2 == 0 then f (n - 1) else f (n - 1) + 1)",
    );

    let proof = prove_tail_recursive_universal(&s, g).expect("a nested If with a self-call in each branch should still get a universal proof");
    assert_eq!(proof.arity, 1);
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.theorem_proof, &proof.theorem_ty)
        .expect("the recorded theorem should independently re-typecheck");

    // f(0)=0, f(1)=1+(f(0)+1)=2, f(2)=2+f(1)=4, f(3)=3+(f(2)+1)=8,
    // f(4)=4+f(3)=12, f(5)=5+(f(4)+1)=18.
    assert_eq!(eval::apply_term(&s, g, &[5]).unwrap(), 18, "interpreter sanity check");

    let instance = prove_closure_expr_instance(&s, g, &[5]).expect("f(5) should get an instance");
    check_instance_proof(&instance);
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

/// A long-running tail recursion used to take the *process* down.
///
/// `prove_closure_expr_instance` accumulates an expression that deepens
/// a couple of levels per trace step, and both the kernel's recursive
/// traversals and the recursive `Drop` of the resulting `Expr`
/// chain have finite stack. With the old 10,000-step budget a loop
/// like this built a ~40,000-level expression and died with
/// `STATUS_STACK_OVERFLOW` -- not a failed proof, a crashed process,
/// reachable from `jit::JitEngine::apply`. See `RELATED_WORK.md` §30.
///
/// Declining is the correct outcome here; surviving to decline is the
/// point of the test.
#[test]
fn a_long_running_trace_declines_instead_of_overflowing_the_stack() {
    // 20,000 iterations -- far past any budget, which is exactly the
    // case that used to crash rather than return.
    let mut s = TermStore::new();
    let h = source(&mut s, "rec f n x = if n <= 0 then x else f (n - 1) (x + 1)");

    assert_eq!(eval::apply_term(&s, h, &[20_000, 0]).unwrap(), 20_000);
    assert!(prove_closure_expr_instance(&s, h, &[20_000, 0]).is_none());

    // And a trace short enough to stay under every ceiling still
    // proves, so the bound above isn't simply switching the strategy
    // off.
    assert!(prove_closure_expr_instance(&s, h, &[10, 0]).is_some());
}

#[test]
fn an_instance_whose_branch_divides_by_zero_gets_no_proof() {
    // `eval` fails with DivByZero and the Wasm traps, so no branch is taken.
    // The instance prover once picked one by its own `x / 0 = 0` (cleanup plan CU1),
    // in a plain `If` and in a tail-recursive loop's condition alike.
    for (src, args) in [(r"if 7 / 0 then 1 else 2", &[][..]), (r"rec go n = if 10 / n then go (n - 1) else 0", &[3][..])] {
        let mut s = TermStore::new();
        let h = crate::syntax::parse(&mut s, src).unwrap();
        assert_eq!(eval::apply_term(&s, h, args), Err(eval::EvalError::DivByZero), "{src}");
        assert!(prove_closure_expr_instance(&s, h, args).is_none(), "{src}");
    }
}

#[test]
fn non_tail_recursion_gets_a_per_instance_proof() {
    let mut s = TermStore::new();
    let fact = factorial(&mut s);
    for n in [0, 1, 5, 10] {
        let proof = prove_closure_expr_instance(&s, fact, &[n]).unwrap_or_else(|| panic!("factorial({n}) should get a per-instance proof"));
        assert_eq!(proof.arity, 1);
        check_instance_proof(&proof);
    }
}

#[test]
fn fibonacci_branching_leaves_get_per_instance_proofs() {
    let mut s = TermStore::new();
    let fib = fib(&mut s);
    // The proof follows the whole call tree, so it grows with it (171 nodes at fib(8), 446 at fib(10)) and the step
    // budget declines from fib(11); the deleted memoized witness stayed linear and reached fib(16).
    for n in [1, 2, 8, 10] {
        let proof = prove_closure_expr_instance(&s, fib, &[n]).unwrap_or_else(|| panic!("fib({n}) should get a per-instance proof"));
        assert_eq!(proof.arity, 1);
        check_instance_proof(&proof);
    }
}

#[test]
fn one_functions_instance_proof_is_rejected_against_anothers_type() {
    // Same adversarial shape as one_functions_theorem_proof_is_rejected_against_anothers_type,
    // one level down: a per-instance proof built for one call must not typecheck against another's
    // (different function, different denotation).
    let mut s = TermStore::new();
    let g = gcd(&mut s);
    let gcd_proof = prove_closure_expr_instance(&s, g, &[48, 18]).expect("gcd instance proof");
    let fact = factorial(&mut s);
    let fact_proof = prove_closure_expr_instance(&s, fact, &[5]).expect("factorial instance proof");

    assert!(
        kernel::check_in(
            &gcd_proof.globals,
            &Ctx::new(),
            &gcd_proof.proof,
            &kernel::id(fact_proof.result_ty, fact_proof.denotation, fact_proof.denotation),
        )
        .is_err(),
        "gcd's instance proof should be rejected against factorial's instance type"
    );
}

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
    // pap_ref no longer rejects a recursive root -- compile::peel/
    // compile::free_vars/param_types_for were already generic over
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
    // separately scoped future work (see `RELATED_WORK.md`'s own
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
    // arity-indexed `Clo_k` refactor (`TYPES.md` section 7), was a
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
    // to assign it one at all (see `TYPES.md` section 3.1's own
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

/// Independently re-typechecks `proof` from scratch (not just
/// trusting the `.ok()?` inside `prove_closure_expr_instance`) --
/// the same discipline `tail_recursive_call_gets_a_per_execution_proof`
/// applies.
fn check_instance_proof(proof: &EquivalenceProof) {
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.proof, &kernel::id(proof.result_ty, proof.denotation, proof.denotation))
        .expect("the recorded per-instance proof should independently re-typecheck");
}

#[test]
fn prove_closure_expr_declines_where_the_instance_proof_picks_up() {
    // Same shape as compile.rs's
    // `an_inconsistently_called_parameter_matching_its_own_saturating_arity_agrees_with_the_interpreter`
    // -- documents exactly why the new strategy is needed: the
    // universal, structural proof still declines this shape (`f`'s
    // own inconsistent arity has no honest static type), even though
    // it's now perfectly provable per-instance.
    let mut s = TermStore::new();
    let top = inconsistent_arity_saturating_instance(&mut s);

    assert!(prove_closure_expr(&s, top).is_none());
    let proof = prove_closure_expr_instance(&s, top, &[]).expect("should be provable per-instance");
    assert_eq!(proof.arity, 0);
    check_instance_proof(&proof);
}

#[test]
fn an_under_applying_instance_gets_a_per_instance_proof_too() {
    // compile.rs's
    // `an_inconsistently_called_parameter_matching_its_own_under_applying_arity_agrees_with_the_interpreter`.
    let mut s = TermStore::new();
    let top = inconsistent_arity_under_applying_instance(&mut s);

    assert!(prove_closure_expr(&s, top).is_none());
    let proof = prove_closure_expr_instance(&s, top, &[]).expect("should be provable per-instance");
    check_instance_proof(&proof);
}

#[test]
fn a_captured_value_reached_through_an_inlined_call_gets_a_per_instance_proof() {
    // compile.rs's
    // `a_capturing_closure_reached_through_an_inconsistently_called_parameter_agrees_with_the_interpreter`
    // -- exercises the two-frame fix directly: `\a b. k + a + b`'s own
    // capture of `k` must resolve against `top`'s own (outer) frame, not
    // whatever frame is active once `\f. ...`'s body is inlined.
    let mut s = TermStore::new();
    let top = inconsistent_arity_capturing_instance(&mut s);

    assert!(prove_closure_expr(&s, top).is_none());
    for k_val in [100i64, -7] {
        let proof = prove_closure_expr_instance(&s, top, &[k_val]).unwrap_or_else(|| panic!("k={k_val} should be provable per-instance"));
        check_instance_proof(&proof);
    }
}

#[test]
fn a_runtime_chosen_literal_gets_a_per_instance_proof() {
    // compile.rs's
    // `a_parameters_own_value_arriving_via_an_if_between_two_literals_still_agrees_once_dispatched_generically`
    // -- the sharpest case: `f`'s own concrete identity isn't known
    // until `eval_dyn` concretely resolves the `If` choosing between
    // `\a b. a + b` and `\a b. a - b`, *before* `\f. ...`'s own body is
    // even reached.
    let mut s = TermStore::new();
    let top = inconsistent_arity_runtime_chosen_instance(&mut s);

    assert!(prove_closure_expr(&s, top).is_none());
    for pick_val in [1i64, -1] {
        let proof = prove_closure_expr_instance(&s, top, &[pick_val]).unwrap_or_else(|| panic!("pick={pick_val} should be provable per-instance"));
        check_instance_proof(&proof);
    }
}

#[test]
fn a_tail_recursive_loop_carrying_an_inconsistently_classified_closure_parameter_gets_a_per_instance_proof() {
    // Same shape as jit::tests::
    // a_tail_recursive_loop_compiles_and_is_kernel_verified_once_its_own_closure_parameter_turns_inconsistent
    // (and samples::inconsistent_arity_loop_carried_parameter_loop),
    // `g` baked in as `inc`. The dead `g x 999` call site
    // makes `param_types_for(it)` classify `g` as `Inconsistent` (->
    // `None`, same as an absent one) even though every call actually
    // taken passes it exactly one argument -- exactly the gap
    // `eval_dyn_direct_call` used to decline outright for a
    // `Rec`-wrapped root (`root_is_rec` check), and that
    // `eval_dyn_tail_recursive` now closes by following the loop's
    // own tail self-calls concretely instead of trying (and failing)
    // to classify `g` statically.
    let mut s = TermStore::new();
    let it = inconsistent_arity_iterate(&mut s);

    assert!(param_types_for(&s, it).unwrap().contains(&None));
    assert!(prove_closure_expr(&s, it).is_none(), "it itself has no fixed arity to prove universally over g's own slot");

    for n_val in [0i64, 1, 10] {
        let top = inconsistent_arity_loop_carried_parameter_loop(&mut s, n_val);
        assert!(prove_closure_expr(&s, top).is_none(), "n={n_val}: top's own call to it still can't be classified statically");
        let proof = prove_closure_expr_instance(&s, top, &[]).unwrap_or_else(|| panic!("n={n_val} should be provable per-instance"));
        check_instance_proof(&proof);
        assert_eq!(eval::apply_term(&s, top, &[]).unwrap(), n_val, "n={n_val}: sanity check against the interpreter");
    }
}

#[test]
fn a_loop_carried_call_result_that_itself_gates_termination_gets_a_per_instance_proof() {
    // `g` baked in as `\y. y - 1` -- unlike the test
    // just above (where the loop-carried call's own result, `g(x)`,
    // never itself influences which branch a later iteration takes,
    // only `n` does), here `g(x)`'s own concrete value is exactly
    // what the next iteration's own `x<=0` branches on. This is the
    // sharper regression guard `eval_dyn_tail_recursive`'s own
    // `eval_concrete_dyn` call needs: deliberately corrupting
    // `dyn_frame_to_env`'s own reversal (dropping its `.rev()`) is
    // *not* caught by the test above at all (nothing there ever reads
    // `x`'s own concrete numeral back), but *is* caught here, via the
    // sanity check against the interpreter below -- confirmed by
    // hand before trusting this test to mean anything.
    let mut s = TermStore::new();
    let it_src = r"rec f g x = if 1 < 0 then g x 999 else if x <= 0 then x else f g (g x)";
    let it = source(&mut s, it_src);

    assert!(param_types_for(&s, it).unwrap().contains(&None));

    for x_val in [0i64, 1, 5] {
        let top = source(&mut s, &format!(r"({it_src}) (\y. y - 1) ({x_val})"));

        let proof = prove_closure_expr_instance(&s, top, &[]).unwrap_or_else(|| panic!("x={x_val} should be provable per-instance"));
        check_instance_proof(&proof);
        assert_eq!(eval::apply_term(&s, top, &[]).unwrap(), 0, "x={x_val}: sanity check against the interpreter");
    }
}

#[test]
fn a_closure_argument_arriving_via_a_separate_saturated_call_that_itself_returns_a_clo_gets_a_per_instance_proof() {
    // `pick` (arity 1, its own saturated call returns a further Clo_2 -- `combinator_return_type`
    // recognizes an `If` between two same-arity literal lambdas, same
    // as `denote_closure`'s own `ite_clo` case does structurally);
    // `f` (arity 1, `k` called at
    // two different arities -- `Inconsistent`, same trick as every
    // other per-instance test); `top = f(pick(3))`. `pick(3)`'s own
    // result never arrives as a bare literal lambda value the way
    // every other per-instance test's closure argument does -- it's
    // the result of a *separate* saturated call, so `eval_dyn_direct_call`
    // must inline *that* call too (previously declined outright via
    // its own `return_ty.is_some()` check) before `f`'s own
    // needs-inline logic even gets a `Clo` to work with at all.
    let mut s = TermStore::new();
    let pick_src = r"\s. if 0 < s then (\a b. a + b) else (\a b. a - b)";
    let pick = source(&mut s, pick_src);

    let f_src = r"\k. if 0 < 1 then k 1 2 else k 1";
    let f = source(&mut s, f_src);

    assert!(param_types_for(&s, f).unwrap().contains(&None) && combinator_return_type(&s, pick).unwrap() == Some(2));

    for s_val in [3i64, -3] {
        let top = source(&mut s, &format!(r"({f_src}) (({pick_src}) ({s_val}))"));

        assert!(prove_closure_expr(&s, top).is_none(), "s={s_val}: f's own inconsistent k still can't be classified statically");
        let proof = prove_closure_expr_instance(&s, top, &[]).unwrap_or_else(|| panic!("s={s_val} should be provable per-instance"));
        check_instance_proof(&proof);
        let expected = if s_val > 0 { 1 + 2 } else { 1 - 2 };
        assert_eq!(eval::apply_term(&s, top, &[]).unwrap(), expected, "s={s_val}: sanity check against the interpreter");
    }
}

#[test]
fn a_non_tail_self_call_carrying_an_inconsistently_classified_closure_parameter_gets_a_per_instance_proof() {
    // Same dead-call-site trick as the tail-recursive precedent
    // (`a_tail_recursive_loop_carrying_an_inconsistently_classified_closure_parameter_gets_a_per_instance_proof`
    // above), but the self-call now sits *inside* `1 + ..`, not in
    // tail position. `classify_step`'s own
    // `match_self_call` only recognizes a self-call that's the
    // *entire* remaining leaf, so this leaf -- `1 + f(...)` -- is a
    // `Base` case as far as `eval_dyn_tail_recursive`'s own loop is
    // concerned; the embedded self-call inside it is only reachable
    // via `eval_dyn`'s own new recognition, calling back into
    // `eval_dyn_tail_recursive` one Rust stack frame at a time.
    let mut s = TermStore::new();
    let it_src = r"rec f n g x = if 1 < 0 then g x 999 else if n <= 0 then x else 1 + f (n - 1) g (g x)";
    let it = source(&mut s, it_src);

    assert!(param_types_for(&s, it).unwrap().contains(&None));

    for n_val in [0i64, 1, 3, 10, 100] {
        let top = source(&mut s, &format!(r"({it_src}) ({n_val}) (\y. y + 1) 0"));

        assert!(prove_closure_expr(&s, top).is_none(), "n={n_val}: top's own call to it still can't be classified statically");
        let proof = prove_closure_expr_instance(&s, top, &[]).unwrap_or_else(|| panic!("n={n_val} should be provable per-instance"));
        check_instance_proof(&proof);
        // x reaches n_val (one increment per level) by the time the
        // base case returns it, and "1 +" is added back once per
        // level on the way out -- n_val of each.
        assert_eq!(eval::apply_term(&s, top, &[]).unwrap(), 2 * n_val, "n={n_val}: sanity check against the interpreter");
    }

    // Past `DynBudget::steps`, this must
    // decline *cleanly* (a graceful `None`, the same "sound, not
    // complete" tolerance every other bounded search in this module
    // already has) rather than actually overflowing the native Rust
    // stack that many real embedded self-calls would otherwise
    // recurse through -- confirms the bound is a genuine safety net,
    // not just delaying a crash to a slightly deeper input.
    let top = source(&mut s, &format!(r"({it_src}) (1000000) (\y. y + 1) 0"));
    assert!(
        prove_closure_expr_instance(&s, top, &[]).is_none(),
        "n=1_000_000 exceeds DynBudget::steps and should decline cleanly, not overflow the stack"
    );
}

#[test]
fn a_self_application_reached_only_through_a_captured_closure_is_bounded_by_the_step_budget() {
    // `top` applies `step` to itself -- a plain (non-`Rec`) Y-combinator-
    // style self-application. Every recursive step reaches "step" again
    // only by reading `g` back out of the frame as an ordinary captured
    // `Clo` value, never via `eval_dyn`'s own `self_ctx`-based
    // embedded-self-call recognition (there is no `self_ctx` here at
    // all -- `eval_dyn_direct_call` always inlines with a *fresh* `None`
    // self_ctx for whatever combinator it steps into, per its own
    // docs) and never via `eval_dyn_tail_recursive`'s flat loop (`step`
    // isn't `Rec`-wrapped). The dead `g(999)` call site (arity 1)
    // against the live `g(g, n-1)` call site (arity 2) makes
    // `param_types_for(step)` classify `g` as `Inconsistent`, so every
    // level goes through `eval_dyn_direct_call`'s own `needs_inline`
    // branch -- one genuine native Rust stack frame per level, via
    // `eval_dyn_direct_call` -> `eval_dyn` -> (App spine) ->
    // `eval_dyn_direct_call` again. This is the regression guard for
    // `budget.steps` actually being charged on *that* path: a non-
    // `Rec` body is the one descent `eval_dyn_tail_recursive`'s loop
    // never counts.
    let mut s = TermStore::new();
    let step_src = r"\g n. if 1 < 0 then g 999 else if n <= 0 then n else g g (n - 1)";
    let step = source(&mut s, step_src);

    assert!(
        param_types_for(&s, step).unwrap().contains(&None),
        "g's own dead call site at a different arity should make it Inconsistent"
    );

    for n_val in [0i64, 1, 3, 10, 100] {
        let top = source(&mut s, &format!(r"({step_src}) ({step_src}) ({n_val})"));

        assert!(prove_closure_expr(&s, top).is_none(), "n={n_val}: top's own call to step still can't be classified statically");
        let proof = prove_closure_expr_instance(&s, top, &[]).unwrap_or_else(|| panic!("n={n_val} should be provable per-instance"));
        check_instance_proof(&proof);
        assert_eq!(eval::apply_term(&s, top, &[]).unwrap(), 0, "n={n_val}: sanity check -- counts down to 0 either way");
    }

    // Past `DynBudget::steps`, this must
    // decline *cleanly* rather than actually overflowing the native
    // Rust stack that many real inlined levels would otherwise
    // recurse through -- unlike the embedded-self-call boundary test
    // above, this path goes entirely through `eval_dyn_direct_call`'s
    // own inline branch, never `eval_dyn`'s `self_ctx` recognition.
    let top = source(&mut s, &format!(r"({step_src}) ({step_src}) (1000000)"));
    assert!(
        prove_closure_expr_instance(&s, top, &[]).is_none(),
        "n=1_000_000 exceeds DynBudget::steps via eval_dyn_direct_call's own inline path and should decline cleanly, not overflow the stack"
    );
}

#[test]
fn a_capturing_clo_returning_root_declines_without_evaluating_its_own_argument() {
    // `eval_dyn_direct_call` used to evaluate every argument (each its
    // own, possibly expensive, recursive `eval_dyn` call) *before*
    // checking whether `root` even qualifies for the `needs_inline`
    // path it's about to take -- wasted work whenever `return_ty`
    // alone (a fact about `root`'s own static structure, entirely
    // independent of the arguments) already forces `needs_inline` and
    // that path is about to decline anyway (`root`'s own captures are
    // non-empty -- out of this function's own scope, see its docs).
    //
    // `pick_a = \s. if s>0 then add5cap else sub5cap`, where
    // `add5cap`/`sub5cap` are 2-ary lambdas referencing `cap` from an
    // *outer* scope -- so `pick_a` itself both returns a further `Clo`
    // (`combinator_return_type` recognizes the `If`-between-lambdas
    // shape, same as `add5cap`/`sub5cap` in the plain
    // `a_closure_argument_arriving_via_a_separate_saturated_call...`
    // test above) *and* captures `cap` (unlike that test's two
    // closures, which are fully closed) -- exactly the combination this
    // function declines on. `\cap. if 0 < 1 then pick_a else pick_a`
    // supplies `cap` and hands back `pick_a` as a genuine `Clo` value;
    // a `let`-bound call `g (huge_sum)` (the usual dead-call
    // trick forces `g`'s own classification `Inconsistent`, so this
    // whole chain is actually traced via `eval_dyn` rather than
    // deferred to the opaque, non-executing postulate path) then
    // reaches `pick_a` as `root` with a needlessly expensive argument.
    //
    // Confirmed directly (not just by code reading) that this isn't
    // merely a performance nicety: with the early check reverted back
    // to living inside `eval_dyn_inline_call` (checked only *after*
    // every argument is evaluated, its original position), this exact
    // term reliably overflowed the native stack in an unoptimized
    // debug-build test thread -- `huge_sum`'s own 301-deep, genuinely
    // non-tail `Prim` chain is bounded by no `DynBudget` counter at
    // all (unlike the self-call/inline-call paths those bound), so
    // evaluating it wastefully was a real crash risk, not just wasted
    // cycles, whenever it was about to be thrown away regardless. Since
    // `eval_dyn` runs through `kernel::grow` (`RELATED_WORK.md` 32) it
    // is only wasted cycles; the test still pins the early decline.
    let mut s = TermStore::new();
    // Open on `cap`, used alone: the parser rejects it.
    // add5cap = \a b. a + b + cap  (cap = var(3) from inside here)
    let a1 = s.var(1);
    let b1 = s.var(0);
    let ab = s.prim(PrimOp::Add, a1, b1);
    let cap1 = s.var(3);
    let add5cap_body = s.prim(PrimOp::Add, ab, cap1);
    let add5cap_inner = s.abs(add5cap_body); // binds b
    let add5cap = s.abs(add5cap_inner); // binds a

    // sub5cap = \a b. a - b + cap
    let a2 = s.var(1);
    let b2 = s.var(0);
    let asubb = s.prim(PrimOp::Sub, a2, b2);
    let cap2 = s.var(3);
    let sub5cap_body = s.prim(PrimOp::Add, asubb, cap2);
    let sub5cap_inner = s.abs(sub5cap_body);
    let sub5cap = s.abs(sub5cap_inner);

    // pick_a = \s. if s>0 then add5cap else sub5cap
    let s_var = s.var(0);
    let zero_p = s.lit(0);
    let pick_cond = s.prim(PrimOp::Lt, zero_p, s_var);
    let pick_a_body = s.if_(pick_cond, add5cap, sub5cap);
    let pick_a = s.abs(pick_a_body);

    assert_eq!(combinator_return_type(&s, pick_a), Some(Some(2)), "pick_a should itself return a further arity-2 Clo");
    let (pa_arity, pa_body, pa_is_rec) = compile::peel(&s, pick_a).unwrap();
    assert!(
        !compile::free_vars(&s, pa_body, pa_arity, pa_is_rec).is_empty(),
        "pick_a should genuinely capture cap from outside its own scope"
    );

    let huge_sum = std::iter::repeat("1").take(301).collect::<Vec<_>>().join(" + ");
    let wrapper_src = format!(r"\g. if 1 < 0 then g 999 888 else g ({huge_sum})");
    let let_wrapper = source(&mut s, &wrapper_src);

    assert!(
        param_types_for(&s, let_wrapper).unwrap().contains(&None),
        "g's own dead call site at a different arity should make it Inconsistent, forcing this whole chain to be traced via eval_dyn rather than deferred"
    );

    let pick_src = r"(\s. if 0 < s then (\a b. a + b + cap) else (\a b. a - b + cap))";
    let top = source(&mut s, &format!(r"({wrapper_src}) ((\cap. if 0 < 1 then {pick_src} else {pick_src}) 7)"));
    // Must decline (pick_a's own captures put it out of this
    // function's scope) without overflowing the stack getting there.
    assert!(prove_closure_expr_instance(&s, top, &[]).is_none());
}

#[test]
fn branching_non_tail_self_calls_carrying_an_inconsistently_classified_closure_parameter_get_a_per_instance_proof() {
    // A genuinely *branching* non-tail shape (two self-calls in the
    // same leaf, Fibonacci-style), not just one embedded call,
    // `g` baked in as `\y. y + 1`. Each
    // occurrence of `f ..` is just another embedded self-call as far
    // as `eval_dyn`'s own recognition is concerned -- this test
    // exists specifically to confirm that claim (from `eval_dyn`'s
    // own doc comment) holds for a real branching trace, not just a
    // single non-tail one.
    let mut s = TermStore::new();
    let it_src = r"rec f n g = if 1 < 0 then g 0 999 else if n <= 1 then g n else f (n - 1) g + f (n - 2) g";
    let it = source(&mut s, it_src);

    assert!(param_types_for(&s, it).unwrap().contains(&None));

    for n_val in [0i64, 1, 2, 3, 4] {
        let top = source(&mut s, &format!(r"({it_src}) ({n_val}) (\y. y + 1)"));

        assert!(prove_closure_expr(&s, top).is_none(), "n={n_val}: top's own call to it still can't be classified statically");
        let proof = prove_closure_expr_instance(&s, top, &[]).unwrap_or_else(|| panic!("n={n_val} should be provable per-instance"));
        check_instance_proof(&proof);
        // f(n) = inc(n) for n<=1, else f(n-1)+f(n-2) -- 1,2,3,5,8 for
        // n=0..4, hand-computed independently rather than derived
        // from the term itself, so this is a real cross-check.
        let expected = [1i64, 2, 3, 5, 8][n_val as usize];
        assert_eq!(eval::apply_term(&s, top, &[]).unwrap(), expected, "n={n_val}: sanity check against the interpreter");
    }
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
