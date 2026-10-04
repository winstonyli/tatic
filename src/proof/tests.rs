use super::*;
use crate::eval;
use crate::kernel::Ctx;
use crate::term::TermStore;

#[test]
fn every_arith_postulates_starts_from_one_checked_prelude() {
    // `push` type-checks each entry (RELATED_WORK §69), so building the
    // 10-entry prelude per proof cost ~5 µs, half of a small proof.
    // Each `new` must reuse one checked copy: same nodes, not rebuilt.
    let a = ArithPostulates::new();
    let mut b = ArithPostulates::new();
    assert_eq!(a.p.globals.len(), 10);
    let (Expr::Pi(x, _), Expr::Pi(y, _)) = (&a.p.globals[1], &b.p.globals[1]) else { panic!("a binop's type is an arrow") };
    assert!(kernel::Rc::ptr_eq(x, y), "the prelude was rebuilt");
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
    let mut s = TermStore::new();
    let x = s.var(0);
    let a = s.prim(PrimOp::Mul, x, x);
    let body = s.prim(PrimOp::Add, a, a);
    let (arith, params) = setup(&s, body, 1, None).unwrap();
    let d = denote(&s, body, &arith, &params).unwrap();
    // `d` is `App(App(+, da), da')`; `da`, `da'` are `App(App(*, x), x)`.
    let Expr::App(plus_da, da2) = &d else { panic!() };
    let Expr::App(_, da1) = &**plus_da else { panic!() };
    let (Expr::App(f1, _), Expr::App(f2, _)) = (&**da1, &**da2) else { panic!() };
    assert!(kernel::Rc::ptr_eq(f1, f2), "the two operands were denoted separately");
}

#[test]
fn straight_line_term_gets_a_kernel_checked_proof() {
    // \a b. if a < b then a * 2 else b + 1
    let mut s = TermStore::new();
    let a = s.var(1);
    let b = s.var(0);
    let cond = s.prim(PrimOp::Lt, a, b);
    let two = s.lit(2);
    let then_branch = s.prim(PrimOp::Mul, a, two);
    let one = s.lit(1);
    let else_branch = s.prim(PrimOp::Add, b, one);
    let body = s.if_(cond, then_branch, else_branch);
    let inner = s.abs(body);
    let f = s.abs(inner);

    let proof = prove_pure_expr(&s, f).expect("straight-line term should be provable");
    assert_eq!(proof.arity, 2);
    // Independently re-typecheck from scratch (not just trusting the
    // `.ok()?` inside `prove_pure_expr`).
    kernel::check_in(
        &proof.globals,
        &Ctx::new(),
        &proof.proof,
        &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
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
        let mut ty = int_ty.clone();
        for _ in 0..k {
            ty = kernel::arrow(int_ty.clone(), ty);
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
        kernel::app3(nat.bool_rec(&arith.p), const_motive.clone(), f.clone(), g.clone()),
        cond,
    );
    arith.p.check(&chosen, &clo2_ty).expect("ite(Clo2, true, f, g) should typecheck at Clo2");

    // Calling it directly through ordinary `App` -- no `apply_ref`
    // postulate anywhere in this construction at all.
    let called = kernel::app2(chosen.clone(), a, b);
    arith.p.check(&called, &int_ty)
        .expect("calling a Clo2-shaped value with 2 Ints should typecheck as Int, with no apply_ref axiom");

    // The computation rule (`ite(true) = f`) is already derivable from
    // `bool_rec_true_eq` at this instantiation -- no new `ite_true_eq`
    // postulate needed either.
    let true_eq_generic = nat.bool_rec_true_eq(&arith.p);
    let instantiated = kernel::app3(true_eq_generic, const_motive, f.clone(), g.clone());
    let expected_ty = kernel::id(clo2_ty.clone(), chosen, f);
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
    // rec f n = if n <= 1 then 1 else n * f(n - 1)
    let mut s = TermStore::new();
    let n = s.var(0);
    let fv = s.var(1);
    let one = s.lit(1);
    let cond = s.prim(PrimOp::Le, n, one);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one);
    let rec_call = s.app(fv, n_minus_1);
    let else_branch = s.prim(PrimOp::Mul, n, rec_call);
    let body = s.if_(cond, one, else_branch);
    let abs = s.abs(body);
    let fact = s.rec(abs);

    assert!(prove_pure_expr(&s, fact).is_none());
}

#[test]
fn genuinely_higher_order_term_is_out_of_scope() {
    let mut s = TermStore::new();
    let f = s.var(1);
    let x = s.var(0);
    let fx = s.app(f, x);
    let ffx = s.app(f, fx);
    let inner = s.abs(ffx);
    let twice = s.abs(inner);
    assert!(prove_pure_expr(&s, twice).is_none());
}

fn gcd(s: &mut TermStore) -> Hash {
    // rec f a b = if b == 0 then a else f(b, a mod b) -- genuinely tail
    // recursive: the self-call is the whole else-branch, not nested
    // inside another operation, so compile.rs turns it into a loop.
    let b = s.var(0);
    let a = s.var(1);
    let f = s.var(2);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Eq, b, zero);
    let a_mod_b = s.prim(PrimOp::Mod, a, b);
    let rec_call = s.app2(f, b, a_mod_b);
    let body = s.if_(cond, a, rec_call);
    let inner = s.abs(body);
    let abs = s.abs(inner);
    s.rec(abs)
}

#[test]
fn tail_recursive_call_gets_a_relational_proof() {
    let mut s = TermStore::new();
    let g = gcd(&mut s);

    for (a, b) in [(48, 18), (270, 192), (17, 5), (0, 7)] {
        let proof = prove_tail_recursive_call(&s, g, &[a, b])
            .unwrap_or_else(|| panic!("gcd({a},{b}) should get a relational proof"));
        assert_eq!(proof.arity, 2);
        kernel::check_in(
            &proof.globals,
            &Ctx::new(),
            &proof.proof,
            &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
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

/// `rec f n g x = if n <= 0 then x else f(n-1, g, g(x))` -- "iterate a
/// closure-typed parameter `n` times, starting at `x`", tail-recursive,
/// threading `g` (a `Clo_1`-typed parameter, called via ordinary `App`
/// each iteration) through the recursion unchanged -- the fragment
/// `build_universal`'s own `param_types` extension covers: a
/// closure-typed *parameter*, never a closure *created* inside the
/// body. `n`=Var(2), `g`=Var(1), `x`=Var(0) inside the body (innermost
/// parameter bound first, same convention `gcd`'s own builder above
/// uses).
fn iterate(s: &mut TermStore) -> Hash {
    let x = s.var(0);
    let g = s.var(1);
    let n = s.var(2);
    let f = s.var(3);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Le, n, zero);
    let one = s.lit(1);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one);
    let gx = s.app(g, x);
    let f_n1_g = s.app2(f, n_minus_1, g);
    let rec_call = s.app(f_n1_g, gx);
    let body = s.if_(cond, x, rec_call);
    let g_binder = s.abs(body);
    let n_binder = s.abs(g_binder);
    let abs = s.abs(n_binder);
    s.rec(abs)
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

/// `rec f n acc = if n <= 0 then acc else f(n-1, (\y. acc+y)(n))` --
/// tail-recursive, each iteration *creates and immediately calls* a
/// fresh capturing closure (`\y. acc+y`, capturing `acc`) within the
/// self-call's own argument list -- the exact shape
/// `compile::tests::self_recursion_creating_a_fresh_capturing_closure_every_iteration_compiles`/
/// `jit::tests::capturing_closure_loop` already exercise at the
/// compile/JIT level. `n`=Var(1), `acc`=Var(0), `f`=Var(2) at the
/// body's own top level -- inside the closure's own body, `acc` is
/// Var(1) (one more binder, `y`, in the way), matching
/// `benches/common.rs`'s own builder exactly.
fn capturing_closure_loop(s: &mut TermStore) -> Hash {
    let y = s.var(0);
    let acc_captured = s.var(1);
    let sum = s.prim(PrimOp::Add, acc_captured, y);
    let closure = s.abs(sum);
    let n_ref = s.var(1);
    let new_acc = s.app(closure, n_ref);
    let n = s.var(1);
    let acc = s.var(0);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Le, n, zero);
    let one = s.lit(1);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one);
    let f = s.var(2);
    let f_n1 = s.app(f, n_minus_1);
    let rec_call = s.app(f_n1, new_acc);
    let body = s.if_(cond, acc, rec_call);
    let inner = s.abs(body);
    let abs = s.abs(inner);
    s.rec(abs)
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

    // Instance specialization (the weaker, sample-oriented proof --
    // `kernel_verified` never depended on it, see `jit.rs`'s own docs)
    // now succeeds here too: `eval_and_prove`'s own `call_eq_ref`
    // computation-rule axiom (see its docs) covers exactly this shape
    // -- a self-call argument that creates and calls a *capturing*
    // literal lambda (`root`'s own single capture, `acc`, resolved
    // against the outer, all-`Int` frame) whose body is a single
    // `Prim` node.
    assert_eq!(eval::apply_term(&s, h, &[5, 0]).unwrap(), 15, "interpreter sanity check: 5+4+3+2+1");
    let instance = prove_tail_recursive_instance(&s, h, &[5, 0])
        .expect("a self-call argument creating and calling a capturing closure should now get a concrete instance");
    kernel::check_in(&instance.globals, &Ctx::new(), &instance.proof, &kernel::id(instance.int_ty.clone(), instance.lhs.clone(), instance.rhs.clone()))
        .expect("the recorded instance proof should independently re-typecheck");

    assert!(compile::try_compile(&s, h).is_some());
}

#[test]
fn eval_and_prove_call_respects_call_refs_own_argument_order_for_a_non_symmetric_root() {
    // A wrong argument order in `call_eq_ref`'s own axiom construction
    // (or in `eval_and_prove_call`'s own instantiation of it) would
    // still typecheck -- every position here is `Int`, so a swapped
    // axiom is just a *different*, still well-typed, universally
    // quantified fact -- so only comparing the *concrete value*
    // against an independent interpretation (not `kernel::check`
    // alone) can catch it. `x - y` is non-commutative, so swapping
    // `x`/`y` gives a visibly wrong answer rather than one that
    // happens to coincide. This calls the private `eval_and_prove`
    // directly (this module's own test submodule can) rather than
    // going through a full self-recursive scaffold, since the bug
    // this guards is local to `eval_and_prove_call` itself.
    let mut s = TermStore::new();
    let x = s.var(1); // first-applied
    let y = s.var(0); // last-applied
    let diff = s.prim(PrimOp::Sub, x, y);
    let inner = s.abs(diff);
    let root = s.abs(inner);
    let five = s.lit(5);
    let three = s.lit(3);
    let applied_to_x = s.app(root, five);
    let h = s.app(applied_to_x, three);

    assert_eq!(eval::apply_term(&s, h, &[]).unwrap(), 2, "interpreter sanity check: 5 - 3 = 2");

    let mut combinators = ClosureCombinators::new(&s);
    combinators.cp.arith.lit(5);
    combinators.cp.arith.lit(3);
    let (result, denotation, proof) = eval_and_prove(&s, h, &mut combinators, &[], &[], &[])
        .expect("a non-capturing literal-lambda self-call-argument should get a concrete witness");
    assert_eq!(result, 2, "eval_and_prove_call must not swap call_ref's own argument order");
    combinators.cp.arith.p.check(
        &proof,
        &kernel::id(combinators.cp.arith.int_ty(), denotation, combinators.cp.arith.lit_ref(2)),
    )
    .expect("the recorded witness should independently re-typecheck");
}

#[test]
fn eval_and_prove_call_over_gets_a_concrete_instance_for_the_canonical_if_between_closures_shape() {
    // f = \a b. if 0 < a then (\c. a+b+c) else (\c. a-b+c); f(a,b,c) --
    // the exact same canonical over-application shape as
    // `an_over_applied_literal_lambda_returning_a_closure_gets_a_closure_proof`,
    // now also checked for a concrete instance (both branches of the
    // `If`), via `clo_eq_ref`/`ite_clo_eq_ref`/`apply_clo_eq_ref`.
    let mut s = TermStore::new();
    let c1 = s.var(0);
    let b1 = s.var(1);
    let a1 = s.var(2);
    let ab1 = s.prim(PrimOp::Add, a1, b1);
    let abc1 = s.prim(PrimOp::Add, ab1, c1);
    let closure1 = s.abs(abc1);

    let c2 = s.var(0);
    let b2 = s.var(1);
    let a2 = s.var(2);
    let amb2 = s.prim(PrimOp::Sub, a2, b2);
    let ambc2 = s.prim(PrimOp::Add, amb2, c2);
    let closure2 = s.abs(ambc2);

    let a_body = s.var(1);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Lt, zero, a_body);
    let f_body = s.if_(cond, closure1, closure2);
    let f_inner = s.abs(f_body);
    let f = s.abs(f_inner);

    for (a_val, b_val, c_val, expected) in [(10, 3, 100, 113), (-5, 3, 100, 92)] {
        let a_lit = s.lit(a_val);
        let b_lit = s.lit(b_val);
        let c_lit = s.lit(c_val);
        let fa = s.app(f, a_lit);
        let fab = s.app(fa, b_lit);
        let h = s.app(fab, c_lit);

        assert_eq!(eval::apply_term(&s, h, &[]).unwrap(), expected, "interpreter sanity check");

        let mut combinators = ClosureCombinators::new(&s);
        combinators.cp.arith.lit(a_val);
        combinators.cp.arith.lit(b_val);
        combinators.cp.arith.lit(c_val);
        let (result, denotation, proof) = eval_and_prove(&s, h, &mut combinators, &[], &[], &[])
            .expect("an over-applied literal lambda returning an If-chosen closure should get a concrete witness");
        assert_eq!(result, expected);
        combinators.cp.arith.p.check(
            &proof,
            &kernel::id(combinators.cp.arith.int_ty(), denotation, combinators.cp.arith.lit_ref(expected)),
        )
        .expect("the recorded witness should independently re-typecheck");
    }
}

#[test]
fn eval_and_prove_call_over_respects_the_over_applied_calls_own_argument_order_for_a_non_symmetric_root() {
    // f = \a. if 0<a then (\c d. c-d) else (\c d. d-c); f(a,c,d) -- k=2
    // extra arguments, non-commutative in each branch. `k=1` (the
    // canonical shape above) has no argument order to get wrong at
    // all, so this is the one that actually exercises
    // `apply_clo_eq_ref`'s own descending `p_{k-1}..p_0`
    // instantiation, the same reason the `call_eq_ref` pass's own
    // regression test used a 2-arg root.
    let mut s = TermStore::new();
    let d1 = s.var(0);
    let c1 = s.var(1);
    let cd1 = s.prim(PrimOp::Sub, c1, d1);
    let closure1_inner = s.abs(cd1);
    let closure1 = s.abs(closure1_inner); // \c d. c - d

    let c2 = s.var(1);
    let d2 = s.var(0);
    let dc2 = s.prim(PrimOp::Sub, d2, c2);
    let closure2_inner = s.abs(dc2);
    let closure2 = s.abs(closure2_inner); // \c d. d - c

    let a_body = s.var(0);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Lt, zero, a_body);
    let f_body = s.if_(cond, closure1, closure2);
    let f = s.abs(f_body); // \a. if 0<a then closure1 else closure2

    for (a_val, c_val, d_val, expected) in [(5, 10, 3, 7), (-5, 10, 3, -7)] {
        let a_lit = s.lit(a_val);
        let c_lit = s.lit(c_val);
        let d_lit = s.lit(d_val);
        let fa = s.app(f, a_lit);
        let fac = s.app(fa, c_lit);
        let h = s.app(fac, d_lit);

        assert_eq!(eval::apply_term(&s, h, &[]).unwrap(), expected, "interpreter sanity check");

        let mut combinators = ClosureCombinators::new(&s);
        combinators.cp.arith.lit(a_val);
        combinators.cp.arith.lit(c_val);
        combinators.cp.arith.lit(d_val);
        let (result, denotation, proof) = eval_and_prove(&s, h, &mut combinators, &[], &[], &[])
            .expect("a non-symmetric over-applied closure call should get a concrete witness");
        assert_eq!(result, expected, "eval_and_prove_call_over must not swap the over-applied call's own argument order");
        combinators.cp.arith.p.check(
            &proof,
            &kernel::id(combinators.cp.arith.int_ty(), denotation, combinators.cp.arith.lit_ref(expected)),
        )
        .expect("the recorded witness should independently re-typecheck");
    }
}

#[test]
fn a_call_shaped_if_tree_leaf_whose_own_target_is_itself_a_further_if_tree_gets_a_concrete_instance() {
    // g = \x. if 0<x then (\c. x+c) else (\c. x-c) -- arity 1, an
    // ordinary IfTree-shaped closure (ClosureRhsShape::IfTree, two
    // bare Abs leaves).
    //
    // root = \a b. if 0<a then g(b) else (\c. b*2+c) -- arity 2. The
    // `then` branch, `g(b)`, is a saturated call to `g`
    // (ClosureIfTreeLeafShape::Call), whose own resolution recurses
    // into `g`'s own shape via `resolve_closure_shape_to_leaf` -- here
    // testing whether that recursion already handles `g_shape` itself
    // being `IfTree` (not just `Abs`/`Pap`/a further `Call`), since
    // `resolve_closure_shape_to_leaf` dispatches generically on
    // whatever shape it's handed, without a hardcoded assumption about
    // what produced it.
    let mut s = TermStore::new();
    let c1 = s.var(0);
    let x1 = s.var(1);
    let x_plus_c = s.prim(PrimOp::Add, x1, c1);
    let g_then = s.abs(x_plus_c);

    let c2 = s.var(0);
    let x2 = s.var(1);
    let x_minus_c = s.prim(PrimOp::Sub, x2, c2);
    let g_else = s.abs(x_minus_c);

    let x_cond = s.var(0);
    let zero1 = s.lit(0);
    let g_cond = s.prim(PrimOp::Lt, zero1, x_cond);
    let g_body = s.if_(g_cond, g_then, g_else);
    let g = s.abs(g_body); // \x. if 0<x then (\c.x+c) else (\c.x-c)

    let b_ref = s.var(0);
    let then_branch = s.app(g, b_ref); // g(b) -- Call-shaped leaf

    let c_r = s.var(0);
    let b_shifted = s.var(1);
    let two = s.lit(2);
    let b2 = s.prim(PrimOp::Mul, b_shifted, two);
    let b2_plus_c = s.prim(PrimOp::Add, b2, c_r);
    let else_branch = s.abs(b2_plus_c); // \c. b*2+c -- bare Abs leaf, captures b

    let a_ref = s.var(1);
    let zero2 = s.lit(0);
    let cond = s.prim(PrimOp::Lt, zero2, a_ref);
    let root_body = s.if_(cond, then_branch, else_branch);
    let root_b_binder = s.abs(root_body);
    let root = s.abs(root_b_binder); // \a b. if 0<a then g(b) else (\c. b*2+c)

    // Hand-verified against the reference interpreter before trusting
    // the term shape: a=5,b=3,c=7 (0<a, then 0<b: g's own `then`
    // taken) -> g(3) = \c.3+c, called at 7 -> 10; a=5,b=-3,c=7 (0<a,
    // then b<=0: g's own `else` taken) -> g(-3) = \c.-3-c, called at
    // 7 -> -10 (asymmetric from the first case, catching a
    // g-internal-branch mixup); a=-5,b=3,c=7 (a<=0: root's own
    // `else`, g never even resolved) -> 3*2+7 = 13.
    for (a_val, b_val, c_val, expected) in [(5, 3, 7, 10), (5, -3, 7, -10), (-5, 3, 7, 13)] {
        let a_lit = s.lit(a_val);
        let b_lit = s.lit(b_val);
        let c_lit = s.lit(c_val);
        let root_a = s.app(root, a_lit);
        let root_ab = s.app(root_a, b_lit);
        let h_term = s.app(root_ab, c_lit);
        assert_eq!(
            eval::apply_term(&s, h_term, &[]).unwrap(),
            expected,
            "a={a_val} b={b_val} c={c_val}: interpreter sanity check"
        );

        let mut combinators = ClosureCombinators::new(&s);
        combinators.cp.arith.lit(a_val);
        combinators.cp.arith.lit(b_val);
        combinators.cp.arith.lit(c_val);
        let (result, denotation, proof) = eval_and_prove(&s, h_term, &mut combinators, &[], &[], &[]).unwrap_or_else(|| {
            panic!("a={a_val} b={b_val} c={c_val}: a Call-shaped leaf targeting a further IfTree should get a concrete instance")
        });
        assert_eq!(
            result, expected,
            "a={a_val} b={b_val} c={c_val}: should agree with the reference interpreter, not just typecheck"
        );
        combinators.cp.arith.p.check(
            &proof,
            &kernel::id(combinators.cp.arith.int_ty(), denotation, combinators.cp.arith.lit_ref(expected)),
        )
        .unwrap_or_else(|e| panic!("a={a_val} b={b_val} c={c_val}: the recorded witness should independently re-typecheck: {e}"));
    }
}

#[test]
fn eval_and_prove_call_over_resolves_an_inner_closures_own_captures_against_roots_frame_not_double_shifted() {
    // f = \a. if 0<a then (\c. a+w+c) else (\c. a-w-c), where `w` is
    // captured by `f` itself from an outer frame -- `t`/`e` (the two
    // inner closures) each *also* capture something from `f`'s own
    // frame (`a`, f's own param, *and* `w`, f's own capture, at
    // different absolute positions). An off-by-`root_arity` double
    // shift when indexing `t`/`e`'s own captures into `params_full`
    // (mistakenly adding `f`'s own arity on top of the relative index
    // `compile::free_vars` already gives, by analogy with how `f`'s
    // *own* captures genuinely do need that shift) would read the
    // wrong slot and produce a visibly wrong value here, not a
    // rejection -- `eval::apply_term` is the independent check.
    let mut s = TermStore::new();
    let c1 = s.var(0); // t's own param
    let a1 = s.var(1); // f's own param, one level deeper than in f's own body
    let w1 = s.var(2); // f's own capture, one level deeper than in f's own body
    let aw1 = s.prim(PrimOp::Add, a1, w1);
    let awc1 = s.prim(PrimOp::Add, aw1, c1);
    let closure_t = s.abs(awc1); // \c. a + w + c

    let c2 = s.var(0);
    let a2 = s.var(1);
    let w2 = s.var(2);
    let aw2 = s.prim(PrimOp::Sub, a2, w2);
    let awc2 = s.prim(PrimOp::Sub, aw2, c2);
    let closure_e = s.abs(awc2); // \c. a - w - c

    let a_body = s.var(0);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Lt, zero, a_body);
    let f_body = s.if_(cond, closure_t, closure_e);
    let f = s.abs(f_body); // \a. if 0<a then closure_t else closure_e -- captures `w`

    for (w_val, a_val, c_val, expected) in [(100, 10, 5, 115), (100, -10, 5, -115)] {
        let a_lit = s.lit(a_val);
        let c_lit = s.lit(c_val);
        let fa = s.app(f, a_lit);
        let h = s.app(fa, c_lit); // h's own only free variable is `w`, at Var(0)
        let h_closed = s.abs(h); // eval::apply_term expects a function value, not a bare free variable

        assert_eq!(eval::apply_term(&s, h_closed, &[w_val]).unwrap(), expected, "interpreter sanity check");

        let mut combinators = ClosureCombinators::new(&s);
        combinators.cp.arith.lit(w_val);
        let w_lit = combinators.cp.arith.lit_ref(w_val);
        let w_param = w_lit.clone();
        let w_fact = kernel::refl(w_lit);
        combinators.cp.arith.lit(a_val);
        combinators.cp.arith.lit(c_val);
        let (result, denotation, proof) = eval_and_prove(&s, h, &mut combinators, &[w_param], &[w_val], &[w_fact])
            .expect("an inner closure capturing both root's own param and root's own capture should get a concrete witness");
        assert_eq!(result, expected, "eval_and_prove_call_over must resolve an inner closure's own captures against root's frame directly, not double-shifted by root's own arity");
        combinators.cp.arith.p.check(
            &proof,
            &kernel::id(combinators.cp.arith.int_ty(), denotation, combinators.cp.arith.lit_ref(expected)),
        )
        .expect("the recorded witness should independently re-typecheck");
    }
}

#[test]
fn a_pap_producing_root_gets_a_concrete_instance_for_eval_and_prove_call_over() {
    // g = \x y. x*10 + y (arity 2, deliberately asymmetric so an
    // index-order bug between x/y would change the result, not just
    // its symmetry); f = \a. g(a) -- f's own saturated call is a
    // *partial application* of g (root_arity=1, k=1, per
    // `return_type_of`'s own `Ordering::Less` branch), not an `If`
    // between two closures -- `clo_eq_ref_pap` (not
    // `clo_eq_ref_if_between`) covers this shape now. `f(a)(c)` is
    // over-application: `f`'s own saturated call denotes `g` partially
    // applied to `a`, then the extra argument `c` completes it, so the
    // whole term should agree with calling `g(a, c)` directly.
    let mut s = TermStore::new();
    let x = s.var(1);
    let y = s.var(0);
    let ten = s.lit(10);
    let x10 = s.prim(PrimOp::Mul, x, ten);
    let xy = s.prim(PrimOp::Add, x10, y);
    let g_inner = s.abs(xy);
    let g = s.abs(g_inner);

    let a_ref = s.var(0);
    let f_body = s.app(g, a_ref);
    let f = s.abs(f_body); // \a. g(a) -- a PAP of g, arity 1

    let a_lit = s.lit(5);
    let c_lit = s.lit(3);
    let fa = s.app(f, a_lit);
    let h = s.app(fa, c_lit);

    // Hand-verified against the reference interpreter before trusting
    // the term shape, per this project's own established discipline:
    // g(5, 3) = 5*10 + 3 = 53 (an index swap would instead give
    // g(3, 5) = 3*10 + 5 = 35, a different number, so this is a real
    // regression guard, not just a symmetry check).
    assert_eq!(eval::apply_term(&s, h, &[]).unwrap(), 53);

    let mut combinators = ClosureCombinators::new(&s);
    combinators.cp.arith.lit(5);
    combinators.cp.arith.lit(3);
    let (result, denoted, proof) =
        eval_and_prove(&s, h, &mut combinators, &[], &[], &[]).expect("a PAP-producing root's over-application should get a concrete instance");
    assert_eq!(result, 53, "should agree with the reference interpreter, not just typecheck");
    let int_ty = combinators.cp.arith.int_ty();
    combinators.cp.arith.p.check(&proof, &kernel::id(int_ty, denoted, combinators.cp.arith.lit_ref(result)))
        .expect("the recorded proof should independently re-typecheck");
}

#[test]
fn a_further_indirectly_called_combinator_gets_a_concrete_instance_for_eval_and_prove_call_over() {
    // h = \p q. p*10 + q (arity 2, asymmetric coefficients so an
    // index-order bug changes the result, not just its symmetry);
    // middle = \b. h(b) -- a PAP of h (arity 1, `middle`'s own
    // saturated call returns `Clo_1`); root = \x y. middle(y) -- arity
    // 2, `x` a decoy left unused so a `root`-level saturating-args
    // order bug (e.g. `build_clo_call_bridge`'s own inner-frame
    // construction) swaps in `x`'s own value where `y`'s belongs,
    // catchably -- calls `middle` *saturated* (middle's own arity is
    // 1, matching `args.len()`), so this is `ClosureRhsShape::Call`,
    // not `Pap`: `root`'s own body doesn't itself hold the literal
    // lambda that will eventually be called, only a further,
    // statically-known indirection to one (`middle`, itself
    // Clo-returning) -- the "further nested-call-producing root"
    // shape. `root(x)(y)(c)` is over-application: `root`'s own
    // saturated call denotes `middle`'s own saturated call (itself a
    // further `Clo_1`), and *that* denotes `h` partially applied to
    // `y`; the extra argument `c` completes it, so the whole term
    // should agree with `h(y, c)` directly (never `x`).
    let mut s = TermStore::new();
    let p = s.var(1);
    let q = s.var(0);
    let ten = s.lit(10);
    let p10 = s.prim(PrimOp::Mul, p, ten);
    let pq = s.prim(PrimOp::Add, p10, q);
    let h_inner = s.abs(pq);
    let h = s.abs(h_inner); // \p q. p*10 + q

    let b_ref = s.var(0);
    let middle_body = s.app(h, b_ref);
    let middle = s.abs(middle_body); // \b. h(b) -- a PAP of h, arity 1

    let y_ref = s.var(0);
    let root_body = s.app(middle, y_ref);
    let root_y_binder = s.abs(root_body);
    let root = s.abs(root_y_binder); // \x y. middle(y) -- a saturated call to middle, arity 2

    let x_lit = s.lit(100); // decoy: must never influence the result
    let y_lit = s.lit(7);
    let c_lit = s.lit(2);
    let root_x = s.app(root, x_lit);
    let root_xy = s.app(root_x, y_lit);
    let h_term = s.app(root_xy, c_lit);

    // Hand-verified against the reference interpreter before trusting
    // the term shape, per this project's own established discipline:
    // h(7, 2) = 7*10 + 2 = 72 (an index swap would instead give
    // h(2, 7) = 27, or pick up the decoy `x` for a very different
    // number like h(100, 2) = 1002).
    assert_eq!(eval::apply_term(&s, h_term, &[]).unwrap(), 72);

    let mut combinators = ClosureCombinators::new(&s);
    combinators.cp.arith.lit(100);
    combinators.cp.arith.lit(7);
    combinators.cp.arith.lit(2);
    let (result, denoted, proof) = eval_and_prove(&s, h_term, &mut combinators, &[], &[], &[])
        .expect("a further indirectly-called combinator's over-application should get a concrete instance");
    assert_eq!(result, 72, "should agree with the reference interpreter, not just typecheck");
    let int_ty = combinators.cp.arith.int_ty();
    combinators.cp.arith.p.check(&proof, &kernel::id(int_ty, denoted, combinators.cp.arith.lit_ref(result)))
        .expect("the recorded proof should independently re-typecheck");
}

#[test]
fn two_levels_of_further_indirection_still_get_a_concrete_instance() {
    // h = \p q. p - q (arity 2, asymmetric so an operand-order bug
    // changes the result); middle = \b. h(b) -- a PAP of h, arity 1;
    // outer = \a. middle(a) -- `Call`, one level of indirection (as
    // the test above); root = \a. outer(a) -- *another* saturated
    // call to a further Clo-returning combinator, since
    // `combinator_return_type(outer)` itself recurses through
    // `outer`'s own `Call` shape to find `Some(1)` -- a *second*
    // `Call` layer, confirming `resolve_closure_shape_to_leaf`'s own
    // recursion isn't hardcoded to depth 1. `root(a)(c)` should agree
    // with `h(a, c)` directly, chaining through `outer` and `middle`
    // both.
    let mut s = TermStore::new();
    let p = s.var(1);
    let q = s.var(0);
    let pq = s.prim(PrimOp::Sub, p, q);
    let h_inner = s.abs(pq);
    let h = s.abs(h_inner); // \p q. p - q

    let b_ref = s.var(0);
    let middle_body = s.app(h, b_ref);
    let middle = s.abs(middle_body); // \b. h(b)

    let a_ref1 = s.var(0);
    let outer_body = s.app(middle, a_ref1);
    let outer = s.abs(outer_body); // \a. middle(a)

    let a_ref2 = s.var(0);
    let root_body = s.app(outer, a_ref2);
    let root = s.abs(root_body); // \a. outer(a)

    let a_lit = s.lit(11);
    let c_lit = s.lit(4);
    let root_a = s.app(root, a_lit);
    let h_term = s.app(root_a, c_lit);

    // Hand-verified against the reference interpreter first: h(11,4)
    // = 11-4 = 7 (the operand-swapped h(4,11) = -7 would be a clearly
    // different, wrong number).
    assert_eq!(eval::apply_term(&s, h_term, &[]).unwrap(), 7);

    let mut combinators = ClosureCombinators::new(&s);
    combinators.cp.arith.lit(11);
    combinators.cp.arith.lit(4);
    let (result, denoted, proof) =
        eval_and_prove(&s, h_term, &mut combinators, &[], &[], &[]).expect("two levels of further indirection should still get a concrete instance");
    assert_eq!(result, 7, "should agree with the reference interpreter, not just typecheck");
    let int_ty = combinators.cp.arith.int_ty();
    combinators.cp.arith.p.check(&proof, &kernel::id(int_ty, denoted, combinators.cp.arith.lit_ref(result)))
        .expect("the recorded proof should independently re-typecheck");
}

#[test]
fn a_pap_producing_root_with_two_supplied_args_and_a_capturing_g_gets_a_concrete_instance() {
    // g = \p q r. p*100 + q*10 + r + captured_y (arity 3), where
    // `captured_y` is a *capture*, not one of g's own params --
    // relative to g's own 3-ary scope that's `Var(3)` (one beyond p/q/r,
    // `p`=Var(2)/`q`=Var(1)/`r`=Var(0) innermost-last), which resolves
    // (per `free_vars`' own "no additional shift" convention for a
    // lambda referenced directly, with no binders of its own in
    // between) to `f`'s own `y` -- `g_x` sits immediately inside `f`'s
    // body, introducing no binders of its own before that point.
    // Fully asymmetric coefficients so any swap among the *two* args
    // `f` itself supplies (p, q), the one extra arg (r), or the
    // captured value (`y`, doubly used: both a supplied arg *and* a
    // capture) changes the result.
    //
    // f = \x y. g(x, y) -- a PAP of g supplying 2 of its 3 remaining
    // params (s=2, k=1), specifically exercising the *ordering among
    // the supplied args themselves* (the single-supplied-arg test
    // above can't distinguish this, since reversing one element is a
    // no-op) together with `g`'s own capture.
    let mut s = TermStore::new();
    let p = s.var(2);
    let q = s.var(1);
    let r = s.var(0);
    let captured_y = s.var(3);
    let hundred = s.lit(100);
    let ten = s.lit(10);
    let p100 = s.prim(PrimOp::Mul, p, hundred);
    let q10 = s.prim(PrimOp::Mul, q, ten);
    let sum1 = s.prim(PrimOp::Add, p100, q10);
    let sum2 = s.prim(PrimOp::Add, sum1, r);
    let sum3 = s.prim(PrimOp::Add, sum2, captured_y);
    let g_r = s.abs(sum3);
    let g_q = s.abs(g_r);
    let g_p = s.abs(g_q); // g = \p q r. p*100+q*10+r+captured_y, capturing Var(3) relative to its own arity-3 scope

    let f_x = s.var(1);
    let f_y = s.var(0);
    let f_body = s.app2(g_p, f_x, f_y); // g(x, y) -- a 2-of-3 partial application of g
    let f_y_binder = s.abs(f_body);
    let f = s.abs(f_y_binder); // f = \x y. g(x, y), arity 2

    let x_lit = s.lit(5);
    let y_lit = s.lit(7);
    let r_lit = s.lit(3);
    let f_at_x = s.app(f, x_lit);
    let f_at_x_y = s.app(f_at_x, y_lit);
    let h = s.app(f_at_x_y, r_lit); // ((f(x))(y))(r) -- f(x,y)'s own saturated call is the PAP, r is the over-application

    // Hand-verified: g(p=5,q=7,r=3,captured_y=7) = 5*100+7*10+3+7 = 580.
    // Swapping p/q would instead give 7*100+5*10+3+7 = 760.
    assert_eq!(eval::apply_term(&s, h, &[]).unwrap(), 580);

    let mut combinators = ClosureCombinators::new(&s);
    for lit in [5, 7, 3] {
        combinators.cp.arith.lit(lit);
    }
    let (result, denoted, proof) =
        eval_and_prove(&s, h, &mut combinators, &[], &[], &[]).expect("a capturing PAP-producing root's over-application should get a concrete instance");
    assert_eq!(result, 580, "should agree with the reference interpreter, not just typecheck");
    let int_ty = combinators.cp.arith.int_ty();
    combinators.cp.arith.p.check(&proof, &kernel::id(int_ty, denoted, combinators.cp.arith.lit_ref(result)))
        .expect("the recorded proof should independently re-typecheck");
}

#[test]
fn a_further_nested_if_inside_a_branch_gets_a_concrete_instance_for_eval_and_prove_call_over() {
    // f = \a. if 0<a then (if a>10 then (\c. c) else (\c. c+1)) else (\c. c-1)
    // -- `t` is itself a further `If`, not a bare `Term::Abs` -- a
    // depth-2 decision tree, not the depth-1 `clo_eq_ref_if_between`
    // (now `clo_eq_ref_if_tree`) originally supported. Three leaves,
    // exercising all of them: the identity closure (`a>10`), `c+1`
    // (`0<a<=10`), and `c-1` (`a<=0`).
    let mut s = TermStore::new();
    let c1 = s.var(0);
    let one = s.lit(1);
    let c_plus_1 = s.prim(PrimOp::Add, c1, one);
    let inner_then = s.abs(c_plus_1);
    let c2 = s.var(0);
    let inner_else = s.abs(c2);
    let a_body1 = s.var(0);
    let ten = s.lit(10);
    let inner_cond = s.prim(PrimOp::Lt, ten, a_body1);
    let t = s.if_(inner_cond, inner_else, inner_then); // if a>10 then (\c.c) else (\c.c+1)

    let c3 = s.var(0);
    let one2 = s.lit(1);
    let c_minus_1 = s.prim(PrimOp::Sub, c3, one2);
    let e = s.abs(c_minus_1);

    let a_body2 = s.var(0);
    let zero = s.lit(0);
    let outer_cond = s.prim(PrimOp::Lt, zero, a_body2);
    let f_body = s.if_(outer_cond, t, e);
    let f = s.abs(f_body);

    // Hand-verified against the reference interpreter before trusting
    // the term shape: a=5 (0<a, a<=10) -> c+1 = 4; a=20 (0<a, a>10) ->
    // c = 3; a=-5 (a<=0) -> c-1 = 2.
    for (a_val, c_val, expected) in [(5, 3, 4), (20, 3, 3), (-5, 3, 2)] {
        let a_lit = s.lit(a_val);
        let c_lit = s.lit(c_val);
        let fa = s.app(f, a_lit);
        let h = s.app(fa, c_lit);
        assert_eq!(eval::apply_term(&s, h, &[]).unwrap(), expected, "a={a_val} c={c_val}: interpreter sanity check");

        let mut combinators = ClosureCombinators::new(&s);
        combinators.cp.arith.lit(a_val);
        combinators.cp.arith.lit(c_val);
        let (result, denotation, proof) = eval_and_prove(&s, h, &mut combinators, &[], &[], &[])
            .unwrap_or_else(|| panic!("a={a_val} c={c_val}: a further-nested If inside a branch should get a concrete instance"));
        assert_eq!(result, expected, "a={a_val} c={c_val}: should agree with the reference interpreter, not just typecheck");
        combinators.cp.arith.p.check(
            &proof,
            &kernel::id(combinators.cp.arith.int_ty(), denotation, combinators.cp.arith.lit_ref(expected)),
        )
        .unwrap_or_else(|e| panic!("a={a_val} c={c_val}: the recorded witness should independently re-typecheck: {e}"));
    }
}

#[test]
fn an_if_tree_leaf_that_is_itself_a_partial_application_gets_a_concrete_instance() {
    // h = \p q r. p*100 + q*10 + r (arity 3, fully asymmetric
    // coefficients so any permutation of the three args changes the
    // result, not just its symmetry); root = \a b1 b2. if 0<a then
    // h(b1,b2) else (\c. c-1) -- arity 3, the `then` branch
    // (`h(b1,b2)`) is a *partial application* of a further literal
    // lambda h (two of its three args supplied), not a bare
    // `Term::Abs` -- previously out of scope
    // (`closure_if_tree_leaves_are_abs`'s own restriction), now
    // `ClosureIfTreeLeafShape::Pap`. `root(a,b1,b2)(c)` is
    // over-application (k=1): when `0<a`, the whole term should
    // agree with `h(b1, b2, c)` directly (asymmetric enough that a
    // supplied-args order bug in `chosen_arg_prefix`'s own handling
    // would give a different, wrong number, not just fail to
    // typecheck); otherwise with `c-1` (the `else` branch, still a
    // bare `Abs` leaf, exercising both shapes in the same tree).
    let mut s = TermStore::new();
    let p = s.var(2);
    let q = s.var(1);
    let r = s.var(0);
    let hundred = s.lit(100);
    let ten = s.lit(10);
    let p100 = s.prim(PrimOp::Mul, p, hundred);
    let q10 = s.prim(PrimOp::Mul, q, ten);
    let p100q10 = s.prim(PrimOp::Add, p100, q10);
    let pqr = s.prim(PrimOp::Add, p100q10, r);
    let h_inner2 = s.abs(pqr);
    let h_inner1 = s.abs(h_inner2);
    let h = s.abs(h_inner1); // \p q r. p*100 + q*10 + r

    let b1_ref = s.var(1);
    let b2_ref = s.var(0);
    let h_b1 = s.app(h, b1_ref);
    let then_branch = s.app(h_b1, b2_ref); // h(b1, b2) -- a Pap of h, arity 1

    let c1 = s.var(0);
    let one = s.lit(1);
    let c_minus_1 = s.prim(PrimOp::Sub, c1, one);
    let else_branch = s.abs(c_minus_1); // \c. c-1 -- a bare Abs leaf

    let a_ref = s.var(2);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Lt, zero, a_ref);
    let root_body = s.if_(cond, then_branch, else_branch);
    let root_b2_binder = s.abs(root_body);
    let root_b1_binder = s.abs(root_b2_binder);
    let root = s.abs(root_b1_binder); // \a b1 b2. if 0<a then h(b1,b2) else (\c.c-1)

    // Hand-verified against the reference interpreter before trusting
    // the term shape: a=5 (0<a) with b1=3,b2=7,c=2 ->
    // h(3,7,2) = 3*100+7*10+2 = 372 (h(7,3,2) = 732 would be a clearly
    // different, wrong number, catching a supplied-args order bug);
    // a=-5 (a<=0) with b1=3,b2=7 (unused, decoys),c=2 -> c-1=1.
    for (a_val, b1_val, b2_val, c_val, expected) in [(5, 3, 7, 2, 372), (-5, 3, 7, 2, 1)] {
        let a_lit = s.lit(a_val);
        let b1_lit = s.lit(b1_val);
        let b2_lit = s.lit(b2_val);
        let c_lit = s.lit(c_val);
        let root_a = s.app(root, a_lit);
        let root_ab1 = s.app(root_a, b1_lit);
        let root_ab1b2 = s.app(root_ab1, b2_lit);
        let h_term = s.app(root_ab1b2, c_lit);
        assert_eq!(
            eval::apply_term(&s, h_term, &[]).unwrap(),
            expected,
            "a={a_val} b1={b1_val} b2={b2_val} c={c_val}: interpreter sanity check"
        );

        let mut combinators = ClosureCombinators::new(&s);
        combinators.cp.arith.lit(a_val);
        combinators.cp.arith.lit(b1_val);
        combinators.cp.arith.lit(b2_val);
        combinators.cp.arith.lit(c_val);
        let (result, denotation, proof) = eval_and_prove(&s, h_term, &mut combinators, &[], &[], &[]).unwrap_or_else(|| {
            panic!("a={a_val} b1={b1_val} b2={b2_val} c={c_val}: a Pap-shaped IfTree leaf should get a concrete instance")
        });
        assert_eq!(
            result, expected,
            "a={a_val} b1={b1_val} b2={b2_val} c={c_val}: should agree with the reference interpreter, not just typecheck"
        );
        combinators.cp.arith.p.check(
            &proof,
            &kernel::id(combinators.cp.arith.int_ty(), denotation, combinators.cp.arith.lit_ref(expected)),
        )
        .unwrap_or_else(|e| panic!("a={a_val} b1={b1_val} b2={b2_val} c={c_val}: the recorded witness should independently re-typecheck: {e}"));
    }
}

#[test]
fn an_if_tree_leaf_reached_only_through_a_further_saturated_call_gets_a_concrete_instance() {
    // h = \p q. p*10+q (arity 2); middle = \x. h(x) -- arity 1, its own
    // body a *partial* application of h (one of two args supplied), so
    // `combinator_return_type(middle) == Some(1)`: middle's own
    // *saturated* call is itself Clo_1-typed.
    //
    // root = \a b. if 0<a then middle(b) else (\y. y-1) -- arity 2. The
    // `then` branch, `middle(b)`, is a *saturated* call to middle
    // (args.len() == middle's own arity, 1) whose own saturated call is
    // Clo_1-typed -- `ClosureIfTreeLeafShape::Call`, previously "a
    // further, natural generalization, not attempted here". The `else`
    // branch is a bare Abs leaf, exercising both shapes in the same
    // tree exactly like the Pap-leaf test above does. `root(a,b)(c)` is
    // over-application (k=1): when `0<a`, resolving the Call-shaped
    // leaf must recurse into `middle`'s own further resolution (a
    // Pap of h) to reach h itself, mirroring the root-level `Call`
    // arm's own indirection-following exactly, just one level deeper
    // inside an `If`.
    let mut s = TermStore::new();
    let p = s.var(1);
    let q = s.var(0);
    let ten = s.lit(10);
    let p10 = s.prim(PrimOp::Mul, p, ten);
    let pq = s.prim(PrimOp::Add, p10, q);
    let h_inner = s.abs(pq);
    let h = s.abs(h_inner); // \p q. p*10+q

    let x = s.var(0);
    let h_x = s.app(h, x);
    let middle = s.abs(h_x); // \x. h(x) -- Pap of h, arity 1

    let b_ref = s.var(0);
    let then_branch = s.app(middle, b_ref); // middle(b) -- saturated call to middle

    let y = s.var(0);
    let one = s.lit(1);
    let y_minus_1 = s.prim(PrimOp::Sub, y, one);
    let else_branch = s.abs(y_minus_1); // \y. y-1 -- bare Abs leaf

    let a_ref = s.var(1);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Lt, zero, a_ref);
    let root_body = s.if_(cond, then_branch, else_branch);
    let root_b_binder = s.abs(root_body);
    let root = s.abs(root_b_binder); // \a b. if 0<a then middle(b) else (\y.y-1)

    // Hand-verified against the reference interpreter before trusting
    // the term shape: a=5 (0<a) with b=3,c=7 -> middle(3)(7) = h(3)(7)
    // = 3*10+7 = 37 (b and c at asymmetric weights, so a supplied-arg
    // ordering bug in the Call-leaf's own further resolution would give
    // a different, wrong number); a=-5 (a<=0) with b=3 (unused decoy),
    // c=7 -> c-1 = 6.
    for (a_val, b_val, c_val, expected) in [(5, 3, 7, 37), (-5, 3, 7, 6)] {
        let a_lit = s.lit(a_val);
        let b_lit = s.lit(b_val);
        let c_lit = s.lit(c_val);
        let root_a = s.app(root, a_lit);
        let root_ab = s.app(root_a, b_lit);
        let h_term = s.app(root_ab, c_lit);
        assert_eq!(
            eval::apply_term(&s, h_term, &[]).unwrap(),
            expected,
            "a={a_val} b={b_val} c={c_val}: interpreter sanity check"
        );

        let mut combinators = ClosureCombinators::new(&s);
        combinators.cp.arith.lit(a_val);
        combinators.cp.arith.lit(b_val);
        combinators.cp.arith.lit(c_val);
        let (result, denotation, proof) = eval_and_prove(&s, h_term, &mut combinators, &[], &[], &[]).unwrap_or_else(|| {
            panic!("a={a_val} b={b_val} c={c_val}: a Call-shaped IfTree leaf should get a concrete instance")
        });
        assert_eq!(
            result, expected,
            "a={a_val} b={b_val} c={c_val}: should agree with the reference interpreter, not just typecheck"
        );
        combinators.cp.arith.p.check(
            &proof,
            &kernel::id(combinators.cp.arith.int_ty(), denotation, combinators.cp.arith.lit_ref(expected)),
        )
        .unwrap_or_else(|e| panic!("a={a_val} b={b_val} c={c_val}: the recorded witness should independently re-typecheck: {e}"));
    }
}

#[test]
fn a_self_recursive_root_whose_body_never_actually_self_calls_gets_a_concrete_instance() {
    // rec helper a = if 0<a then (\c. c+a) else (\c. c-a) -- arity 1,
    // wrapped in `Term::Rec` (syntactically self-recursive), but its
    // own body never actually references the self-binder anywhere.
    // Previously declined outright by `clo_eq_ref`'s own blanket
    // `if is_rec { return None; }` check regardless of whether `body`
    // genuinely used the self-reference; now `compile::free_vars`'s
    // own `is_rec`-aware capture computation is threaded through
    // instead, and a term like this one -- which never actually needs
    // it -- gets a concrete instance same as a non-recursive root
    // would. `helper(a)(c)` is over-application (k=1): the whole term
    // should agree with `a+c` (0<a) or `c-a` (a<=0) directly.
    let mut s = TermStore::new();
    let a_ref1 = s.var(0);
    let c1 = s.var(0);
    let a_shifted1 = s.var(1);
    let c_plus_a = s.prim(PrimOp::Add, c1, a_shifted1);
    let then_branch = s.abs(c_plus_a); // \c. c+a

    let c2 = s.var(0);
    let a_shifted2 = s.var(1);
    let c_minus_a = s.prim(PrimOp::Sub, c2, a_shifted2);
    let else_branch = s.abs(c_minus_a); // \c. c-a

    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Lt, zero, a_ref1);
    let helper_body = s.if_(cond, then_branch, else_branch);
    let helper_abs = s.abs(helper_body); // \a. if 0<a then (\c.c+a) else (\c.c-a)
    let helper = s.rec(helper_abs); // rec-wrapped, never actually self-calling

    // Hand-verified against the reference interpreter before trusting
    // the term shape: a=5 (0<a) with c=3 -> c+a=8; a=-5 (a<=0) with
    // c=10 -> c-a=15 -- distinct numbers, so picking the wrong branch
    // would be caught, not masked by a coincidental match.
    for (a_val, c_val, expected) in [(5, 3, 8), (-5, 10, 15)] {
        let a_lit = s.lit(a_val);
        let c_lit = s.lit(c_val);
        let helper_a = s.app(helper, a_lit);
        let h_term = s.app(helper_a, c_lit);
        assert_eq!(eval::apply_term(&s, h_term, &[]).unwrap(), expected, "a={a_val} c={c_val}: interpreter sanity check");

        let mut combinators = ClosureCombinators::new(&s);
        combinators.cp.arith.lit(a_val);
        combinators.cp.arith.lit(c_val);
        let (result, denotation, proof) = eval_and_prove(&s, h_term, &mut combinators, &[], &[], &[])
            .unwrap_or_else(|| panic!("a={a_val} c={c_val}: a self-recursive root that never self-calls should get a concrete instance"));
        assert_eq!(result, expected, "a={a_val} c={c_val}: should agree with the reference interpreter, not just typecheck");
        combinators.cp.arith.p.check(
            &proof,
            &kernel::id(combinators.cp.arith.int_ty(), denotation, combinators.cp.arith.lit_ref(expected)),
        )
        .unwrap_or_else(|e| panic!("a={a_val} c={c_val}: the recorded witness should independently re-typecheck: {e}"));
    }
}

#[test]
fn an_over_application_with_the_wrong_number_of_extra_args_is_out_of_scope() {
    // f = \a. if 0<a then (\c d. c-d) else (\c d. d-c) -- k=2, but
    // called with only 1 extra argument (a partial dispatch against
    // the chosen closure) -- `AppShape::LitLambdaOver`'s own
    // `args.len() != root_arity + k` guard should reject this.
    let mut s = TermStore::new();
    let d1 = s.var(0);
    let c1 = s.var(1);
    let cd1 = s.prim(PrimOp::Sub, c1, d1);
    let closure1_inner = s.abs(cd1);
    let closure1 = s.abs(closure1_inner);
    let c2 = s.var(1);
    let d2 = s.var(0);
    let dc2 = s.prim(PrimOp::Sub, d2, c2);
    let closure2_inner = s.abs(dc2);
    let closure2 = s.abs(closure2_inner);
    let a_body = s.var(0);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Lt, zero, a_body);
    let f_body = s.if_(cond, closure1, closure2);
    let f = s.abs(f_body);

    let a_lit = s.lit(5);
    let c_lit = s.lit(10);
    let fa = s.app(f, a_lit);
    let h = s.app(fa, c_lit); // only 1 extra arg, k=2 expected

    let mut combinators = ClosureCombinators::new(&s);
    assert!(
        eval_and_prove(&s, h, &mut combinators, &[], &[], &[]).is_none(),
        "an under-applied over-application should stay out of scope, not panic"
    );
}

#[test]
fn a_capturing_partial_application_created_inside_a_self_call_argument_gets_a_universal_proof() {
    // rec f n acc = if n <= 0 then acc else f(n-1, caller(capturing_add(n)))
    // where capturing_add = \x y. x + y + acc (captures f's own second
    // parameter) and caller = \g. g(4) -- same shape as
    // capturing_closure_loop above, but the self-call argument
    // partially applies a *capturing* literal lambda (one argument
    // short) and completes it through caller, rather than creating and
    // immediately calling a fully-applied closure. This is exactly the
    // shape that exposed a real staleness bug, caught by compile_fuzz's
    // random-term fuzzing before this dedicated regression test existed:
    // a missed `mk_env_ref` push under scope-time priming (`RELATED_WORK.md`
    // §70); kept as a regression test.
    let mut s = TermStore::new();
    let x = s.var(1);
    let y = s.var(0);
    let acc_captured = s.var(2); // acc, shifted by capturing_add's own 2 binders
    let xy = s.prim(PrimOp::Add, x, y);
    let xyz = s.prim(PrimOp::Add, xy, acc_captured);
    let inner_ca = s.abs(xyz);
    let capturing_add = s.abs(inner_ca);

    let n_ref = s.var(1);
    let partial = s.app(capturing_add, n_ref); // capturing_add(n) -- one arg short

    let g = s.var(0);
    let four = s.lit(4);
    let call_g = s.app(g, four);
    let caller = s.abs(call_g);

    let new_acc = s.app(caller, partial); // caller(partial) = n + 4 + acc

    let n = s.var(1);
    let acc = s.var(0);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Le, n, zero);
    let one = s.lit(1);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one);
    let f = s.var(2);
    let f_n1 = s.app(f, n_minus_1);
    let rec_call = s.app(f_n1, new_acc);
    let body = s.if_(cond, acc, rec_call);
    let inner = s.abs(body);
    let abs = s.abs(inner);
    let h = s.rec(abs);

    let proof = prove_tail_recursive_universal(&s, h)
        .expect("a self-recursive loop partially applying a fresh capturing literal each iteration should get a universal proof");
    assert_eq!(proof.arity, 2);
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.theorem_proof, &proof.theorem_ty)
        .expect("the recorded theorem should independently re-typecheck");

    assert!(compile::try_compile(&s, h).is_some());
}

#[test]
fn a_closure_created_in_a_leafs_own_top_level_expression_gets_a_universal_proof() {
    // rec f n = if n <= 0 then 0 else (\y. n+y)(5) + f(n-1) -- the
    // closure creation+call sits in the leaf's own top-level
    // expression (combined arithmetically with the recursive call),
    // not nested inside a self-call's own argument list --
    // find_self_calls/denote_with_placeholders now cover this too
    // (mirroring denote_closure_typed's own Term::Abs | Term::Rec
    // handling), not just a self-call argument's own closure creation.
    let mut s = TermStore::new();
    let y = s.var(0);
    let n_captured = s.var(1);
    let sum = s.prim(PrimOp::Add, n_captured, y);
    let closure = s.abs(sum);
    let five = s.lit(5);
    let call = s.app(closure, five);
    let n = s.var(0);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Le, n, zero);
    let one = s.lit(1);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one);
    let f = s.var(1);
    let rec_call = s.app(f, n_minus_1);
    let sum2 = s.prim(PrimOp::Add, call, rec_call);
    let body = s.if_(cond, zero, sum2);
    let abs = s.abs(body);
    let h = s.rec(abs);

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
    // fully-saturated call to the self-recursive combinator `it`,
    // which `prove_closure_expr`'s own `Term::Rec` widening covers --
    // see a_directly_called_self_recursive_combinator_gets_a_closure_proof
    // below for the same shape without a closure-typed parameter
    // involved), independently of `prove_tail_recursive_universal`'s
    // own new coverage that
    // `a_closure_typed_loop_carried_parameter_gets_a_universal_proof`
    // above exercises directly against `it` itself.
    let mut s = TermStore::new();
    let it = iterate(&mut s);
    let i = inc(&mut s);
    let five = s.lit(5);
    let three = s.lit(3);
    let it_3_i = s.app2(it, three, i);
    let applied = s.app(it_3_i, five); // iterate(3, inc, 5) = 8

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
    let n = s2.var(0);
    let fv = s2.var(1);
    let one = s2.lit(1);
    let cond = s2.prim(PrimOp::Le, n, one);
    let n_minus_1 = s2.prim(PrimOp::Sub, n, one);
    let rec_call = s2.app(fv, n_minus_1);
    let else_branch = s2.prim(PrimOp::Mul, n, rec_call);
    let body = s2.if_(cond, one, else_branch);
    let abs = s2.abs(body);
    let fact = s2.rec(abs);
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
    // rec f n = if n > 0 then f(n - 1) else n -- unlike `gcd` above, the
    // tail call is the *then*-branch and the base case is the *else*-
    // branch, exercising the other `cond`-gating polarity
    // (`prove_tail_recursive_universal`'s `base_lit = 0` arm, vs gcd's
    // `base_lit = 1`) that gcd alone never touches.
    let mut s = TermStore::new();
    let n = s.var(0);
    let f = s.var(1);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Lt, zero, n);
    let one = s.lit(1);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one);
    let rec_call = s.app(f, n_minus_1);
    let body = s.if_(cond, rec_call, n);
    let abs = s.abs(body);
    let countdown = s.rec(abs);

    let proof = prove_tail_recursive_universal(&s, countdown)
        .expect("countdown should get a universal proof");
    assert_eq!(proof.arity, 1);
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.theorem_proof, &proof.theorem_ty)
        .expect("the recorded theorem should independently re-typecheck");
}

#[test]
fn tail_recursive_gcd_with_two_base_cases_gets_a_universal_proof() {
    // rec f a b = if a == 0 then b else if b == 0 then a else f(b, a mod b)
    // -- deeper than a single `If`: two base leaves (`b` at path
    // [a==0], `a` at path [a!=0, b==0]) and one tail leaf (`f(b, a mod
    // b)` at path [a!=0, b!=0]), exercising the widened
    // `prove_tail_recursive_universal` (one `Ev` constructor per leaf,
    // each gated by its own *conjunction* of path premises, not a
    // single top-level condition).
    let mut s = TermStore::new();
    let b = s.var(0);
    let a = s.var(1);
    let f = s.var(2);
    let zero = s.lit(0);
    let cond_a = s.prim(PrimOp::Eq, a, zero);
    let cond_b = s.prim(PrimOp::Eq, b, zero);
    let a_mod_b = s.prim(PrimOp::Mod, a, b);
    let rec_call = s.app2(f, b, a_mod_b);
    let inner_if = s.if_(cond_b, a, rec_call);
    let body = s.if_(cond_a, b, inner_if);
    let inner = s.abs(body);
    let abs = s.abs(inner);
    let g = s.rec(abs);

    let proof =
        prove_tail_recursive_universal(&s, g).expect("gcd with two base cases should get a universal proof");
    assert_eq!(proof.arity, 2);
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.theorem_proof, &proof.theorem_ty)
        .expect("the recorded theorem should independently re-typecheck");
}

#[test]
fn non_tail_recursion_gets_a_universal_proof_now() {
    // rec f n = if n <= 1 then 1 else n * f(n - 1) -- factorial: the
    // self-call is nested inside a multiplication, not tail position.
    // Generalizing Ev/ev_rec/loop_val to leaves with an arbitrary
    // self-call count, recombined via kernel::cong_n, covers this too
    // (this was the whole point of widening past tail recursion).
    let mut s = TermStore::new();
    let n = s.var(0);
    let fv = s.var(1);
    let one = s.lit(1);
    let cond = s.prim(PrimOp::Le, n, one);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one);
    let rec_call = s.app(fv, n_minus_1);
    let else_branch = s.prim(PrimOp::Mul, n, rec_call);
    let body = s.if_(cond, one, else_branch);
    let abs = s.abs(body);
    let fact = s.rec(abs);

    let proof =
        prove_tail_recursive_universal(&s, fact).expect("factorial should now get a universal proof");
    assert_eq!(proof.arity, 1);
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.theorem_proof, &proof.theorem_ty)
        .expect("the recorded theorem should independently re-typecheck");
}

#[test]
fn fibonacci_two_self_calls_gets_a_universal_proof() {
    // rec f n = if n < 2 then n else f(n-1) + f(n-2) -- naive
    // Fibonacci: two self-calls combined by one Prim, exercising
    // combine_i for k=2 and kernel::cong_n's actual n>1 case
    // (factorial above only needs k=1, where cong_n's loop runs once).
    let mut s = TermStore::new();
    let n = s.var(0);
    let f = s.var(1);
    let two = s.lit(2);
    let cond = s.prim(PrimOp::Lt, n, two);
    let one = s.lit(1);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one);
    let n_minus_2 = s.prim(PrimOp::Sub, n, two);
    let call1 = s.app(f, n_minus_1);
    let call2 = s.app(f, n_minus_2);
    let else_branch = s.prim(PrimOp::Add, call1, call2);
    let body = s.if_(cond, n, else_branch);
    let abs = s.abs(body);
    let fib = s.rec(abs);

    let proof = prove_tail_recursive_universal(&s, fib).expect("fibonacci should get a universal proof");
    assert_eq!(proof.arity, 1);
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.theorem_proof, &proof.theorem_ty)
        .expect("the recorded theorem should independently re-typecheck");
}

#[test]
fn an_if_nested_inside_an_arithmetic_leaf_gets_a_universal_proof() {
    // rec f n = if n <= 0 then (n + (if n == 0 then 1 else 2)) else f(n-1)
    // -- the base leaf has an `If` embedded as a *sub-expression* of a
    // `Prim`, not as the whole body of some branch, so `classify_tree`
    // doesn't extract it into the DecisionTree itself; it stays part
    // of the leaf's own expression instead, and (with no self-call
    // inside it here) `find_self_calls`/`denote_with_placeholders`
    // just walk through it the same way they already walk a `Prim`.
    let mut s = TermStore::new();
    let n = s.var(0);
    let f = s.var(1);
    let zero = s.lit(0);
    let outer_cond = s.prim(PrimOp::Le, n, zero);
    let one = s.lit(1);
    let inner_cond = s.prim(PrimOp::Eq, n, zero);
    let two = s.lit(2);
    let inner_if = s.if_(inner_cond, one, two);
    let base_leaf = s.prim(PrimOp::Add, n, inner_if);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one);
    let rec_call = s.app(f, n_minus_1);
    let body = s.if_(outer_cond, base_leaf, rec_call);
    let abs = s.abs(body);
    let g = s.rec(abs);

    let proof = prove_tail_recursive_universal(&s, g).expect("a purely-arithmetic nested If should get a universal proof");
    assert_eq!(proof.arity, 1);
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.theorem_proof, &proof.theorem_ty)
        .expect("the recorded theorem should independently re-typecheck");
}

#[test]
fn a_self_call_inside_a_nested_if_branch_gets_a_universal_proof_and_a_correct_instance() {
    // rec f n = if n <= 0 then 0
    //           else n + (if n mod 2 == 0 then f(n-1) else f(n-1) + 1)
    // -- the recursive leaf's own `If` isn't the whole branch body
    // either (it's the right-hand operand of the outer `+`), and this
    // time each of its two branches contains its own self-call
    // occurrence: `find_self_calls` must find both (in the same
    // left-to-right order `denote_with_placeholders` substitutes them
    // in), each becoming its own placeholder of the leaf's `combine`
    // function.
    let mut s = TermStore::new();
    let n = s.var(0);
    let f = s.var(1);
    let zero = s.lit(0);
    let outer_cond = s.prim(PrimOp::Le, n, zero);
    let one = s.lit(1);
    let two = s.lit(2);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one);
    let call = s.app(f, n_minus_1);
    let odd_branch = s.prim(PrimOp::Add, call, one);
    let n_mod_2 = s.prim(PrimOp::Mod, n, two);
    let inner_cond = s.prim(PrimOp::Eq, n_mod_2, zero);
    let inner_if = s.if_(inner_cond, call, odd_branch);
    let base_leaf = s.prim(PrimOp::Add, n, inner_if);
    let body = s.if_(outer_cond, zero, base_leaf);
    let abs = s.abs(body);
    let g = s.rec(abs);

    let proof = prove_tail_recursive_universal(&s, g).expect("a nested If with a self-call in each branch should still get a universal proof");
    assert_eq!(proof.arity, 1);
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.theorem_proof, &proof.theorem_ty)
        .expect("the recorded theorem should independently re-typecheck");

    // f(0)=0, f(1)=1+(f(0)+1)=2, f(2)=2+f(1)=4, f(3)=3+(f(2)+1)=8,
    // f(4)=4+f(3)=12, f(5)=5+(f(4)+1)=18.
    assert_eq!(eval::apply_term(&s, g, &[5]).unwrap(), 18, "interpreter sanity check");

    let instance = prove_tail_recursive_instance(&s, g, &[5]).expect("f(5) should get an instance");
    kernel::check_in(&instance.globals, &Ctx::new(), &instance.proof, &kernel::id(instance.int_ty.clone(), instance.lhs.clone(), instance.rhs.clone()))
        .expect("the recorded instance proof should independently re-typecheck");
}

#[test]
fn a_clo_typed_nested_if_as_a_direct_self_call_argument_gets_a_universal_proof() {
    // rec f n g h = if n <= 0 then 0
    //               else f(n-1, (if n mod 2 == 0 then g else h), h) + g(n) + h(n)
    // -- `chosen = if n mod 2 == 0 then g else h` is a self-call's own
    // argument (threaded into the next iteration's `g` slot), and both
    // branches are `Clo`-typed parameters, not `Int`s -- exercises
    // `denote_closure_typed`'s widened `Term::If` arm (mirroring
    // `denote_closure`'s three-way Int/Int-or-Clo/Clo match via
    // `ite_clo_ref`), which builds each self-call argument's own
    // denotation for the leaf's `Ev` constructor. `g`/`h` are each
    // called directly (`g(n)`/`h(n)`) so `infer_closure_arities`
    // classifies both as `Clo`-typed arity-1 parameters in the first
    // place.
    let mut s = TermStore::new();
    let n = s.var(2);
    let g = s.var(1);
    let h = s.var(0);
    let f = s.var(3);

    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Le, n, zero);
    let one = s.lit(1);
    let two = s.lit(2);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one);
    let n_mod_2 = s.prim(PrimOp::Mod, n, two);
    let inner_cond = s.prim(PrimOp::Eq, n_mod_2, zero);
    let chosen = s.if_(inner_cond, g, h);

    let f_n1 = s.app(f, n_minus_1);
    let f_n1_chosen = s.app(f_n1, chosen);
    let self_call = s.app(f_n1_chosen, h);

    let call_g_n = s.app(g, n);
    let call_h_n = s.app(h, n);
    let sum1 = s.prim(PrimOp::Add, self_call, call_g_n);
    let leaf = s.prim(PrimOp::Add, sum1, call_h_n);

    let body = s.if_(cond, zero, leaf);
    let b1 = s.abs(body);
    let b2 = s.abs(b1);
    let abs = s.abs(b2);
    let top = s.rec(abs);

    let proof = prove_tail_recursive_universal(&s, top)
        .expect("a Clo-typed nested If as a direct self-call argument should get a universal proof");
    assert_eq!(proof.arity, 3);
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.theorem_proof, &proof.theorem_ty)
        .expect("the recorded theorem should independently re-typecheck");
}

#[test]
fn a_clo_typed_nested_if_as_an_ad_hoc_closures_own_argument_gets_a_universal_proof() {
    // rec f n g g2 x =
    //   if n <= 0 then x
    //   else g(0) + g2(0) + (\h. h(x))(if n mod 2 == 0 then g else g2)
    //        + f(n-1, g, g2, x)
    // -- unlike the test above, the nested If here isn't a self-call's
    // own argument (find_self_calls's early self-call match would
    // consume the whole call node before ever walking into it); it's
    // the argument to an ad-hoc closure (`\h. h(x)`, itself capturing
    // `x` and calling its own `h` parameter, so `h` is itself
    // Clo-typed) created and called within the leaf, *alongside* a
    // separate, visible self-call in the same leaf's `Prim` tree. This
    // exercises `denote_with_placeholders`'s own widened `Term::If`
    // arm -- the leaf-specific walker that builds the leaf's `combine`
    // function body -- rather than `denote_closure_typed`'s. `g`/`g2`
    // are each called directly (`g(0)`/`g2(0)`) purely so
    // `infer_closure_arities` classifies both as `Clo`-typed.
    let mut s = TermStore::new();
    let n = s.var(3);
    let g = s.var(2);
    let g2 = s.var(1);
    let x = s.var(0);
    let f = s.var(4);

    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Le, n, zero);
    let one = s.lit(1);
    let two = s.lit(2);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one);
    let n_mod_2 = s.prim(PrimOp::Mod, n, two);
    let inner_cond = s.prim(PrimOp::Eq, n_mod_2, zero);
    let chosen = s.if_(inner_cond, g, g2);

    let call_g0 = s.app(g, zero);
    let call_g20 = s.app(g2, zero);
    let ab = s.prim(PrimOp::Add, call_g0, call_g20);

    // `\h. h(x)`, capturing `x` (Var(1) inside the closure's own
    // body, shifted by `h`'s own binder), h itself Clo-typed since
    // it's called right there.
    let h_var = s.var(0);
    let x_in_closure = s.var(1);
    let h_call = s.app(h_var, x_in_closure);
    let closure = s.abs(h_call);
    let closure_applied = s.app(closure, chosen);

    let abc = s.prim(PrimOp::Add, ab, closure_applied);

    let f_n1 = s.app(f, n_minus_1);
    let f_n1_g = s.app(f_n1, g);
    let f_n1_g_g2 = s.app(f_n1_g, g2);
    let self_call = s.app(f_n1_g_g2, x);

    let leaf = s.prim(PrimOp::Add, abc, self_call);
    let body = s.if_(cond, x, leaf);

    let b1 = s.abs(body);
    let b2 = s.abs(b1);
    let b3 = s.abs(b2);
    let abs = s.abs(b3);
    let top = s.rec(abs);

    let proof = prove_tail_recursive_universal(&s, top).expect(
        "a Clo-typed nested If used as an ad-hoc closure's own argument, alongside a separate self-call in the same leaf, should get a universal proof",
    );
    assert_eq!(proof.arity, 4);
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.theorem_proof, &proof.theorem_ty)
        .expect("the recorded theorem should independently re-typecheck");
}

#[test]
fn non_tail_recursion_is_out_of_scope_for_the_relational_proof() {
    // factorial's self-call is nested inside a multiplication (n *
    // f(n-1)), not a bare tail call -- compile.rs itself compiles this
    // via a plain `call`, not a loop, so this proof (which specifically
    // targets the loop transformation) correctly doesn't apply either.
    let mut s = TermStore::new();
    let n = s.var(0);
    let fv = s.var(1);
    let one = s.lit(1);
    let cond = s.prim(PrimOp::Le, n, one);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one);
    let rec_call = s.app(fv, n_minus_1);
    let else_branch = s.prim(PrimOp::Mul, n, rec_call);
    let body = s.if_(cond, one, else_branch);
    let abs = s.abs(body);
    let fact = s.rec(abs);

    assert!(prove_tail_recursive_call(&s, fact, &[5]).is_none());
}

/// A long-running tail recursion used to take the *process* down.
///
/// `prove_tail_recursive_call` accumulates an expression that deepens
/// a couple of levels per trace step, and both the kernel's recursive
/// traversals and the recursive `Drop` of the resulting `Rc<Expr>`
/// chain have finite stack. With the old 10,000-step budget a loop
/// like this built a ~40,000-level expression and died with
/// `STATUS_STACK_OVERFLOW` -- not a failed proof, a crashed process,
/// reachable from `jit::JitEngine::apply` through the sibling
/// `prove_closure_expr_instance`. See `RELATED_WORK.md` §30.
///
/// Declining is the correct outcome here; surviving to decline is the
/// point of the test.
#[test]
fn a_long_running_trace_declines_instead_of_overflowing_the_stack() {
    // rec f n x = if n <= 0 then x else f(n - 1, x + 1), run 20,000
    // times -- far past any budget, which is exactly the case that
    // used to crash rather than return.
    let mut s = TermStore::new();
    let x = s.var(0);
    let n = s.var(1);
    let f = s.var(2);
    let zero = s.lit(0);
    let one = s.lit(1);
    let cond = s.prim(PrimOp::Le, n, zero);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one);
    let x_plus_1 = s.prim(PrimOp::Add, x, one);
    let rec_call = s.app2(f, n_minus_1, x_plus_1);
    let body = s.if_(cond, x, rec_call);
    let inner = s.abs(body);
    let outer = s.abs(inner);
    let h = s.rec(outer);

    assert_eq!(eval::apply_term(&s, h, &[20_000, 0]).unwrap(), 20_000);
    assert!(prove_tail_recursive_call(&s, h, &[20_000, 0]).is_none());

    // And a trace short enough to stay under every ceiling still
    // proves, so the bound above isn't simply switching the strategy
    // off.
    assert!(prove_tail_recursive_call(&s, h, &[10, 0]).is_some());
}

#[test]
fn non_recursive_term_is_out_of_scope_for_the_relational_proof() {
    let mut s = TermStore::new();
    let a = s.var(1);
    let b = s.var(0);
    let sum = s.prim(PrimOp::Add, a, b);
    let inner = s.abs(sum);
    let f = s.abs(inner);
    assert!(prove_tail_recursive_call(&s, f, &[1, 2]).is_none());
}

/// Pins *why* `jit::JitEngine::kernel_verify`'s `prove_tail_recursive_call`
/// step is never the winning strategy in practice (measured: zero
/// firings across the whole lib suite, against six for the
/// `prove_closure_expr_instance` step -- see `RELATED_WORK.md` 28).
///
/// The one place it is genuinely more permissive than
/// `prove_tail_recursive_universal` is the `If` condition:
/// `classify_tree` requires a direct comparison, while `classify_step`
/// just evaluates whatever is there on the concrete arguments. But
/// `compile::build_node`'s `If` arm imposes exactly `classify_tree`'s
/// restriction, so a term in that gap never compiles, and
/// `kernel_verify` never runs on it at all.
///
/// That makes the two restrictions load-bearing *as a pair*. This test
/// fails the moment either is relaxed without the other -- which is
/// precisely when the relational step would start being reachable
/// again, and when the "it's unreached, consider deleting it" note in
/// `RELATED_WORK.md` 28 would stop being true.
#[test]
fn the_relational_steps_extra_reach_lies_entirely_outside_the_compilable_fragment() {
    // rec f n = if (n - 1) then f(n - 1) else 42
    //
    // Tail-recursive and terminating (n=3: 2 -> 1 -> 0 -> 42), but the
    // condition is a `Sub`, not a comparison.
    let mut s = TermStore::new();
    let n = s.var(0);
    let f = s.var(1);
    let one = s.lit(1);
    let base = s.lit(42);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one);
    let rec_call = s.app(f, n_minus_1);
    let body = s.if_(n_minus_1, rec_call, base);
    let abs = s.abs(body);
    let h = s.rec(abs);

    // It really does compute what the shape says.
    assert_eq!(eval::apply_term(&s, h, &[3]).unwrap(), 42);

    // The relational (per-execution) proof accepts it...
    assert!(prove_tail_recursive_call(&s, h, &[3]).is_some());
    // ...the universal one doesn't, because `classify_tree` rejects a
    // non-comparison condition...
    assert!(prove_tail_recursive_universal(&s, h).is_none());
    // ...and none of that matters, because `build_node`'s `If` arm rejects the
    // same condition, so the term never reaches the JIT's cascade.
    assert!(compile::try_compile(&s, h).is_none());
}

#[test]
fn tail_recursive_gcd_gets_a_kernel_checked_instance_proof() {
    let mut s = TermStore::new();
    let g = gcd(&mut s);

    for (a, b) in [(48, 18), (270, 192), (17, 5), (0, 7)] {
        let proof = prove_tail_recursive_instance(&s, g, &[a, b])
            .unwrap_or_else(|| panic!("gcd({a},{b}) should get a kernel-checked instance"));
        assert_eq!(proof.arity, 2);
        kernel::check_in(&proof.globals, &Ctx::new(), &proof.proof, &kernel::id(proof.int_ty.clone(), proof.lhs.clone(), proof.rhs.clone()))
            .expect("the recorded instance proof should independently re-typecheck");
    }
}

#[test]
fn non_tail_recursion_gets_a_kernel_checked_instance_proof() {
    // rec f n = if n <= 1 then 1 else n * f(n - 1)
    let mut s = TermStore::new();
    let n = s.var(0);
    let fv = s.var(1);
    let one = s.lit(1);
    let cond = s.prim(PrimOp::Le, n, one);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one);
    let rec_call = s.app(fv, n_minus_1);
    let else_branch = s.prim(PrimOp::Mul, n, rec_call);
    let body = s.if_(cond, one, else_branch);
    let abs = s.abs(body);
    let fact = s.rec(abs);

    for n in [0, 1, 5, 10] {
        let proof = prove_tail_recursive_instance(&s, fact, &[n])
            .unwrap_or_else(|| panic!("factorial({n}) should get a kernel-checked instance"));
        assert_eq!(proof.arity, 1);
        kernel::check_in(&proof.globals, &Ctx::new(), &proof.proof, &kernel::id(proof.int_ty.clone(), proof.lhs.clone(), proof.rhs.clone()))
            .expect("the recorded instance proof should independently re-typecheck");
    }
}

#[test]
fn fibonacci_branching_leaves_get_kernel_checked_instances() {
    // rec f n = if n < 2 then n else f(n-1) + f(n-2) -- two self-calls
    // in the recursive leaf. Once genuinely out of scope (see
    // build_ev_witness's own docs for the fix: a `memo` DP cache plus a
    // congruence-based recast of each cached witness to the calling
    // leaf's own denoted call arguments) -- covers any number of
    // self-calls per leaf now, not just at most one.
    let mut s = TermStore::new();
    let n = s.var(0);
    let f = s.var(1);
    let two = s.lit(2);
    let cond = s.prim(PrimOp::Lt, n, two);
    let one = s.lit(1);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one);
    let n_minus_2 = s.prim(PrimOp::Sub, n, two);
    let call1 = s.app(f, n_minus_1);
    let call2 = s.app(f, n_minus_2);
    let else_branch = s.prim(PrimOp::Add, call1, call2);
    let body = s.if_(cond, n, else_branch);
    let abs = s.abs(body);
    let fib = s.rec(abs);

    for n in [1, 2, 8] {
        let proof = prove_tail_recursive_instance(&s, fib, &[n]).unwrap_or_else(|| panic!("fib({n}) should get an instance"));
        assert_eq!(proof.arity, 1);
        kernel::check_in(&proof.globals, &Ctx::new(), &proof.proof, &kernel::id(proof.int_ty.clone(), proof.lhs.clone(), proof.rhs.clone()))
            .expect("the recorded instance proof should independently re-typecheck");
    }
}

/// Nodes in `e` counted once per allocation, the size `infer` would
/// walk if it memoised by node.
fn dag_size(e: &Expr) -> usize {
    fn go(e: &Expr, seen: &mut std::collections::HashSet<*const Expr>) -> usize {
        let mut n = 1;
        kernel::same_shape(e, e, |p, _| {
            if seen.insert(kernel::Rc::as_ptr(p)) {
                n += go(p, seen);
            }
            true
        });
        n
    }
    go(e, &mut Default::default())
}

/// `fib(n)`'s witness reuses each smaller call's witness from
/// `build_ev_witness`'s memo. With postulates as constants (rather than
/// `Var`s that shift under a growing context) the DAG grows linearly:
/// the spike measured 5,445 nodes at `fib(8)` and 10,501 at `fib(16)`
/// (`RELATED_WORK.md` §69).
#[test]
fn a_fibonacci_instance_proof_shares_its_repeated_witnesses() {
    let mut s = TermStore::new();
    let n = s.var(0);
    let f = s.var(1);
    let two = s.lit(2);
    let cond = s.prim(PrimOp::Lt, n, two);
    let one = s.lit(1);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one);
    let n_minus_2 = s.prim(PrimOp::Sub, n, two);
    let call1 = s.app(f, n_minus_1);
    let call2 = s.app(f, n_minus_2);
    let else_branch = s.prim(PrimOp::Add, call1, call2);
    let body = s.if_(cond, n, else_branch);
    let abs = s.abs(body);
    let fib = s.rec(abs);

    let size = |n: i64| dag_size(&prove_tail_recursive_instance(&s, fib, &[n]).unwrap().proof);
    let (small, large) = (size(8), size(16));
    assert!(2 * large < 5 * small, "fib(8): {small} nodes, fib(16): {large}");
}

/// `fib(16)`'s instance proof, built and re-checked. With postulates
/// as constants it's a linear DAG (§69); before, it was 227k nodes and
/// seconds of work.
#[test]
fn fib16_instance_proof_builds_and_checks_quickly() {
    // same fib TermStore setup as fib16_instance_proof_cost
    let mut s = TermStore::new();
    let n = s.var(0);
    let f = s.var(1);
    let two = s.lit(2);
    let cond = s.prim(PrimOp::Lt, n, two);
    let one = s.lit(1);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one);
    let n_minus_2 = s.prim(PrimOp::Sub, n, two);
    let call1 = s.app(f, n_minus_1);
    let call2 = s.app(f, n_minus_2);
    let else_branch = s.prim(PrimOp::Add, call1, call2);
    let body = s.if_(cond, n, else_branch);
    let abs = s.abs(body);
    let fib = s.rec(abs);

    let t = std::time::Instant::now();
    let proof = prove_tail_recursive_instance(&s, fib, &[16]).unwrap();
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.proof, &kernel::id(proof.int_ty.clone(), proof.lhs.clone(), proof.rhs.clone()))
        .expect("fib(16)'s instance proof re-checks");
    let took = t.elapsed();
    assert!(took < std::time::Duration::from_secs(3), "took {took:?}");
}

/// `fib(16)`'s instance proof: its DAG size, and the time to build it
/// and to check it again. The headline number for the §64 stages.
/// Ignored, since it takes seconds. Run with
/// `cargo test --release --lib fib16_instance_proof_cost -- --ignored --nocapture`.
#[test]
#[ignore]
fn fib16_instance_proof_cost() {
    let mut s = TermStore::new();
    let n = s.var(0);
    let f = s.var(1);
    let two = s.lit(2);
    let cond = s.prim(PrimOp::Lt, n, two);
    let one = s.lit(1);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one);
    let n_minus_2 = s.prim(PrimOp::Sub, n, two);
    let call1 = s.app(f, n_minus_1);
    let call2 = s.app(f, n_minus_2);
    let else_branch = s.prim(PrimOp::Add, call1, call2);
    let body = s.if_(cond, n, else_branch);
    let abs = s.abs(body);
    let fib = s.rec(abs);

    let t = std::time::Instant::now();
    let proof = prove_tail_recursive_instance(&s, fib, &[16]).unwrap();
    let build = t.elapsed();
    let t = std::time::Instant::now();
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.proof, &kernel::id(proof.int_ty.clone(), proof.lhs.clone(), proof.rhs.clone()))
        .expect("fib(16)'s instance proof re-checks");
    println!("fib16 dag={} build={build:?} check={:?}", dag_size(&proof.proof), t.elapsed());
}

#[test]
fn one_functions_instance_proof_is_rejected_against_anothers_type() {
    // Same adversarial shape as
    // one_functions_theorem_proof_is_rejected_against_anothers_type,
    // one level down: an instance proof built for one function must
    // not typecheck against another's (unrelated Ev/combine layout,
    // different concrete call).
    let mut s = TermStore::new();
    let g = gcd(&mut s);
    let gcd_proof = prove_tail_recursive_instance(&s, g, &[48, 18]).expect("gcd instance proof");

    let mut s2 = TermStore::new();
    let n = s2.var(0);
    let fv = s2.var(1);
    let one = s2.lit(1);
    let cond = s2.prim(PrimOp::Le, n, one);
    let n_minus_1 = s2.prim(PrimOp::Sub, n, one);
    let rec_call = s2.app(fv, n_minus_1);
    let else_branch = s2.prim(PrimOp::Mul, n, rec_call);
    let body = s2.if_(cond, one, else_branch);
    let abs = s2.abs(body);
    let fact = s2.rec(abs);
    let fact_proof = prove_tail_recursive_instance(&s2, fact, &[5]).expect("factorial instance proof");

    assert!(
        kernel::check_in(
            &gcd_proof.globals,
            &Ctx::new(),
            &gcd_proof.proof,
            &kernel::id(fact_proof.int_ty.clone(), fact_proof.lhs.clone(), fact_proof.rhs.clone()),
        )
        .is_err(),
        "gcd's instance proof should be rejected against factorial's instance type"
    );
}

/// `\f. \x. f (f x)` -- both `f` and `x` are its own parameters, no
/// captures (same shape `compile::tests::twice` uses).
fn twice(s: &mut TermStore) -> Hash {
    let f = s.var(1);
    let x = s.var(0);
    let fx = s.app(f, x);
    let ffx = s.app(f, fx);
    let inner = s.abs(ffx);
    s.abs(inner)
}

/// `\y. y + 1`.
fn inc(s: &mut TermStore) -> Hash {
    let y = s.var(0);
    let one = s.lit(1);
    let y_plus_1 = s.prim(PrimOp::Add, y, one);
    s.abs(y_plus_1)
}

#[test]
fn twice_inc_5_gets_a_kernel_checked_closure_proof() {
    // (twice inc) 5 -- the higher-order demo term main.rs uses: a
    // closed (arity 0), non-recursive expression combining two
    // non-capturing combinators.
    let mut s = TermStore::new();
    let t = twice(&mut s);
    let i = inc(&mut s);
    let five = s.lit(5);
    let applied = s.app2(t, i, five);

    let proof = prove_closure_expr(&s, applied).expect("(twice inc) 5 should get a closure proof");
    assert_eq!(proof.arity, 0);
    kernel::check_in(
        &proof.globals,
        &Ctx::new(),
        &proof.proof,
        &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
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
        &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
    )
    .expect("the recorded proof should independently re-typecheck");
}

/// `rec f n = if n <= 1 then 1 else n * f(n-1)`, factorial -- used below
/// as a named self-recursive combinator, the same way `twice`/`inc` are
/// used as non-recursive ones.
fn fact(s: &mut TermStore) -> Hash {
    let n = s.var(0);
    let f = s.var(1);
    let one = s.lit(1);
    let cond = s.prim(PrimOp::Le, n, one);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one);
    let rec_call = s.app(f, n_minus_1);
    let else_branch = s.prim(PrimOp::Mul, n, rec_call);
    let body = s.if_(cond, one, else_branch);
    let abs = s.abs(body);
    s.rec(abs)
}

#[test]
fn a_directly_called_self_recursive_combinator_gets_a_closure_proof() {
    // fact(10) -- a direct static call to a self-recursive combinator,
    // the App-root `Term::Rec` branch (mirroring the `Term::Abs`
    // direct-call path `twice_inc_5` already exercises): the call is
    // postulated opaque either way, so widening the pattern needed no
    // new proof machinery.
    let mut s = TermStore::new();
    let f = fact(&mut s);
    let ten = s.lit(10);
    let applied = s.app(f, ten);

    let proof = prove_closure_expr(&s, applied).expect("fact(10) should get a closure proof");
    assert_eq!(proof.arity, 0);
    kernel::check_in(
        &proof.globals,
        &Ctx::new(),
        &proof.proof,
        &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
    )
    .expect("the recorded proof should independently re-typecheck");

    assert!(compile::try_compile(&s, applied).is_some());
}

#[test]
fn a_self_recursive_combinator_used_as_a_value_gets_a_closure_proof() {
    // (\g. g 10) fact -- what `let fact = rec f n = .. in fact 10`
    // desugars to (found via the REPL -- see syntax.rs/repl.rs, and
    // jit::tests::a_let_bound_self_recursive_function_compiles_and_is_kernel_verified
    // for the same shape checked directly against jit.rs): `fact`
    // itself, a bare `Term::Rec` value, gets registered
    // (`ClosureCombinators::register`) the same way a non-recursive
    // literal does, then called through `wrapper`'s own closure-typed
    // parameter via call_indirect.
    let mut s = TermStore::new();
    let f = fact(&mut s);
    let g = s.var(0);
    let ten = s.lit(10);
    let call_g = s.app(g, ten);
    let wrapper = s.abs(call_g);
    let applied = s.app(wrapper, f);

    let proof = prove_closure_expr(&s, applied).expect("(\\g. g 10) fact should get a closure proof");
    assert_eq!(proof.arity, 0);
    kernel::check_in(
        &proof.globals,
        &Ctx::new(),
        &proof.proof,
        &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
    )
    .expect("the recorded proof should independently re-typecheck");

    assert!(compile::try_compile(&s, applied).is_some());
}

#[test]
fn a_partially_applied_self_recursive_combinator_used_as_a_value_gets_a_closure_proof() {
    // fact(1) supplied as a 1-of-1 partial application isn't a
    // meaningful example on its own (fact's arity is already 1), so
    // use a 2-ary self-recursive combinator instead: rec f n acc =
    // if n <= 0 then acc else f(n-1, n*acc); partial = f(3) (under-
    // applied by one arg); caller = \g. g(1); top = caller(partial).
    // pap_ref no longer rejects a recursive root -- compile::peel/
    // compile::free_vars/param_types_for were already generic over
    // is_rec (a call is always postulated opaque regardless), and
    // compile.rs's register_partial_app/lower_wat.rs's emit_pap_wrapper
    // never special-cased it either (a PAP wrapper only ever forwards a
    // static call to its root, indifferent to whether that root's own
    // codegen happens to loop), so the only thing standing in the way
    // was pap_ref's own extra is_rec check.
    let mut s = TermStore::new();
    let acc = s.var(0);
    let n = s.var(1);
    let f = s.var(2);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Le, n, zero);
    let one = s.lit(1);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one);
    let n_times_acc = s.prim(PrimOp::Mul, n, acc);
    let rec_call = s.app2(f, n_minus_1, n_times_acc);
    let body = s.if_(cond, acc, rec_call);
    let inner = s.abs(body);
    let abs = s.abs(inner);
    let fact2 = s.rec(abs);

    let three = s.lit(3);
    let partial = s.app(fact2, three);

    let g = s.var(0);
    let one2 = s.lit(1);
    let call_g = s.app(g, one2);
    let caller = s.abs(call_g);

    let top = s.app(caller, partial);

    let proof = prove_closure_expr(&s, top)
        .expect("a partially applied self-recursive combinator used as a value should get a closure proof");
    assert_eq!(proof.arity, 0);
    kernel::check_in(
        &proof.globals,
        &Ctx::new(),
        &proof.proof,
        &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
    )
    .expect("the recorded proof should independently re-typecheck");

    assert!(compile::try_compile(&s, top).is_some());
}

#[test]
fn partial_application_of_a_capturing_self_recursive_combinator_gets_a_closure_proof() {
    // The two pap_ref restrictions lifted independently this session
    // (a capturing root, then a self-recursive root) combined in one
    // term, to confirm they actually compose rather than each having
    // only been checked in isolation: \z. caller(fact2(3)) where
    // fact2 = rec f n acc = if n <= 0 then acc else f(n-1, n*acc+z)
    // captures z from the *enclosing* scope (not one of fact2's own
    // parameters), and is itself partially applied (one arg short) --
    // caller = \g. g(1) as before.
    let mut s = TermStore::new();
    let acc = s.var(0);
    let n = s.var(1);
    let f = s.var(2);
    let z = s.var(3); // captured from the enclosing \z. scope, not one of fact2's own params
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Le, n, zero);
    let one = s.lit(1);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one);
    let n_times_acc = s.prim(PrimOp::Mul, n, acc);
    let plus_z = s.prim(PrimOp::Add, n_times_acc, z);
    let rec_call = s.app2(f, n_minus_1, plus_z);
    let body = s.if_(cond, acc, rec_call);
    let acc_abs = s.abs(body);
    let n_abs = s.abs(acc_abs);
    let fact2 = s.rec(n_abs);

    let three = s.lit(3);
    let partial = s.app(fact2, three);

    let g = s.var(0);
    let one2 = s.lit(1);
    let call_g = s.app(g, one2);
    let caller = s.abs(call_g);

    let top_inner = s.app(caller, partial);
    let top = s.abs(top_inner);

    let proof = prove_closure_expr(&s, top).expect(
        "a partially applied self-recursive combinator that also captures an outer variable should get a closure proof",
    );
    assert_eq!(proof.arity, 1);
    kernel::check_in(
        &proof.globals,
        &Ctx::new(),
        &proof.proof,
        &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
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
    // since it's `build_universal`'s job, not this fragment's, to
    // prove what a self-recursive function's *own* body computes.
    let mut s = TermStore::new();
    let t = twice(&mut s);
    let i = inc(&mut s);
    let x = s.var(0);
    let applied = s.app2(t, i, x);
    let inner = s.abs(applied);
    let wrapped = s.rec(inner);

    assert!(prove_closure_expr(&s, wrapped).is_none());
}

#[test]
fn inconsistent_call_arity_for_a_parameter_is_still_out_of_scope_for_the_closure_proof() {
    // \f. f(1) + f(1, 2) -- `f`, a *parameter*, called with
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
    let f1 = s.var(0);
    let one = s.lit(1);
    let call1 = s.app(f1, one);
    let f2 = s.var(0);
    let two = s.lit(2);
    let call2 = s.app2(f2, one, two);
    let body = s.prim(PrimOp::Add, call1, call2);
    let g = s.abs(body);

    assert!(prove_closure_expr(&s, g).is_none());
}

#[test]
fn a_partially_applied_literal_lambda_used_as_a_value_gets_a_closure_proof() {
    // add = \x y. x + y; partial = add(3) (under-applied by one
    // argument); caller = \g. g(4); top = caller(partial) -- same
    // shape as compile::tests::partial_application_of_a_literal_lambda_compiles.
    // `partial` is denoted via pap_ref's new `Less`-arity branch (a
    // Clo-typed value), then completed through caller's own
    // call_indirect the same way any other Clo-typed argument would be.
    let mut s = TermStore::new();
    let x = s.var(1);
    let y = s.var(0);
    let sum = s.prim(PrimOp::Add, x, y);
    let inner_add = s.abs(sum);
    let add = s.abs(inner_add);

    let three = s.lit(3);
    let partial = s.app(add, three);

    let g = s.var(0);
    let four = s.lit(4);
    let call_g = s.app(g, four);
    let caller = s.abs(call_g);

    let top = s.app(caller, partial);

    let proof = prove_closure_expr(&s, top).expect("a partially applied literal lambda used as a value should get a closure proof");
    assert_eq!(proof.arity, 0);
    kernel::check_in(
        &proof.globals,
        &Ctx::new(),
        &proof.proof,
        &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
    )
    .expect("the recorded proof should independently re-typecheck");

    // Also actually compiles, and the two readings agree on scope.
    assert!(compile::try_compile(&s, top).is_some());
}

#[test]
fn a_partially_applied_literal_lambda_with_mixed_parameter_types_gets_a_closure_proof() {
    // caller2(twice(inc)) -- `twice`'s own param_types are
    // [None(x), Some(1)(f)] (mixed: x plain Int, f closure-typed),
    // unlike the add-based test above where both parameters happen to
    // be Int and so can't distinguish a correct `pap_ref` type slice
    // from an incorrectly-shifted one. Supplying only `f` (`inc`) is a
    // 1-of-2 partial application, so pap_ref's type must be built from
    // param_types[arity-k..] = param_types[1..2] = [Some(1)] (f's own
    // Clo type) -- not param_types[..k] = param_types[0..1] (x's Int
    // type, wrong parameter entirely). caller2 = \h. h(5) then
    // completes the wrapper with the missing `x` argument.
    let mut s = TermStore::new();
    let t = twice(&mut s);
    let i = inc(&mut s);
    let partial = s.app(t, i); // twice(inc) -- under-applied by one arg (x)

    let h = s.var(0);
    let five = s.lit(5);
    let call_h = s.app(h, five);
    let caller2 = s.abs(call_h);

    let top = s.app(caller2, partial);

    let proof = prove_closure_expr(&s, top).expect("a partially applied combinator with mixed parameter types should get a closure proof");
    assert_eq!(proof.arity, 0);
    kernel::check_in(
        &proof.globals,
        &Ctx::new(),
        &proof.proof,
        &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
    )
    .expect("the recorded proof should independently re-typecheck");

    assert!(compile::try_compile(&s, top).is_some());
}

#[test]
fn a_partially_applied_capturing_literal_lambda_used_as_a_value_gets_a_closure_proof() {
    // g = \z. (\g2. g2(4)) ((\x y. x + y + z)(3)) -- same shape as
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
    let y = s.var(0);
    let x = s.var(1);
    let z_captured = s.var(2);
    let xy = s.prim(PrimOp::Add, x, y);
    let xyz = s.prim(PrimOp::Add, xy, z_captured);
    let inner = s.abs(xyz);
    let capturing_add = s.abs(inner);

    let three = s.lit(3);
    let partial = s.app(capturing_add, three);

    let g2 = s.var(0);
    let four = s.lit(4);
    let call_g2 = s.app(g2, four);
    let caller = s.abs(call_g2);

    let called = s.app(caller, partial);
    let g = s.abs(called);

    let proof = prove_closure_expr(&s, g).expect("a partially applied capturing literal lambda used as a value should get a closure proof");
    assert_eq!(proof.arity, 1);
    kernel::check_in(
        &proof.globals,
        &Ctx::new(),
        &proof.proof,
        &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
    )
    .expect("the recorded proof should independently re-typecheck");

    assert!(compile::try_compile(&s, g).is_some());
}

#[test]
fn if_branches_with_different_pap_extra_arity_are_not_conflated_into_a_false_proof() {
    // root = \p a. if a == 0 then (\b. b) else (\b. a + b) -- root's
    // own saturated call (both p and a supplied) denotes a further
    // Clo_1, not Int, so `root`'s 1-of-2 partial application `root x`
    // (p supplied, a still missing) genuinely has remaining shape
    // Clo_2 (`a`, then `b`) -- not Clo_1, which is what every call
    // site of `combinator_return_type` assumed before `pap_extra_arity`
    // was folded in (see the doc comment on `pap_extra_arity` itself).
    //
    // top = \x. (\g. g 5) (if x == 0 then (root x) else (\y. y + 1))
    // puts that genuinely-Clo_2 value in one arm of an `If` whose other
    // arm, `\y. y + 1`, is a genuine, unrelated Clo_1 -- and then calls
    // the result with a single argument, as if it were uniformly
    // Clo_1. Before the fix this compiled to a claimed *universal*
    // (`refl`-based) kernel proof despite the two branches genuinely
    // disagreeing in arity; the kernel itself can't catch this,
    // because `Clo_k` is a literal Pi type family, so a wrong-but-
    // internally-consistent arity still typechecks on its own. The fix
    // must make this decline instead.
    let mut s = TermStore::new();
    let a0 = s.var(0);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Eq, a0, zero);
    let b0_id = s.var(0);
    let identity_b = s.abs(b0_id);
    let a1 = s.var(1);
    let b0 = s.var(0);
    let a_plus_b = s.prim(PrimOp::Add, a1, b0);
    let add_a_b = s.abs(a_plus_b);
    let a_body = s.if_(cond, identity_b, add_a_b);
    let a_abs = s.abs(a_body);
    let root = s.abs(a_abs);

    let x = s.var(0);
    let root_x = s.app(root, x);

    let inc_term = inc(&mut s);

    let x_for_cond = s.var(0);
    let zero_for_cond = s.lit(0);
    let outer_cond = s.prim(PrimOp::Eq, x_for_cond, zero_for_cond);
    let branch = s.if_(outer_cond, root_x, inc_term);

    let g = s.var(0);
    let five = s.lit(5);
    let call_g = s.app(g, five);
    let caller = s.abs(call_g);

    let call_arg = s.app(caller, branch);
    let top = s.abs(call_arg);

    assert!(
        prove_closure_expr(&s, top).is_none(),
        "the two If branches genuinely differ in arity (Clo_2 vs Clo_1); \
         claiming a universal proof here would be unsound"
    );
}

#[test]
fn over_application_of_a_literal_lambda_is_still_out_of_scope_for_the_closure_proof() {
    // add = \x y. x + y, called with three arguments -- rejected by
    // denote_closure's own args.len() > arity check (proof.rs has no
    // fragment for over-application at all, unlike compile.rs, which
    // now compiles the shape -- see lower_wat.rs's module docs and
    // compile::tests::an_over_applied_literal_lambda_returning_a_closure_compiles_and_matches_interpreter
    // -- though not *this* term specifically: `add`'s body is a plain
    // `Int`, never a further closure, so this one is genuinely
    // ill-typed and would only ever be trusted via jit.rs's own
    // sample verification, never a kernel-checked proof).
    let mut s = TermStore::new();
    let x = s.var(1);
    let y = s.var(0);
    let sum = s.prim(PrimOp::Add, x, y);
    let inner_add = s.abs(sum);
    let add = s.abs(inner_add);

    let one = s.lit(1);
    let two = s.lit(2);
    let three = s.lit(3);
    let partial = s.app2(add, one, two);
    let over_applied = s.app(partial, three);

    assert!(prove_closure_expr(&s, over_applied).is_none());
}

#[test]
fn calling_a_literal_lambda_whose_own_body_picks_between_two_closures_gets_a_closure_proof() {
    // \x. (\g. g 5) (if 0 < x then (\y. x + y) else (\y. x - y)) --
    // the same term compile.rs's own
    // a_capturing_closure_compiles_and_matches_interpreter test uses.
    // `picker` (whose own body is the If) is *directly called*
    // (`chosen = picker(x2)`, a fully-saturated application of a
    // literal lambda) -- `call_ref`'s own postulated type used to
    // always assume a directly-called combinator returns `Int`,
    // causing `chosen`'s claimed `Int` type to fail `inn`'s own
    // `.clo()?` check where it's used as `g`. `call_ref` now consults
    // `combinator_return_type` for its own return type instead of
    // universally assuming `Int` -- correctly classifying `picker`'s
    // body (an `If` between two closures) as `Clo`-typed, without
    // `call_ref` itself ever denoting `picker`'s own body -- so this
    // now gets a genuine kernel-checked proof.
    let mut s = TermStore::new();
    let x = s.var(0);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Lt, zero, x);
    let y_pos = s.var(0);
    let x_pos = s.var(1);
    let plus = s.prim(PrimOp::Add, x_pos, y_pos);
    let then_closure = s.abs(plus);
    let y_neg = s.var(0);
    let x_neg = s.var(1);
    let minus = s.prim(PrimOp::Sub, x_neg, y_neg);
    let else_closure = s.abs(minus);
    let body = s.if_(cond, then_closure, else_closure);
    let picker = s.abs(body);

    let g = s.var(0);
    let five = s.lit(5);
    let call_g = s.app(g, five);
    let inn = s.abs(call_g);

    let x2 = s.var(0);
    let chosen = s.app(picker, x2);
    let called = s.app(inn, chosen);
    let f = s.abs(called);

    assert!(compile::try_compile(&s, f).is_some(), "compile.rs should compile this via closure conversion");
    let proof = prove_closure_expr(&s, f).expect("picker's own Clo-typed body should now be reachable through call_ref");
    assert_eq!(proof.arity, 1);
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.proof, &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()))
        .expect("the recorded proof should independently re-typecheck");
}

#[test]
fn a_literal_lambda_picking_between_two_different_arity_closures_is_out_of_scope() {
    // Same shape as the test above -- `\x. (\g. g 5) (if 0 < x then
    // (\y. x + y) else (\y. \z. x - y - z))` -- except `picker`'s own
    // `else` branch now has arity *2*, not 1: `Clo`, before the
    // arity-indexed `Clo_k` refactor (`TYPES.md` section 7), was a
    // single, arity-blind kernel type, so this exact shape would have
    // kernel-*typechecked* under the old scheme (`ite_clo : Int -> Clo
    // -> Clo -> Clo` accepts any two `Clo`-typed branches, whatever
    // their underlying arity) while being genuinely unsound --
    // `inn`'s own `g 5` call commits to arity 1, silently wrong
    // whenever `picker` actually took the `else` branch. Both
    // `return_type_of`'s own arity-consistency check (in
    // `combinator_return_type`'s classification of `picker`'s body)
    // and, independently, `kernel::check`'s definitional-inequality
    // between `Clo_1` and `Clo_2` now reject this -- `call_ref` falls
    // back to assuming `picker`'s call is plain `Int`-typed (the
    // classifier can't determine a single consistent arity), which
    // then fails `inn`'s own `.clo()?` check on `g`, so
    // `prove_closure_expr` returns `None` rather than a
    // kernel-"verified" but unsound proof.
    let mut s = TermStore::new();
    let x = s.var(0);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Lt, zero, x);
    let y_pos = s.var(0);
    let x_pos = s.var(1);
    let plus = s.prim(PrimOp::Add, x_pos, y_pos);
    let then_closure = s.abs(plus); // arity 1: \y. x + y
    let z_neg = s.var(0);
    let y_neg = s.var(1);
    let x_neg = s.var(2);
    let x_minus_y = s.prim(PrimOp::Sub, x_neg, y_neg);
    let minus_z = s.prim(PrimOp::Sub, x_minus_y, z_neg);
    let else_inner = s.abs(minus_z);
    let else_closure = s.abs(else_inner); // arity 2: \y. \z. x - y - z
    let body = s.if_(cond, then_closure, else_closure);
    let picker = s.abs(body);

    let g = s.var(0);
    let five = s.lit(5);
    let call_g = s.app(g, five);
    let inn = s.abs(call_g);

    let x2 = s.var(0);
    let chosen = s.app(picker, x2);
    let called = s.app(inn, chosen);
    let f = s.abs(called);

    assert!(
        prove_closure_expr(&s, f).is_none(),
        "an If between two different-arity closures should be rejected, not accepted as a single blind Clo"
    );
}

#[test]
fn an_over_applied_literal_lambda_returning_a_closure_gets_a_closure_proof() {
    // f = \a b. if 0 < a then (\c. a+b+c) else (\c. a-b+c); f(a,b,c) --
    // same shape as compile::tests::
    // an_over_applied_literal_lambda_returning_a_closure_compiles_and_matches_interpreter/
    // jit::tests::an_over_applied_literal_lambda_returning_a_closure_compiles_and_is_kernel_verified.
    // Unlike the test above (a directly-called combinator's own
    // Clo-typed result used as a *value*), this is genuine
    // over-application: `f`'s own saturated call (`f(a,b)`) is
    // denoted first via `call_ref` (now correctly `Clo`-typed, same
    // classifier), then dispatched on the extra argument `c`
    // directly, exactly the way calling a closure-typed variable
    // already denotes.
    let mut s = TermStore::new();
    let c1 = s.var(0);
    let b1 = s.var(1);
    let a1 = s.var(2);
    let ab1 = s.prim(PrimOp::Add, a1, b1);
    let abc1 = s.prim(PrimOp::Add, ab1, c1);
    let closure1 = s.abs(abc1);

    let c2 = s.var(0);
    let b2 = s.var(1);
    let a2 = s.var(2);
    let amb2 = s.prim(PrimOp::Sub, a2, b2);
    let ambc2 = s.prim(PrimOp::Add, amb2, c2);
    let closure2 = s.abs(ambc2);

    let a_body = s.var(1);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Lt, zero, a_body);
    let body = s.if_(cond, closure1, closure2);
    let b_binder = s.abs(body);
    let f = s.abs(b_binder);

    let a_param = s.var(2);
    let b_param = s.var(1);
    let c_param = s.var(0);
    let fa = s.app(f, a_param);
    let fab = s.app(fa, b_param);
    let fabc = s.app(fab, c_param);
    let c_binder = s.abs(fabc);
    let bc_binder = s.abs(c_binder);
    let top = s.abs(bc_binder);

    assert_eq!(eval::apply_term(&s, top, &[10, 3, 100]).unwrap(), 113, "interpreter sanity check");
    assert_eq!(eval::apply_term(&s, top, &[-5, 3, 100]).unwrap(), 92, "interpreter sanity check");

    let proof = prove_closure_expr(&s, top).expect("an over-applied literal lambda returning a closure should get a proof");
    assert_eq!(proof.arity, 3);
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.proof, &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()))
        .expect("the recorded proof should independently re-typecheck");
}

#[test]
fn a_capturing_closure_used_as_a_value_gets_a_closure_proof() {
    // g = \x. (\h. h 5) (\y. x + y) -- `\y. x + y` captures `x`, g's
    // own parameter, and is used as a plain *value* (an argument to
    // `\h. h 5`), not directly called -- exercises
    // ClosureCombinators::register's mk_clo_ref path and
    // build_env_expr together with the pre-existing
    // call-through-a-parameter path, unmodified.
    let mut s = TermStore::new();
    let y = s.var(0);
    let x = s.var(1);
    let sum = s.prim(PrimOp::Add, x, y);
    let closure = s.abs(sum);

    let h = s.var(0);
    let five = s.lit(5);
    let call_h = s.app(h, five);
    let inn = s.abs(call_h);

    let applied = s.app(inn, closure);
    let g = s.abs(applied);

    let proof = prove_closure_expr(&s, g).expect("a capturing closure used as a value should get a proof now");
    assert_eq!(proof.arity, 1);
    kernel::check_in(
        &proof.globals,
        &Ctx::new(),
        &proof.proof,
        &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
    )
    .expect("the recorded proof should independently re-typecheck");

    for x_val in [-5, 0, 1, 42] {
        let interpreted = eval::apply_term(&s, g, &[x_val]).unwrap();
        assert_eq!(interpreted, x_val + 5, "sanity check on the term itself, not the proof");
    }
}

#[test]
fn a_directly_called_capturing_closure_gets_a_closure_proof() {
    // g = \x. (\y. x + y) 5 -- `\y. x + y` captures g's own `x`, and
    // is called *directly* (a literal lambda in function position),
    // exercising call_ref's new Env-prefixed signature and
    // build_env_expr in the direct-call branch of denote_closure.
    let mut s = TermStore::new();
    let y = s.var(0);
    let x = s.var(1);
    let sum = s.prim(PrimOp::Add, x, y);
    let closure = s.abs(sum);
    let five = s.lit(5);
    let called = s.app(closure, five);
    let g = s.abs(called);

    let proof = prove_closure_expr(&s, g).expect("a directly called capturing closure should get a proof now");
    assert_eq!(proof.arity, 1);
    kernel::check_in(
        &proof.globals,
        &Ctx::new(),
        &proof.proof,
        &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
    )
    .expect("the recorded proof should independently re-typecheck");
}

#[test]
fn a_capture_of_a_closure_typed_value_gets_a_closure_proof() {
    // g = \cb. cb(1) + (\h. h 5) (\y. cb) -- `cb(1)` makes g's own
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
    let cb1 = s.var(0);
    let one = s.lit(1);
    let call_cb = s.app(cb1, one);

    let cb_captured = s.var(1); // \y. cb -- ignores y, returns the captured cb
    let closure = s.abs(cb_captured);

    let h = s.var(0);
    let five = s.lit(5);
    let call_h = s.app(h, five);
    let inn = s.abs(call_h);

    let applied = s.app(inn, closure);
    let body = s.prim(PrimOp::Add, call_cb, applied);
    let g = s.abs(body);

    let proof =
        prove_closure_expr(&s, g).expect("a capture of a closure-typed value should get a closure proof");
    assert_eq!(proof.arity, 1);
    kernel::check_in(
        &proof.globals,
        &Ctx::new(),
        &proof.proof,
        &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
    )
    .expect("the recorded proof should independently re-typecheck");

    assert!(compile::try_compile(&s, g).is_some());
}

#[test]
fn a_closure_created_in_a_self_call_argument_capturing_a_closure_typed_loop_parameter_gets_a_universal_proof() {
    // rec f n g x = if n <= 0 then x else f(n-1, g, g x + (\y. g y + 1) x)
    // -- same closure-typed loop-carried parameter as `iterate`, but
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
    // Exercises `denote_closure_typed`'s own value-leaf registration
    // with a `Clo`-typed capture, inside `build_universal`'s full
    // induction pipeline (not just the non-recursive `prove_closure_expr`
    // fragment `a_capture_of_a_closure_typed_value_gets_a_closure_proof`
    // above checks).
    let mut s = TermStore::new();
    let x = s.var(0);
    let g = s.var(1);
    let n = s.var(2);
    let f = s.var(3);

    let gx = s.app(g, x);

    let y = s.var(0);
    let g_captured = s.var(2); // g, shifted by the wrapper's own y binder
    let gy = s.app(g_captured, y);
    let one = s.lit(1);
    let gy_plus_1 = s.prim(PrimOp::Add, gy, one);
    let wrapper = s.abs(gy_plus_1);
    let wrapper_call = s.app(wrapper, x);

    let new_x = s.prim(PrimOp::Add, gx, wrapper_call);

    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Le, n, zero);
    let one2 = s.lit(1);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one2);
    let f_n1_g = s.app2(f, n_minus_1, g);
    let rec_call = s.app(f_n1_g, new_x);
    let body = s.if_(cond, x, rec_call);
    let g_binder = s.abs(body);
    let n_binder = s.abs(g_binder);
    let abs = s.abs(n_binder);
    let it = s.rec(abs);

    let proof = prove_tail_recursive_universal(&s, it)
        .expect("a closure created in a self-call argument capturing a closure-typed loop parameter should get a universal proof");
    assert_eq!(proof.arity, 3);
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.theorem_proof, &proof.theorem_ty)
        .expect("the recorded theorem should independently re-typecheck");

    // inc = \y. y + 1, baked in as the initial g, run for real: each
    // iteration computes new_x = g(x) + (g(x)+1) = 2*inc(x) + 1 =
    // 2x + 3. Starting from x=0: 3, 9, 21, 45, 93 after 1..5
    // iterations (hand-derived and cross-checked against eval::apply_term
    // directly while building this test).
    let y2 = s.var(0);
    let one3 = s.lit(1);
    let inc_body = s.prim(PrimOp::Add, y2, one3);
    let inc = s.abs(inc_body);
    let n_lit = s.lit(5);
    let x0 = s.lit(0);
    let partial = s.app2(it, n_lit, inc);
    let top = s.app(partial, x0);

    assert_eq!(eval::apply_term(&s, top, &[]).unwrap(), 93);
    assert!(compile::try_compile(&s, top).is_some());
}

#[test]
fn a_whole_functions_result_being_a_closure_now_gets_a_closure_proof() {
    // \x. if x > 0 then inc else inc -- an `If` choosing between two
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
    let x = s.var(0);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Lt, zero, x);
    let i1 = inc(&mut s);
    let i2 = inc(&mut s);
    let picked = s.if_(cond, i1, i2);
    let f = s.abs(picked);

    let proof = prove_closure_expr(&s, f).expect("a Clo-typed top-level result should now get a closure proof");
    assert_eq!(proof.arity, 1);
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.proof, &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()))
        .expect("the recorded proof should independently re-typecheck");
}

#[test]
fn a_bare_closure_typed_parameter_read_gets_a_closure_proof() {
    // \f. if (f 0) then f else f -- `f`'s own arity is inferred as 1
    // only because `infer_closure_arities` needs *some* use-site call
    // to assign it one at all (see `TYPES.md` section 3.1's own
    // "Default" rule), supplied here by the condition `f 0` (its own
    // value otherwise unused); both branches then read `f` itself as
    // a bare value, exercising `Term::Var(i)`'s own `Denoted::Clo`
    // case as `prove_closure_expr`'s own top-level result -- the
    // simplest possible instance of the new capability.
    let mut s = TermStore::new();
    let f = s.var(0);
    let zero = s.lit(0);
    let cond = s.app(f, zero);
    let body = s.if_(cond, f, f);
    let h = s.abs(body);

    let proof = prove_closure_expr(&s, h).expect("a bare Clo-typed parameter read should get a closure proof");
    assert_eq!(proof.arity, 1);
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.proof, &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()))
        .expect("the recorded proof should independently re-typecheck");
}

/// `\z. z - 1`.
fn dec(s: &mut TermStore) -> Hash {
    let z = s.var(0);
    let one = s.lit(1);
    let z_minus_1 = s.prim(PrimOp::Sub, z, one);
    s.abs(z_minus_1)
}

#[test]
fn a_closure_typed_ifs_own_result_used_as_a_value_gets_a_closure_proof() {
    // \w. caller(if 0 < w then inc else dec, 5) where
    // caller = \g x. g(x) -- the If's own result (Denoted::Clo, via
    // the new `ite_clo` postulate) is used as caller's *argument*
    // (matching caller's own closure-typed parameter `g`), not as a
    // directly-called combinator's implicit return -- exactly the
    // shape `ite_clo` actually needs to be reachable (see
    // calling_a_literal_lambda_whose_own_body_picks_between_two_closures_is_still_out_of_scope
    // above for the shape that still isn't).
    let mut s = TermStore::new();
    let x = s.var(0);
    let g = s.var(1);
    let call_gx = s.app(g, x);
    let caller_inner = s.abs(call_gx);
    let caller = s.abs(caller_inner);

    let w = s.var(0);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Lt, zero, w);
    let i = inc(&mut s);
    let d = dec(&mut s);
    let picked = s.if_(cond, i, d);
    let five = s.lit(5);
    let top = s.app2(caller, picked, five);
    let f = s.abs(top);

    let proof = prove_closure_expr(&s, f).expect("an If between two closures used as a value should get a closure proof");
    assert_eq!(proof.arity, 1);
    kernel::check_in(
        &proof.globals,
        &Ctx::new(),
        &proof.proof,
        &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
    )
    .expect("the recorded proof should independently re-typecheck");

    assert!(compile::try_compile(&s, f).is_some());
}

#[test]
fn an_if_mismatching_int_and_clo_branches_is_out_of_scope() {
    // \w. caller(if 0 < w then inc else 5, 5) -- one branch Clo
    // (`inc`), the other Int (`5`) -- neither ite_ref nor ite_clo
    // applies; rejected as a genuine type mismatch, not silently
    // accepted as either.
    let mut s = TermStore::new();
    let x = s.var(0);
    let g = s.var(1);
    let call_gx = s.app(g, x);
    let caller_inner = s.abs(call_gx);
    let caller = s.abs(caller_inner);

    let w = s.var(0);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Lt, zero, w);
    let i = inc(&mut s);
    let five_branch = s.lit(5);
    let picked = s.if_(cond, i, five_branch);
    let five = s.lit(5);
    let top = s.app2(caller, picked, five);
    let f = s.abs(top);

    assert!(prove_closure_expr(&s, f).is_none());
}

#[test]
fn one_closure_terms_proof_is_rejected_against_anothers_type() {
    // Adversarial: twice_inc_5's proof, checked in its own ctx, against
    // twice-alone's type -- must be rejected, not somehow typecheck.
    let mut s = TermStore::new();
    let t = twice(&mut s);
    let i = inc(&mut s);
    let five = s.lit(5);
    let applied = s.app2(t, i, five);
    let applied_proof = prove_closure_expr(&s, applied).expect("(twice inc) 5 should get a closure proof");

    let mut s2 = TermStore::new();
    let t2 = twice(&mut s2);
    let alone_proof = prove_closure_expr(&s2, t2).expect("twice alone should get a closure proof");

    assert!(
        kernel::check_in(
            &applied_proof.globals,
            &Ctx::new(),
            &applied_proof.proof,
            &kernel::id(alone_proof.result_ty.clone(), alone_proof.denotation.clone(), alone_proof.denotation.clone()),
        )
        .is_err(),
        "(twice inc) 5's proof should be rejected against twice-alone's type"
    );
}

/// Independently re-typechecks `proof` from scratch (not just
/// trusting the `.ok()?` inside `prove_closure_expr_instance`) --
/// the same discipline `tail_recursive_call_gets_a_relational_proof`
/// already applies to `prove_tail_recursive_call`'s own per-instance
/// proofs, which this function's own methodology mirrors.
fn check_instance_proof(proof: &EquivalenceProof) {
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.proof, &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()))
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
    let a = s.var(1);
    let b = s.var(0);
    let add = s.prim(PrimOp::Add, a, b);
    let inner = s.abs(add);
    let f_lit = s.abs(inner);

    let f1 = s.var(0);
    let one1 = s.lit(1);
    let two1 = s.lit(2);
    let call_2 = s.app2(f1, one1, two1);
    let f2 = s.var(0);
    let one2 = s.lit(1);
    let call_1 = s.app(f2, one2);
    let zero = s.lit(0);
    let one_c = s.lit(1);
    let cond = s.prim(PrimOp::Lt, zero, one_c);
    let inner_body = s.if_(cond, call_2, call_1);
    let f_abs = s.abs(inner_body);
    let top = s.app(f_abs, f_lit);

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
    let a = s.var(0);
    let hundred = s.lit(100);
    let a_plus_100 = s.prim(PrimOp::Add, a, hundred);
    let f_lit = s.abs(a_plus_100);

    let f1 = s.var(0);
    let one1 = s.lit(1);
    let two1 = s.lit(2);
    let call_2 = s.app2(f1, one1, two1);
    let f2 = s.var(0);
    let one2 = s.lit(1);
    let call_1 = s.app(f2, one2);
    let one_c = s.lit(1);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Lt, one_c, zero); // always false
    let inner_body = s.if_(cond, call_2, call_1);
    let f_abs = s.abs(inner_body);
    let top = s.app(f_abs, f_lit);

    assert!(prove_closure_expr(&s, top).is_none());
    let proof = prove_closure_expr_instance(&s, top, &[]).expect("should be provable per-instance");
    check_instance_proof(&proof);
}

#[test]
fn a_captured_value_reached_through_an_inlined_call_gets_a_per_instance_proof() {
    // compile.rs's
    // `a_capturing_closure_reached_through_an_inconsistently_called_parameter_agrees_with_the_interpreter`
    // -- exercises the two-frame fix directly: `f_lit`'s own capture
    // of `k` must resolve against `top`'s own (outer) frame, not
    // whatever frame is active once `f_abs`'s body is inlined.
    let mut s = TermStore::new();
    let k = s.var(2);
    let a = s.var(1);
    let b = s.var(0);
    let k_plus_a = s.prim(PrimOp::Add, k, a);
    let sum = s.prim(PrimOp::Add, k_plus_a, b);
    let inner = s.abs(sum);
    let f_lit = s.abs(inner);

    let f1 = s.var(0);
    let one1 = s.lit(1);
    let two1 = s.lit(2);
    let call_2 = s.app2(f1, one1, two1);
    let f2 = s.var(0);
    let one2 = s.lit(1);
    let call_1 = s.app(f2, one2);
    let zero = s.lit(0);
    let one_c = s.lit(1);
    let cond = s.prim(PrimOp::Lt, zero, one_c);
    let inner_body = s.if_(cond, call_2, call_1);
    let f_abs = s.abs(inner_body);
    let app = s.app(f_abs, f_lit);
    let top = s.abs(app);

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
    // `add_lit`/`sub_lit`, *before* `f_abs`'s own body is even
    // reached.
    let mut s = TermStore::new();
    let a1 = s.var(1);
    let b1 = s.var(0);
    let add_body = s.prim(PrimOp::Add, a1, b1);
    let add_inner = s.abs(add_body);
    let add_lit = s.abs(add_inner);

    let a2 = s.var(1);
    let b2 = s.var(0);
    let sub_body = s.prim(PrimOp::Sub, a2, b2);
    let sub_inner = s.abs(sub_body);
    let sub_lit = s.abs(sub_inner);

    let pick = s.var(0);
    let zero_p = s.lit(0);
    let pick_cond = s.prim(PrimOp::Lt, zero_p, pick);
    let f_value = s.if_(pick_cond, add_lit, sub_lit);

    let f1 = s.var(0);
    let one1 = s.lit(1);
    let two1 = s.lit(2);
    let call_2 = s.app2(f1, one1, two1);
    let f2 = s.var(0);
    let one2 = s.lit(1);
    let call_1 = s.app(f2, one2);
    let zero_c = s.lit(0);
    let one_c = s.lit(1);
    let cond = s.prim(PrimOp::Lt, zero_c, one_c);
    let inner_body = s.if_(cond, call_2, call_1);
    let f_abs = s.abs(inner_body);
    let app = s.app(f_abs, f_value);
    let top = s.abs(app);

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
    // (and benches/common.rs's own
    // inconsistent_arity_loop_carried_parameter_loop): `rec f n g x =
    // if 1<0 then g(x,999) else (if n<=0 then x else f(n-1,g,g(x)))`,
    // `g` baked in as `inc = \y. y+1`. The dead `g(x,999)` call site
    // makes `param_types_for(it)` classify `g` as `Inconsistent` (->
    // `None`, same as an absent one) even though every call actually
    // taken passes it exactly one argument -- exactly the gap
    // `eval_dyn_direct_call` used to decline outright for a
    // `Rec`-wrapped root (`root_is_rec` check), and that
    // `eval_dyn_tail_recursive` now closes by following the loop's
    // own tail self-calls concretely instead of trying (and failing)
    // to classify `g` statically.
    let mut s = TermStore::new();
    let x_dead = s.var(0);
    let nine_ninety_nine = s.lit(999);
    let g_dead = s.var(1);
    let dead_call = s.app2(g_dead, x_dead, nine_ninety_nine);

    let x = s.var(0);
    let g = s.var(1);
    let n = s.var(2);
    let f = s.var(3);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Le, n, zero);
    let one = s.lit(1);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one);
    let gx = s.app(g, x);
    let f_n1_g = s.app2(f, n_minus_1, g);
    let rec_call = s.app(f_n1_g, gx);
    let live_body = s.if_(cond, x, rec_call);

    let one_c = s.lit(1);
    let zero_c = s.lit(0);
    let dead_cond = s.prim(PrimOp::Lt, one_c, zero_c); // always false
    let body = s.if_(dead_cond, dead_call, live_body);

    let g_binder = s.abs(body);
    let n_binder = s.abs(g_binder);
    let abs = s.abs(n_binder);
    let it = s.rec(abs);

    let y = s.var(0);
    let one2 = s.lit(1);
    let inc_body = s.prim(PrimOp::Add, y, one2);
    let inc = s.abs(inc_body);

    assert!(param_types_for(&s, it).unwrap().contains(&None));
    assert!(prove_closure_expr(&s, it).is_none(), "it itself has no fixed arity to prove universally over g's own slot");

    for n_val in [0i64, 1, 10] {
        let n_lit = s.lit(n_val);
        let x0 = s.lit(0);
        let partial = s.app2(it, n_lit, inc);
        let top = s.app(partial, x0);

        assert!(prove_closure_expr(&s, top).is_none(), "n={n_val}: top's own call to it still can't be classified statically");
        let proof = prove_closure_expr_instance(&s, top, &[]).unwrap_or_else(|| panic!("n={n_val} should be provable per-instance"));
        check_instance_proof(&proof);
        assert_eq!(eval::apply_term(&s, top, &[]).unwrap(), n_val, "n={n_val}: sanity check against the interpreter");
    }
}

#[test]
fn a_loop_carried_call_result_that_itself_gates_termination_gets_a_per_instance_proof() {
    // rec f g x = if 1<0 then g(x,999) else (if x<=0 then x else
    // f(g, g(x))), `g` baked in as `dec = \y. y-1` -- unlike the test
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
    let x_dead = s.var(0);
    let nine_ninety_nine = s.lit(999);
    let g_dead = s.var(1);
    let dead_call = s.app2(g_dead, x_dead, nine_ninety_nine);

    let x = s.var(0);
    let g = s.var(1);
    let f = s.var(2);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Le, x, zero);
    let gx = s.app(g, x);
    let rec_call = s.app2(f, g, gx);
    let live_body = s.if_(cond, x, rec_call);

    let one_c = s.lit(1);
    let zero_c = s.lit(0);
    let dead_cond = s.prim(PrimOp::Lt, one_c, zero_c); // always false
    let body = s.if_(dead_cond, dead_call, live_body);

    let x_binder = s.abs(body);
    let g_binder = s.abs(x_binder);
    let it = s.rec(g_binder);

    let y = s.var(0);
    let one2 = s.lit(1);
    let dec_body = s.prim(PrimOp::Sub, y, one2);
    let dec = s.abs(dec_body);

    assert!(param_types_for(&s, it).unwrap().contains(&None));

    for x_val in [0i64, 1, 5] {
        let x0 = s.lit(x_val);
        let top = s.app2(it, dec, x0);

        let proof = prove_closure_expr_instance(&s, top, &[]).unwrap_or_else(|| panic!("x={x_val} should be provable per-instance"));
        check_instance_proof(&proof);
        assert_eq!(eval::apply_term(&s, top, &[]).unwrap(), 0, "x={x_val}: sanity check against the interpreter");
    }
}

#[test]
fn a_closure_argument_arriving_via_a_separate_saturated_call_that_itself_returns_a_clo_gets_a_per_instance_proof() {
    // `pick = \s. if s > 0 then add5 else sub5` (arity 1, its own
    // saturated call returns a further Clo_2 -- `combinator_return_type`
    // recognizes an `If` between two same-arity literal lambdas, same
    // as `denote_closure`'s own `ite_clo` case does structurally);
    // `f = \k. if 0<1 then k(1,2) else k(1)` (arity 1, `k` called at
    // two different arities -- `Inconsistent`, same trick as every
    // other per-instance test); `top = f(pick(3))`. `pick(3)`'s own
    // result never arrives as a bare literal lambda value the way
    // every other per-instance test's closure argument does -- it's
    // the result of a *separate* saturated call, so `eval_dyn_direct_call`
    // must inline *that* call too (previously declined outright via
    // its own `return_ty.is_some()` check) before `f`'s own
    // needs-inline logic even gets a `Clo` to work with at all.
    let mut s = TermStore::new();
    let a1 = s.var(1);
    let b1 = s.var(0);
    let add_body = s.prim(PrimOp::Add, a1, b1);
    let add_inner = s.abs(add_body);
    let add5 = s.abs(add_inner);

    let a2 = s.var(1);
    let b2 = s.var(0);
    let sub_body = s.prim(PrimOp::Sub, a2, b2);
    let sub_inner = s.abs(sub_body);
    let sub5 = s.abs(sub_inner);

    let s_var = s.var(0);
    let zero_p = s.lit(0);
    let pick_cond = s.prim(PrimOp::Lt, zero_p, s_var); // 0 < s, i.e. s > 0
    let pick_body = s.if_(pick_cond, add5, sub5);
    let pick = s.abs(pick_body);

    let k1 = s.var(0);
    let one_a = s.lit(1);
    let two_a = s.lit(2);
    let call2 = s.app2(k1, one_a, two_a);
    let k2 = s.var(0);
    let one_b = s.lit(1);
    let call1 = s.app(k2, one_b);
    let zero_c = s.lit(0);
    let one_c = s.lit(1);
    let f_cond = s.prim(PrimOp::Lt, zero_c, one_c); // 0 < 1, always true
    let f_body = s.if_(f_cond, call2, call1);
    let f = s.abs(f_body);

    assert!(param_types_for(&s, f).unwrap().contains(&None) && combinator_return_type(&s, pick).unwrap() == Some(2));

    for s_val in [3i64, -3] {
        let s_lit = s.lit(s_val);
        let pick_s = s.app(pick, s_lit);
        let top = s.app(f, pick_s);

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
    // tail position: `rec f n g x = if 1<0 then g(x,999) else (if
    // n<=0 then x else 1 + f(n-1,g,g(x)))`. `classify_step`'s own
    // `match_self_call` only recognizes a self-call that's the
    // *entire* remaining leaf, so this leaf -- `1 + f(...)` -- is a
    // `Base` case as far as `eval_dyn_tail_recursive`'s own loop is
    // concerned; the embedded self-call inside it is only reachable
    // via `eval_dyn`'s own new recognition, calling back into
    // `eval_dyn_tail_recursive` one Rust stack frame at a time.
    let mut s = TermStore::new();
    let x_dead = s.var(0);
    let nine_ninety_nine = s.lit(999);
    let g_dead = s.var(1);
    let dead_call = s.app2(g_dead, x_dead, nine_ninety_nine);

    let x = s.var(0);
    let g = s.var(1);
    let n = s.var(2);
    let f = s.var(3);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Le, n, zero);
    let one = s.lit(1);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one);
    let gx = s.app(g, x);
    let f_n1_g = s.app2(f, n_minus_1, g);
    let rec_call = s.app(f_n1_g, gx); // f(n-1, g, g(x))
    let one_addend = s.lit(1);
    let non_tail_call = s.prim(PrimOp::Add, one_addend, rec_call); // 1 + f(n-1,g,g(x))
    let live_body = s.if_(cond, x, non_tail_call);

    let one_c = s.lit(1);
    let zero_c = s.lit(0);
    let dead_cond = s.prim(PrimOp::Lt, one_c, zero_c); // always false
    let body = s.if_(dead_cond, dead_call, live_body);

    let g_binder = s.abs(body);
    let n_binder = s.abs(g_binder);
    let abs = s.abs(n_binder);
    let it = s.rec(abs);

    let y = s.var(0);
    let one2 = s.lit(1);
    let inc_body = s.prim(PrimOp::Add, y, one2);
    let inc = s.abs(inc_body);

    assert!(param_types_for(&s, it).unwrap().contains(&None));

    for n_val in [0i64, 1, 3, 10, 100] {
        let n_lit = s.lit(n_val);
        let x0 = s.lit(0);
        let partial = s.app2(it, n_lit, inc);
        let top = s.app(partial, x0);

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
    let deep_n = s.lit(1_000_000);
    let x0 = s.lit(0);
    let partial = s.app2(it, deep_n, inc);
    let top = s.app(partial, x0);
    assert!(
        prove_closure_expr_instance(&s, top, &[]).is_none(),
        "n=1_000_000 exceeds DynBudget::steps and should decline cleanly, not overflow the stack"
    );
}

#[test]
fn a_self_application_reached_only_through_a_captured_closure_is_bounded_by_the_step_budget() {
    // step = \g n. if 1<0 then g(999) else (if n<=0 then n else g(g, n-1)),
    // called as top = step(step, n0) -- a plain (non-`Rec`) Y-combinator-
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
    let g_dead = s.var(1);
    let nine_ninety_nine = s.lit(999);
    let dead_call = s.app(g_dead, nine_ninety_nine);

    let n_live = s.var(0);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Le, n_live, zero);
    let n_ret = s.var(0);
    let n_for_sub = s.var(0);
    let one = s.lit(1);
    let n_minus_1 = s.prim(PrimOp::Sub, n_for_sub, one);
    let g_fn = s.var(1);
    let g_arg = s.var(1);
    let rec_call = s.app2(g_fn, g_arg, n_minus_1); // g(g, n-1)
    let live_body = s.if_(cond, n_ret, rec_call);

    let one_c = s.lit(1);
    let zero_c = s.lit(0);
    let dead_cond = s.prim(PrimOp::Lt, one_c, zero_c); // always false
    let body = s.if_(dead_cond, dead_call, live_body);

    let inner = s.abs(body); // binds n (var 0)
    let step = s.abs(inner); // binds g (var 1) -- step = \g n. body

    assert!(
        param_types_for(&s, step).unwrap().contains(&None),
        "g's own dead call site at a different arity should make it Inconsistent"
    );

    for n_val in [0i64, 1, 3, 10, 100] {
        let n_lit = s.lit(n_val);
        let top = s.app2(step, step, n_lit);

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
    let deep_n = s.lit(1_000_000);
    let top = s.app2(step, step, deep_n);
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
    // test above) *and* captures `cap` (unlike that test's `add5`/
    // `sub5`, which are fully closed) -- exactly the combination this
    // function declines on. `mega = \cap. if 0<1 then pick_a else
    // pick_a` supplies `cap` and hands back `pick_a` as a genuine
    // `Clo` value; a `let`-bound call `g(HUGE_S)` (the usual dead-call
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
    // debug-build test thread -- `HUGE_S`'s own 300-deep, genuinely
    // non-tail `Prim` chain is bounded by no `DynBudget` counter at
    // all (unlike the self-call/inline-call paths those bound), so
    // evaluating it wastefully was a real crash risk, not just wasted
    // cycles, whenever it was about to be thrown away regardless. Since
    // `eval_dyn` runs through `kernel::grow` (`RELATED_WORK.md` 32) it
    // is only wasted cycles; the test still pins the early decline.
    let mut s = TermStore::new();
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

    // mega = \cap. if 0<1 then pick_a else pick_a
    let zero_m = s.lit(0);
    let one_m = s.lit(1);
    let cond0 = s.prim(PrimOp::Lt, zero_m, one_m);
    let mega_body = s.if_(cond0, pick_a, pick_a);
    let mega = s.abs(mega_body);

    // let g = mega(7) in if 1<0 then g(999,888) else g(HUGE_S)
    let cap_lit = s.lit(7);
    let mega_cap_call = s.app(mega, cap_lit);

    let g_dead = s.var(0);
    let nine_ninety_nine = s.lit(999);
    let eight_eighty_eight = s.lit(888);
    let dead_call = s.app2(g_dead, nine_ninety_nine, eight_eighty_eight);
    let g_live = s.var(0);
    let mut huge_s = s.lit(1);
    for _ in 0..300 {
        let one = s.lit(1);
        huge_s = s.prim(PrimOp::Add, huge_s, one);
    }
    let live_call = s.app(g_live, huge_s);
    let one_d = s.lit(1);
    let zero_d = s.lit(0);
    let dead_cond = s.prim(PrimOp::Lt, one_d, zero_d);
    let let_body = s.if_(dead_cond, dead_call, live_call);
    let let_wrapper = s.abs(let_body);

    assert!(
        param_types_for(&s, let_wrapper).unwrap().contains(&None),
        "g's own dead call site at a different arity should make it Inconsistent, forcing this whole chain to be traced via eval_dyn rather than deferred"
    );

    let top = s.app(let_wrapper, mega_cap_call);
    // Must decline (pick_a's own captures put it out of this
    // function's scope) without overflowing the stack getting there.
    assert!(prove_closure_expr_instance(&s, top, &[]).is_none());
}

#[test]
fn branching_non_tail_self_calls_carrying_an_inconsistently_classified_closure_parameter_get_a_per_instance_proof() {
    // A genuinely *branching* non-tail shape (two self-calls in the
    // same leaf, Fibonacci-style), not just one embedded call:
    // `rec f n g = if 1<0 then g(0,999) else (if n<=1 then g(n) else
    // f(n-1,g) + f(n-2,g))`, `g` baked in as `inc = \y. y+1`. Each
    // occurrence of `f(..)` is just another embedded self-call as far
    // as `eval_dyn`'s own recognition is concerned -- this test
    // exists specifically to confirm that claim (from `eval_dyn`'s
    // own doc comment) holds for a real branching trace, not just a
    // single non-tail one.
    // Convention (matching every other per-instance test in this
    // module): the innermost binder is `Var(0)`, bound by whatever's
    // applied *last* -- `it.app2(n_lit, inc)` applies `n_lit` first,
    // `inc` last, so `g = Var(0)` (last-applied, innermost) and
    // `n = Var(1)` (first-applied, outermost); `f` (the self-
    // reference) sits at `Var(arity) = Var(2)`.
    let mut s = TermStore::new();
    let g_dead = s.var(0);
    let zero_dead = s.lit(0);
    let nine_ninety_nine = s.lit(999);
    let dead_call = s.app2(g_dead, zero_dead, nine_ninety_nine);

    let g_base = s.var(0);
    let n_base = s.var(1);
    let base_call = s.app(g_base, n_base); // g(n)

    let g1 = s.var(0);
    let n1 = s.var(1);
    let f1 = s.var(2);
    let one1 = s.lit(1);
    let n_minus_1 = s.prim(PrimOp::Sub, n1, one1);
    let call_n1 = s.app2(f1, n_minus_1, g1); // f(n-1, g)

    let g2 = s.var(0);
    let n2 = s.var(1);
    let f2 = s.var(2);
    let two2 = s.lit(2);
    let n_minus_2 = s.prim(PrimOp::Sub, n2, two2);
    let call_n2 = s.app2(f2, n_minus_2, g2); // f(n-2, g)

    let branch_sum = s.prim(PrimOp::Add, call_n1, call_n2);

    let n_cond = s.var(1);
    let one_c2 = s.lit(1);
    let cond = s.prim(PrimOp::Le, n_cond, one_c2); // n <= 1
    let live_body = s.if_(cond, base_call, branch_sum);

    let one_c = s.lit(1);
    let zero_c = s.lit(0);
    let dead_cond = s.prim(PrimOp::Lt, one_c, zero_c); // always false
    let body = s.if_(dead_cond, dead_call, live_body);

    let g_binder = s.abs(body); // innermost -- binds g (Var(0))
    let n_binder = s.abs(g_binder); // outermost -- binds n (Var(1))
    let it = s.rec(n_binder);

    let y = s.var(0);
    let one2 = s.lit(1);
    let inc_body = s.prim(PrimOp::Add, y, one2);
    let inc = s.abs(inc_body);

    assert!(param_types_for(&s, it).unwrap().contains(&None));

    for n_val in [0i64, 1, 2, 3, 4] {
        let n_lit = s.lit(n_val);
        let top = s.app2(it, n_lit, inc);

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
