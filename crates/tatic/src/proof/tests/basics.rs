use super::*;

#[test]
fn every_arith_postulates_starts_from_one_checked_prelude() {
    // `push` type-checks each entry (docs/related-work/ §69), so building the
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
/// caches see one subterm, not two copies (`docs/related-work/` §48).
#[test]
fn a_shared_subterm_is_denoted_once() {
    // Hand-built: an open body (`x` free), with one `Int` postulate for `x`.
    let mut s = TermStore::new();
    let x = s.var(0);
    let a = s.prim(PrimOp::Mul, x, x);
    let body = s.prim(PrimOp::Add, a, a);
    let mut arith = ArithPostulates::new();
    let int = arith.int_ty();
    let pos = arith.p.push(int);
    let params = vec![arith.p.get(pos)];
    let d = denote(&s, body, &arith, &params).unwrap();
    // `d` is `App(App(+, da), da')`; `da`, `da'` are `App(App(*, x), x)`.
    let kernel::Node::App(plus_da, da2) = d.node() else { panic!() };
    let kernel::Node::App(_, da1) = plus_da.node() else { panic!() };
    let (kernel::Node::App(f1, _), kernel::Node::App(f2, _)) = (da1.node(), da2.node()) else { panic!() };
    assert!(kernel::node_key(&f1) == kernel::node_key(&f2), "the two operands were denoted separately");
}

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
    // in where a Clo2 is expected -- the soundness gain `docs/types.md`
    // section 6.2/7 documents survives this representation change.
    assert!(
        arith.p.check(&h, &clo2_ty).is_err(),
        "a Clo3-shaped value must still be rejected where a Clo2 is expected"
    );
}
