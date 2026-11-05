use super::*;

#[test]
fn universes_stratify() {
    assert_eq!(typecheck(&sort(0)).unwrap(), sort(1));
    assert_eq!(typecheck(&sort(5)).unwrap(), sort(6));
}

#[test]
fn a_maximal_universe_level_is_a_clean_type_error_not_an_overflow_panic() {
    // Type_{u32::MAX} has no successor sort representable in this
    // encoding -- infer's own `i.checked_add(1)` reports that as an
    // ordinary Err, rather than panicking on the arithmetic overflow
    // `i + 1` would otherwise trigger (checked in debug builds, wrapping
    // silently to Type0 in release -- neither of which is the honest
    // "this term doesn't typecheck" answer every other rejection here
    // gives).
    assert!(typecheck(&sort(u32::MAX)).is_err());
}

#[test]
fn identity_function_typechecks() {
    // \A:Type0. \x:A. x  :  Pi A:Type0. A -> A
    let f = lam(sort(0), lam(var(0), var(0)));
    let ty = typecheck(&f).unwrap();
    let expected = pi(sort(0), arrow(var(0), var(0)));
    assert!(def_eq(&ty, &expected), "got {ty:?}");
}

#[test]
fn refl_typechecks_for_a_postulated_element() {
    let mut p = Postulates::new();
    let a_pos = p.push(sort(0)); // A : Type0
    let a0_pos = p.push(p.get(a_pos)); // a0 : A

    let a0 = p.get(a0_pos);
    let ty = p.infer(&refl(a0)).unwrap();
    assert!(def_eq(&ty, &id(p.get(a_pos), a0, a0)));
}

#[test]
fn a_const_has_its_globals_type() {
    let g = two_globals();
    let a = mk(Node::Const(1));
    assert_eq!(infer_in(&g, &Ctx::new(), &a), Ok(mk(Node::Const(0))));
    assert_eq!(check_in(&g, &Ctx::new(), &refl(a), &id(mk(Node::Const(0)), a, a)), Ok(()));
    // No shift: the same `Const` has the same type under a binder.
    assert_eq!(infer_in(&g, &Ctx::new(), &lam(sort(0), mk(Node::Const(1)))), Ok(pi(sort(0), mk(Node::Const(0)))));
}

#[test]
fn a_const_past_the_environment_is_rejected() {
    assert!(infer_in(&two_globals(), &Ctx::new(), &mk(Node::Const(2))).is_err());
    assert!(infer(&Ctx::new(), &mk(Node::Const(0))).is_err(), "no globals at all");
}

/// `Const(l)` names a global, never a binder the kernel pushed. With one
/// global, `Const(1)` under a binder would be that binder if constants
/// and binders shared one vector, and `(λx:A. Const(1)) a` would then
/// reduce to a `Const(1)` that refers to nothing.
#[test]
fn a_const_at_a_binders_position_is_rejected() {
    let mut g = Globals::new();
    g.push_back(persist(sort(0)));
    assert!(infer_in(&g, &Ctx::new(), &lam(mk(Node::Const(0)), mk(Node::Const(1)))).is_err());
    let mut ctx = Ctx::new();
    ctx.push_back(mk(Node::Const(0)));
    assert!(infer_in(&g, &ctx, &mk(Node::Const(1))).is_err(), "a caller's local isn't a global either");
}

/// A global's type must be closed: no loose `Var` (it would mean a
/// different thing at every depth) and no `Free`.
#[test]
fn a_global_whose_type_is_open_is_rejected() {
    for bad in [var(0), mk(Node::Free(0)), pi(sort(0), var(1))] {
        let mut g = Globals::new();
        g.push_back(persist(bad));
        assert!(infer_in(&g, &Ctx::new(), &mk(Node::Const(0))).is_err(), "{bad:?}");
    }
}

/// A `Free` fails the check wherever it sits, including where `infer`
/// never looks: a lambda's domain under `check` (compared by `def_eq`
/// only) and the expected type, each under a redex that reduces the
/// `Free` away. `infer_in` faces the same trap: `infer` hands an
/// `App`'s argument to `Checker::check`, so a `Free` hidden in that
/// argument's own lambda domain (or, for `WRec`, in `children_ty`)
/// reduces away under `def_eq` and is never itself inferred -- this is
/// the case the final review's counterexample found with the door
/// removed (`RELATED_WORK.md` §67).
#[test]
fn a_free_is_rejected_everywhere() {
    let g = two_globals();
    let none = Ctx::new();
    let hide = |x: Expr| app(lam(mk(Node::Free(0)), x), mk(Node::Const(1))); // reduces to x
    let unhide = |x: Expr| app(lam(mk(Node::Const(0)), x), mk(Node::Const(1)));
    assert!(infer_in(&g, &none, &mk(Node::Free(0))).is_err());
    assert!(infer_in(&g, &none, &lam(sort(0), mk(Node::Free(0)))).is_err(), "under a binder");
    assert!(infer_in(&g, &none, &pi(mk(Node::Free(0)), sort(0))).is_err(), "in a type");
    assert!(check_in(&g, &none, &mk(Node::Const(1)), &hide(mk(Node::Const(0)))).is_err(), "in the expected type");
    let lam_hidden_dom = lam(hide(mk(Node::Const(0))), mk(Node::Const(1)));
    assert!(check_in(&g, &none, &lam_hidden_dom, &pi(mk(Node::Const(0)), mk(Node::Const(0)))).is_err(), "in a checked lambda's domain");
    let mut ctx = Ctx::new();
    ctx.push_back(mk(Node::Free(0)));
    assert!(infer_in(&g, &ctx, &var(0)).is_err(), "in a context entry");

    // `infer_in`, not just `check_in`: an `App`'s argument goes to
    // `Checker::check`, whose `Lam` rule against a `Pi` compares the domain
    // by `def_eq` and never infers it. With the door removed, this
    // exact term type-checked and returned `Ok(Const(0))` -- the
    // hidden `Free` in the argument's lambda domain reduced away
    // under `def_eq` without ever being inferred.
    let arg_hidden_dom = app(
        lam(arrow(mk(Node::Const(0)), mk(Node::Const(0))), mk(Node::Const(1))),
        lam(hide(mk(Node::Const(0))), mk(Node::Const(1))),
    );
    assert!(infer_in(&g, &none, &arg_hidden_dom).is_err(), "in an argument's lambda domain");
    let arg_unhidden_dom = app(
        lam(arrow(mk(Node::Const(0)), mk(Node::Const(0))), mk(Node::Const(1))),
        lam(unhide(mk(Node::Const(0))), mk(Node::Const(1))),
    );
    assert_eq!(infer_in(&g, &none, &arg_unhidden_dom), Ok(mk(Node::Const(0))));

    // Same trap in `WRec`: `children_ty` is only compared by `def_eq`
    // against the target's own inferred children type, never inferred
    // itself. Build a well-typed `W(A,Bc)` recursor entirely from
    // globals, so `children_ty` can hide a `Free` behind a redex.
    let a_ty = mk(Node::Const(0)); // A : Type0 (g[0])
    let bc_ty = mk(Node::Const(1)); // Bc : Type0 (g[1])
    let mut gw = Globals::new();
    gw.push_back(persist(sort(0))); // 0: A : Type0
    gw.push_back(persist(sort(0))); // 1: Bc : Type0
    gw.push_back(persist(a_ty)); // 2: a0 : A
    gw.push_back(persist(arrow(bc_ty, wty(a_ty, bc_ty)))); // 3: f0 : Bc -> W(A,Bc)
    let a0 = mk(Node::Const(2));
    let f0 = mk(Node::Const(3));
    let w_ty = wty(a_ty, bc_ty);
    let motive = lam(w_ty, w_ty); // constant motive
    let f_ty = pi(bc_ty, w_ty);
    let ih_ty = pi(bc_ty, app(motive, app(var(1), var(0))));
    let step = lam(a_ty, lam(f_ty, lam(ih_ty, sup(var(2), var(1)))));
    let target = sup(a0, f0);
    let wrec_good = wrec(motive, bc_ty, step, target);
    assert_eq!(infer_in(&gw, &none, &wrec_good), Ok(app(motive, target)), "unhidden children_ty");
    let wrec_hidden_children_ty = wrec(motive, hide(bc_ty), step, target);
    assert!(infer_in(&gw, &none, &wrec_hidden_children_ty).is_err(), "a Free hidden under a redex in children_ty");

    // The same terms without the `Free` are fine, so the rejections
    // above are the `Free`'s doing.
    assert_eq!(check_in(&g, &none, &mk(Node::Const(1)), &unhide(mk(Node::Const(0)))), Ok(()));
    assert_eq!(check_in(&g, &none, &lam(unhide(mk(Node::Const(0))), mk(Node::Const(1))), &pi(mk(Node::Const(0)), mk(Node::Const(0)))), Ok(()));
}

/// `check_in` checks its claim is a type before checking the proof, as
/// Lean's `check_constant_val` and Coq's `infer_definition` do
/// (RELATED_WORK §67). Without that, a malformed claim is "proved".
#[test]
fn a_claim_that_isnt_a_type_is_rejected() {
    let g = two_globals();
    let none = Ctx::new();
    let a = mk(Node::Const(1)); // a term of type A, not a type
    assert!(check_in(&g, &none, &lam(a, var(0)), &pi(a, a)).is_err(), "Π(x:a). a");
    let ghost = app(lam(mk(Node::Const(99)), mk(Node::Const(0))), a); // reduces to A
    assert!(check_in(&g, &none, &a, &ghost).is_err(), "a claim naming a constant that doesn't exist");
    // Well-formed claims still check.
    assert_eq!(check_in(&g, &none, &lam(mk(Node::Const(0)), var(0)), &pi(mk(Node::Const(0)), mk(Node::Const(0)))), Ok(()));
    assert_eq!(check_in(&g, &none, &a, &app(lam(mk(Node::Const(0)), mk(Node::Const(0))), a)), Ok(()));
}

/// Checking a lambda against a Π infers its annotation to a `Sort`,
/// as `infer` does, rather than only comparing it with the domain:
/// here the claim is well-formed and the annotation reduces to the
/// domain, but names a constant that doesn't exist.
#[test]
fn a_checked_lambdas_annotation_must_be_a_type() {
    let g = two_globals();
    let none = Ctx::new();
    let ghost = app(lam(mk(Node::Const(99)), mk(Node::Const(0))), mk(Node::Const(1))); // reduces to A
    let claim = pi(mk(Node::Const(0)), mk(Node::Const(0)));
    assert!(check_in(&g, &none, &lam(ghost, var(0)), &claim).is_err());
    let fine = app(lam(mk(Node::Const(0)), mk(Node::Const(0))), mk(Node::Const(1)));
    assert_eq!(check_in(&g, &none, &lam(fine, var(0)), &claim), Ok(()));
}

#[test]
fn w_recursor_computes_definitionally() {
    // Postulate a base type A with a witness a0, a (tag-independent)
    // children-index type Bc, and a children function
    // f0 : Bc -> W(A, Bc). See `Postulates` docs above for why this is
    // postulated rather than derived.
    let mut p = Postulates::new();
    let a_pos = p.push(sort(0)); // A : Type0
    let a0_pos = p.push(p.get(a_pos)); // a0 : A
    let bc_pos = p.push(sort(0)); // Bc : Type0
    let w_ty_pre = wty(p.get(a_pos), shift(&p.get(bc_pos), 0, 1));
    let f0_pos = p.push(arrow(p.get(bc_pos), w_ty_pre)); // f0 : Bc -> W(A,Bc)

    // p.globals now has 4 entries; re-fetch references at this depth.
    let a_ref = p.get(a_pos);
    let bc_ref = p.get(bc_pos);
    let w_ty = wty(a_ref, shift(&bc_ref, 0, 1));
    let target = sup(p.get(a0_pos), p.get(f0_pos));
    assert!(def_eq(&p.infer(&target).unwrap(), &w_ty));

    // motive := \_ : W(A,Bc). W(A,Bc)   (constant motive)
    let motive = lam(w_ty, shift(&w_ty, 0, 1));

    // step := \a:A. \f:(Bc->W). \ih:(Pi y:Bc. motive (f y)). sup(a, f)
    // i.e. "reconstruct the node, ignoring the induction hypothesis" —
    // this makes `wrec(motive, step, _)` the identity on W, defined via
    // its own recursor rather than as a primitive.
    // Note: `pi`, not `arrow` -- `shift(&w_ty, 0, 2)` already lands the
    // codomain at the right depth (one deeper than this Pi's own
    // placement at depth1); wrapping it in `arrow` would shift it twice.
    let f_ty_d1 = pi(shift(&bc_ref, 0, 1), shift(&w_ty, 0, 2));
    let ih_ty_d2 = pi(
        shift(&bc_ref, 0, 2),
        app(shift(&motive, 0, 3), app(var(1), var(0))), // motive (f y)
    );
    let step = lam(a_ref, lam(f_ty_d1, lam(ih_ty_d2, sup(var(2), var(1)))));

    let reduced = wrec(motive, shift(&bc_ref, 0, 1), step, target);
    p.check(&reduced, &w_ty).expect("wrec application should typecheck");
    // The payoff of choosing W over an impredicative/Church encoding:
    // this holds by `refl` alone — the recursor genuinely *computes*,
    // it doesn't just make the equation provable with extra work.
    p.check(&refl(target), &id(w_ty, reduced, target))
        .expect("wrec(motive, step, sup(a,f)) should reduce definitionally to sup(a,f)");
}

#[test]
fn sup_rejects_a_children_function_whose_codomain_genuinely_depends_on_its_own_argument() {
    // `Sup(a, f)`'s own typing rule (see its doc) requires `f`'s
    // codomain to be a constant `W(A,B)`, independent of `f`'s own
    // bound argument -- otherwise `subst_top(cod, a)` is only ever
    // validated at this one concrete `a`, silently trusting every
    // other point of `f`'s domain agrees. Build a minimal witness
    // where that's structurally false: `g : D -> Type0` postulated
    // opaque (so its result genuinely varies per input, as far as the
    // kernel can tell -- no reduction could ever prove otherwise),
    // and `mk : Pi x:D. g(x)`, so `mk` itself has exactly the
    // offending shape `Pi x:D. cod` with `cod = g(x)` mentioning `x`.
    let mut p = Postulates::new();
    let a_pos = p.push(sort(0)); // A : Type0
    let a0_pos = p.push(p.get(a_pos)); // a0 : A
    let d_pos = p.push(sort(0)); // D : Type0
    let g_pos = p.push(arrow(p.get(d_pos), sort(0))); // g : D -> Type0
    let mk_ty = pi(p.get(d_pos), app(shift(&p.get(g_pos), 0, 1), var(0))); // Pi x:D. g(x)
    let mk_pos = p.push(mk_ty);

    let target = sup(p.get(a0_pos), p.get(mk_pos));
    let err = p.infer(&target).expect_err("a dependent codomain must be rejected, not silently trusted");
    assert!(
        err.contains("must not depend"),
        "expected the dependent-codomain error, got: {err}"
    );
}

#[test]
fn is_var_free_tracks_binder_depth_and_is_checked_against_normal_form_not_raw_syntax() {
    // `Sup`'s new occurs-check (above) runs `is_var_free` on `cod`'s
    // *normal form*, not its raw syntax, precisely so a codomain that
    // only syntactically mentions its own argument -- but beta-
    // reduces free of it -- is still accepted rather than wrongly
    // rejected. Exercise `is_var_free` itself directly, including
    // that specific reduces-away shape, rather than through the
    // fragile nested-W-type indexing a full `Sup` witness would need.
    assert!(is_var_free(&var(0), 0));
    assert!(!is_var_free(&var(1), 0));
    // `\_:Sort0. (outer Var(0))`, written under one more binder as
    // `Var(1)` -- does this Lam depend on the *outer* Var(0)? Yes.
    assert!(is_var_free(&lam(sort(0), var(1)), 0));
    // `\_:Sort0. Var(0)` (the lambda's *own* argument) -- does this
    // depend on something *outside* the lambda at outer-index 0? No.
    assert!(!is_var_free(&lam(sort(0), var(0)), 0));

    // `(\_:Sort0. Sort(1)) (Var 0)` mentions `Var(0)` syntactically as
    // the application's argument, but beta-reduces to plain
    // `Sort(1)`, genuinely independent of it.
    let redex = app(lam(sort(0), sort(1)), var(0));
    assert!(is_var_free(&redex, 0), "the raw syntax does mention Var(0)");
    assert!(!is_var_free(&nf(&redex), 0), "but it reduces away");
}

