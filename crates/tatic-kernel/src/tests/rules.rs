use super::*;

#[test]
fn sigma_pairing_typechecks_and_projects_by_refl() {
    // A postulated type A, an element a0:A, a second type B, an
    // element b0:B -- a non-dependent pair Sigma(A, \_.B), the
    // simplest instance, isolating pairing/projection from
    // dependency itself (see
    // `sigma_family_genuinely_varies_with_the_tag` below for a case
    // that needs real dependency).
    let mut p = Postulates::new();
    let a_pos = p.push(sort(0));
    let a0_pos = p.push(p.get(a_pos));
    let b_pos = p.push(sort(0));
    let b0_pos = p.push(p.get(b_pos));

    let a_ref = p.get(a_pos);
    let a0_ref = p.get(a0_pos);
    let b_ref = p.get(b_pos);
    let b0_ref = p.get(b0_pos);

    let fam = shift(&b_ref, 0, 1); // \_:A. B, written one binder deeper
    let sig_ty = sigma(a_ref, fam);
    let target = pair(fam, a0_ref, b0_ref);
    p.check(&target, &sig_ty).expect("pair(fam, a0, b0) : Sigma(A, fam)");

    // motive := \_:Sigma(A,fam). A  (constant motive)
    let motive = lam(sig_ty, shift(&a_ref, 0, 1));
    // step := \a:A. \b:B. a  -- i.e. "fst"
    let step = lam(a_ref, lam(fam, var(1)));
    let reduced = sigrec(motive, step, target);
    p.check(&reduced, &a_ref).expect("sigrec application should typecheck");
    // The same payoff `w_recursor_computes_definitionally` already
    // established for `W`: this holds by `refl` alone -- the
    // recursor genuinely *computes*, not just propositionally.
    p.check(&refl(a0_ref), &id(a_ref, reduced, a0_ref))
        .expect("sigrec(motive, step, pair(fam,a0,b0)) should reduce definitionally to a0");
}

#[test]
fn sigma_family_genuinely_varies_with_the_tag() {
    // A postulated type A and element a0:A; fam(x) := Id(A, x, a0),
    // a family that genuinely varies with the tag (not just carried
    // along unused, unlike the constant-family test above) --
    // Sigma(A,fam) is "an x together with a proof that x=a0".
    // pair(fam, a0, refl(a0)) should typecheck, needing
    // `subst_top(fam,a)`'s own substitution to correctly produce
    // `Id(A,a0,a0)` for `refl(a0)` to check against.
    let mut p = Postulates::new();
    let a_pos = p.push(sort(0));
    let a0_pos = p.push(p.get(a_pos));
    let a_ref = p.get(a_pos);
    let a0_ref = p.get(a0_pos);

    // fam := Id(A, Var(0), a0), one binder deeper than A (the tag x)
    let fam = id(shift(&a_ref, 0, 1), var(0), shift(&a0_ref, 0, 1));
    let sig_ty = sigma(a_ref, fam);
    let target = pair(fam, a0_ref, refl(a0_ref));
    p.check(&target, &sig_ty).expect("pair(fam, a0, refl(a0)) : Sigma(A, fam)");
}

#[test]
fn pair_with_a_mismatched_second_component_is_rejected() {
    let mut p = Postulates::new();
    let a_pos = p.push(sort(0));
    let a0_pos = p.push(p.get(a_pos));
    let b_pos = p.push(sort(0));

    let a0_ref = p.get(a0_pos);
    let b_ref = p.get(b_pos);
    let fam = shift(&b_ref, 0, 1); // \_:A. B
    // second component should be B-typed, not A-typed
    let bad = pair(fam, a0_ref, a0_ref);
    assert!(p.infer(&bad).is_err(), "pair's own second component must check against fam(a), not anything else");
}

/// The soundness gate `infer`'s own `WRec` case now needs (see
/// `Node::WRec`'s own doc): a term whose `children_ty` field doesn't
/// match `target`'s own real children-type family must be rejected
/// outright, not silently trusted. Without this check, `whnf_in`
/// would honestly (per its own, now-correct reduction rule) type an
/// induction-hypothesis closure at whatever *wrong* domain a
/// maliciously- or accidentally-constructed `children_ty` names --
/// letting a step function's own body get away with treating that
/// closure's argument as something it isn't.
#[test]
fn wrec_with_a_mismatched_children_ty_is_rejected() {
    let mut p = Postulates::new();
    let a_pos = p.push(sort(0)); // A : Type0
    let a0_pos = p.push(p.get(a_pos)); // a0 : A
    let bc_pos = p.push(sort(0)); // Bc : Type0
    let w_ty_pre = wty(p.get(a_pos), shift(&p.get(bc_pos), 0, 1));
    let f0_pos = p.push(arrow(p.get(bc_pos), w_ty_pre));

    let a_ref = p.get(a_pos);
    let bc_ref = p.get(bc_pos);
    let w_ty = wty(a_ref, shift(&bc_ref, 0, 1));
    let target = sup(p.get(a0_pos), p.get(f0_pos));
    let motive = lam(w_ty, shift(&w_ty, 0, 1));
    let f_ty_d1 = pi(shift(&bc_ref, 0, 1), shift(&w_ty, 0, 2));
    let ih_ty_d2 = pi(shift(&bc_ref, 0, 2), app(shift(&motive, 0, 3), app(var(1), var(0))));
    let step = lam(a_ref, lam(f_ty_d1, lam(ih_ty_d2, sup(var(2), var(1)))));

    // The real, matching children_ty (`shift(&bc_ref, 0, 1)`) is
    // exactly what `w_recursor_computes_definitionally` above uses,
    // and typechecks fine -- substituted here for a wrong one
    // (`Sort(0)`, `Bc`'s own type, one universe too high to even be
    // `def_eq` to `Bc` itself) that names the wrong children family.
    let wrong = wrec(motive, sort(0), step, target);
    assert!(
        p.infer(&wrong).is_err(),
        "a WRec term whose children_ty doesn't match target's own real children-type should be rejected, not silently trusted"
    );
}

#[test]
fn j_proves_symmetry_of_id() {
    // sym : Pi A:Type0. Pi x y:A. Id A x y -> Id A y x
    // sym = \A x y p. J(motive = \x y _. Id A y x, base = \x. refl x, x, y, p)
    //
    // Depths while building the body (A=d1,x=d2,y=d3,p=d4; at d4:
    // A=Var3, x=Var2, y=Var1, p=Var0).
    let motive = lam(
        var(3), // A, at d4 (motive's own binder x' sits at d4)
        lam(
            var(4), // A, at d5 (one more binder, y', intervened)
            lam(
                id(var(5), var(1), var(0)), // Id A x' y', at d6
                id(var(6), var(1), var(2)), // Id A y' x', at d7 (swapped)
            ),
        ),
    );
    let base = lam(var(3), refl(var(0))); // \x:A. refl x, at d4

    let sym = lam(
        sort(0),
        lam(
            var(0),
            lam(
                shift(&var(0), 0, 1),
                lam(
                    id(shift(&var(0), 0, 2), var(1), var(0)),
                    jelim(motive, base, var(2), var(1), var(0)),
                ),
            ),
        ),
    );

    let ty = typecheck(&sym).unwrap();
    let expected = pi(
        sort(0),
        pi(
            var(0),
            pi(
                shift(&var(0), 0, 1),
                arrow(
                    id(shift(&var(0), 0, 2), var(1), var(0)),
                    id(shift(&var(0), 0, 2), var(0), var(1)),
                ),
            ),
        ),
    );
    assert!(def_eq(&ty, &expected), "got {ty:?}\nexpected {expected:?}");

    // Sanity: sym A a a (refl a) reduces to refl a, for a postulated A/a.
    let mut p = Postulates::new();
    let a_pos = p.push(sort(0));
    let a0_pos = p.push(p.get(a_pos));
    let a_ty = p.get(a_pos);
    let a0 = p.get(a0_pos);
    let applied = app(
        app(app(app(sym, a_ty), a0), a0),
        refl(a0),
    );
    assert_eq!(nf(&applied), nf(&refl(a0)));
}

#[test]
fn sym_typechecks_and_flips_the_equality() {
    let mut p = Postulates::new();
    let a_ty_pos = p.push(sort(0));
    let a_pos = p.push(p.get(a_ty_pos));
    let b_pos = p.push(p.get(a_ty_pos));
    let p1_pos = p.push(id(p.get(a_ty_pos), p.get(a_pos), p.get(b_pos)));

    let a_ty = p.get(a_ty_pos);
    let a = p.get(a_pos);
    let b = p.get(b_pos);
    let p1 = p.get(p1_pos);

    let flipped = sym(&a_ty, &a, &b, p1);
    p.check(&flipped, &id(a_ty, b, a)).expect("sym(x,y,p) : Id(A, y, x)");
}

#[test]
fn transport_moves_a_value_across_a_propositional_type_equality() {
    // Postulate two Sort(0)-level types A, B, a proof p : Id(Sort0,A,B),
    // and a : A -- transport(p, a) should typecheck at B.
    let mut p = Postulates::new();
    let a_ty_pos = p.push(sort(0));
    let b_ty_pos = p.push(sort(0));
    let p_pos = p.push(id(sort(0), p.get(a_ty_pos), p.get(b_ty_pos)));
    let a_pos = p.push(p.get(a_ty_pos));

    let a_ty = p.get(a_ty_pos);
    let b_ty = p.get(b_ty_pos);
    let proof = p.get(p_pos);
    let a = p.get(a_pos);

    let moved = transport(0, a_ty, b_ty, proof, a);
    p.check(&moved, &b_ty).expect("transport(p,a) : B");
}

#[test]
fn transport_along_refl_is_the_identity() {
    // p = refl A : Id(Sort0,A,A) -- transport should reduce to `a`
    // itself definitionally (the base case of J is the identity fn).
    let mut p = Postulates::new();
    let a_ty_pos = p.push(sort(0));
    let a_pos = p.push(p.get(a_ty_pos));

    let a_ty = p.get(a_ty_pos);
    let a = p.get(a_pos);

    let moved = transport(0, a_ty, a_ty, refl(a_ty), a);
    assert_eq!(nf(&moved), nf(&a), "transport along refl should compute to the identity");
}

#[test]
fn cong1_and_trans_typecheck_and_compose() {
    // Postulate A, a, b, c and proofs p1:Id(A,a,b), p2:Id(A,b,c), plus
    // a function f:A->A, then check cong1/trans against their expected
    // types and that they chain: trans(cong1(f,a,b,p1), cong1(f,b,c,p2))
    // : Id(A, f a, f c).
    let mut p = Postulates::new();
    let a_ty_pos = p.push(sort(0));
    let a_pos = p.push(p.get(a_ty_pos));
    let b_pos = p.push(p.get(a_ty_pos));
    let c_pos = p.push(p.get(a_ty_pos));
    let p1_pos = p.push(id(p.get(a_ty_pos), p.get(a_pos), p.get(b_pos)));
    let p2_pos = p.push(id(p.get(a_ty_pos), p.get(b_pos), p.get(c_pos)));
    let f_pos = p.push(arrow(p.get(a_ty_pos), p.get(a_ty_pos)));

    let a_ty = p.get(a_ty_pos);
    let a = p.get(a_pos);
    let b = p.get(b_pos);
    let c = p.get(c_pos);
    let p1 = p.get(p1_pos);
    let p2 = p.get(p2_pos);
    let f = p.get(f_pos);

    let c1 = cong1(&a_ty, &a_ty, &f, a, b, p1);
    p.check(&c1, &id(a_ty, app(f, a), app(f, b)))
        .expect("cong1(f,a,b,p1) : Id(A, f a, f b)");

    let c2 = cong1(&a_ty, &a_ty, &f, b, c, p2);
    p.check(&c2, &id(a_ty, app(f, b), app(f, c)))
        .expect("cong1(f,b,c,p2) : Id(A, f b, f c)");

    let chained = trans_proof(&a_ty, &app(f, a), &app(f, b), &app(f, c), c1, c2);
    p.check(&chained, &id(a_ty, app(f, a), app(f, c)))
        .expect("trans(cong1(..p1), cong1(..p2)) : Id(A, f a, f c)");
}

#[test]
fn cong1_with_a_different_codomain_than_domain_typechecks() {
    // f : A -> B (B distinct from A) -- every prior caller of cong1/
    // cong_n happened to have f's codomain equal its domain, so this
    // exercises the b_ty-distinct-from-a_ty case on its own for the
    // first time. cong1(f,a,b,p) : Id(B, f a, f b), not Id(A, ..).
    let mut p = Postulates::new();
    let a_ty_pos = p.push(sort(0));
    let b_ty_pos = p.push(sort(0));
    let a_pos = p.push(p.get(a_ty_pos));
    let b_pos = p.push(p.get(a_ty_pos));
    let f_pos = p.push(arrow(p.get(a_ty_pos), p.get(b_ty_pos)));
    let p1_pos = p.push(id(p.get(a_ty_pos), p.get(a_pos), p.get(b_pos)));

    let a_ty = p.get(a_ty_pos);
    let b_ty = p.get(b_ty_pos);
    let a = p.get(a_pos);
    let b = p.get(b_pos);
    let f = p.get(f_pos);
    let p1 = p.get(p1_pos);

    let c1 = cong1(&a_ty, &b_ty, &f, a, b, p1);
    p.check(&c1, &id(b_ty, app(f, a), app(f, b))).expect("cong1(f,a,b,p1) : Id(B, f a, f b)");
}

#[test]
fn cong_n_with_a_different_codomain_than_domain_typechecks() {
    // Same distinction one level up: g : A -> A -> B.
    let mut p = Postulates::new();
    let a_ty_pos = p.push(sort(0));
    let b_ty_pos = p.push(sort(0));
    let g_pos = p.push(arrow(p.get(a_ty_pos), arrow(p.get(a_ty_pos), p.get(b_ty_pos))));
    let x0_pos = p.push(p.get(a_ty_pos));
    let y0_pos = p.push(p.get(a_ty_pos));
    let x1_pos = p.push(p.get(a_ty_pos));
    let y1_pos = p.push(p.get(a_ty_pos));
    let p0_pos = p.push(id(p.get(a_ty_pos), p.get(x0_pos), p.get(y0_pos)));
    let p1_pos = p.push(id(p.get(a_ty_pos), p.get(x1_pos), p.get(y1_pos)));

    let a_ty = p.get(a_ty_pos);
    let b_ty = p.get(b_ty_pos);
    let g = p.get(g_pos);
    let x0 = p.get(x0_pos);
    let y0 = p.get(y0_pos);
    let x1 = p.get(x1_pos);
    let y1 = p.get(y1_pos);
    let p0 = p.get(p0_pos);
    let p1 = p.get(p1_pos);

    let proof = cong_n(&a_ty, &b_ty, &g, &[x0, x1], &[y0, y1], vec![p0, p1]);
    let expected = id(b_ty, app(app(g, x0), x1), app(app(g, y0), y1));
    p.check(&proof, &expected).expect("cong_n(g,[x0,x1],[y0,y1],[p0,p1]) : Id(B, g x0 x1, g y0 y1)");
}

#[test]
fn cong_n_typechecks_for_a_binary_function() {
    // Postulate A, a binary g:A->A->A, x0,y0,x1,y1:A and proofs
    // p0:Id(A,x0,y0), p1:Id(A,x1,y1); check cong_n(g,[x0,x1],[y0,y1],[p0,p1])
    // : Id(A, g x0 x1, g y0 y1) -- the n=2 case `proof.rs`'s non-tail-
    // recursion congruence step needs (e.g. for `f(n-1) + f(n-2)`).
    let mut p = Postulates::new();
    let a_ty_pos = p.push(sort(0));
    let g_pos = p.push(arrow(p.get(a_ty_pos), arrow(p.get(a_ty_pos), p.get(a_ty_pos))));
    let x0_pos = p.push(p.get(a_ty_pos));
    let y0_pos = p.push(p.get(a_ty_pos));
    let x1_pos = p.push(p.get(a_ty_pos));
    let y1_pos = p.push(p.get(a_ty_pos));
    let p0_pos = p.push(id(p.get(a_ty_pos), p.get(x0_pos), p.get(y0_pos)));
    let p1_pos = p.push(id(p.get(a_ty_pos), p.get(x1_pos), p.get(y1_pos)));

    let a_ty = p.get(a_ty_pos);
    let g = p.get(g_pos);
    let x0 = p.get(x0_pos);
    let y0 = p.get(y0_pos);
    let x1 = p.get(x1_pos);
    let y1 = p.get(y1_pos);
    let p0 = p.get(p0_pos);
    let p1 = p.get(p1_pos);

    let proof = cong_n(&a_ty, &a_ty, &g, &[x0, x1], &[y0, y1], vec![p0, p1]);
    let expected = id(a_ty, app(app(g, x0), x1), app(app(g, y0), y1));
    p.check(&proof, &expected).expect("cong_n(g,[x0,x1],[y0,y1],[p0,p1]) : Id(A, g x0 x1, g y0 y1)");
}

#[test]
fn cong_n_with_swapped_proofs_is_rejected() {
    // Adversarial: does cong_n's own construction actually get caught
    // when misused, or does it silently produce something that
    // typechecks regardless? Same setup as
    // cong_n_typechecks_for_a_binary_function, but pass p0/p1 in the
    // WRONG order (p1, meant for position 1, supplied for position 0
    // and vice versa) -- p1 : Id(A,x1,y1) doesn't witness Id(A,x0,y0)
    // (x0/x1/y0/y1 are four *distinct* postulates, unrelated to each
    // other), so the resulting term's underlying `J` node should be
    // ill-typed, not vacuously accepted.
    let mut p = Postulates::new();
    let a_ty_pos = p.push(sort(0));
    let g_pos = p.push(arrow(p.get(a_ty_pos), arrow(p.get(a_ty_pos), p.get(a_ty_pos))));
    let x0_pos = p.push(p.get(a_ty_pos));
    let y0_pos = p.push(p.get(a_ty_pos));
    let x1_pos = p.push(p.get(a_ty_pos));
    let y1_pos = p.push(p.get(a_ty_pos));
    let p0_pos = p.push(id(p.get(a_ty_pos), p.get(x0_pos), p.get(y0_pos)));
    let p1_pos = p.push(id(p.get(a_ty_pos), p.get(x1_pos), p.get(y1_pos)));

    let a_ty = p.get(a_ty_pos);
    let g = p.get(g_pos);
    let x0 = p.get(x0_pos);
    let y0 = p.get(y0_pos);
    let x1 = p.get(x1_pos);
    let y1 = p.get(y1_pos);
    let p0 = p.get(p0_pos);
    let p1 = p.get(p1_pos);

    // Sanity: correctly-ordered proofs typecheck (mirrors the test above).
    let good = cong_n(
        &a_ty,
        &a_ty,
        &g,
        &[x0, x1],
        &[y0, y1],
        vec![p0, p1],
    );
    let expected = id(a_ty, app(app(g, x0), x1), app(app(g, y0), y1));
    p.check(&good, &expected).expect("correctly-ordered cong_n should typecheck");

    // Adversarial: swap the proof order.
    let bad = cong_n(&a_ty, &a_ty, &g, &[x0, x1], &[y0, y1], vec![p1, p0]);
    assert!(
        p.check(&bad, &expected).is_err(),
        "cong_n with mismatched (swapped) proofs should be rejected, not silently accepted"
    );
}

