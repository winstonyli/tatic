// Church-encoded Bool/Nat plus a "Good" subtype (induction witness), built on the public
// kernel API only: no kernel change. Shows beta-computation is definitional and that
// the dependent recursor's computation rule holds by `def_eq`. See
// docs/superpowers/specs/2026-09-30-bitvector-interface-design.md, section 12.
use tatic::kernel::*;

fn report(_name: &str, _ok: &str) {}

fn tc(name: &str, e: &Expr) {
    match typecheck(e) {
        Ok(_) => report(name, "typechecks"),
        Err(m) => panic!("{name}: {}", m.chars().take(300).collect::<String>()),
    }
}

fn ck(name: &str, e: &Expr, ty: &Expr) {
    match check(&Ctx::new(), e, ty) {
        Ok(()) => report(name, "checks"),
        Err(m) => panic!("{name}: {}", m.chars().take(300).collect::<String>()),
    }
}

#[test]
fn church_bool_nat_and_good_subtype_compute_by_conv() {
    // ---- Church Bool at Sort0: Pi C:Sort0. C -> C -> C
    let bool0 = pi(sort(0), arrow(var(0), arrow(var(0), var(0))));
    let t0 = lam(sort(0), lam(var(0), lam(var(1), var(1))));
    let f0 = lam(sort(0), lam(var(0), lam(var(1), var(0))));
    // and a b = \C t f. a C (b C t f) f   ctx [a,b,C,t,f]: f=0 t=1 C=2 b=3 a=4
    let and = lam(bool0.clone(), lam(bool0.clone(), lam(sort(0), lam(var(0), lam(var(1),
        app3(var(4), var(2), app3(var(3), var(2), var(1), var(0)), var(0)))))));
    tc("bool0", &bool0);
    ck("true0 : bool0", &t0, &bool0);
    tc("and", &and);
    assert!(def_eq(&app2(and.clone(), t0.clone(), f0.clone()), &f0), "and true false == false");
    assert!(def_eq(&app2(and.clone(), t0.clone(), t0.clone()), &t0), "and true true == true");
    assert!(!def_eq(&app2(and.clone(), t0.clone(), f0.clone()), &t0), "and true false == true (must be false)");

    // ---- Church Nat at Sort0: Pi C:Sort0. Pi z:C. Pi s:(C->C). C
    let nat = pi(sort(0), pi(var(0), pi(arrow(var(1), var(1)), var(2))));
    let zero = lam(sort(0), lam(var(0), lam(arrow(var(1), var(1)), var(1))));
    // succ n = \C z s. s (n C z s)   ctx [n,C,z,s]: s=0 z=1 C=2 n=3
    let succ = lam(nat.clone(), lam(sort(0), lam(var(0), lam(arrow(var(1), var(1)),
        app(var(0), app3(var(3), var(2), var(1), var(0)))))));
    // add a b = \C z s. a C (b C z s) s   ctx [a,b,C,z,s]
    let add = lam(nat.clone(), lam(nat.clone(), lam(sort(0), lam(var(0), lam(arrow(var(1), var(1)),
        app3(var(4), var(2), app3(var(3), var(2), var(1), var(0)), var(0)))))));
    let num = |n: u32| {
        let mut e = zero.clone();
        for _ in 0..n {
            e = app(succ.clone(), e);
        }
        e
    };
    tc("nat", &nat);
    ck("zero : nat", &zero, &nat);
    tc("succ", &succ);
    tc("add", &add);
    assert!(def_eq(&app2(add.clone(), num(2), num(2)), &num(4)), "add 2 2 == 4");
    assert!(!def_eq(&app2(add.clone(), num(2), num(2)), &num(5)), "add 2 2 == 5 (must be false)");

    // ---- Good n := Pi P:(Nat->Sort0). P zero -> (Pi m:Nat. P m -> P (succ m)) -> P n
    let steptys = pi(nat.clone(), pi(app(var(2), var(0)), app(var(3), app(succ.clone(), var(1)))));
    let good_body = pi(arrow(nat.clone(), sort(0)), pi(app(var(0), zero.clone()), pi(steptys.clone(), app(var(2), var(3)))));
    let good = lam(nat.clone(), good_body.clone());
    tc("Good", &good);
    // good_zero = \P h0 hs. h0
    let good_zero = lam(arrow(nat.clone(), sort(0)), lam(app(var(0), zero.clone()), lam(steptys.clone(), var(1))));
    ck("good_zero : Good zero", &good_zero, &app(good.clone(), zero.clone()));
    // good_succ = \n g P h0 hs. hs n (g P h0 hs)   ctx [n,g,P,h0,hs]: hs=0 h0=1 P=2 g=3 n=4
    let good_succ = lam(nat.clone(), lam(app(good.clone(), var(0)), lam(arrow(nat.clone(), sort(0)),
        lam(app(var(0), zero.clone()), lam(steptys.clone(),
            app2(var(0), var(4), app3(var(3), var(2), var(1), var(0))))))));
    tc("good_succ", &good_succ);
    let gs_ty = pi(nat.clone(), arrow(app(good.clone(), var(0)), app(good.clone(), app(succ.clone(), var(0)))));
    ck("good_succ : Pi n. Good n -> Good (succ n)", &good_succ, &gs_ty);
    // good3 = good_succ 2 (good_succ 1 (good_succ 0 good_zero))
    let mut g = good_zero.clone();
    for k in 0..3 {
        g = app2(good_succ.clone(), num(k), g);
    }
    ck("good3 : Good 3", &g, &app(good.clone(), num(3)));
    // Dependent-recursor computation: \P h0 hs. good3 P h0 hs  ==  \P h0 hs. hs 2 (hs 1 (hs 0 h0))
    let lhs = lam(arrow(nat.clone(), sort(0)), lam(app(var(0), zero.clone()), lam(steptys.clone(),
        app3(g.clone(), var(2), var(1), var(0)))));
    let rhs = lam(arrow(nat.clone(), sort(0)), lam(app(var(0), zero.clone()), lam(steptys.clone(),
        app2(var(0), num(2), app2(var(0), num(1), app2(var(0), num(0), var(1)))))));
    assert!(def_eq(&lhs, &rhs), "good3 computes to hs 2 (hs 1 (hs 0 h0))");

    // ---- Sigma(Nat, Good) and a pair
    let nat_good = sigma(nat.clone(), good_body.clone());
    tc("Sigma Nat Good", &nat_good);
    let p0 = pair(good_body.clone(), zero.clone(), good_zero.clone());
    ck("(zero, good_zero) : Sigma", &p0, &nat_good);

    // ---- The W tag: Bool at Sort1 so its eliminator reaches Sort0
    let bool1 = pi(sort(2), arrow(var(0), arrow(var(0), var(0))));
    let t1 = lam(sort(2), lam(var(0), lam(var(1), var(1))));
    let f1 = lam(sort(2), lam(var(0), lam(var(1), var(0))));
    let unit = id(nat.clone(), zero.clone(), zero.clone());
    tc("bool1", &bool1);
    tc("unit", &unit);
    let empty = wty(unit.clone(), unit.clone());
    tc("empty = W(unit, \\_.unit)", &empty);
    // ChildTy = \b:Bool1. b Sort0 unit empty
    let child_ty = lam(bool1.clone(), app3(var(0), sort(1), unit.clone(), empty.clone()));
    tc("ChildTy", &child_ty);
    assert!(def_eq(&app(child_ty.clone(), t1.clone()), &unit), "ChildTy true1 == unit");
    assert!(def_eq(&app(child_ty.clone(), f1.clone()), &empty), "ChildTy false1 == empty");
    let nat_w = wty(bool1.clone(), app(child_ty.clone(), var(0)));
    tc("W(Bool1, ChildTy)", &nat_w);

    // ---- Pair equality: two routes to Good 1 agree definitionally (beta only)...
    let good1_a = app2(good_succ.clone(), num(0), good_zero.clone());
    let good1_b = lam(arrow(nat.clone(), sort(0)), lam(app(var(0), zero.clone()), lam(steptys.clone(),
        app2(var(0), num(0), var(1)))));
    assert!(def_eq(&good1_a, &good1_b), "canonical Good 1 proofs agree");
    let p_a = pair(good_body.clone(), num(1), good1_a.clone());
    let p_b = pair(good_body.clone(), num(1), good1_b.clone());
    assert!(def_eq(&p_a, &p_b), "pairs with agreeing proofs agree");
    // ...but a symbolic proof is not its own eta-expansion (no eta in the kernel).
    let ident = lam(nat.clone(), lam(app(good.clone(), var(0)), var(0)));
    let eta = lam(nat.clone(), lam(app(good.clone(), var(0)),
        lam(arrow(nat.clone(), sort(0)), lam(app(var(0), zero.clone()), lam(steptys.clone(),
            app3(var(3), var(2), var(1), var(0)))))));
    assert!(!def_eq(&ident, &eta), "no eta: a symbolic Good proof differs from its expansion");

    // ---- Empty -> Nat by WRec with a constant motive (empty = W(unit, \_.unit)).
    let unit = id(nat.clone(), zero.clone(), zero.clone());
    let empty = wty(unit.clone(), unit.clone());
    let motive = lam(empty.clone(), nat.clone());
    // step u f ih = ih tt   ctx [u,f,ih]: ih = var0
    let step = lam(unit.clone(), lam(arrow(unit.clone(), empty.clone()), lam(pi(unit.clone(), nat.clone()),
        app(var(0), refl(zero.clone())))));
    let elim = lam(empty.clone(), wrec(motive, unit.clone(), step, var(0)));
    ck("empty elim : empty -> nat", &elim, &arrow(empty.clone(), nat.clone()));
}
