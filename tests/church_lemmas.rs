// First universal lemmas over Church Bools, on the unchanged kernel: a symbolic bit `a` with a
// `GoodBool` witness (its own induction principle) gives `x + 0 = x`'s per-bit facts.
use tatic::kernel::*;

fn bool0() -> Expr {
    pi(sort(0), arrow(var(0), arrow(var(0), var(0))))
}
fn t() -> Expr {
    lam(sort(0), lam(var(0), lam(var(1), var(1))))
}
fn f() -> Expr {
    lam(sort(0), lam(var(0), lam(var(1), var(0))))
}
fn bool2(body: Expr) -> Expr {
    lam(bool0(), lam(bool0(), lam(sort(0), lam(var(0), lam(var(1), body)))))
}
fn and(a: Expr, b: Expr) -> Expr {
    app2(bool2(app3(var(4), var(2), app3(var(3), var(2), var(1), var(0)), var(0))), a, b)
}
fn or(a: Expr, b: Expr) -> Expr {
    app2(bool2(app3(var(4), var(2), var(1), app3(var(3), var(2), var(1), var(0)))), a, b)
}
fn xor(a: Expr, b: Expr) -> Expr {
    app2(bool2(app3(var(4), var(2), app3(var(3), var(2), var(0), var(1)), app3(var(3), var(2), var(1), var(0)))), a, b)
}

/// GoodBool a := Pi P:(Bool0 -> Sort1). (Sort1, not Sort0: `Id` over Bool0 lives in Sort1.) P true -> P false -> P a   (a closed or given as var(0) in ctx [a])
fn good_bool_body() -> Expr {
    // ctx [a]: P = var0 after binding; result P a: ctx [a,P,h1,h2] -> P=var2, a=var3
    pi(arrow(bool0(), sort(1)), pi(app(var(0), t()), pi(app(var(1), f()), app(var(2), var(3)))))
}
fn good_bool() -> Expr {
    lam(bool0(), good_bool_body())
}

/// `\a:Bool0. \g:GoodBool a. g (\b. Id(Bool0, lhs(b), rhs(b))) (refl t-case) (refl f-case)`
/// The motive body is given at ctx [a,g,b]: `b` is var(0).
fn lemma(motive_body: Expr, at_true: Expr, at_false: Expr) -> (Expr, Expr) {
    let motive = lam(bool0(), motive_body.clone());
    // ctx [a, g]: g = var0
    let proof = lam(bool0(), lam(app(good_bool(), var(0)), app3(var(0), motive, at_true, at_false)));
    // type: Pi a. GoodBool a -> (motive a); motive a at ctx [a,g]: shift a
    // `arrow` shifts its codomain, so the statement is written at ctx [a]: `a` is var(0).
    let ty = pi(bool0(), arrow(app(good_bool(), var(0)), motive_body));
    (proof, ty)
}
#[test]
fn per_bit_facts_for_add_zero_hold_for_a_symbolic_good_bit() {
    // sum bit: xor(xor(a, false), false) = a
    let (p1, ty1) = lemma(
        id(bool0(), xor(xor(var(0), f()), f()), var(0)),
        refl(t()),
        refl(f()),
    );
    match check(&Ctx::new(), &p1, &ty1) {
        Ok(()) => {}
        Err(m) => panic!("sum-bit lemma: {}", m.chars().take(300).collect::<String>()),
    }
    // carry out with b = 0: or(and(a, false), and(false, xor(a, false))) = false
    let carry = or(and(var(0), f()), and(f(), xor(var(0), f())));
    let (p2, ty2) = lemma(id(bool0(), carry, f()), refl(f()), refl(f()));
    match check(&Ctx::new(), &p2, &ty2) {
        Ok(()) => {}
        Err(m) => panic!("carry lemma: {}", m.chars().take(300).collect::<String>()),
    }
    // A false statement must be rejected: xor(a, false) = false is not provable for a = true.
    let (p3, ty3) = lemma(id(bool0(), xor(var(0), f()), f()), refl(f()), refl(f()));
    assert!(check(&Ctx::new(), &p3, &ty3).is_err(), "xor(a,false) = false must not check");
}
