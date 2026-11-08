use super::*;

// ---- Division wrapper obligations (design doc section 5): D3 and the equality test it needs.
// `div_s` is abstract: only the wrapper's guard is under test, so its result `r = div_s a b` is a
// variable with a `GoodBv` witness (a Church Bool0 cannot select between Bv values, so the
// wrapper muxes bitwise with and/or/not).

/// `\a C t f. a C f t`: one gate, not `xor a true`.
pub fn not_(x: Expr) -> Expr {
    app(constant(|| lam(bool0(), lam(sort(0), lam(var(0), lam(var(1), app3(var(3), var(2), var(0), var(1))))))), x)
}
/// `\c x y C t f. c C (x C t f) (y C t f)`: one gate, not `or (and c x) (and (not c) y)`.
pub fn mux(c: Expr, x: Expr, y: Expr) -> Expr {
    // ctx [c, x, y, C, t, f]: f=0 t=1 C=2 y=3 x=4 c=5
    let gate = || lam(bool0(), bool2(app3(var(5), var(2), app3(var(4), var(2), var(1), var(0)), app3(var(3), var(2), var(1), var(0)))));
    app3(constant(gate), c, x, y)
}
/// `\a b. a Bool0 (\a_i. b Bool0 (\b_i. and_i xnor(a_i, b_i)))`, closed, of type `Bv_n -> Bv_n -> Bool0`.
pub fn eq_bv(n: usize) -> Expr {
    // ctx [a, b, a_0.., b_0..]: a_i = var(2n-1-i), b_i = var(n-1-i)
    let mut acc = t();
    for i in 0..n {
        acc = and(acc, not_(xor(var((2 * n - 1 - i) as u32), var((n - 1 - i) as u32))));
    }
    for _ in 0..n {
        acc = lam(bool0(), acc);
    }
    let mut inner = app2(var(n as u32), bool0(), acc);
    for _ in 0..n {
        inner = lam(bool0(), inner);
    }
    lam(bv_ty(n), lam(bv_ty(n), app2(var(1), bool0(), inner)))
}
/// `wrapping_div`'s result for operands `a`, `b` given the raw quotient `r`: `MIN` when `a = MIN` and
/// `b = -1`, else `r`, bit by bit.
pub fn wrap_div(n: usize, a: Expr, b: Expr, r: Expr) -> Expr {
    let min = 1u128 << (n - 1);
    let all = if n == 128 { u128::MAX } else { (1u128 << n) - 1 };
    // the guard sits under `C k r_0..`, so `a` and `b` move past those n + 2 binders
    let cond = and(app2(eq_bv(n), shift(&a, 0, n as i32 + 2), lit(n, min)), app2(eq_bv(n), shift(&b, 0, n as i32 + 2), lit(n, all)));
    // ctx [.., C, k, r_0..]: k = var(n), r_i = var(n-1-i)
    let outs = (0..n).map(|i| mux(cond, bit((min >> i) & 1 == 1), var((n - 1 - i) as u32))).collect();
    let mut body = apps(var(n as u32), outs);
    for _ in 0..n {
        body = lam(bool0(), body);
    }
    lam(sort(1), lam(karrow(n), app2(shift(&r, 0, 2), var(1), body)))
}
/// `(proof, statement)` of `Pi r. GoodBv r -> Id(Bv_n, wrap_div(a, b, r), MIN)`; true for
/// `a = MIN, b = -1` (D3: `wrapping_div MIN (-1) = MIN`), false (and rejected) for other operands.
pub fn wrap_div_min_proof(n: usize, a: u128, b: u128) -> (Expr, Expr) {
    let min = 1u128 << (n - 1);
    let body = |r: Expr| id(bv_ty(n), wrap_div(n, lit(n, a), lit(n, b), r), lit(n, min));
    let mut step = refl(lit(n, min));
    for _ in 0..n {
        step = lam(app(good_bool(), var(n as u32 - 1)), step);
    }
    for _ in 0..n {
        step = lam(bool0(), step);
    }
    let motive = lam(bv_ty(n), body(var(0)));
    let proof = lam(bv_ty(n), lam(app(good_bv(n), var(0)), app2(var(0), motive, step)));
    let stmt = pi(bv_ty(n), arrow(app(good_bv(n), var(0)), body(var(0))));
    (proof, stmt)
}

// ---- H1 probe (design doc section 86): the numeric view `toN` on a vector with a `GoodBv` witness.
// A Church `Bool0` eliminates only into Sort0, but the Church `Nat` below lives in Sort1, so a bit
// cannot be turned into a number by applying it; the `GoodBool` eliminator (motive into Sort1) can.

/// Church Nat at Sort0: `Pi C:Sort0. C -> (C -> C) -> C`.
pub fn nat_ty() -> Expr {
    pi(sort(0), pi(var(0), pi(arrow(var(1), var(1)), var(2))))
}
pub fn nat_lit(k: u128) -> Expr {
    let mut body = var(1);
    for _ in 0..k {
        body = app(var(0), body);
    }
    lam(sort(0), lam(var(0), lam(arrow(var(1), var(1)), body)))
}
/// `\a b. \C z s. a C (b C z s) s`
pub fn nat_add() -> Expr {
    lam(nat_ty(), lam(nat_ty(), lam(sort(0), lam(var(0), lam(arrow(var(1), var(1)),
        app3(var(4), var(2), app3(var(3), var(2), var(1), var(0)), var(0)))))))
}
/// `GoodBv` with the motive in Sort1 (so it can eliminate into `Nat`): `Pi P:(Bv_n -> Sort1). step -> P x`.
pub fn good_bv1(n: usize) -> Expr {
    lam(bv_ty(n), pi(arrow(bv_ty(n), sort(1)), pi(good_bv_step(n), app(var(1), var(2)))))
}
/// `\x g. g good_bv1 (\a.. ga.. P s. s a.. ga..)`, of type `Pi x. GoodBv x -> GoodBv1 x`: the Sort2
/// witness gives the Sort1 one, by eliminating into `GoodBv1` itself (a Sort2 type).
pub fn lift_good(n: usize) -> Expr {
    // ctx [x, g, a_0.., ga_0.., P, s]: a_i = var(2n+1-i), ga_i = var(n+1-i)
    let args = (0..n).map(|i| var((2 * n + 1 - i) as u32)).chain((0..n).map(|i| var((n + 1 - i) as u32))).collect();
    let mut step = lam(arrow(bv_ty(n), sort(1)), lam(good_bv_step(n), apps(var(0), args)));
    for _ in 0..n {
        step = lam(app(good_bool(), var(n as u32 - 1)), step);
    }
    for _ in 0..n {
        step = lam(bool0(), step);
    }
    lam(bv_ty(n), lam(app(good_bv(n), var(0)), app2(var(0), good_bv1(n), step)))
}
/// `\x. \g:GoodBv x. (lift g) (\_. Nat) (\a_0.. ga_0.. . sum_i (ga_i (\_. Nat) 2^i 0))`
pub fn to_n(n: usize) -> Expr {
    // ctx [x, g, a_0.., ga_0..]: ga_i = var(n-1-i)
    let mut sum = nat_lit(0);
    for i in 0..n {
        let bit_val = app3(var((n - 1 - i) as u32), lam(bool0(), nat_ty()), nat_lit(1 << i), nat_lit(0));
        sum = app2(nat_add(), sum, bit_val);
    }
    for _ in 0..n {
        sum = lam(app(good_bool(), var(n as u32 - 1)), sum);
    }
    for _ in 0..n {
        sum = lam(bool0(), sum);
    }
    let motive = lam(bv_ty(n), nat_ty());
    let lifted = app2(lift_good(n), var(1), var(0));
    lam(bv_ty(n), lam(app(good_bv(n), var(0)), app2(lifted, motive, sum)))
}
/// Canonical `GoodBv (lit n v)`: `\P step. step bits.. (\P h1 h0. h_bit)..`
pub fn good_lit(n: usize, v: u128) -> Expr {
    let bit_good = |b: bool| lam(arrow(bool0(), sort(1)), lam(app(var(0), t()), lam(app(var(1), f()), var(if b { 1 } else { 0 }))));
    let mut args: Vec<Expr> = (0..n).map(|i| bit((v >> i) & 1 == 1)).collect();
    args.extend((0..n).map(|i| bit_good((v >> i) & 1 == 1)));
    lam(arrow(bv_ty(n), sort(2)), lam(good_bv_step(n), apps(var(0), args)))
}

/// Whether `sdiv a b` is `Some`: `not (eq b 0 or (eq a MIN and eq b -1))`, a `Bool0`. The `Option` is
/// the pair (this flag, `wrap_div a b (div_s a b)`): a `Bool0` cannot select between `Option` values
/// (design doc section 86), so the flag stands for None/Some.
pub fn sdiv_some(n: usize, a: Expr, b: Expr) -> Expr {
    let min = 1u128 << (n - 1);
    let all = if n == 128 { u128::MAX } else { (1u128 << n) - 1 };
    let overflow = and(app2(eq_bv(n), a, lit(n, min)), app2(eq_bv(n), b, lit(n, all)));
    not_(or(app2(eq_bv(n), b, lit(n, 0)), overflow))
}

/// `(proof, statement)` of `Pi x. GoodBv x -> Id(Bool0, eq_bv x L, true) -> Id(Bv_n, x, L)`, `L = lit(n, l)`.
pub fn eq_lit_sound(n: usize, l: u128, stated: u128) -> (Expr, Expr) {
    let lb = |i: usize| (l >> i) & 1 == 1;
    let (peel_l, _) = and_peel(true);
    let (peel_r, _) = and_peel(false);
    let (good_and, _) = good_and_lemma();
    let (bit_eq_t, _) = bit_from_xnor(true);
    let (bit_eq_f, _) = bit_from_xnor(false);
    let (gx_t, _) = good_xnor_lit(true);
    let (gx_f, _) = good_xnor_lit(false);
    // ctx of the step body: [x, g, a_0.., ga_0.., h]; `at(d)` places a_i / ga_i at depth d
    let a_at = |d: usize, i: usize| var((d - 1 - (2 + i)) as u32);
    let ga_at = |d: usize, i: usize| var((d - 1 - (2 + n + i)) as u32);
    let chain = |d: usize, k: usize| {
        let mut acc = t();
        for i in 0..k {
            acc = and(acc, not_(xor(a_at(d, i), bit(lb(i)))));
        }
        acc
    };
    let d = 2 + 2 * n;
    let dh = d + 1;
    // good witnesses of the chain prefixes and of each xnor, at depth dh
    let xn = |i: usize| not_(xor(a_at(dh, i), bit(lb(i))));
    let gxn = |i: usize| apps(if lb(i) { gx_t } else { gx_f }, vec![a_at(dh, i), ga_at(dh, i)]);
    let mut gc = vec![good_bit(true)];
    for i in 0..n {
        gc.push(apps(good_and, vec![chain(dh, i), xn(i), gc[i], gxn(i)]));
    }
    // peel h : Id(chain_n, true) down to Id(xnor_i, true), then to Id(a_i, l_i)
    let mut h = var(0);
    let mut ps = vec![None; n];
    for k in (1..=n).rev() {
        let args = |gcv: &Expr| vec![chain(dh, k - 1), xn(k - 1), *gcv, gxn(k - 1), h];
        let hx = apps(peel_r, args(&gc[k - 1]));
        let h_next = apps(peel_l, args(&gc[k - 1]));
        let be = if lb(k - 1) { bit_eq_t } else { bit_eq_f };
        ps[k - 1] = Some(apps(be, vec![a_at(dh, k - 1), ga_at(dh, k - 1), hx]));
        h = h_next;
    }
    let ps: Vec<Expr> = ps.into_iter().map(|p| p.unwrap()).collect();
    let xs: Vec<Expr> = (0..n).map(|i| a_at(dh, i)).collect();
    let ls: Vec<Expr> = (0..n).map(|i| bit(lb(i))).collect();
    let fbody = bits_to_bv(n);
    let concl = cong_n(&bool0(), &bv_ty(n), &fbody, &xs, &ls, ps);
    let mut step = lam(id_t(chain(d, n)), concl);
    for _ in 0..n {
        step = lam(app(good_bool(), var(n as u32 - 1)), step);
    }
    for _ in 0..n {
        step = lam(bool0(), step);
    }
    let big_l = lit(n, stated);
    let claim = |x: Expr| arrow(id_t(app2(eq_bv(n), x, lit(n, l))), id(bv_ty(n), x, big_l));
    let motive = lam(bv_ty(n), claim(var(0)));
    let proof = lam(bv_ty(n), lam(app(good_bv(n), var(0)), app2(var(0), motive, step)));
    let stmt = pi(bv_ty(n), arrow(app(good_bv(n), var(0)), claim(var(0))));
    (proof, stmt)
}

// ---- D1 (guard => None) and D2 (payload) for symbolic operands (design doc section 87).

pub fn min_all(n: usize) -> (u128, u128) {
    (1u128 << (n - 1), if n == 128 { u128::MAX } else { (1u128 << n) - 1 })
}
/// `(proof, statement)` of `Pi a b. Id(b, lit z) -> Id(sdiv_some a b, false)`: true for `z = 0`, false (and
/// rejected) otherwise.
pub fn sdiv_none_if_zero(n: usize, z: u128) -> (Expr, Expr) {
    // ctx [a, b, h]: a = var 2, b = var 1
    let ff = lam(bv_ty(n), sdiv_some(n, var(3), var(0)));
    let proof = lam(bv_ty(n), lam(bv_ty(n), lam(id(bv_ty(n), var(0), lit(n, z)),
        cong1(&bv_ty(n), &bool0(), &ff, var(1), lit(n, z), var(0)))));
    // statement at ctx [a, b]: Id(b, lit z) -> Id(flag, f)   (arrow: bodies at ctx [a, b])
    let stmt = pi(bv_ty(n), pi(bv_ty(n), arrow(id(bv_ty(n), var(0), lit(n, z)), id(bool0(), sdiv_some(n, var(1), var(0)), f()))));
    (proof, stmt)
}
/// `(proof, statement)` of `Pi a b. Id(a, MIN) -> Id(b, lit w) -> Id(sdiv_some a b, false)`; `w = -1` is the overflow case.
pub fn sdiv_none_on_overflow(n: usize, w: u128) -> (Expr, Expr) {
    let (min, all) = min_all(n);
    // F = \a' b'. flag a' b'   (closed)
    let ff = lam(bv_ty(n), lam(bv_ty(n), sdiv_some(n, var(1), var(0))));
    // ctx [a, b, ha, hb]
    let proof = lam(bv_ty(n), lam(bv_ty(n), lam(id(bv_ty(n), var(1), lit(n, min)), lam(id(bv_ty(n), var(1), lit(n, w)),
        cong_n(&bv_ty(n), &bool0(), &ff, &[var(3), var(2)], &[lit(n, min), lit(n, all)], vec![var(1), var(0)])))));
    let stmt = pi(bv_ty(n), pi(bv_ty(n), arrow(id(bv_ty(n), var(1), lit(n, min)), arrow(id(bv_ty(n), var(0), lit(n, w)),
        id(bool0(), sdiv_some(n, var(1), var(0)), f())))));
    (proof, stmt)
}
/// `(proof, statement)` of `Pi a b. Id(Bool0, guard a b, false) -> Pi r. GoodBv r -> Id(Bv, wrap_div a b r, r)`,
/// where `guard a b = eq a MIN and eq b -1`: with the guard false the wrapper returns the raw quotient `r`.
pub fn wrap_div_keeps_r(n: usize, claimed: bool) -> (Expr, Expr) {
    let (min, all) = min_all(n);
    let guard = |a: Expr, b: Expr| and(app2(eq_bv(n), a, lit(n, min)), app2(eq_bv(n), b, lit(n, all)));
    // F c = \C k. k (mux c m_0 r_0) .. with r = mk r_0..; at ctx [a, b, h, r, gr, r_0.., gr_0.., c]
    let m = |i: usize| bit((min >> i) & 1 == 1);
    let d = 5 + 2 * n; // ctx depth before the \c binder
    let r_at = |i: usize, depth: usize| var((depth - 1 - (5 + i)) as u32);
    // under \C k: depth d + 1 + 2, c = var(2), r_i = var(d+2 - 1 - (5+i) + 0)
    let outs: Vec<Expr> = (0..n).map(|i| mux(var(2), m(i), r_at(i, d + 3))).collect();
    let fbody = lam(sort(1), lam(karrow(n), apps(var(0), outs)));
    let ff = lam(bool0(), fbody);
    let g_at = |a: Expr, b: Expr| guard(a, b);
    // h : Id(guard a b, f) at ctx [a, b, h, ...]: h = var(d - 1 - 2)
    let h = var((d - 1 - 2) as u32);
    let (ga, gb) = (var((d - 1) as u32), var((d - 2) as u32));
    let guard_ab = g_at(ga, gb);
    let to_f = cong1(&bool0(), &bv_ty(n), &ff, guard_ab, f(), h);
    // With the guard false each bit is `mux f m r_i`, which computes to the eta-expansion of `r_i` (and
    // conversion has no eta), so close the gap bit by bit: `r_i = eta r_i` by cases on `GoodBool r_i`.
    let eta = |x: Expr| lam(sort(0), lam(var(0), lam(var(1), app3(shift(&x, 0, 3), var(2), var(1), var(0)))));
    let (e_lemma, _) = bit_lemma(id(bool0(), var(0), eta(var(0))), refl(t()), refl(f()));
    let gr_at = |i: usize| var((d - 1 - (5 + n + i)) as u32);
    let ps: Vec<Expr> = (0..n)
        .map(|i| sym(&bool0(), &r_at(i, d), &eta(r_at(i, d)), app2(e_lemma, r_at(i, d), gr_at(i))))
        .collect();
    let etas: Vec<Expr> = (0..n).map(|i| eta(r_at(i, d))).collect();
    let rs: Vec<Expr> = (0..n).map(|i| r_at(i, d)).collect();
    let mut tuple = apps(var(0), (0..n).map(|i| var((n + 1 - i) as u32)).collect());
    tuple = lam(sort(1), lam(karrow(n), tuple));
    for _ in 0..n {
        tuple = lam(bool0(), tuple);
    }
    let to_r = cong_n(&bool0(), &bv_ty(n), &tuple, &etas, &rs, ps);
    let f_false = app(ff, f());
    let mk_r = church_tuple(&rs);
    let step_body = trans_proof(&bv_ty(n), &app(ff, guard_ab), &f_false, &mk_r, to_f, to_r);
    let mut step = step_body;
    for _ in 0..n {
        step = lam(app(good_bool(), var(n as u32 - 1)), step);
    }
    for _ in 0..n {
        step = lam(bool0(), step);
    }
    // statement pieces at ctx [a, b, h, r]
    let target = |a: Expr, b: Expr, r: Expr| id(bv_ty(n), wrap_div(n, a, b, r), if claimed { r } else { lit(n, 0) });
    // motive at ctx [a, b, h, r, gr, r']: a = var 5, b = var 4
    let motive = lam(bv_ty(n), target(var(5), var(4), var(0)));
    let body = app2(var(0), motive, step);
    let proof = lam(bv_ty(n), lam(bv_ty(n), lam(id(bool0(), guard(var(1), var(0)), f()),
        lam(bv_ty(n), lam(app(good_bv(n), var(0)), body)))));
    // statement: Pi a b. Id(guard, f) -> Pi r. GoodBv r -> target   (arrow bodies at the outer ctx)
    let stmt = pi(bv_ty(n), pi(bv_ty(n), arrow(id(bool0(), guard(var(1), var(0)), f()),
        pi(bv_ty(n), arrow(app(good_bv(n), var(0)), target(var(2), var(1), var(0)))))));
    (proof, stmt)
}

