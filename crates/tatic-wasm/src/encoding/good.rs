use super::*;

// ---- Universal lemma over a symbolic n-bit tuple: `add x zero = x` for `x` with a `GoodBv` witness.

/// GoodBool a := Pi P:(Bool -> Sort1). P true -> P false -> P a   (ctx [a])
pub fn good_bool() -> Expr {
    constant(|| lam(bool0(), pi(arrow(bool0(), sort(1)), pi(app(var(0), t()), pi(app(var(1), f()), app(var(2), var(3)))))))
}
/// `\a g. g motive at_true at_false`, with its type; `motive_body` is written at ctx [b].
pub fn bit_lemma(motive_body: Expr, at_true: Expr, at_false: Expr) -> (Expr, Expr) {
    let motive = lam(bool0(), motive_body);
    let proof = lam(bool0(), lam(app(good_bool(), var(0)), app3(var(0), motive, at_true, at_false)));
    let ty = pi(bool0(), arrow(app(good_bool(), var(0)), motive_body));
    (proof, ty)
}
pub fn church_tuple(args: &[Expr]) -> Expr {
    let n = args.len();
    lam(sort(1), lam(karrow(n), apps(var(0), args.iter().map(|a| shift(a, 0, 2)).collect())))
}
/// The hypothesis type of `GoodBv`, placed with `P` as the innermost outer binder:
/// `Pi a_0..a_(n-1). GoodBool a_0 -> .. -> GoodBool a_(n-1) -> P (mk a_0 .. a_(n-1))`.
pub fn good_bv_step(n: usize) -> Expr {
    // at ctx [.. P a_0..a_(n-1) ga_0..ga_(n-1)]: P = var(2n), a_i = var(2n-1-i)
    let args: Vec<Expr> = (0..n).map(|i| var((2 * n - 1 - i) as u32)).collect();
    let mut body = app(var(2 * n as u32), church_tuple(&args));
    for _ in 0..n {
        body = pi(app(good_bool(), var(n as u32 - 1)), body);
    }
    for _ in 0..n {
        body = pi(bool0(), body);
    }
    body
}
/// GoodBv x := Pi P:(Bv_n -> Sort2). (step) -> P x   (ctx [x])
pub fn good_bv(n: usize) -> Expr {
    lam(bv_ty(n), pi(arrow(bv_ty(n), sort(2)), pi(good_bv_step(n), app(var(1), var(2)))))
}

/// Whether the closed `e : ty` (`Lemmas::holds` for a term over a job's lemma parameters).
pub fn holds(e: &Expr, ty: &Expr) -> Result<(), String> {
    check(&Ctx::new(), e, ty)
}
/// `holds`, panicking with `name` when it fails.
pub fn ck(name: &str, e: &Expr, ty: &Expr) {
    checked(name, holds(e, ty))
}
/// Panics with `name` and the start of the error when a check failed.
pub fn checked(name: &str, r: Result<(), String>) {
    if let Err(m) = r {
        panic!("{name}: {}", m.chars().take(400).collect::<String>());
    }
}

// ---- H3, forward direction (design doc section 87): `GoodBv x -> eq x L = true -> x = L` for a literal `L`.

/// `GoodBool` of a literal bit: `\P h1 h0. h_b`.
pub fn good_bit(b: bool) -> Expr {
    lam(arrow(bool0(), sort(1)), lam(app(var(0), t()), lam(app(var(1), f()), var(if b { 1 } else { 0 }))))
}
/// Closed `Pi a b. GoodBool a -> GoodBool b -> body(a, b)` by case analysis on both; `leaf(va, vb)` proves
/// `body(lit va, lit vb)` (it must be a closed term).
pub fn lemma2(body: &dyn Fn(Expr, Expr) -> Expr, leaf: &dyn Fn(bool, bool) -> Expr) -> (Expr, Expr) {
    // ctx [a, b, ga, gb]; eliminating `a` under a motive binder puts `b` at var 3
    let elim_b = |va: bool| app3(var(0), lam(bool0(), body(bit(va), var(0))), leaf(va, true), leaf(va, false));
    let proof_body = app3(var(1), lam(bool0(), body(var(0), var(3))), elim_b(true), elim_b(false));
    let proof = lam(bool0(), lam(bool0(), lam(app(good_bool(), var(1)), lam(app(good_bool(), var(1)), proof_body))));
    let ty = pi(bool0(), pi(bool0(), pi(app(good_bool(), var(1)), pi(app(good_bool(), var(1)), body(var(3), var(2))))));
    (proof, ty)
}
pub fn id_t(x: Expr) -> Expr {
    id(bool0(), x, t())
}
/// `\h. h` against a hypothesis `Id(Bool0, v, true)` whose `v` computes to `false`, or `refl`.
pub fn hyp_or_refl(h_ty: Expr, trivial: bool) -> Expr {
    lam(h_ty, if trivial { refl(t()) } else { var(0) })
}
/// `(proof, type)` of `Pi c y. Good c -> Good y -> Id(and c y, true) -> Id(c, true)` (`left`) or `-> Id(y, true)`.
pub fn and_peel(left: bool) -> (Expr, Expr) {
    lemma2(
        &move |c, y| arrow(id_t(and(c, y)), id_t(if left { c } else { y })),
        &move |a, b| hyp_or_refl(id_t(and(bit(a), bit(b))), if left { a } else { b }),
    )
}
/// `Pi c y. Good c -> Good y -> Good (and c y)`. Not by `lemma2`: `Good` is a Sort2 claim and the bit
/// eliminator reaches only Sort1, so this applies the witnesses to the caller's own motive `P`:
/// `fun c y gc gy P h1 h0 => gc (fun c' => P (and c' y)) (gy (fun y' => P (and true y')) h1 h0) h0`.
pub fn good_and_lemma() -> (Expr, Expr) {
    // ctx [c, y, gc, gy, P, h1, h0, c']
    let motive = lam(bool0(), app(var(3), and(var(0), var(6))));
    // `and true y` is the eta-expansion of `y`, which conversion does not identify with `y`: eliminate `y` too
    let motive_y = lam(bool0(), app(var(3), and(t(), var(0))));
    let body = app3(var(4), motive, app3(var(3), motive_y, var(1), var(0)), var(0));
    let pty = arrow(bool0(), sort(1));
    let proof = lam(bool0(), lam(bool0(), lam(app(good_bool(), var(1)), lam(app(good_bool(), var(1)),
        lam(pty, lam(app(var(0), t()), lam(app(var(1), f()), body)))))));
    let ty = pi(bool0(), pi(bool0(), pi(app(good_bool(), var(1)), pi(app(good_bool(), var(1)),
        app(good_bool(), and(var(3), var(2)))))));
    (proof, ty)
}
/// `Pi x:Bool0. Good x -> Id(xnor(x, l), true) -> Id(x, l)` for the literal bit `l`.
pub fn bit_from_xnor(l: bool) -> (Expr, Expr) {
    let xn = move |x: Expr| not_(xor(x, bit(l)));
    bit_lemma_hyp(
        move |x| arrow(id_t(xn(x)), id(bool0(), x, bit(l))),
        // x = true / x = false: equal to `l` (refl), else the hypothesis is `false = true`
        move |v| {
            let h = id_t(xn(bit(v)));
            lam(h, if v == l { refl(bit(l)) } else if v { sym(&bool0(), &f(), &t(), var(0)) } else { var(0) })
        },
    )
}
/// `Pi x. Good x -> Good (xnor(x, l))`, as `good_and_lemma`: `fun x gx P h1 h0 => gx (fun x' => P (xnor x' l)) h_(!l) h_l`.
pub fn good_xnor_lit(l: bool) -> (Expr, Expr) {
    // ctx [x, gx, P, h1, h0, x']
    let motive = lam(bool0(), app(var(3), not_(xor(var(0), bit(l)))));
    // xnor(true, l) is true iff l; xnor(false, l) is true iff !l
    let hv = |v: bool| if v == l { var(1) } else { var(0) };
    let body = app3(var(3), motive, hv(true), hv(false));
    let proof = lam(bool0(), lam(app(good_bool(), var(0)), lam(arrow(bool0(), sort(1)),
        lam(app(var(0), t()), lam(app(var(1), f()), body)))));
    let ty = pi(bool0(), arrow(app(good_bool(), var(0)), app(good_bool(), not_(xor(var(0), bit(l))))));
    (proof, ty)
}
/// `bit_lemma` with the two leaves made by `leaf(value)`; `body` builds the claim from the variable.
pub fn bit_lemma_hyp(body: impl Fn(Expr) -> Expr, leaf: impl Fn(bool) -> Expr) -> (Expr, Expr) {
    bit_lemma(body(var(0)), leaf(true), leaf(false))
}

// ---- `GoodBv` is preserved by `add` (design doc section 87): the witness `toN` needs for `add x y`.

/// `Pi c y. Good c -> Good y -> Good (op c y)` for a binary bit operation with truth table `tab`, by
/// eliminating both witnesses into the caller's own motive `P` (Good is Sort2; see `good_and_lemma`).
pub fn good2(op: &dyn Fn(Expr, Expr) -> Expr, tab: &dyn Fn(bool, bool) -> bool) -> (Expr, Expr) {
    // ctx [c, y, gc, gy, P, h1, h0]; `hv` picks the leaf for a truth value
    let hv = |v: bool| if v { var(1) } else { var(0) };
    let motive = lam(bool0(), app(var(3), op(var(0), var(6))));
    let branch = |c: bool| {
        // under the `y'` binder: P = var 3
        let m = lam(bool0(), app(var(3), op(bit(c), var(0))));
        app3(var(3), m, hv(tab(c, true)), hv(tab(c, false)))
    };
    let body = app3(var(4), motive, branch(true), branch(false));
    let proof = lam(bool0(), lam(bool0(), lam(app(good_bool(), var(1)), lam(app(good_bool(), var(1)),
        lam(arrow(bool0(), sort(1)), lam(app(var(0), t()), lam(app(var(1), f()), body)))))));
    let ty = pi(bool0(), pi(bool0(), pi(app(good_bool(), var(1)), pi(app(good_bool(), var(1)),
        app(good_bool(), op(var(3), var(2)))))));
    (proof, ty)
}

/// `(proof, type)` of `Pi x y. GoodBv x -> GoodBv y -> GoodBv (add x y)`.
pub fn good_add(n: usize) -> (Expr, Expr) {
    good_ripple(n, false)
}
/// `(proof, type)` of `Pi x y. GoodBv x -> GoodBv y -> GoodBv (sub x y)`.
pub fn good_sub(n: usize) -> (Expr, Expr) {
    good_ripple(n, true)
}
pub fn good_ripple(n: usize, sub: bool) -> (Expr, Expr) {
    let (g_and, _) = good2(&|a, b| and(a, b), &and_truth);
    let (g_or, _) = good2(&|a, b| or(a, b), &or_truth);
    let (g_xor, _) = good2(&|a, b| xor(a, b), &xor_truth);
    good_vec(n, if sub { self::sub(n) } else { add(n) }, &move |a, b, ga, gb| {
        let mut c = f();
        let mut gc = good_bit(false);
        let (mut s, mut gs) = (vec![], vec![]);
        for i in 0..n {
            let x = xor(a[i], b[i]);
            let gx = apps(g_xor, vec![a[i], b[i], ga[i], gb[i]]);
            s.push(xor(x, c));
            gs.push(apps(g_xor, vec![x, c, gx, gc]));
            // the carry's operands: (a, b, x) for add; (~a, b, ~a ^ b) for the borrow
            let (p, gp) = if sub {
                (xor(a[i], t()), apps(g_xor, vec![a[i], t(), ga[i], good_bit(true)]))
            } else {
                (a[i], ga[i])
            };
            let (y, gy) = (b[i], gb[i]);
            let (x2, gx2) = if sub { (xor(p, y), apps(g_xor, vec![p, y, gp, gy])) } else { (x, gx) };
            let ab = and(p, y);
            let g_ab = apps(g_and, vec![p, y, gp, gy]);
            let cx = and(c, x2);
            let g_cx = apps(g_and, vec![c, x2, gc, gx2]);
            let nc = or(ab, cx);
            gc = apps(g_or, vec![ab, cx, g_ab, g_cx]);
            c = nc;
        }
        (s, gs)
    })
}

/// Two bit lists: the result bits and their `GoodBool` witnesses.
pub type BitPair = (Vec<Expr>, Vec<Expr>);
/// The result bits and witnesses from both operands' bits and witnesses.
pub type Bits4<'a> = &'a dyn Fn(&[Expr], &[Expr], &[Expr], &[Expr]) -> BitPair;

/// `(proof, type)` of `Pi x y. GoodBv x -> GoodBv y -> GoodBv (vec x y)` for a binary vector operation
/// whose result bits and their `GoodBool` witnesses `bits(a, b, ga, gb)` are built from the operands'.
pub fn good_vec(n: usize, vec: Expr, bits: Bits4) -> (Expr, Expr) {
    // `GoodBv (add x y)` is a Sort3 claim, so it cannot be a motive for the witnesses (`Bv -> Sort2`):
    // take the claim's own `P` and `st` first, then eliminate `gx` and `gy` into `P (add x' y')`.
    // ctx: x, y, gx, gy, P, st, a_0.., ga_0.., b_0.., gb_0..
    let da = 6 + 2 * n;
    let db = da + 2 * n;
    let a = |i: usize| var((db - 1 - (6 + i)) as u32);
    let ga = |i: usize| var((db - 1 - (6 + n + i)) as u32);
    let b = |i: usize| var((db - 1 - (da + i)) as u32);
    let gb = |i: usize| var((db - 1 - (da + n + i)) as u32);
    let (s, gs) = bits(
        &(0..n).map(a).collect::<Vec<_>>(),
        &(0..n).map(b).collect::<Vec<_>>(),
        &(0..n).map(ga).collect::<Vec<_>>(),
        &(0..n).map(gb).collect::<Vec<_>>(),
    );
    let m = s.len(); // the result width
    let st_b = var((db - 1 - 5) as u32);
    let step_y = binders(n, apps(st_b, s.into_iter().chain(gs).collect()));
    let a_da = |i: usize| var((da - 1 - (6 + i)) as u32);
    let mka = church_tuple(&(0..n).map(|i| shift(&a_da(i), 0, 1)).collect::<Vec<_>>());
    // under the `y'` binder at depth da + 1: P = var(da - 1 - 4 + 1)
    let motive_y = lam(bv_ty(n), app(var((da - 4) as u32), app2(vec, mka, var(0))));
    let gy = var((da - 1 - 3) as u32);
    let step_x = binders(n, app2(gy, motive_y, step_y));
    // under the `x'` binder at depth 7: P = var 2, y = var 5
    let motive_x = lam(bv_ty(n), app(var(2), app2(vec, var(0), var(5))));
    let body = app2(var(3), motive_x, step_x);
    let proof = lam(bv_ty(n), lam(bv_ty(n), lam(app(good_bv(n), var(1)), lam(app(good_bv(n), var(1)),
        lam(arrow(bv_ty(m), sort(2)), lam(good_bv_step(m), body))))));
    let ty = pi(bv_ty(n), pi(bv_ty(n), arrow(app(good_bv(n), var(1)), arrow(app(good_bv(n), var(0)),
        app(good_bv(m), app2(vec, var(1), var(0)))))));
    (proof, ty)
}

/// `Pi a b. GoodBv a -> GoodBv b -> GoodBv_1 (lt_u a b)`: `good_sub`'s borrow chain, keeping only the last borrow.
pub fn good_lt(n: usize) -> (Expr, Expr) {
    let (g_and, _) = good2(&|a, b| and(a, b), &and_truth);
    let (g_or, _) = good2(&|a, b| or(a, b), &or_truth);
    let (g_xor, _) = good2(&|a, b| xor(a, b), &xor_truth);
    good_vec(n, lt_u(n), &move |a, b, ga, gb| {
        let (mut c, mut gc) = (f(), good_bit(false));
        for i in 0..n {
            let p = xor(a[i], t());
            let gp = apps(g_xor, vec![a[i], t(), ga[i], good_bit(true)]);
            let x2 = xor(p, b[i]);
            let gx2 = apps(g_xor, vec![p, b[i], gp, gb[i]]);
            let (ab, g_ab) = (and(p, b[i]), apps(g_and, vec![p, b[i], gp, gb[i]]));
            let (cx, g_cx) = (and(c, x2), apps(g_and, vec![c, x2, gc, gx2]));
            gc = apps(g_or, vec![ab, cx, g_ab, g_cx]);
            c = or(ab, cx);
        }
        (vec![c], vec![gc])
    })
}

// ---- Case splits at Sort0 (docs/tier-cycle/, "An invariant across an `if`"). `GoodBool`'s motive is in Sort1 and
// the kernel has no cumulativity, so a claim in Sort0 (an invariant over Sort0 answers) cannot split a bit through it;
// `GoodBool0`, a Sort1 type, can, and `GoodBool` eliminates into it.

/// GoodBool0 a := Pi P:(Bool0 -> Sort0). P true -> P false -> P a   (ctx [a])
pub fn good_bool0() -> Expr {
    lam(bool0(), pi(arrow(bool0(), sort(0)), pi(app(var(0), t()), pi(app(var(1), f()), app(var(2), var(3))))))
}
fn good0_bit(b: bool) -> Expr {
    lam(arrow(bool0(), sort(0)), lam(app(var(0), t()), lam(app(var(1), f()), var(if b { 1 } else { 0 }))))
}
/// `Pi a. GoodBool a -> GoodBool0 a`: eliminate at the motive `\b. GoodBool0 b`.
pub fn lower_bit() -> (Expr, Expr) {
    let motive = lam(bool0(), app(good_bool0(), var(0)));
    let p = lam(bool0(), lam(app(good_bool(), var(0)), app3(var(0), motive, good0_bit(true), good0_bit(false))));
    (p, pi(bool0(), arrow(app(good_bool(), var(0)), app(good_bool0(), var(0)))))
}
/// `good_bv_step` over `GoodBool0` witnesses.
fn good_bv0_step(n: usize) -> Expr {
    let args: Vec<Expr> = (0..n).map(|i| var((2 * n - 1 - i) as u32)).collect();
    let mut body = app(var(2 * n as u32), church_tuple(&args));
    for _ in 0..n {
        body = pi(app(good_bool0(), var(n as u32 - 1)), body);
    }
    for _ in 0..n {
        body = pi(bool0(), body);
    }
    body
}
/// GoodBv0 x := Pi P:(Bv_n -> Sort0). (step over GoodBool0) -> P x, a Sort2 type, so a legal motive for `GoodBv`.
pub fn good_bv0(n: usize) -> Expr {
    lam(bv_ty(n), pi(arrow(bv_ty(n), sort(0)), pi(good_bv0_step(n), app(var(1), var(2)))))
}
/// `Pi x. GoodBv x -> GoodBv0 x`, shaped as `lift_good`, lowering each bit's witness.
pub fn lower_bv(n: usize) -> (Expr, Expr) {
    lower_bv_bits(n, true)
}
/// `lower_bv`; with `lower` false the bits' witnesses pass unlowered, which must not check.
pub fn lower_bv_bits(n: usize, lower: bool) -> (Expr, Expr) {
    let (lb, _) = lower_bit();
    // ctx [x, g, a_0.., ga_0.., P, s]: a_i = var(2n+1-i), ga_i = var(n+1-i)
    let a = |i: usize| var((2 * n + 1 - i) as u32);
    let ga = |i: usize| var((n + 1 - i) as u32);
    let args = (0..n).map(a).chain((0..n).map(|i| if lower { app2(lb, a(i), ga(i)) } else { ga(i) })).collect();
    let mut step = lam(arrow(bv_ty(n), sort(0)), lam(good_bv0_step(n), apps(var(0), args)));
    for _ in 0..n {
        step = lam(app(good_bool(), var(n as u32 - 1)), step);
    }
    for _ in 0..n {
        step = lam(bool0(), step);
    }
    let p = lam(bv_ty(n), lam(app(good_bv(n), var(0)), app2(var(0), good_bv0(n), step)));
    (p, pi(bv_ty(n), arrow(app(good_bv(n), var(0)), app(good_bv0(n), var(0)))))
}

