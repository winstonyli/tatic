// A fixed-width bit-vector as a Church-encoded n-ary tuple of Church Bools, with an
// unrolled ripple-carry `add`, on the unchanged kernel (public API only).
use std::time::Instant;
use tatic::kernel::*;

// The allocator `main.rs` ships with: the lib's own `#[global_allocator]` is
// `#[cfg(test)]`, so without this these timings ran on the system heap.
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn bool0() -> Expr {
    pi(sort(0), arrow(var(0), arrow(var(0), var(0))))
}
fn t() -> Expr {
    lam(sort(0), lam(var(0), lam(var(1), var(1))))
}
fn f() -> Expr {
    lam(sort(0), lam(var(0), lam(var(1), var(0))))
}
fn bit(b: bool) -> Expr {
    if b { t() } else { f() }
}
fn bool2(body: Expr) -> Expr {
    // \a b : Bool0. \C t f. body   ctx [a,b,C,t,f]: f=0 t=1 C=2 b=3 a=4
    lam(bool0(), lam(bool0(), lam(sort(0), lam(var(0), lam(var(1), body)))))
}
fn and_() -> Expr {
    bool2(app3(var(4), var(2), app3(var(3), var(2), var(1), var(0)), var(0)))
}
fn or_() -> Expr {
    bool2(app3(var(4), var(2), var(1), app3(var(3), var(2), var(1), var(0))))
}
fn xor_() -> Expr {
    bool2(app3(var(4), var(2), app3(var(3), var(2), var(0), var(1)), app3(var(3), var(2), var(1), var(0))))
}
fn and(a: Expr, b: Expr) -> Expr { app2(and_(), a, b) }
fn or(a: Expr, b: Expr) -> Expr { app2(or_(), a, b) }
fn xor(a: Expr, b: Expr) -> Expr { app2(xor_(), a, b) }

/// Bool0 -> ... -> Bool0 -> C (n arrows), in a context whose top variable is C.
fn karrow(n: usize) -> Expr {
    if n == 0 { var(0) } else { arrow(bool0(), karrow(n - 1)) }
}
fn bv_ty(n: usize) -> Expr {
    pi(sort(1), arrow(karrow(n), var(0)))
}
fn apps(mut f: Expr, args: Vec<Expr>) -> Expr {
    for a in args {
        f = app(f, a);
    }
    f
}
/// Literal: \C k. k b0 .. b(n-1), least significant bit first.
fn lit(n: usize, v: u128) -> Expr {
    let bits = (0..n).map(|i| bit((v >> i) & 1 == 1)).collect();
    lam(sort(1), lam(karrow(n), apps(var(0), bits)))
}
/// \a b. \C k. a C (\a0..a(n-1). b C (\b0..b(n-1). k s0 .. s(n-1)))  with ripple-carry sums.
fn add(n: usize) -> Expr {
    let d = 4 + 2 * n; // depth at the innermost body: a b C k a0.. b0..
    let v = |pos: usize| var((d - 1 - pos) as u32);
    let k = v(3);
    let ai = |i: usize| v(4 + i);
    let bi = |i: usize| v(4 + n + i);
    let mut carry = f();
    let mut sums = Vec::new();
    for i in 0..n {
        let x = xor(ai(i), bi(i));
        sums.push(xor(x.clone(), carry.clone()));
        carry = or(and(ai(i), bi(i)), and(carry, x));
    }
    let mut body = apps(k, sums);
    for _ in 0..n {
        body = lam(bool0(), body);
    }
    // at depth 4 + n (inside a's bits): b = var(n+2), C = var(n+1)
    let mut inner = app2(var(n as u32 + 2), var(n as u32 + 1), body);
    for _ in 0..n {
        inner = lam(bool0(), inner);
    }
    // at depth 4: a = var(3), C = var(1)
    let outer = app2(var(3), var(1), inner);
    lam(bv_ty(n), lam(bv_ty(n), lam(sort(1), lam(karrow(n), outer))))
}

/// Like `add`, but each carry is bound once by `(\c. rest) carry_expr`, so the body stays O(n)
/// nodes instead of O(n^2) (a carry used twice per position is otherwise copied by every beta).
fn add_shared(n: usize) -> Expr {
    add_mode(n, 0)
}
fn add_mode(n: usize, mode: u8) -> Expr {
    let d0 = 4 + 2 * n; // depth with all of a's and b's bits open
    let a_at = |j: usize, depth: usize| var((depth - 1 - (4 + j)) as u32);
    let b_at = |j: usize, depth: usize| var((depth - 1 - (4 + n + j)) as u32);
    let df = d0 + n.saturating_sub(1); // depth once c_1 .. c_(n-1) are bound
    let carry_at_final = |j: usize| if j == 0 { f() } else { var((n - 1 - j) as u32) };
    let sums = (0..n)
        .map(|i| match mode {
            1 => f(),
            2 => xor(a_at(i, df), b_at(i, df)),
            _ => xor(xor(a_at(i, df), b_at(i, df)), carry_at_final(i)),
        })
        .collect();
    let mut body = apps(var((df - 1 - 3) as u32), sums);
    for i in (0..if mode == 0 { n.saturating_sub(1) } else { 0 }).rev() {
        let depth = d0 + i; // i carries bound so far; c_i is var(0) when i >= 1
        let ci = if i == 0 { f() } else { var(0) };
        let x = xor(a_at(i, depth), b_at(i, depth));
        let e = or(and(a_at(i, depth), b_at(i, depth)), and(ci, x));
        body = app(lam(bool0(), body), e);
    }
    for _ in 0..n {
        body = lam(bool0(), body);
    }
    let mut inner = app2(var(n as u32 + 2), var(n as u32 + 1), body);
    for _ in 0..n {
        inner = lam(bool0(), inner);
    }
    let outer = app2(var(3), var(1), inner);
    lam(bv_ty(n), lam(bv_ty(n), lam(sort(1), lam(karrow(n), outer))))
}

fn is_ok(r: Result<Expr, String>) -> bool {
    match r {
        Ok(_) => true,
        Err(m) => panic!("{}", m.chars().take(300).collect::<String>()),
    }
}

fn run(n: usize) {
    {
        let ad = add(n);
        let t0 = Instant::now();
        assert!(is_ok(typecheck(&bv_ty(n))));
        let tc0 = Instant::now();
        assert!(is_ok(typecheck(&ad)), "add typechecks at n={n}");
        println!("  typecheck add: {:?}", tc0.elapsed());
        let mask = if n == 64 { u64::MAX as u128 } else { (1u128 << n) - 1 };
        let cases: [(u128, u128); 4] = [(0, 0), (1, 1), (0xFF, 1), (0x0123_4567_89AB_CDEF, 0xFEDC_BA98_7654_3210)];
        for (x, y) in cases {
            let (x, y) = (x & mask, y & mask);
            let got = app2(ad.clone(), lit(n, x), lit(n, y));
            let e0 = Instant::now();
            assert!(def_eq(&got, &lit(n, (x + y) & mask)), "add n={n} {x:#x}+{y:#x}");
            println!("  def_eq one add: {:?}", e0.elapsed());
            assert!(!def_eq(&got, &lit(n, (x + y + 1) & mask)), "must reject wrong sum n={n}");
        }
        println!("church bv n={n}: typecheck + 4 adds in {:?}", t0.elapsed());
    }
}

#[test]
fn church_bitvector_add_computes_by_conv_at_8_bits() {
    run(8);
}

/// ~0.8 s per add on a loaded machine (98% CPU); superlinear in width (8 bits: ~2 ms).
#[test]
#[ignore]
fn church_bitvector_add_computes_by_conv_at_64_bits() {
    run(64);
}

#[test]
#[ignore]
fn scaling_probe() {
    for n in [8usize, 16, 24, 32, 48] {
        let ad = add_shared(n);
        let mask = (1u128 << n) - 1;
        let (x, y) = (0x0123_4567_89AB_CDEFu128 & mask, 0xFEDC_BA98_7654_3210u128 & mask);
        let got = app2(ad.clone(), lit(n, x), lit(n, y));
        let t0 = Instant::now();
        let w = normalize(&got);
        let tn = t0.elapsed();
        let t1 = Instant::now();
        assert!(def_eq(&got, &lit(n, (x + y) & mask)));
        println!("SCALE n={n}: normalize {tn:?}, def_eq {:?}", t1.elapsed());
        let _ = w;
    }
}

#[test]
#[ignore]
fn skeleton_probe() {
    for mode in [1u8, 2] {
        for n in [16usize, 32, 64] {
            let ad = add_mode(n, mode);
            let got = app2(ad, lit(n, 0x5555), lit(n, 0x3333));
            let t0 = Instant::now();
            let _ = normalize(&got);
            println!("SKEL mode={mode} n={n}: normalize {:?}", t0.elapsed());
        }
    }
}

// ---- Universal lemma over a symbolic n-bit tuple: `add x zero = x` for `x` with a `GoodBv` witness.

/// GoodBool a := Pi P:(Bool -> Sort1). P true -> P false -> P a   (ctx [a])
fn good_bool() -> Expr {
    lam(bool0(), pi(arrow(bool0(), sort(1)), pi(app(var(0), t()), pi(app(var(1), f()), app(var(2), var(3))))))
}
/// `\a g. g motive at_true at_false`, with its type; `motive_body` is written at ctx [b].
fn bit_lemma(motive_body: Expr, at_true: Expr, at_false: Expr) -> (Expr, Expr) {
    let motive = lam(bool0(), motive_body.clone());
    let proof = lam(bool0(), lam(app(good_bool(), var(0)), app3(var(0), motive, at_true, at_false)));
    let ty = pi(bool0(), arrow(app(good_bool(), var(0)), motive_body));
    (proof, ty)
}
fn mk(args: &[Expr]) -> Expr {
    let n = args.len();
    lam(sort(1), lam(karrow(n), apps(var(0), args.iter().map(|a| shift(a, 0, 2)).collect())))
}
/// The hypothesis type of `GoodBv`, placed with `P` as the innermost outer binder:
/// `Pi a_0..a_(n-1). GoodBool a_0 -> .. -> GoodBool a_(n-1) -> P (mk a_0 .. a_(n-1))`.
fn good_bv_step(n: usize) -> Expr {
    // at ctx [.. P a_0..a_(n-1) ga_0..ga_(n-1)]: P = var(2n), a_i = var(2n-1-i)
    let args: Vec<Expr> = (0..n).map(|i| var((2 * n - 1 - i) as u32)).collect();
    let mut body = app(var(2 * n as u32), mk(&args));
    for _ in 0..n {
        body = pi(app(good_bool(), var(n as u32 - 1)), body);
    }
    for _ in 0..n {
        body = pi(bool0(), body);
    }
    body
}
/// GoodBv x := Pi P:(Bv_n -> Sort2). (step) -> P x   (ctx [x])
fn good_bv(n: usize) -> Expr {
    lam(bv_ty(n), pi(arrow(bv_ty(n), sort(2)), pi(good_bv_step(n), app(var(1), var(2)))))
}

fn ck(name: &str, e: &Expr, ty: &Expr) {
    if let Err(m) = check(&Ctx::new(), e, ty) {
        panic!("{name}: {}", m.chars().take(400).collect::<String>());
    }
}

/// `(proof, statement)` of `Pi x:Bv_n. GoodBv x -> Id(Bv_n, add x (lit rhs_lit), x)` using the
/// `add x 0 = x` proof; `rhs_lit != 0` gives a statement the proof must not check against.
fn add_zero_proof(n: usize, rhs_lit: u128) -> (Expr, Expr) {
    add_identity_proof(n, rhs_lit, false)
}

/// `left = true` proves `add zero x = x` instead (the literal is the first operand).
fn add_identity_proof(n: usize, rhs_lit: u128, left: bool) -> (Expr, Expr) {
    // `xor(a, false)` with the operands in the order `add` uses them
    let xf = move |a: Expr| if left { xor(f(), a) } else { xor(a, f()) };
    let carry = move |a: Expr, c: Expr| {
        if left { or(and(f(), a.clone()), and(c, xor(f(), a))) } else { or(and(a.clone(), f()), and(c, xor(a, f()))) }
    };
    let (p1, _) = bit_lemma(id(bool0(), xor(xf(var(0)), f()), var(0)), refl(t()), refl(f()));
    let (p2, _) = bit_lemma(id(bool0(), carry(var(0), f()), f()), refl(f()), refl(f()));

    // ctx of the step body: [x, g, a_0..a_(n-1), ga_0..ga_(n-1)], depth d = 2 + 2n
    let d = 2 + 2 * n;
    let a = |i: usize| var((d - 1 - (2 + i)) as u32);
    let ga = |i: usize| var((d - 1 - (2 + n + i)) as u32);
    // carries c_0 = false, c_(i+1) = carry(a_i, c_i), with proofs pc_i : Id(c_i, false)
    let mut c = vec![f()];
    let mut pc: Vec<Option<Expr>> = vec![None]; // None = c_0 is literally `false`
    for i in 0..n {
        let next = carry(a(i), c[i].clone());
        // carry(a_i, c_i) = carry(a_i, false) by c_i = false, then = false by the bit lemma
        let step_to_false = app2(p2.clone(), a(i), ga(i));
        let proof = match &pc[i] {
            None => step_to_false,
            Some(pci) => {
                let ai1 = shift(&a(i), 0, 1);
                let fmap = lam(bool0(), carry(ai1, var(0)));
                let rewritten = cong1(&bool0(), &bool0(), &fmap, c[i].clone(), f(), pci.clone());
                trans_proof(&bool0(), &next, &carry(a(i), f()), &f(), rewritten, step_to_false)
            }
        };
        c.push(next);
        pc.push(Some(proof));
    }
    // sum bits s_i = xor(xor(a_i, false), c_i) = a_i
    let mut s = Vec::new();
    let mut e = Vec::new();
    for i in 0..n {
        let s_i = xor(xf(a(i)), c[i].clone());
        let to_a = app2(p1.clone(), a(i), ga(i)); // xor(xf(a_i),f) = a_i
        let proof = match &pc[i] {
            None => to_a,
            Some(pci) => {
                let ai1 = shift(&a(i), 0, 1);
                let fmap = lam(bool0(), xor(xf(ai1), var(0)));
                let rewritten = cong1(&bool0(), &bool0(), &fmap, c[i].clone(), f(), pci.clone());
                trans_proof(&bool0(), &s_i, &xor(xf(a(i)), f()), &a(i), rewritten, to_a)
            }
        };
        s.push(s_i);
        e.push(proof);
    }
    let ys: Vec<Expr> = (0..n).map(|i| a(i)).collect();
    // f_n = \u_0..u_(n-1). \C k. k u_0 .. u_(n-1)   (ctx [u.., C, k]: k = var0, u_i = var(n+1-i))
    let mut fbody = apps(var(0), (0..n).map(|i| var((n + 1 - i) as u32)).collect());
    fbody = lam(sort(1), lam(karrow(n), fbody));
    for _ in 0..n {
        fbody = lam(bool0(), fbody);
    }
    let body = cong_n(&bool0(), &bv_ty(n), &fbody, &s, &ys, e);
    let mut step = body;
    for _ in 0..n {
        step = lam(app(good_bool(), var(n as u32 - 1)), step);
    }
    for _ in 0..n {
        step = lam(bool0(), step);
    }
    let rhs = lit(n, rhs_lit);
    let sum = |x: Expr, r: Expr| if left { app2(add(n), r, x) } else { app2(add(n), x, r) };
    let motive = lam(bv_ty(n), id(bv_ty(n), sum(var(0), rhs.clone()), var(0)));
    let proof = lam(bv_ty(n), lam(app(good_bv(n), var(0)), app2(var(0), motive, step)));
    let stmt = pi(bv_ty(n), arrow(app(good_bv(n), var(0)), id(bv_ty(n), sum(var(0), rhs), var(0))));
    (proof, stmt)
}

#[test]
fn add_zero_is_the_identity_on_a_symbolic_good_vector() {
    // per-bit lemma, stated against its own type
    let (p1, ty1) = bit_lemma(id(bool0(), xor(xor(var(0), f()), f()), var(0)), refl(t()), refl(f()));
    ck("sum bit", &p1, &ty1);
    // GoodBv is inhabited by canonical tuples (n = 2): good_mk = \a0 a1 ga0 ga1 P h. h a0 a1 ga0 ga1
    let n = 2;
    let good_mk = lam(bool0(), lam(bool0(), lam(app(good_bool(), var(1)), lam(app(good_bool(), var(1)),
        lam(arrow(bv_ty(n), sort(2)), lam(good_bv_step(n),
            app(app(app(app(var(0), var(5)), var(4)), var(3)), var(2))))))));
    let good_mk_ty = pi(bool0(), pi(bool0(), pi(app(good_bool(), var(1)), pi(app(good_bool(), var(1)),
        app(good_bv(n), mk(&[var(3), var(2)]))))));
    ck("good_mk", &good_mk, &good_mk_ty);

    for n in [1usize, 2, 3, 4, 8] {
        let (proof, stmt) = add_zero_proof(n, 0);
        let t0 = Instant::now();
        ck(&format!("add x 0 = x at n={n}"), &proof, &stmt);
        println!("LEMMA n={n}: add x 0 = x checked in {:?}", t0.elapsed());
        // Mutation: the same proof must not prove `add x 1 = x`.
        let (proof1, stmt1) = add_zero_proof(n, 1);
        assert!(check(&Ctx::new(), &proof1, &stmt1).is_err(), "add x 1 = x must be rejected at n={n}");

        // Left identity: add zero x = x, by the same pattern with the operands swapped.
        let (lp, lstmt) = add_identity_proof(n, 0, true);
        let t1 = Instant::now();
        ck(&format!("add 0 x = x at n={n}"), &lp, &lstmt);
        println!("LEMMA n={n}: add 0 x = x checked in {:?}", t1.elapsed());
        let (lp1, lstmt1) = add_identity_proof(n, 1, true);
        assert!(check(&Ctx::new(), &lp1, &lstmt1).is_err(), "add 1 x = x must be rejected at n={n}");
    }
}

/// Growth of the universal lemma's check time with width (machine load varies; indicative only).
#[test]
#[ignore]
fn add_zero_lemma_scaling() {
    for n in [8usize, 16, 32, 64] {
        let (proof, stmt) = add_zero_proof(n, 0);
        let t0 = Instant::now();
        ck(&format!("n={n}"), &proof, &stmt);
        println!("LEMMA-SCALE n={n}: {:?}", t0.elapsed());
    }
}

// ---- Commutativity: `add x y = add y x` for `x`, `y` with `GoodBv` witnesses.

/// Closed proof of `Pi a b c c'. GoodBool a -> GoodBool b -> Id(c, c') -> Id(F(a,b,c), F(b,a,c'))`,
/// by case analysis on `a` and `b` only (`c`, `c'` stay symbolic). Each leaf is a congruence in
/// the last argument; the swap `F(a,b,_)` vs `F(b,a,_)` is closed by conversion once `a`, `b` are
/// literal bits (it is valid only for an `F` that is commutative in its first two arguments).
fn comm_lemma(ff: &dyn Fn(Expr, Expr, Expr) -> Expr) -> Expr {
    // ctx [a, b, c, c', ga, gb]
    fn elim(ff: &dyn Fn(Expr, Expr, Expr) -> Expr, vals: [Option<bool>; 2]) -> Expr {
        let which = match vals.iter().position(|v| v.is_none()) {
            Some(w) => w,
            None => {
                let (av, bv) = (bit(vals[0].unwrap()), bit(vals[1].unwrap()));
                let fmap = lam(bool0(), ff(av, bv, var(0)));
                // under the \p binder: c = var 4, c' = var 3
                return lam(id(bool0(), var(3), var(2)), cong1(&bool0(), &bool0(), &fmap, var(4), var(3), var(0)));
            }
        };
        // motive at depth 7 (inside its own binder): c = var 4, c' = var 3
        let operand = |k: usize| match vals[k] {
            _ if k == which => var(0),
            Some(v) => bit(v),
            None => var(6 - k as u32),
        };
        let (x, y) = (operand(0), operand(1));
        let body = pi(
            id(bool0(), var(4), var(3)),
            id(
                bool0(),
                shift(&ff(x.clone(), y.clone(), var(4)), 0, 1),
                shift(&ff(y, x, var(3)), 0, 1),
            ),
        );
        let motive = lam(bool0(), body);
        let g = var(1 - which as u32);
        let mut vt = vals;
        vt[which] = Some(true);
        let mut vf = vals;
        vf[which] = Some(false);
        app3(g, motive, elim(ff, vt), elim(ff, vf))
    }
    let body = elim(ff, [None, None]);
    lam(bool0(), lam(bool0(), lam(bool0(), lam(bool0(),
        lam(app(good_bool(), var(3)), lam(app(good_bool(), var(3)), body))))))
}

/// `(proof, statement)` of `Pi x y. GoodBv x -> GoodBv y -> Id(Bv_n, add x y, add y x)`.
/// `wrong` changes the statement's right-hand side to `add x x`, which the proof must not check against.
fn add_comm_proof(n: usize, wrong: bool) -> (Expr, Expr) {
    let carry = |a: Expr, b: Expr, c: Expr| or(and(a.clone(), b.clone()), and(c, xor(a, b)));
    let sum = |a: Expr, b: Expr, c: Expr| xor(xor(a, b), c);
    let cc = comm_lemma(&carry);
    let sc = comm_lemma(&sum);
    // ctx: x, y, gx, gy, a_0.., ga_0.., b_0.., gb_0..
    let d1 = 4 + 2 * n;
    let d2 = d1 + 2 * n;
    let a = |i: usize| var((d2 - 1 - (4 + i)) as u32);
    let ga = |i: usize| var((d2 - 1 - (4 + n + i)) as u32);
    let b = |i: usize| var((d2 - 1 - (d1 + i)) as u32);
    let gb = |i: usize| var((d2 - 1 - (d1 + n + i)) as u32);
    // c_i = carry of add (mk a) (mk b); c'_i = carry of add (mk b) (mk a); pc_i : Id(c_i, c'_i)
    let mut c = vec![f()];
    let mut c2 = vec![f()];
    let mut pc = vec![refl(f())];
    let (mut s, mut s2, mut e) = (vec![], vec![], vec![]);
    for i in 0..n {
        s.push(sum(a(i), b(i), c[i].clone()));
        s2.push(sum(b(i), a(i), c2[i].clone()));
        e.push(apps(sc.clone(), vec![a(i), b(i), c[i].clone(), c2[i].clone(), ga(i), gb(i), pc[i].clone()]));
        let (nc, nc2) = (carry(a(i), b(i), c[i].clone()), carry(b(i), a(i), c2[i].clone()));
        pc.push(apps(cc.clone(), vec![a(i), b(i), c[i].clone(), c2[i].clone(), ga(i), gb(i), pc[i].clone()]));
        c.push(nc);
        c2.push(nc2);
    }
    // f_n = \u_0..u_(n-1). \C k. k u_0 .. u_(n-1)
    let mut fbody = apps(var(0), (0..n).map(|i| var((n + 1 - i) as u32)).collect());
    fbody = lam(sort(1), lam(karrow(n), fbody));
    for _ in 0..n {
        fbody = lam(bool0(), fbody);
    }
    let binders = |mut body: Expr| {
        for _ in 0..n {
            body = lam(app(good_bool(), var(n as u32 - 1)), body);
        }
        for _ in 0..n {
            body = lam(bool0(), body);
        }
        body
    };
    let step_y = binders(cong_n(&bool0(), &bv_ty(n), &fbody, &s, &s2, e));
    // inside the a-step (depth d1): eliminate y
    let a1 = |i: usize| var((d1 - 1 - (4 + i)) as u32);
    let mka = mk(&(0..n).map(|i| shift(&a1(i), 0, 1)).collect::<Vec<_>>());
    let motive_y = lam(bv_ty(n), id(bv_ty(n), app2(add(n), mka.clone(), var(0)), app2(add(n), var(0), mka)));
    let gy = var((d1 - 1 - 3) as u32);
    let step_x = binders(app2(gy, motive_y, step_y));
    let rhs = |x: Expr, y: Expr| if wrong { app2(add(n), x.clone(), x) } else { app2(add(n), y, x) };
    // depth 5 (inside the motive binder): x' = var 0, y = var 3
    let motive_x = lam(bv_ty(n), id(bv_ty(n), app2(add(n), var(0), var(3)), rhs(var(0), var(3))));
    let body = app2(var(1), motive_x, step_x);
    let proof = lam(bv_ty(n), lam(bv_ty(n), lam(app(good_bv(n), var(1)), lam(app(good_bv(n), var(1)), body))));
    // statement at ctx [x, y, gx, gy]: x = var 3, y = var 2
    let stmt = pi(bv_ty(n), pi(bv_ty(n), pi(app(good_bv(n), var(1)), pi(app(good_bv(n), var(1)),
        id(bv_ty(n), app2(add(n), var(3), var(2)), rhs(var(3), var(2)))))));
    (proof, stmt)
}

#[test]
fn add_is_commutative_on_symbolic_good_vectors() {
    for n in [1usize, 2, 4] {
        let (proof, stmt) = add_comm_proof(n, false);
        let t0 = Instant::now();
        ck(&format!("add x y = add y x at n={n}"), &proof, &stmt);
        println!("COMM n={n}: checked in {:?}", t0.elapsed());
        // Mutation: `add x y = add x x` must be rejected, by its own proof and by this one.
        let (wp, ws) = add_comm_proof(n, true);
        assert!(check(&Ctx::new(), &wp, &ws).is_err(), "wrong statement must be rejected at n={n}");
        assert!(check(&Ctx::new(), &proof, &ws).is_err(), "add x y = add x x must be rejected at n={n}");
    }
}

#[test]
#[ignore]
fn add_comm_scaling() {
    for n in [8usize, 16, 32] {
        let (proof, stmt) = add_comm_proof(n, false);
        let t0 = Instant::now();
        ck(&format!("n={n}"), &proof, &stmt);
        println!("COMM-SCALE n={n}: {:?}", t0.elapsed());
    }
}
