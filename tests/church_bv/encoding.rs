use super::*;

pub fn bool0() -> Expr {
    pi(sort(0), arrow(var(0), arrow(var(0), var(0))))
}
pub fn t() -> Expr {
    lam(sort(0), lam(var(0), lam(var(1), var(1))))
}
pub fn f() -> Expr {
    lam(sort(0), lam(var(0), lam(var(1), var(0))))
}
pub fn bit(b: bool) -> Expr {
    if b { t() } else { f() }
}
pub fn bool2(body: Expr) -> Expr {
    // \a b : Bool0. \C t f. body   ctx [a,b,C,t,f]: f=0 t=1 C=2 b=3 a=4
    lam(bool0(), lam(bool0(), lam(sort(0), lam(var(0), lam(var(1), body)))))
}
pub fn and_() -> Expr {
    bool2(app3(var(4), var(2), app3(var(3), var(2), var(1), var(0)), var(0)))
}
pub fn or_() -> Expr {
    bool2(app3(var(4), var(2), var(1), app3(var(3), var(2), var(1), var(0))))
}
pub fn xor_() -> Expr {
    bool2(app3(var(4), var(2), app3(var(3), var(2), var(0), var(1)), app3(var(3), var(2), var(1), var(0))))
}
pub fn and(a: Expr, b: Expr) -> Expr { app2(and_(), a, b) }
pub fn or(a: Expr, b: Expr) -> Expr { app2(or_(), a, b) }
pub fn xor(a: Expr, b: Expr) -> Expr { app2(xor_(), a, b) }

/// The `n` low bits set (`n` up to 128).
pub fn low_bits(n: usize) -> u128 {
    if n >= 128 { u128::MAX } else { (1u128 << n) - 1 }
}

/// Bool0 -> ... -> Bool0 -> C (n arrows), in a context whose top variable is C.
pub fn karrow(n: usize) -> Expr {
    if n == 0 { var(0) } else { arrow(bool0(), karrow(n - 1)) }
}
pub fn bv_ty(n: usize) -> Expr {
    pi(sort(1), arrow(karrow(n), var(0)))
}
pub fn apps(mut f: Expr, args: Vec<Expr>) -> Expr {
    for a in args {
        f = app(f, a);
    }
    f
}
/// Literal: \C k. k b0 .. b(n-1), least significant bit first.
pub fn lit(n: usize, v: u128) -> Expr {
    let bits = (0..n).map(|i| bit((v >> i) & 1 == 1)).collect();
    lam(sort(1), lam(karrow(n), apps(var(0), bits)))
}
/// \a b. \C k. a C (\a0..a(n-1). b C (\b0..b(n-1). k s0 .. s(n-1)))  with ripple-carry sums.
pub fn add(n: usize) -> Expr {
    ripple(n, false)
}
/// `a - b` (mod 2^n) as a ripple-borrow chain: the same circuit with the borrow `maj(~a, b, borrow)` as carry.
pub fn sub(n: usize) -> Expr {
    ripple(n, true)
}
/// `lt_u a b` as a one-bit vector (a `Bool0` result would live one universe below the claims about it): the final
/// borrow of the ripple-borrow chain of `a - b`, set iff `a < b` as unsigned numbers.
pub fn lt_u(n: usize) -> Expr {
    let d = 4 + 2 * n; // depth at the innermost body: a b C k a0.. b0..
    let v = |pos: usize| var((d - 1 - pos) as u32);
    let mut carry = f();
    for i in 0..n {
        let (a, b) = (v(4 + i), v(4 + n + i));
        carry = ripple_carry(true, a.clone(), b.clone(), carry, xor(a, b));
    }
    let mut body = app(v(3), carry);
    for _ in 0..n {
        body = lam(bool0(), body);
    }
    let mut inner = app2(var(n as u32 + 2), var(n as u32 + 1), body);
    for _ in 0..n {
        inner = lam(bool0(), inner);
    }
    let outer = app2(var(3), var(1), inner);
    lam(bv_ty(n), lam(bv_ty(n), lam(sort(1), lam(karrow(1), outer))))
}
/// The next carry (or borrow) of one position, given its operand bits, the incoming carry and `x = a ^ b`.
pub fn ripple_carry(sub: bool, a: Expr, b: Expr, c: Expr, x: Expr) -> Expr {
    if sub {
        let na = xor(a, t());
        or(and(na.clone(), b.clone()), and(c, xor(na, b)))
    } else {
        or(and(a, b), and(c, x))
    }
}
pub fn ripple(n: usize, sub: bool) -> Expr {
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
        carry = ripple_carry(sub, ai(i), bi(i), carry, x);
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
pub fn add_shared(n: usize) -> Expr {
    add_mode(n, 0)
}
pub fn add_mode(n: usize, mode: u8) -> Expr {
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

pub fn is_ok(r: Result<Expr, String>) -> bool {
    match r {
        Ok(_) => true,
        Err(m) => panic!("{}", m.chars().take(300).collect::<String>()),
    }
}

pub fn run(n: usize) {
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
pub fn church_bitvector_add_computes_by_conv_at_8_bits() {
    run(8);
}

/// ~0.8 s per add on a loaded machine (98% CPU); superlinear in width (8 bits: ~2 ms).
#[test]
#[ignore]
pub fn church_bitvector_add_computes_by_conv_at_64_bits() {
    run(64);
}

#[test]
#[ignore]
pub fn scaling_probe() {
    for n in [8usize, 16, 24, 32, 48] {
        let ad = add_shared(n);
        let mask = low_bits(n);
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
pub fn skeleton_probe() {
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
pub fn good_bool() -> Expr {
    lam(bool0(), pi(arrow(bool0(), sort(1)), pi(app(var(0), t()), pi(app(var(1), f()), app(var(2), var(3))))))
}
/// `\a g. g motive at_true at_false`, with its type; `motive_body` is written at ctx [b].
pub fn bit_lemma(motive_body: Expr, at_true: Expr, at_false: Expr) -> (Expr, Expr) {
    let motive = lam(bool0(), motive_body.clone());
    let proof = lam(bool0(), lam(app(good_bool(), var(0)), app3(var(0), motive, at_true, at_false)));
    let ty = pi(bool0(), arrow(app(good_bool(), var(0)), motive_body));
    (proof, ty)
}
pub fn mk(args: &[Expr]) -> Expr {
    let n = args.len();
    lam(sort(1), lam(karrow(n), apps(var(0), args.iter().map(|a| shift(a, 0, 2)).collect())))
}
/// The hypothesis type of `GoodBv`, placed with `P` as the innermost outer binder:
/// `Pi a_0..a_(n-1). GoodBool a_0 -> .. -> GoodBool a_(n-1) -> P (mk a_0 .. a_(n-1))`.
pub fn good_bv_step(n: usize) -> Expr {
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
pub fn good_bv(n: usize) -> Expr {
    lam(bv_ty(n), pi(arrow(bv_ty(n), sort(2)), pi(good_bv_step(n), app(var(1), var(2)))))
}

pub fn ck(name: &str, e: &Expr, ty: &Expr) {
    if let Err(m) = check(&Ctx::new(), e, ty) {
        panic!("{name}: {}", m.chars().take(400).collect::<String>());
    }
}

/// `(proof, statement)` of `Pi x:Bv_n. GoodBv x -> Id(Bv_n, add x (lit rhs_lit), x)` using the
/// `add x 0 = x` proof; `rhs_lit != 0` gives a statement the proof must not check against.
pub fn add_zero_proof(n: usize, rhs_lit: u128) -> (Expr, Expr) {
    add_identity_proof(n, rhs_lit, false)
}

/// `left = true` proves `add zero x = x` instead (the literal is the first operand).
pub fn add_identity_proof(n: usize, rhs_lit: u128, left: bool) -> (Expr, Expr) {
    add_identity_proof_over(n, rhs_lit, left, add)
}

/// Same, with the statement stated over `adder` (`add` or `add_shared`); the proof body is unchanged,
/// so `adder`'s result must be convertible to the inlined-carry tuple the proof builds.
pub fn add_identity_proof_over(n: usize, rhs_lit: u128, left: bool, adder: fn(usize) -> Expr) -> (Expr, Expr) {
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
    let ys: Vec<Expr> = (0..n).map(a).collect();
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
    let sum = |x: Expr, r: Expr| if left { app2(adder(n), r, x) } else { app2(adder(n), x, r) };
    let motive = lam(bv_ty(n), id(bv_ty(n), sum(var(0), rhs.clone()), var(0)));
    let proof = lam(bv_ty(n), lam(app(good_bv(n), var(0)), app2(var(0), motive, step)));
    let stmt = pi(bv_ty(n), arrow(app(good_bv(n), var(0)), id(bv_ty(n), sum(var(0), rhs), var(0))));
    (proof, stmt)
}

/// `add_identity_proof_over` with the carries bound once in the proof as well (design doc section 90b): each carry `c_j`
/// and its proof `pc_j : Id(c_j, false)` are lambda-bound variables, `(\c pc. rest) (carry a_(j-1) c_(j-1)) proof_j`, so
/// every term and type the proof body builds mentions `c_j` as one variable, not an O(j)-node expression. Stated over
/// `adder` (use `add_shared`, so the statement is shaped the same way).
pub fn add_identity_proof_shared(n: usize, rhs_lit: u128, left: bool, adder: fn(usize) -> Expr) -> (Expr, Expr) {
    let xf = move |a: Expr| if left { xor(f(), a) } else { xor(a, f()) };
    let carry = move |a: Expr, c: Expr| {
        if left { or(and(f(), a.clone()), and(c, xor(f(), a))) } else { or(and(a.clone(), f()), and(c, xor(a, f()))) }
    };
    let (p1, _) = bit_lemma(id(bool0(), xor(xf(var(0)), f()), var(0)), refl(t()), refl(f()));
    let (p2, _) = bit_lemma(id(bool0(), carry(var(0), f()), f()), refl(f()), refl(f()));
    // step-body context [x, g, a_0..a_(n-1), ga_0..ga_(n-1), c_1, pc_1, c_2, pc_2, ..]; `k` pairs are bound
    let d = 2 + 2 * n;
    let a = move |i: usize, k: usize| var((d + 2 * k - 1 - (2 + i)) as u32);
    let ga = move |i: usize, k: usize| var((d + 2 * k - 1 - (2 + n + i)) as u32);
    let cv = move |j: usize, k: usize| if j == 0 { f() } else { var((d + 2 * k - 1 - (d + 2 * (j - 1))) as u32) };
    let pv = move |j: usize, k: usize| var((d + 2 * k - 1 - (d + 2 * (j - 1) + 1)) as u32);
    // proof that c_(j+1) = carry(a_j, c_j) is false, at `k` bound pairs (j <= k)
    let next_false = |j: usize, k: usize| {
        let step_to_false = app2(p2.clone(), a(j, k), ga(j, k));
        if j == 0 {
            return step_to_false;
        }
        let cj = cv(j, k);
        let fmap = lam(bool0(), carry(shift(&a(j, k), 0, 1), var(0)));
        let rewritten = cong1(&bool0(), &bool0(), &fmap, cj.clone(), f(), pv(j, k));
        trans_proof(&bool0(), &carry(a(j, k), cj), &carry(a(j, k), f()), &f(), rewritten, step_to_false)
    };
    let kn = n.saturating_sub(1);
    // innermost: the sums with every carry a variable
    let mut s = Vec::new();
    let mut e = Vec::new();
    for i in 0..n {
        let ci = cv(i, kn);
        let s_i = xor(xf(a(i, kn)), ci.clone());
        let to_a = app2(p1.clone(), a(i, kn), ga(i, kn));
        let proof = if i == 0 {
            to_a
        } else {
            let fmap = lam(bool0(), xor(xf(shift(&a(i, kn), 0, 1)), var(0)));
            let rewritten = cong1(&bool0(), &bool0(), &fmap, ci.clone(), f(), pv(i, kn));
            trans_proof(&bool0(), &s_i, &xor(xf(a(i, kn)), f()), &a(i, kn), rewritten, to_a)
        };
        s.push(s_i);
        e.push(proof);
    }
    let ys: Vec<Expr> = (0..n).map(|i| a(i, kn)).collect();
    let mut fbody = apps(var(0), (0..n).map(|i| var((n + 1 - i) as u32)).collect());
    fbody = lam(sort(1), lam(karrow(n), fbody));
    for _ in 0..n {
        fbody = lam(bool0(), fbody);
    }
    let mut body = cong_n(&bool0(), &bv_ty(n), &fbody, &s, &ys, e);
    // bind c_(j+1), pc_(j+1) from the inside out: level k binds the pair for j = k
    for k in (0..kn).rev() {
        let binder = lam(bool0(), lam(id(bool0(), var(0), f()), body));
        body = app2(binder, carry(a(k, k), cv(k, k)), next_false(k, k));
    }
    let mut step = body;
    for _ in 0..n {
        step = lam(app(good_bool(), var(n as u32 - 1)), step);
    }
    for _ in 0..n {
        step = lam(bool0(), step);
    }
    let rhs = lit(n, rhs_lit);
    let sum = |x: Expr, r: Expr| if left { app2(adder(n), r, x) } else { app2(adder(n), x, r) };
    let motive = lam(bv_ty(n), id(bv_ty(n), sum(var(0), rhs.clone()), var(0)));
    let proof = lam(bv_ty(n), lam(app(good_bv(n), var(0)), app2(var(0), motive, step)));
    let stmt = pi(bv_ty(n), arrow(app(good_bv(n), var(0)), id(bv_ty(n), sum(var(0), rhs), var(0))));
    (proof, stmt)
}

#[test]
pub fn shared_carry_proof_checks_and_rejects_wrong_statements() {
    for n in [1usize, 2, 3, 4, 8] {
        for left in [false, true] {
            let (proof, stmt) = add_identity_proof_shared(n, 0, left, add_shared);
            ck(&format!("shared n={n} left={left}"), &proof, &stmt);
            let (proof1, stmt1) = add_identity_proof_shared(n, 1, left, add_shared);
            assert!(check(&Ctx::new(), &proof1, &stmt1).is_err(), "rhs 1 must be rejected at n={n} left={left}");
        }
    }
}

/// Section 90b: the shared-carry proof against the inlined one, same exe, alternating, n = 16, 32 (and 64 with `SHARED_N64=1`).
#[test]
#[ignore]
pub fn shared_carry_scaling() {
    let ns: Vec<usize> = if std::env::var("SHARED_N64").is_ok() { vec![16, 32, 64] } else { vec![16, 32] };
    for n in ns {
        for round in 0..2 {
            let (p, s) = add_identity_proof_shared(n, 0, false, add_shared);
            let t0 = Instant::now();
            ck("shared", &p, &s);
            let shared = t0.elapsed();
            let (p, s) = add_identity_proof(n, 0, false);
            let t1 = Instant::now();
            ck("inlined", &p, &s);
            println!("SHARED-CARRY n={n} round={round}: shared {shared:?}, inlined {:?}", t1.elapsed());
        }
    }
}

#[test]
pub fn add_zero_is_the_identity_on_a_symbolic_good_vector() {
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

/// Scaling gate: the `add x 0 = x` proof's size (nodes counted once per allocation) must keep growing
/// by no more than 4.5x per doubling of the width, and stay under a fixed size at n=64. Both were
/// breached by an unshared shift in `cong_n`/`trans_proof` (design doc sections 54-56: 8x per doubling,
/// 1.58M nodes at n=64, against 3.0x and 288k now). A new proof builder that copies where it should
/// share fails here, not months later in a timing. Check-time visit counts are gated by hand with
/// `walk_counts_on_hard_queries` (needs the `record-defeq` feature).
#[test]
pub fn add_zero_proof_size_scales_gently() {
    let size = |n: usize| tatic::kernel::term_sizes(&add_zero_proof(n, 0).0).0;
    let (s16, s32, s64) = (size(16), size(32), size(64));
    assert!(s32 as f64 / s16 as f64 <= 4.5, "n=16 -> 32: {s16} -> {s32} nodes");
    assert!(s64 as f64 / s32 as f64 <= 4.5, "n=32 -> 64: {s32} -> {s64} nodes");
    assert!(s64 <= 400_000, "n=64: {s64} nodes");
}

/// Size of the generated proof by width, without checking it.
#[test]
#[ignore]
pub fn proof_size_scaling() {
    for n in [16usize, 32, 64, 128, 256] {
        let (proof, _) = add_zero_proof(n, 0);
        println!("PROOF-SIZE n={n}: dag={}", tatic::kernel::term_sizes(&proof).0);
    }
}

/// Growth of the universal lemma's check time with width (machine load varies; indicative only).
#[test]
#[ignore]
pub fn add_zero_lemma_scaling() {
    for n in [8usize, 16, 32, 64, 128, 256, 512] {
        let (proof, stmt) = add_zero_proof(n, 0);
        let t0 = Instant::now();
        ck(&format!("n={n}"), &proof, &stmt);
        println!("LEMMA-SCALE n={n}: {:?}", t0.elapsed());
    }
}

/// As `add_zero_lemma_scaling`, but building and checking inside one `InternScope`, so the proof is
/// interned as it is built (design doc section 69). Prints build and check time separately.
#[test]
#[ignore]
pub fn add_zero_lemma_scaling_scoped() {
    for n in [8usize, 16, 32, 64, 128, 256, 512] {
        let _scope = std::env::var("NO_SCOPE").is_err().then(tatic::kernel::InternScope::enter);
        let t0 = Instant::now();
        let (proof, stmt) = add_zero_proof(n, 0);
        let built = t0.elapsed();
        let t1 = Instant::now();
        ck(&format!("n={n}"), &proof, &stmt);
        println!(
            "SCOPED n={n}: build {built:?}, check {:?}, proof dag={}",
            t1.elapsed(),
            tatic::kernel::term_sizes(&proof).0
        );
    }
}

// ---- Commutativity: `add x y = add y x` for `x`, `y` with `GoodBv` witnesses.

/// Closed proof of `Pi a b c c'. GoodBool a -> GoodBool b -> Id(c, c') -> Id(F(a,b,c), F(b,a,c'))`,
/// by case analysis on `a` and `b` only (`c`, `c'` stay symbolic). Each leaf is a congruence in
/// the last argument; the swap `F(a,b,_)` vs `F(b,a,_)` is closed by conversion once `a`, `b` are
/// literal bits (it is valid only for an `F` that is commutative in its first two arguments).
pub fn comm_lemma(ff: &dyn Fn(Expr, Expr, Expr) -> Expr) -> Expr {
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
pub fn add_comm_proof(n: usize, wrong: bool) -> (Expr, Expr) {
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
pub fn add_is_commutative_on_symbolic_good_vectors() {
    // n=16 guards the failure path: rejecting a false statement once printed its terms as trees, which
    // took minutes at this width (doc section 82).
    for n in [1usize, 2, 4, 16] {
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
pub fn add_comm_scaling() {
    for n in [8usize, 16, 32] {
        let (proof, stmt) = add_comm_proof(n, false);
        let t0 = Instant::now();
        ck(&format!("n={n}"), &proof, &stmt);
        println!("COMM-SCALE n={n}: {:?}", t0.elapsed());
    }
}

/// One rejection check at width `COMM_N`: `COMM_CASE` is `own` (the wrong statement against its own
/// proof) or `right` (the right proof against the wrong statement). Prints the verdict and time.
/// For running one case under a memory watchdog (design doc section 82).
#[test]
#[ignore]
pub fn add_comm_rejection_probe() {
    let n: usize = std::env::var("COMM_N").unwrap().parse().unwrap();
    let case = std::env::var("COMM_CASE").unwrap();
    let _scope = std::env::var("NO_SCOPE").is_err().then(tatic::kernel::InternScope::enter);
    let (proof, _) = add_comm_proof(n, false);
    let (wp, ws) = add_comm_proof(n, true);
    let t0 = Instant::now();
    let r = if case == "own" { check(&Ctx::new(), &wp, &ws) } else { check(&Ctx::new(), &proof, &ws) };
    println!("REJECT n={n} {case}: rejected={} in {:?}", r.is_err(), t0.elapsed());
}

/// As `add_comm_scaling`, built and checked inside one `InternScope`, up to the widths in the
/// environment variable `COMM_NS` (comma separated; default 8,16,32,64). Prints build and check time
/// separately and the proof DAG (design doc section 81).
#[test]
#[ignore]
pub fn add_comm_scaling_scoped() {
    let ns: Vec<usize> = std::env::var("COMM_NS")
        .unwrap_or_else(|_| "8,16,32,64".into())
        .split(',')
        .map(|v| v.trim().parse().unwrap())
        .collect();
    for n in ns {
        let _scope = std::env::var("NO_SCOPE").is_err().then(tatic::kernel::InternScope::enter);
        let t0 = Instant::now();
        let (proof, stmt) = add_comm_proof(n, false);
        let built = t0.elapsed();
        let t1 = Instant::now();
        ck(&format!("n={n}"), &proof, &stmt);
        println!(
            "COMM-SCOPED n={n}: build {built:?}, check {:?}, proof dag={}",
            t1.elapsed(),
            tatic::kernel::term_sizes(&proof).0
        );
    }
}

/// Probe: `add_shared x 0 = x` (carries let-bound in the statement), original `add` kept alongside.
#[test]
pub fn add_shared_zero_is_the_identity_on_a_symbolic_good_vector() {
    for n in [1usize, 2, 4, 8] {
        let (proof, stmt) = add_identity_proof_over(n, 0, false, add_shared);
        let t0 = Instant::now();
        ck(&format!("add_shared x 0 = x at n={n}"), &proof, &stmt);
        println!("SHARED n={n}: checked in {:?}", t0.elapsed());
        let (p1, s1) = add_identity_proof_over(n, 1, false, add_shared);
        assert!(check(&Ctx::new(), &p1, &s1).is_err(), "add_shared x 1 = x must be rejected at n={n}");
    }
}

#[test]
#[ignore]
pub fn add_shared_zero_scaling() {
    for n in [8usize, 16, 32] {
        let (proof, stmt) = add_identity_proof_over(n, 0, false, add_shared);
        let t0 = Instant::now();
        ck(&format!("n={n}"), &proof, &stmt);
        println!("SHARED-SCALE n={n}: {:?}", t0.elapsed());
    }
}

/// Replays every `def_eq` query the `add x 0 = x` lemma's check makes through the kernel and
/// through `kernel_lazy`, same exe back to back. Needs `--features record-defeq`.
/// Run: `cargo test --release --features record-defeq --test church_bv replay_defeq -- --ignored --nocapture`
#[cfg(feature = "record-defeq")]
#[test]
#[ignore]
pub fn replay_defeq_queries() {
    use tatic::kernel_lazy::{def_eq_lazy_shared, take_stats};
    for n in [8usize, 16, 32] {
        let (proof, stmt) = add_zero_proof(n, 0);
        let _ = take_defeq_log();
        ck(&format!("n={n}"), &proof, &stmt);
        let qs = take_defeq_log();
        let hard: Vec<_> = qs.iter().filter(|(a, b, _)| a != b).collect();
        {
            // Probe: eq visits per easy (equal) query, bucketed.
            let _ = take_walk_counts();
            let mut buckets = [(0u64, 0u64); 5]; // (queries, visits) for 0, 1-3, 4-15, 16-63, 64+
            for (a, b, _) in qs.iter().filter(|(a, b, _)| a == b) {
                let v0 = take_walk_counts()[2];
                assert!(def_eq(a, b));
                let v = take_walk_counts()[2];
                let _ = v0;
                let k = match v { 0 => 0, 1..=3 => 1, 4..=15 => 2, 16..=63 => 3, _ => 4 };
                buckets[k].0 += 1;
                buckets[k].1 += v;
            }
            println!("EASY n={n}: (queries, eq visits) by visits-per-query 0 / 1-3 / 4-15 / 16-63 / 64+ = {buckets:?}");
        }
        let t0 = Instant::now();
        let _ = take_beta_count();
        let k: Vec<bool> = hard.iter().map(|(a, b, _)| def_eq(a, b)).collect();
        let tk = t0.elapsed();
        let kernel_betas = take_beta_count();
        let _ = take_stats();
        let t1 = Instant::now();
        let s: Vec<bool> = hard.iter().map(|(a, b, d)| def_eq_lazy_shared(a, b, *d)).collect();
        let ts = t1.elapsed();
        let st = take_stats();
        println!("REPLAY n={n}: queries={} hard={} kernel {tk:?} shared {ts:?} agree={} kernel_betas={kernel_betas} lazy_betas={}", qs.len(), hard.len(), k == s, st.betas);
        println!("REPLAY n={n}: evals={} conv={}", st.eval_calls, st.conv_calls);
    }
}

/// Which traversals pay by tree node: visits per kernel function on the hard queries.
/// Run like `replay_defeq_queries`.
#[cfg(feature = "record-defeq")]
#[test]
#[ignore]
pub fn walk_counts_on_hard_queries() {
    for n in [8usize, 16, 32, 64] {
        let (proof, stmt) = add_zero_proof(n, 0);
        let _ = take_defeq_log();
        let _ = take_site_counts();
        let _ = take_walk_counts();
        let _ = (tatic::kernel::take_hc_built(), tatic::kernel::take_hc_inst());
        let tck = Instant::now();
        ck(&format!("n={n}"), &proof, &stmt);
        {
            let (built, new) = tatic::kernel::take_hc_built();
            let i = tatic::kernel::take_hc_inst();
            println!("HC n={n}: nodes built in the check={built}, of which structurally new={new} ({:.1}% would be intern hits)", 100.0 * (built - new) as f64 / built.max(1) as f64);
            for (k, name) in ["instantiate", "shift", "whnf_step", "conv_whnf"].iter().enumerate() {
                let c = i[k];
                println!("REPEAT n={n} {name}: calls={} maximal repeated calls={} work skipped by a global memo={} of {} ({:.1}%)", c[0], c[1], c[2], c[3], 100.0 * c[2] as f64 / c[3].max(1) as f64);
            }
        }
        println!("CHECK n={n}: whole check {:?}", tck.elapsed());
        { let (pd, pt) = tatic::kernel::term_sizes(&proof); let (sd, st) = tatic::kernel::term_sizes(&stmt); println!("SIZE n={n}: proof dag={pd} tree={pt}; statement dag={sd} tree={st}"); }
        { let w = take_walk_counts(); println!("CHECK n={n}: whole-check visits instantiate={} shift={} eq={} conv_whnf={} shift-in-ctx_lookup={}", w[0], w[1], w[2], w[3], w[17]); println!("INFER-MEMO n={n}: single-ref calls={} hits={} misses={} binder entries={}", w[18], w[19], w[20], w[21]); println!("RELAXED-MEMO n={n}: memo-eligible lookups={} extra hits under a relevance key={} of which closed nodes={} (strict misses {}), mean window={:.1}", w[22], w[23], w[25], w[20], w[24] as f64 / w[22].max(1) as f64); }
        {
            let sc = take_site_counts();
            println!("SITES n={n} [instantiate, shift, eq]: other={:?} ctx_lookup={:?} app_subst={:?} def_eq={:?}", sc[0], sc[1], sc[2], sc[3]);
        }
        let qs = take_defeq_log();
        let hard: Vec<_> = qs.iter().filter(|(a, b, _)| a != b).collect();
        {
            // Probe: eq visits per easy (equal) query, bucketed.
            let _ = take_walk_counts();
            let mut buckets = [(0u64, 0u64); 5]; // (queries, visits) for 0, 1-3, 4-15, 16-63, 64+
            for (a, b, _) in qs.iter().filter(|(a, b, _)| a == b) {
                let v0 = take_walk_counts()[2];
                assert!(def_eq(a, b));
                let v = take_walk_counts()[2];
                let _ = v0;
                let k = match v { 0 => 0, 1..=3 => 1, 4..=15 => 2, 16..=63 => 3, _ => 4 };
                buckets[k].0 += 1;
                buckets[k].1 += v;
            }
            println!("EASY n={n}: (queries, eq visits) by visits-per-query 0 / 1-3 / 4-15 / 16-63 / 64+ = {buckets:?}");
        }
        let _ = take_walk_counts();
        let _ = take_beta_count();
        let t0 = Instant::now();
        for (a, b, _) in &hard {
            assert!(def_eq(a, b));
        }
        let w = take_walk_counts();
        println!(
            "WALK n={n}: time={:?} betas={} instantiate={} shift={} eq={} conv_whnf={} nf_whnf={}",
            t0.elapsed(),
            take_beta_count(),
            w[0], w[1], w[2], w[3], w[4]
        );
        // Option C probe: rename the context to Frees, then compare.
        let _ = take_walk_counts();
        let t1 = Instant::now();
        let mut rename_visits = 0;
        let mut renamed = Vec::new();
        for (a, b, c) in &hard {
            let (ra, rb) = rename_pair_memo(a, b, *c);
            renamed.push((ra, rb));
        }
        let rw = take_walk_counts();
        rename_visits += rw[0];
        let t_rename = t1.elapsed();
        let t2 = Instant::now();
        for (ra, rb) in &renamed {
            assert!(def_eq(ra, rb));
        }
        let cw = take_walk_counts();
        println!(
            "RENAME n={n}: rename {t_rename:?} ({rename_visits} visits); then def_eq {:?} instantiate={} shift={} eq={} conv_whnf={} (plain: instantiate={} shift={} eq={})",
            t2.elapsed(), cw[0], cw[1], cw[2], cw[3], w[0], w[1], w[2]
        );
        println!(
            "PROBE n={n}: uses={} depth0={} deeper-closed={} deeper-loose={} shift visits from deeper-loose={} of {}",
            w[5], w[6], w[7], w[8], w[9], w[1]
        );
        println!(
            "PROBE2 n={n}: conv binders opened={}; deeper-loose uses internal={} ctx-only={}; shift visits internal={} ctx-only={}",
            w[14], w[10], w[11], w[12], w[13]
        );
        println!(
            "PROBE3 n={n}: distinct (arg,depth) shifts per def_eq={} of {}; their shift visits={} of {}",
            w[15], w[8], w[16], w[1]
        );
    }
}

/// Whole-check wall time without the `record-defeq` feature, best of 3 per width, with the machine's
/// CPU load before and after (`LONG_RUNS.md`): the figure to compare across kernel changes.
#[test]
#[ignore]
pub fn whole_check_time() {
    for n in [32usize, 64] {
        let (proof, stmt) = add_zero_proof(n, 0);
        let mut best = std::time::Duration::MAX;
        for _ in 0..3 {
            let t0 = Instant::now();
            ck(&format!("n={n}"), &proof, &stmt);
            best = best.min(t0.elapsed());
        }
        println!("WHOLE n={n}: best of 3 = {best:?}");
    }
}

/// One check of the universal lemma at n=64, for profiling (`SAMPLY.md`): no timing, no logging.
#[test]
#[ignore]
pub fn profile_add_zero_n64() {
    let (proof, stmt) = add_zero_proof(64, 0);
    ck("profile n=64", &proof, &stmt);
}

/// As `profile_add_zero_n64`, at n=128.
#[test]
#[ignore]
pub fn profile_add_zero_n128() {
    let (proof, stmt) = add_zero_proof(128, 0);
    ck("profile n=128", &proof, &stmt);
}

/// As `profile_add_zero_n64`, at n=256.
#[test]
#[ignore]
pub fn profile_add_zero_n256() {
    let (proof, stmt) = add_zero_proof(256, 0);
    ck("profile n=256", &proof, &stmt);
}

/// As `profile_add_zero_n64`, at n=512.
#[test]
#[ignore]
pub fn profile_add_zero_n512() {
    let (proof, stmt) = add_zero_proof(512, 0);
    ck("profile n=512", &proof, &stmt);
}

/// Build and check the n=256 / n=512 lemma inside one `InternScope`, for profiling the scoped check
/// alone per width (`SAMPLY.md`; the profiling task passes no environment, so one test per width).
pub fn profile_scoped(n: usize) {
    let _scope = tatic::kernel::InternScope::enter();
    let (proof, stmt) = add_zero_proof(n, 0);
    ck("profile scoped", &proof, &stmt);
}

/// As `profile_scoped_n512`, on a thread with a 1 GiB stack, so `grow` never needs a new segment.
#[test]
#[ignore]
pub fn profile_scoped_n512_big_stack() {
    std::thread::Builder::new().stack_size(1 << 30).spawn(|| profile_scoped(512)).unwrap().join().unwrap();
}

#[test]
#[ignore]
pub fn profile_scoped_n256() {
    profile_scoped(256);
}

#[test]
#[ignore]
pub fn profile_scoped_n512() {
    profile_scoped(512);
}

/// A large check must not churn stack segments: before `check_in` ran large checks on one big
/// segment, n=256 switched about 11,000 times and n=512 over 65,000 (doc sections 76 and 77), each a
/// Windows fiber. Ignored because n=256 is slow in a debug build; run with `--release`.
#[test]
#[ignore]
pub fn a_large_check_does_not_churn_stack_segments() {
    let (proof, stmt) = add_zero_proof(256, 0);
    let before = tatic::kernel::segment_switches();
    ck("n=256", &proof, &stmt);
    let switches = tatic::kernel::segment_switches() - before;
    println!("segment switches in the n=256 check: {switches}");
    assert!(switches < 100, "{switches} stack segment switches in one check");
}

/// Cost of an intern-table hit against building a node, for the hash-consing design (doc section 59):
/// 16 million App nodes over a pool of 16k leaves and 64k distinct (child, child) pairs, built fresh
/// with `Rc::new` against looked up in a pointer-keyed map.
#[test]
#[ignore]
pub fn intern_lookup_vs_rc_new() {
    use std::collections::HashMap;
    use std::hash::{BuildHasherDefault, Hasher};
    #[derive(Default)]
    struct Fx(u64);
    impl Hasher for Fx {
        fn finish(&self) -> u64 {
            self.0.rotate_left(26)
        }
        fn write(&mut self, _: &[u8]) {
            unreachable!()
        }
        fn write_usize(&mut self, x: usize) {
            self.0 = (self.0.rotate_left(5) ^ x as u64).wrapping_mul(0x517c_c1b7_2722_0a95);
        }
    }
    use tatic::kernel::Rc;
    let leaves: Vec<Rc<Expr>> = (0..16384u32).map(|i| Rc::new(Expr::Var(i))).collect();
    let mut state = 12345u64;
    let mut next = move || {
        state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        (state >> 33) as usize
    };
    let pairs: Vec<(usize, usize)> = (0..65536).map(|_| (next() % 16384, next() % 16384)).collect();
    const N: usize = 16_000_000;
    let mut sink = 0usize;
    let t = Instant::now();
    for k in 0..N {
        let (a, b) = pairs[k & 65535];
        let node = Rc::new(Expr::App(leaves[a].clone(), leaves[b].clone()));
        sink += node.loose() as usize;
    }
    let build = t.elapsed();
    let mut table: HashMap<(usize, usize), Rc<Expr>, BuildHasherDefault<Fx>> = HashMap::default();
    let t = Instant::now();
    for k in 0..N {
        let (a, b) = pairs[k & 65535];
        let key = (Rc::as_ptr(&leaves[a]) as usize, Rc::as_ptr(&leaves[b]) as usize);
        let node = table.entry(key).or_insert_with(|| Rc::new(Expr::App(leaves[a].clone(), leaves[b].clone()))).clone();
        sink += node.loose() as usize;
    }
    let intern = t.elapsed();
    println!("INTERN-BENCH (sink {sink}): {N} builds: Rc::new {:?} ({:.0} ns each), intern lookup {:?} ({:.0} ns each); table entries {}", build, build.as_nanos() as f64 / N as f64, intern, intern.as_nanos() as f64 / N as f64, table.len());
}

/// Cost of a lookup in a pointer-keyed table against the table's size (design doc section 72):
/// random hits in a `hashbrown` map whose entries are 40 bytes, like the instantiate memo's.
#[test]
#[ignore]
pub fn table_lookup_cost_by_size() {
    use hashbrown::HashMap;
    let mut x = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = move || {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        x
    };
    for size in [1usize << 14, 1 << 16, 1 << 18, 1 << 20, 1 << 22] {
        let mut m: HashMap<(usize, u64, u32), (usize, usize)> = HashMap::default();
        let keys: Vec<(usize, u64, u32)> = (0..size).map(|_| (next() as usize, next(), 0)).collect();
        for k in &keys {
            m.insert(*k, (1, 2));
        }
        let probes: Vec<usize> = (0..2_000_000).map(|_| next() as usize % size).collect();
        let t = Instant::now();
        let mut s = 0usize;
        for &i in &probes {
            s += m.get(&keys[i]).unwrap().0;
        }
        let d = t.elapsed();
        println!("LOOKUP size={size}: {:.0} ns per hit (sink {s})", d.as_nanos() as f64 / probes.len() as f64);
    }
}

// ---- Division wrapper obligations (design doc section 5): D3 and the equality test it needs.
// `div_s` is abstract: only the wrapper's guard is under test, so its result `r = div_s a b` is a
// variable with a `GoodBv` witness (a Church Bool0 cannot select between Bv values, so the
// wrapper muxes bitwise with and/or/not).

pub fn not_(x: Expr) -> Expr {
    xor(x, t())
}
pub fn mux(c: Expr, x: Expr, y: Expr) -> Expr {
    or(and(c.clone(), x), and(not_(c), y))
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
    let outs = (0..n).map(|i| mux(cond.clone(), bit((min >> i) & 1 == 1), var((n - 1 - i) as u32))).collect();
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

#[test]
pub fn eq_bv_computes_on_literals() {
    for n in [1usize, 4, 8] {
        let ty = pi(bv_ty(n), pi(bv_ty(n), bool0()));
        ck("eq_bv type", &eq_bv(n), &ty.clone());
        let mask = low_bits(n);
        for (x, y) in [(0u128, 0u128), (1, 1), (mask, mask), (0, 1), (1, 0), (mask, 0), (0b101 & mask, 0b100 & mask)] {
            let got = app2(eq_bv(n), lit(n, x), lit(n, y));
            assert!(def_eq(&got, &bit(x == y)), "eq {x} {y} at n={n}");
        }
    }
}

#[test]
pub fn wrapping_div_min_by_minus_one_is_min() {
    for n in [1usize, 2, 4, 8, 32, 64] {
        let _scope = tatic::kernel::InternScope::enter();
        let (min, all) = (1u128 << (n - 1), if n == 128 { u128::MAX } else { (1u128 << n) - 1 });
        let (p, s) = wrap_div_min_proof(n, min, all);
        let t0 = Instant::now();
        ck(&format!("D3 at n={n}"), &p, &s);
        println!("D3 n={n}: checked in {:?}", t0.elapsed());
        // The guard must bite: other operands leave `r` alone, so the same proof is rejected.
        for (a, b) in [(min, all - 1), (min + 1, all), (0, all), (min, 0)] {
            if n >= 2 || (a, b) != (min, 0) {
                let (p2, s2) = wrap_div_min_proof(n, a & all, b & all);
                if (a & all, b & all) != (min, all) {
                    assert!(check(&Ctx::new(), &p2, &s2).is_err(), "D3 must fail for a={a:#x} b={b:#x} at n={n}");
                }
            }
        }
    }
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

#[test]
pub fn to_n_computes_on_good_literals() {
    for n in [1usize, 4, 8] {
        let ty = pi(bv_ty(n), arrow(app(good_bv(n), var(0)), nat_ty()));
        let lift_ty = pi(bv_ty(n), arrow(app(good_bv(n), var(0)), app(good_bv1(n), var(0))));
        ck("lift_good type", &lift_good(n), &lift_ty);
        ck("toN type", &to_n(n), &ty);
        let mask = low_bits(n);
        for v in [0u128, 1, 5 & mask, mask] {
            ck("good_lit", &good_lit(n, v), &app(good_bv(n), lit(n, v)));
            let got = app2(to_n(n), lit(n, v), good_lit(n, v));
            assert!(def_eq(&got, &nat_lit(v)), "toN {v} at n={n}");
            assert!(!def_eq(&got, &nat_lit(v + 1)), "toN {v}+1 must differ at n={n}");
        }
    }
}

/// Whether `sdiv a b` is `Some`: `not (eq b 0 or (eq a MIN and eq b -1))`, a `Bool0`. The `Option` is
/// the pair (this flag, `wrap_div a b (div_s a b)`): a `Bool0` cannot select between `Option` values
/// (design doc section 86), so the flag stands for None/Some.
pub fn sdiv_some(n: usize, a: Expr, b: Expr) -> Expr {
    let min = 1u128 << (n - 1);
    let all = if n == 128 { u128::MAX } else { (1u128 << n) - 1 };
    let overflow = and(app2(eq_bv(n), a, lit(n, min)), app2(eq_bv(n), b.clone(), lit(n, all)));
    not_(or(app2(eq_bv(n), b, lit(n, 0)), overflow))
}

/// D1/D2 on literals: the flag is `false` exactly for `b = 0` and `a = MIN, b = -1`.
#[test]
pub fn sdiv_flag_matches_the_spec_on_literals() {
    for n in [4usize, 8, 32, 64] {
        let _scope = tatic::kernel::InternScope::enter();
        let all = if n == 64 { u64::MAX as u128 } else { (1u128 << n) - 1 };
        let min = 1u128 << (n - 1);
        let samples = [0u128, 1, 2, min - 1, min, min + 1, all - 1, all];
        for &a in &samples {
            for &b in &samples {
                let some = b != 0 && !(a == min && b == all);
                let got = sdiv_some(n, lit(n, a), lit(n, b));
                assert!(def_eq(&got, &bit(some)), "sdiv flag a={a:#x} b={b:#x} n={n}");
                assert!(!def_eq(&got, &bit(!some)), "flag must not be both, a={a:#x} b={b:#x} n={n}");
            }
        }
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
        &move |c, y| arrow(id_t(and(c.clone(), y.clone())), id_t(if left { c } else { y })),
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
        move |x| arrow(id_t(xn(x.clone())), id(bool0(), x, bit(l))),
        // x = true / x = false: equal to `l` (refl), else the hypothesis is `false = true`
        move |v| {
            let h = id_t(xn(bit(v)));
            lam(h.clone(), if v == l { refl(bit(l)) } else if v { sym(&bool0(), &f(), &t(), var(0)) } else { var(0) })
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
    let gxn = |i: usize| apps(if lb(i) { gx_t.clone() } else { gx_f.clone() }, vec![a_at(dh, i), ga_at(dh, i)]);
    let mut gc = vec![good_bit(true)];
    for i in 0..n {
        gc.push(apps(good_and.clone(), vec![chain(dh, i), xn(i), gc[i].clone(), gxn(i)]));
    }
    // peel h : Id(chain_n, true) down to Id(xnor_i, true), then to Id(a_i, l_i)
    let mut h = var(0);
    let mut ps = vec![None; n];
    for k in (1..=n).rev() {
        let args = |gcv: &Expr| vec![chain(dh, k - 1), xn(k - 1), gcv.clone(), gxn(k - 1), h.clone()];
        let hx = apps(peel_r.clone(), args(&gc[k - 1]));
        let h_next = apps(peel_l.clone(), args(&gc[k - 1]));
        let be = if lb(k - 1) { bit_eq_t.clone() } else { bit_eq_f.clone() };
        ps[k - 1] = Some(apps(be, vec![a_at(dh, k - 1), ga_at(dh, k - 1), hx]));
        h = h_next;
    }
    let ps: Vec<Expr> = ps.into_iter().map(|p| p.unwrap()).collect();
    let xs: Vec<Expr> = (0..n).map(|i| a_at(dh, i)).collect();
    let ls: Vec<Expr> = (0..n).map(|i| bit(lb(i))).collect();
    let mut fbody = apps(var(0), (0..n).map(|i| var((n + 1 - i) as u32)).collect());
    fbody = lam(sort(1), lam(karrow(n), fbody));
    for _ in 0..n {
        fbody = lam(bool0(), fbody);
    }
    let concl = cong_n(&bool0(), &bv_ty(n), &fbody, &xs, &ls, ps);
    let mut step = lam(id_t(chain(d, n)), concl);
    for _ in 0..n {
        step = lam(app(good_bool(), var(n as u32 - 1)), step);
    }
    for _ in 0..n {
        step = lam(bool0(), step);
    }
    let big_l = lit(n, stated);
    let claim = |x: Expr| arrow(id_t(app2(eq_bv(n), x.clone(), lit(n, l))), id(bv_ty(n), x, big_l.clone()));
    let motive = lam(bv_ty(n), claim(var(0)));
    let proof = lam(bv_ty(n), lam(app(good_bv(n), var(0)), app2(var(0), motive, step)));
    let stmt = pi(bv_ty(n), arrow(app(good_bv(n), var(0)), claim(var(0))));
    (proof, stmt)
}

#[test]
pub fn eq_with_a_literal_implies_equality_on_good_vectors() {
    // the bit lemmas, against their own types
    for (name, (p, ty)) in [
        ("and_l", and_peel(true)),
        ("and_r", and_peel(false)),
        ("good_and", good_and_lemma()),
        ("bit_t", bit_from_xnor(true)),
        ("bit_f", bit_from_xnor(false)),
        ("gx_t", good_xnor_lit(true)),
        ("gx_f", good_xnor_lit(false)),
    ] {
        ck(name, &p, &ty);
    }
    for n in [1usize, 2, 4, 8, 32] {
        let _scope = tatic::kernel::InternScope::enter();
        let mask = low_bits(n);
        for l in [0u128, 1, 0b1010 & mask, mask, 1u128 << (n - 1)] {
            let (p, s) = eq_lit_sound(n, l, l);
            let t0 = Instant::now();
            ck(&format!("H3 n={n} l={l:#x}"), &p, &s);
            if l == mask {
                println!("H3 n={n}: checked in {:?}", t0.elapsed());
            }
            // Mutation: the conclusion `x = L'` for another literal must be rejected.
            let (p2, s2) = eq_lit_sound(n, l, l ^ 1);
            assert!(check(&Ctx::new(), &p2, &s2).is_err(), "x = L xor 1 must be rejected, n={n} l={l:#x}");
        }
    }
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
    let to_f = cong1(&bool0(), &bv_ty(n), &ff, guard_ab.clone(), f(), h);
    // With the guard false each bit is `mux f m r_i`, which computes to the eta-expansion of `r_i` (and
    // conversion has no eta), so close the gap bit by bit: `r_i = eta r_i` by cases on `GoodBool r_i`.
    let eta = |x: Expr| lam(sort(0), lam(var(0), lam(var(1), app3(shift(&x, 0, 3), var(2), var(1), var(0)))));
    let (e_lemma, _) = bit_lemma(id(bool0(), var(0), eta(var(0))), refl(t()), refl(f()));
    let gr_at = |i: usize| var((d - 1 - (5 + n + i)) as u32);
    let ps: Vec<Expr> = (0..n)
        .map(|i| sym(&bool0(), &r_at(i, d), &eta(r_at(i, d)), app2(e_lemma.clone(), r_at(i, d), gr_at(i))))
        .collect();
    let etas: Vec<Expr> = (0..n).map(|i| eta(r_at(i, d))).collect();
    let rs: Vec<Expr> = (0..n).map(|i| r_at(i, d)).collect();
    let mut tuple = apps(var(0), (0..n).map(|i| var((n + 1 - i) as u32)).collect());
    tuple = lam(sort(1), lam(karrow(n), tuple));
    for _ in 0..n {
        tuple = lam(bool0(), tuple);
    }
    let to_r = cong_n(&bool0(), &bv_ty(n), &tuple, &etas, &rs, ps);
    let f_false = app(ff.clone(), f());
    let mk_r = mk(&rs);
    let step_body = trans_proof(&bv_ty(n), &app(ff.clone(), guard_ab), &f_false, &mk_r, to_f, to_r);
    let mut step = step_body;
    for _ in 0..n {
        step = lam(app(good_bool(), var(n as u32 - 1)), step);
    }
    for _ in 0..n {
        step = lam(bool0(), step);
    }
    // statement pieces at ctx [a, b, h, r]
    let target = |a: Expr, b: Expr, r: Expr| id(bv_ty(n), wrap_div(n, a, b, r.clone()), if claimed { r } else { lit(n, 0) });
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

#[test]
pub fn sdiv_is_none_on_the_guard_and_wrapper_keeps_r_otherwise() {
    for n in [1usize, 2, 4, 8, 32] {
        let _scope = tatic::kernel::InternScope::enter();
        let (_, all) = min_all(n);
        let (p, s) = sdiv_none_if_zero(n, 0);
        ck(&format!("D1 b=0, n={n}"), &p, &s);
        let (p1, s1) = sdiv_none_if_zero(n, 1);
        assert!(check(&Ctx::new(), &p1, &s1).is_err(), "b=1 must not give None, n={n}");
        let (p, s) = sdiv_none_on_overflow(n, all);
        ck(&format!("D1 overflow, n={n}"), &p, &s);
        let (p1, s1) = sdiv_none_on_overflow(n, all ^ 1);
        assert!(check(&Ctx::new(), &p1, &s1).is_err(), "b=-2 must not give None, n={n}");
        let t0 = Instant::now();
        let (p, s) = wrap_div_keeps_r(n, true);
        ck(&format!("D2 payload, n={n}"), &p, &s);
        println!("D2 payload n={n}: checked in {:?}", t0.elapsed());
        let (p1, s1) = wrap_div_keeps_r(n, false);
        assert!(check(&Ctx::new(), &p1, &s1).is_err(), "payload is not 0, n={n}");
    }
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
    let (g_and, _) = good2(&|a, b| and(a, b), &|a, b| a && b);
    let (g_or, _) = good2(&|a, b| or(a, b), &|a, b| a || b);
    let (g_xor, _) = good2(&|a, b| xor(a, b), &|a, b| a != b);
    good_vec(n, if sub { self::sub(n) } else { add(n) }, &move |a, b, ga, gb| {
        let mut c = f();
        let mut gc = good_bit(false);
        let (mut s, mut gs) = (vec![], vec![]);
        for i in 0..n {
            let x = xor(a[i].clone(), b[i].clone());
            let gx = apps(g_xor.clone(), vec![a[i].clone(), b[i].clone(), ga[i].clone(), gb[i].clone()]);
            s.push(xor(x.clone(), c.clone()));
            gs.push(apps(g_xor.clone(), vec![x.clone(), c.clone(), gx.clone(), gc.clone()]));
            // the carry's operands: (a, b, x) for add; (~a, b, ~a ^ b) for the borrow
            let (p, gp) = if sub {
                (xor(a[i].clone(), t()), apps(g_xor.clone(), vec![a[i].clone(), t(), ga[i].clone(), good_bit(true)]))
            } else {
                (a[i].clone(), ga[i].clone())
            };
            let (y, gy) = (b[i].clone(), gb[i].clone());
            let (x2, gx2) = if sub { (xor(p.clone(), y.clone()), apps(g_xor.clone(), vec![p.clone(), y.clone(), gp.clone(), gy.clone()])) } else { (x.clone(), gx) };
            let ab = and(p.clone(), y.clone());
            let g_ab = apps(g_and.clone(), vec![p, y, gp, gy]);
            let cx = and(c.clone(), x2.clone());
            let g_cx = apps(g_and.clone(), vec![c.clone(), x2, gc.clone(), gx2]);
            let nc = or(ab.clone(), cx.clone());
            gc = apps(g_or.clone(), vec![ab, cx, g_ab, g_cx]);
            c = nc;
        }
        (s, gs)
    })
}

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
    let st_b = var((db - 1 - 5) as u32);
    let binders = |mut body: Expr| {
        for _ in 0..n {
            body = lam(app(good_bool(), var(n as u32 - 1)), body);
        }
        for _ in 0..n {
            body = lam(bool0(), body);
        }
        body
    };
    let step_y = binders(apps(st_b, s.into_iter().chain(gs).collect()));
    let a_da = |i: usize| var((da - 1 - (6 + i)) as u32);
    let mka = mk(&(0..n).map(|i| shift(&a_da(i), 0, 1)).collect::<Vec<_>>());
    // under the `y'` binder at depth da + 1: P = var(da - 1 - 4 + 1)
    let motive_y = lam(bv_ty(n), app(var((da - 4) as u32), app2(vec.clone(), mka, var(0))));
    let gy = var((da - 1 - 3) as u32);
    let step_x = binders(app2(gy, motive_y, step_y));
    // under the `x'` binder at depth 7: P = var 2, y = var 5
    let motive_x = lam(bv_ty(n), app(var(2), app2(vec.clone(), var(0), var(5))));
    let body = app2(var(3), motive_x, step_x);
    let proof = lam(bv_ty(n), lam(bv_ty(n), lam(app(good_bv(n), var(1)), lam(app(good_bv(n), var(1)),
        lam(arrow(bv_ty(n), sort(2)), lam(good_bv_step(n), body))))));
    let ty = pi(bv_ty(n), pi(bv_ty(n), arrow(app(good_bv(n), var(1)), arrow(app(good_bv(n), var(0)),
        app(good_bv(n), app2(vec, var(1), var(0)))))));
    (proof, ty)
}

#[test]
pub fn add_preserves_goodness() {
    for (name, op, tab) in [
        ("and", &(|a, b| and(a, b)) as &dyn Fn(Expr, Expr) -> Expr, &(|a: bool, b: bool| a && b) as &dyn Fn(bool, bool) -> bool),
        ("or", &|a, b| or(a, b), &|a, b| a || b),
        ("xor", &|a, b| xor(a, b), &|a, b| a != b),
    ] {
        let (p, ty) = good2(op, tab);
        ck(&format!("good_{name}"), &p, &ty);
    }
    // a wrong truth table must be rejected
    let (p, ty) = good2(&|a, b| and(a, b), &|a, b| a || b);
    assert!(check(&Ctx::new(), &p, &ty).is_err(), "and with the or table must be rejected");
    for n in [1usize, 2, 4, 8, 32] {
        let _scope = tatic::kernel::InternScope::enter();
        let (p, ty) = good_add(n);
        let t0 = Instant::now();
        ck(&format!("good_add n={n}"), &p, &ty);
        println!("GOOD-ADD n={n}: checked in {:?}", t0.elapsed());
    }
}

/// Width scaling of the H3, D2 and `good_add` proofs (design doc section 89).
#[test]
#[ignore]
pub fn bv_lemma_scaling_h3_d2_good_add() {
    for n in [32usize, 64, 128] {
        let _scope = tatic::kernel::InternScope::enter();
        let l = (1u128 << (n - 1)) | 1;
        let l = if n >= 128 { l } else { l & ((1u128 << n) - 1) };
        let t0 = Instant::now();
        let (p, s) = eq_lit_sound(n, l, l);
        let built = t0.elapsed();
        let t1 = Instant::now();
        ck("H3", &p, &s);
        println!("SCALE-H3 n={n}: build {built:?}, check {:?}", t1.elapsed());
        let t0 = Instant::now();
        let (p, s) = wrap_div_keeps_r(n, true);
        let built = t0.elapsed();
        let t1 = Instant::now();
        ck("D2", &p, &s);
        println!("SCALE-D2 n={n}: build {built:?}, check {:?}", t1.elapsed());
        let t0 = Instant::now();
        let (p, s) = good_add(n);
        let built = t0.elapsed();
        let t1 = Instant::now();
        ck("good_add", &p, &s);
        println!("SCALE-GOODADD n={n}: build {built:?}, check {:?}", t1.elapsed());
    }
}

// ---- H4 (design doc section 89): `toN (or a b) = toN a + toN b` when the bit ranges are disjoint.

/// `\a b. \C k. a C (\a_i.. b C (\b_i.. k (op a_0 b_0) .. (op a_(n-1) b_(n-1))))`, like `add` with no carry.
pub fn bitwise(n: usize, op: &dyn Fn(Expr, Expr) -> Expr) -> Expr {
    let d = 4 + 2 * n;
    let v = |pos: usize| var((d - 1 - pos) as u32);
    let outs = (0..n).map(|i| op(v(4 + i), v(4 + n + i))).collect();
    let mut body = apps(v(3), outs);
    for _ in 0..n {
        body = lam(bool0(), body);
    }
    let mut inner = app2(var(n as u32 + 2), var(n as u32 + 1), body);
    for _ in 0..n {
        inner = lam(bool0(), inner);
    }
    lam(bv_ty(n), lam(bv_ty(n), lam(sort(1), lam(karrow(n), app2(var(3), var(1), inner)))))
}
pub fn or_bv(n: usize) -> Expr {
    bitwise(n, &|a, b| or(a, b))
}
pub fn good_or_bv(n: usize) -> (Expr, Expr) {
    let (g_or, _) = good2(&|a, b| or(a, b), &|a, b| a || b);
    good_vec(n, or_bv(n), &move |a, b, ga, gb| {
        let s = (0..n).map(|i| or(a[i].clone(), b[i].clone())).collect();
        let gs = (0..n).map(|i| apps(g_or.clone(), vec![a[i].clone(), b[i].clone(), ga[i].clone(), gb[i].clone()])).collect();
        (s, gs)
    })
}
/// `\P st. st bits.. goods..`: the canonical `GoodBv (mk bits)` from `GoodBool` witnesses.
pub fn good_tuple(bits: &[Expr], goods: &[Expr]) -> Expr {
    let n = bits.len();
    let sh = |e: &Expr| shift(e, 0, 2);
    lam(arrow(bv_ty(n), sort(2)), lam(good_bv_step(n), apps(var(0), bits.iter().chain(goods).map(sh).collect())))
}

/// `(proof, statement)`: for `a` with free low bits `0..k` (higher bits false) and `b` with free high bits
/// `k..n` (lower bits false), `toN (or a b) = toN a + toN b`, each with its canonical witness.
pub fn or_disjoint_proof(n: usize, k: usize, stated_sum_with_a_twice: bool) -> (Expr, Expr) {
    let (g_or_bv, _) = good_or_bv(n);
    // ctx [bit_0..bit_(n-1), g_0..g_(n-1)]
    let d = 2 * n;
    let bit_v = |j: usize| var((d - 1 - j) as u32);
    let good_v = |j: usize| var((d - 1 - (n + j)) as u32);
    let a_bits: Vec<Expr> = (0..n).map(|i| if i < k { bit_v(i) } else { f() }).collect();
    let a_good: Vec<Expr> = (0..n).map(|i| if i < k { good_v(i) } else { good_bit(false) }).collect();
    let b_bits: Vec<Expr> = (0..n).map(|i| if i >= k { bit_v(i) } else { f() }).collect();
    let b_good: Vec<Expr> = (0..n).map(|i| if i >= k { good_v(i) } else { good_bit(false) }).collect();
    // `mk` shifts its arguments by 2; `good_tuple` does too, so both take the operands at depth d
    let (x, y) = (mk(&a_bits), mk(&b_bits));
    let (gx, gy) = (good_tuple(&a_bits, &a_good), good_tuple(&b_bits, &b_good));
    let gor = apps(g_or_bv, vec![x.clone(), y.clone(), gx.clone(), gy.clone()]);
    let lhs = app2(to_n(n), app2(or_bv(n), x.clone(), y.clone()), gor);
    let (tx, ty) = (app2(to_n(n), x.clone(), gx), app2(to_n(n), y, gy));
    let rhs = if stated_sum_with_a_twice { app2(nat_add(), tx.clone(), tx) } else { app2(nat_add(), tx, ty) };
    let mut proof = refl(lhs.clone());
    let mut stmt = id(nat_ty(), lhs, rhs);
    for _ in 0..n {
        proof = lam(app(good_bool(), var(n as u32 - 1)), proof);
        stmt = pi(app(good_bool(), var(n as u32 - 1)), stmt);
    }
    for _ in 0..n {
        proof = lam(bool0(), proof);
        stmt = pi(bool0(), stmt);
    }
    (proof, stmt)
}

#[test]
pub fn or_of_disjoint_vectors_adds_in_to_n() {
    for n in [2usize, 4, 8] {
        let _scope = tatic::kernel::InternScope::enter();
        for k in 1..n {
            let (p, s) = or_disjoint_proof(n, k, false);
            ck(&format!("H4 n={n} k={k}"), &p, &s);
            let (p2, s2) = or_disjoint_proof(n, k, true);
            assert!(check(&Ctx::new(), &p2, &s2).is_err(), "toN a + toN a must be rejected, n={n} k={k}");
        }
    }
}

/// H4 by width, half-and-half split (design doc section 89). Stops at n=14: `nat_lit(2^i)` is unary, so the
/// terms double in size per bit; n=16 had not finished after 10 minutes.
#[test]
#[ignore]
pub fn or_disjoint_scaling() {
    for n in [6usize, 8, 10, 12, 14] {
        let _scope = tatic::kernel::InternScope::enter();
        let t0 = Instant::now();
        let (p, s) = or_disjoint_proof(n, n / 2, false);
        let built = t0.elapsed();
        let t1 = Instant::now();
        ck("H4", &p, &s);
        println!("SCALE-H4 n={n}: build {built:?}, check {:?}", t1.elapsed());
    }
}

// ---- Associativity of `add` (search note section 11). The two sides keep separate carry states, (c, d) for
// `add (add x y) z` and (e, f) for `add x (add y z)`. Only the *total* matters: c + d = e + f, encoded as the
// pair (xor c d, and c d). Each side's output bit and next pair is a fixed function of (a, b, z, xor, and)
// (a 5-variable case analysis with `refl` leaves, no hypotheses), so the two sides agree by `cong_n` on the
// two equalities carried from the previous bit.

/// Closed `Pi v_0..v_(k-1). GoodBool v_0 -> .. -> GoodBool v_(k-1) -> body(v)`, by case analysis on all `k`
/// bits; `leaf(values)` proves `body(literal bits)`.
pub fn lemma_n(k: usize, body: &dyn Fn(&[Expr]) -> Expr, leaf: &dyn Fn(&[bool]) -> Expr) -> (Expr, Expr) {
    fn elim(k: usize, body: &dyn Fn(&[Expr]) -> Expr, leaf: &dyn Fn(&[bool]) -> Expr, vals: &mut Vec<Option<bool>>) -> Expr {
        let Some(j) = vals.iter().position(|v| v.is_none()) else {
            return leaf(&vals.iter().map(|v| v.unwrap()).collect::<Vec<_>>());
        };
        // inside the motive binder, v_m is var(2k - m) (shifted once)
        let args: Vec<Expr> = (0..k)
            .map(|m| if m == j { var(0) } else { vals[m].map_or_else(|| var((2 * k - m) as u32), bit) })
            .collect();
        let motive = lam(bool0(), body(&args));
        vals[j] = Some(true);
        let on_true = elim(k, body, leaf, vals);
        vals[j] = Some(false);
        let on_false = elim(k, body, leaf, vals);
        vals[j] = None;
        app3(var((k - 1 - j) as u32), motive, on_true, on_false)
    }
    let mut proof = elim(k, body, leaf, &mut vec![None; k]);
    for _ in 0..k {
        proof = lam(app(good_bool(), var(k as u32 - 1)), proof);
    }
    for _ in 0..k {
        proof = lam(bool0(), proof);
    }
    let mut ty = body(&(0..k).map(|m| var((2 * k - 1 - m) as u32)).collect::<Vec<_>>());
    for _ in 0..k {
        ty = pi(app(good_bool(), var(k as u32 - 1)), ty);
    }
    for _ in 0..k {
        ty = pi(bool0(), ty);
    }
    (proof, ty)
}

/// The reduced ordered decision diagram of a truth table over `nv` variables: nodes `(level, hi, lo)` with ids from 2
/// (0 is false, 1 is true), and the root id. A node whose two children coincide is skipped.
pub struct TabBdd {
    pub nodes: Vec<(usize, usize, usize)>,
    pub root: usize,
}

pub fn tab_bdd(nv: usize, tab: &dyn Fn(&[bool]) -> bool) -> TabBdd {
    fn go(nv: usize, tab: &dyn Fn(&[bool]) -> bool, fixed: &mut Vec<bool>, nodes: &mut Vec<(usize, usize, usize)>, unique: &mut std::collections::HashMap<(usize, usize, usize), usize>) -> usize {
        if fixed.len() == nv {
            return tab(fixed) as usize;
        }
        let level = fixed.len();
        fixed.push(true);
        let hi = go(nv, tab, fixed, nodes, unique);
        fixed.pop();
        fixed.push(false);
        let lo = go(nv, tab, fixed, nodes, unique);
        fixed.pop();
        if hi == lo {
            return hi;
        }
        *unique.entry((level, hi, lo)).or_insert_with(|| {
            nodes.push((level, hi, lo));
            nodes.len() + 1
        })
    }
    let mut nodes = vec![];
    let root = go(nv, tab, &mut vec![], &mut nodes, &mut Default::default());
    TabBdd { nodes, root }
}

/// A truth table over `vars` as a closed lambda applied to them (so large argument expressions are not duplicated
/// once per row), whose body is the table's reduced decision diagram as nested `mux`es.
pub fn table_app(vars: &[Expr], tab: &dyn Fn(&[bool]) -> bool) -> Expr {
    let k = vars.len();
    let d = tab_bdd(k, tab);
    let bv: Vec<Expr> = (0..k).map(|i| var((k - 1 - i) as u32)).collect();
    let mut exprs: Vec<Expr> = vec![f(), t()];
    for &(level, hi, lo) in &d.nodes {
        exprs.push(mux(bv[level].clone(), exprs[hi].clone(), exprs[lo].clone()));
    }
    let mut body = exprs[d.root].clone();
    for _ in 0..k {
        body = lam(bool0(), body);
    }
    apps(body, vars.to_vec())
}

/// The Shannon expansion of a truth table over `vars`.
pub fn table_expr(vars: &[Expr], tab: &dyn Fn(&[bool]) -> bool) -> Expr {
    fn go(vars: &[Expr], tab: &dyn Fn(&[bool]) -> bool, fixed: &mut Vec<bool>) -> Expr {
        if fixed.len() == vars.len() {
            return bit(tab(fixed));
        }
        let c = vars[fixed.len()].clone();
        fixed.push(true);
        let hi = go(vars, tab, fixed);
        fixed.pop();
        fixed.push(false);
        let lo = go(vars, tab, fixed);
        fixed.pop();
        mux(c, hi, lo)
    }
    go(vars, tab, &mut vec![])
}

pub fn sum3(a: Expr, b: Expr, c: Expr) -> Expr {
    xor(xor(a, b), c)
}
pub fn maj(a: Expr, b: Expr, c: Expr) -> Expr {
    or(and(a.clone(), b.clone()), and(c, xor(a, b)))
}
/// Table over `[a, b, z, p, q]` (state total `p + 2q`): the output bit (0), the next `p` (1) or next `q` (2).
pub fn assoc_table(which: usize, v: &[bool]) -> bool {
    let m = v[0] as u32 + v[1] as u32 + v[2] as u32 + v[3] as u32 + 2 * v[4] as u32;
    let next = m / 2;
    match which {
        0 => m % 2 == 1,
        1 => next % 2 == 1,
        _ => next >= 2,
    }
}
/// The left or right side's output bit (0), next `xor` (1) or next `and` (2) of its two carries, from `[a, b, z, c, d]`
/// (for the right side `c`, `d` are its `e`, `f`).
pub fn assoc_side(left: bool, which: usize, v: &[Expr]) -> Expr {
    let (a, b, z, c, d) = (v[0].clone(), v[1].clone(), v[2].clone(), v[3].clone(), v[4].clone());
    let (out, c2, d2) = if left {
        let s = sum3(a.clone(), b.clone(), c.clone());
        (sum3(s.clone(), z.clone(), d.clone()), maj(a, b, c), maj(s, z, d))
    } else {
        let t = sum3(b.clone(), z.clone(), c.clone());
        (sum3(a.clone(), t.clone(), d.clone()), maj(b, z, c), maj(a, t, d))
    };
    match which {
        0 => out,
        1 => xor(c2, d2),
        _ => and(c2, d2),
    }
}
/// `G_which(a, b, z, p, q)`.
pub fn assoc_g(which: usize, v: &[Expr]) -> Expr {
    table_expr(v, &|bits| assoc_table(which, bits))
}

/// A `Bool0` expression with its `GoodBool` witness.
#[derive(Clone)]
pub struct Gb {
    pub e: Expr,
    pub g: Expr,
}
pub struct GoodOps {
    pub and: Expr,
    pub or: Expr,
    pub xor: Expr,
}
impl GoodOps {
    pub fn new() -> GoodOps {
        GoodOps {
            and: good2(&|a, b| and(a, b), &|a, b| a && b).0,
            or: good2(&|a, b| or(a, b), &|a, b| a || b).0,
            xor: good2(&|a, b| xor(a, b), &|a, b| a != b).0,
        }
    }
    pub fn go(&self, w: &Expr, e: Expr, x: &Gb, y: &Gb) -> Gb {
        Gb { g: apps(w.clone(), vec![x.e.clone(), y.e.clone(), x.g.clone(), y.g.clone()]), e }
    }
    pub fn and(&self, x: &Gb, y: &Gb) -> Gb {
        self.go(&self.and, and(x.e.clone(), y.e.clone()), x, y)
    }
    pub fn or(&self, x: &Gb, y: &Gb) -> Gb {
        self.go(&self.or, or(x.e.clone(), y.e.clone()), x, y)
    }
    pub fn xor(&self, x: &Gb, y: &Gb) -> Gb {
        self.go(&self.xor, xor(x.e.clone(), y.e.clone()), x, y)
    }
    pub fn sum3(&self, a: &Gb, b: &Gb, c: &Gb) -> Gb {
        let ab = self.xor(a, b);
        self.xor(&ab, c)
    }
    pub fn maj(&self, a: &Gb, b: &Gb, c: &Gb) -> Gb {
        let (ab, x) = (self.and(a, b), self.xor(a, b));
        let cx = self.and(c, &x);
        self.or(&ab, &cx)
    }
}

/// `(proof, statement)` of `Pi x y z. GoodBv x -> GoodBv y -> GoodBv z -> Id(Bv_n, add (add x y) z, add x (add y z))`.
/// `wrong` states `add x (add y y)` on the right instead, which the proof must not check against.
pub fn add_assoc_proof(n: usize, wrong: bool) -> (Expr, Expr) {
    // six lemmas, by (left, which) over [a, b, z, c, d]: Id(F(c, d), G_which(a, b, z, xor c d, and c d))
    let lemma = |left: bool, which: usize| {
        lemma_n(
            5,
            &move |v| {
                let p = xor(v[3].clone(), v[4].clone());
                let q = and(v[3].clone(), v[4].clone());
                id(bool0(), assoc_side(left, which, v), assoc_g(which, &[v[0].clone(), v[1].clone(), v[2].clone(), p, q]))
            },
            &move |bits| refl(assoc_side(left, which, &bits.iter().map(|b| bit(*b)).collect::<Vec<_>>())),
        )
        .0
    };
    let lem: Vec<Vec<Expr>> = [true, false].iter().map(|&l| (0..3).map(|w| lemma(l, w)).collect()).collect();
    let gops = GoodOps::new();
    // ctx: x y z gx gy gz | a.. ga.. | b.. gb.. | z.. gz..
    let d1 = 6 + 2 * n;
    let d2 = 6 + 4 * n;
    let d3 = 6 + 6 * n;
    let at = |d: usize, pos: usize| var((d - 1 - pos) as u32);
    let a = |i: usize| at(d3, 6 + i);
    let ga = |i: usize| at(d3, 6 + n + i);
    let b = |i: usize| at(d3, 6 + 2 * n + i);
    let gb = |i: usize| at(d3, 6 + 3 * n + i);
    let z = |i: usize| at(d3, 6 + 4 * n + i);
    let gz = |i: usize| at(d3, 6 + 5 * n + i);
    let bl = bool0();
    let tr = |x: &Expr, y: &Expr, w: &Expr, p: Expr, q: Expr| trans_proof(&bl, x, y, w, p, q);
    let false_gb = Gb { e: f(), g: good_bit(false) };
    let (mut cl, mut dl, mut er, mut fr) = (false_gb.clone(), false_gb.clone(), false_gb.clone(), false_gb);
    let mut ip = refl(xor(f(), f()));
    let mut iq = refl(and(f(), f()));
    let (mut s1, mut s2, mut e) = (vec![], vec![], vec![]);
    for i in 0..n {
        let (ab, bb, zb) = (Gb { e: a(i), g: ga(i) }, Gb { e: b(i), g: gb(i) }, Gb { e: z(i), g: gz(i) });
        let (pl, ql) = (xor(cl.e.clone(), dl.e.clone()), and(cl.e.clone(), dl.e.clone()));
        let (pr, qr) = (xor(er.e.clone(), fr.e.clone()), and(er.e.clone(), fr.e.clone()));
        let abz = [a(i), b(i), z(i)];
        let inst = |left: bool, which: usize, c: &Gb, d: &Gb| {
            apps(lem[if left { 0 } else { 1 }][which].clone(), vec![
                a(i), b(i), z(i), c.e.clone(), d.e.clone(), ga(i), gb(i), gz(i), c.g.clone(), d.g.clone(),
            ])
        };
        let g_at = |which: usize, p: Expr, q: Expr| assoc_g(which, &[abz[0].clone(), abz[1].clone(), abz[2].clone(), p, q]);
        // Id(G(left state), G(right state)) from the two carried equalities
        let link = |which: usize, ip: &Expr, iq: &Expr| {
            let fmap = lam(bl.clone(), lam(bl.clone(), assoc_g(which, &[shift(&abz[0], 0, 2), shift(&abz[1], 0, 2), shift(&abz[2], 0, 2), var(1), var(0)])));
            cong_n(&bl, &bl, &fmap, &[pl.clone(), ql.clone()], &[pr.clone(), qr.clone()], vec![ip.clone(), iq.clone()])
        };
        // (F_left, F_right, proof of Id(F_left, F_right)) for `which`
        let eq = |which: usize| {
            let fl = assoc_side(true, which, &[abz[0].clone(), abz[1].clone(), abz[2].clone(), cl.e.clone(), dl.e.clone()]);
            let frr = assoc_side(false, which, &[abz[0].clone(), abz[1].clone(), abz[2].clone(), er.e.clone(), fr.e.clone()]);
            let (gl, gr) = (g_at(which, pl.clone(), ql.clone()), g_at(which, pr.clone(), qr.clone()));
            let right_back = sym(&bl, &frr, &gr, inst(false, which, &er, &fr));
            let mid = tr(&gl, &gr, &frr, link(which, &ip, &iq), right_back);
            let proof = tr(&fl, &gl, &frr, inst(true, which, &cl, &dl), mid);
            (fl, frr, proof)
        };
        let (fl0, fr0, p_out) = eq(0);
        let (_, _, p_p) = eq(1);
        let (_, _, p_q) = eq(2);
        s1.push(fl0);
        s2.push(fr0);
        e.push(p_out);
        ip = p_p;
        iq = p_q;
        let s = gops.sum3(&ab, &bb, &cl);
        let (ncl, ndl) = (gops.maj(&ab, &bb, &cl), gops.maj(&s, &zb, &dl));
        let t = gops.sum3(&bb, &zb, &er);
        let (ner, nfr) = (gops.maj(&bb, &zb, &er), gops.maj(&ab, &t, &fr));
        cl = ncl;
        dl = ndl;
        er = ner;
        fr = nfr;
    }
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
    let step_z = binders(cong_n(&bool0(), &bv_ty(n), &fbody, &s1, &s2, e));
    let ad = add(n);
    let claim = |x: Expr, y: Expr, zz: Expr| {
        let rhs_z = if wrong { y.clone() } else { zz.clone() };
        id(bv_ty(n), app2(ad.clone(), app2(ad.clone(), x.clone(), y.clone()), zz), app2(ad.clone(), x, app2(ad.clone(), y, rhs_z)))
    };
    let mk_at = |d: usize, first: usize, extra: i32| mk(&(0..n).map(|i| shift(&at(d, first + i), 0, extra)).collect::<Vec<_>>());
    // at depth d2: eliminate gz into a motive over z'
    let motive_z = lam(bv_ty(n), claim(mk_at(d2, 6, 1), mk_at(d2, 6 + 2 * n, 1), var(0)));
    let step_y = binders(app2(at(d2, 5), motive_z, step_z));
    // at depth d1: eliminate gy into a motive over y'
    let motive_y = lam(bv_ty(n), claim(mk_at(d1, 6, 1), var(0), shift(&at(d1, 2), 0, 1)));
    let step_x = binders(app2(at(d1, 4), motive_y, step_y));
    let motive_x = lam(bv_ty(n), claim(var(0), var(5), var(4)));
    let body = app2(var(2), motive_x, step_x);
    let g = |v: u32| app(good_bv(n), var(v));
    let proof = lam(bv_ty(n), lam(bv_ty(n), lam(bv_ty(n), lam(g(2), lam(g(2), lam(g(2), body))))));
    let stmt = pi(bv_ty(n), pi(bv_ty(n), pi(bv_ty(n), pi(g(2), pi(g(2), pi(g(2), claim(var(5), var(4), var(3))))))));
    (proof, stmt)
}

#[test]
pub fn add_is_associative_on_symbolic_good_vectors() {
    for n in [1usize, 2, 4] {
        let (p, s) = add_assoc_proof(n, false);
        ck(&format!("add assoc n={n}"), &p, &s);
        let (p, s) = add_assoc_proof(n, true);
        assert!(check(&Ctx::new(), &p, &s).is_err(), "add (add x y) z = add x (add y y) must be rejected at n={n}");
    }
}

// ---- `add x (xor x -1) = -1` (x + ~x), a carry that stays false (search note section 12).

/// `(proof, statement)` of `Pi x. GoodBv x -> Id(Bv_n, add x (xor x -1), -1)`; `wrong` states `= 0` instead.
pub fn add_not_proof(n: usize, wrong: bool) -> (Expr, Expr) {
    let nb = |a: Expr| xor(a, t());
    let carry = move |a: Expr, c: Expr| or(and(a.clone(), nb(a.clone())), and(c, xor(a.clone(), nb(a))));
    let sum = move |a: Expr, c: Expr| xor(xor(a.clone(), nb(a)), c);
    let (p1, _) = bit_lemma(id(bool0(), sum(var(0), f()), t()), refl(t()), refl(t()));
    let (p2, _) = bit_lemma(id(bool0(), carry(var(0), f()), f()), refl(f()), refl(f()));
    // ctx of the step body: [x, g, a_0..a_(n-1), ga_0..ga_(n-1)]
    let d = 2 + 2 * n;
    let a = |i: usize| var((d - 1 - (2 + i)) as u32);
    let ga = |i: usize| var((d - 1 - (2 + n + i)) as u32);
    let mut c = vec![f()];
    let mut pc: Vec<Option<Expr>> = vec![None];
    for i in 0..n {
        let next = carry(a(i), c[i].clone());
        let to_false = app2(p2.clone(), a(i), ga(i));
        let proof = match &pc[i] {
            None => to_false,
            Some(pci) => {
                let fmap = lam(bool0(), carry(shift(&a(i), 0, 1), var(0)));
                let rewritten = cong1(&bool0(), &bool0(), &fmap, c[i].clone(), f(), pci.clone());
                trans_proof(&bool0(), &next, &carry(a(i), f()), &f(), rewritten, to_false)
            }
        };
        c.push(next);
        pc.push(Some(proof));
    }
    let (mut s, mut e) = (vec![], vec![]);
    for i in 0..n {
        let s_i = sum(a(i), c[i].clone());
        let to_t = app2(p1.clone(), a(i), ga(i));
        let proof = match &pc[i] {
            None => to_t,
            Some(pci) => {
                let fmap = lam(bool0(), sum(shift(&a(i), 0, 1), var(0)));
                let rewritten = cong1(&bool0(), &bool0(), &fmap, c[i].clone(), f(), pci.clone());
                trans_proof(&bool0(), &s_i, &sum(a(i), f()), &t(), rewritten, to_t)
            }
        };
        s.push(s_i);
        e.push(proof);
    }
    let ys: Vec<Expr> = (0..n).map(|_| t()).collect();
    let mut fbody = apps(var(0), (0..n).map(|i| var((n + 1 - i) as u32)).collect());
    fbody = lam(sort(1), lam(karrow(n), fbody));
    for _ in 0..n {
        fbody = lam(bool0(), fbody);
    }
    let mut step = cong_n(&bool0(), &bv_ty(n), &fbody, &s, &ys, e);
    for _ in 0..n {
        step = lam(app(good_bool(), var(n as u32 - 1)), step);
    }
    for _ in 0..n {
        step = lam(bool0(), step);
    }
    let ones = lit(n, low_bits(n));
    let rhs = if wrong { lit(n, 0) } else { ones.clone() };
    let xv = bitwise(n, &|p, q| xor(p, q));
    let claim = |x: Expr| id(bv_ty(n), app2(add(n), x.clone(), app2(xv.clone(), x, ones.clone())), rhs.clone());
    let motive = lam(bv_ty(n), claim(var(0)));
    let proof = lam(bv_ty(n), lam(app(good_bv(n), var(0)), app2(var(0), motive, step)));
    let stmt = pi(bv_ty(n), arrow(app(good_bv(n), var(0)), claim(var(0))));
    (proof, stmt)
}

#[test]
pub fn add_of_x_and_not_x_is_all_ones() {
    for n in [1usize, 2, 4, 8] {
        let (p, s) = add_not_proof(n, false);
        ck(&format!("add x (xor x -1) = -1 at n={n}"), &p, &s);
        let (p, s) = add_not_proof(n, true);
        assert!(check(&Ctx::new(), &p, &s).is_err(), "... = 0 must be rejected at n={n}");
    }
}

// ---- Conjecture miner (design note 2026-10-01-search-execution-blend-design.md, sections 7-9).
// Terms over x, y (and z) are *run* on every tuple of n-bit literals by the kernel (`normalize`); terms with
// the same results are conjectured equal; each conjecture is then *checked*: by the matching library
// generator, or by a generic builder (`bitwise_law`) that has no template for the particular lemma.
