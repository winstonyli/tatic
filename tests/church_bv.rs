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
    ripple(n, false)
}
/// `a - b` (mod 2^n) as a ripple-borrow chain: the same circuit with the borrow `maj(~a, b, borrow)` as carry.
fn sub(n: usize) -> Expr {
    ripple(n, true)
}
/// `lt_u a b` as a one-bit vector (a `Bool0` result would live one universe below the claims about it): the final
/// borrow of the ripple-borrow chain of `a - b`, set iff `a < b` as unsigned numbers.
fn lt_u(n: usize) -> Expr {
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
fn ripple_carry(sub: bool, a: Expr, b: Expr, c: Expr, x: Expr) -> Expr {
    if sub {
        let na = xor(a, t());
        or(and(na.clone(), b.clone()), and(c, xor(na, b)))
    } else {
        or(and(a, b), and(c, x))
    }
}
fn ripple(n: usize, sub: bool) -> Expr {
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
    add_identity_proof_over(n, rhs_lit, left, add)
}

/// Same, with the statement stated over `adder` (`add` or `add_shared`); the proof body is unchanged,
/// so `adder`'s result must be convertible to the inlined-carry tuple the proof builds.
fn add_identity_proof_over(n: usize, rhs_lit: u128, left: bool, adder: fn(usize) -> Expr) -> (Expr, Expr) {
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
    let sum = |x: Expr, r: Expr| if left { app2(adder(n), r, x) } else { app2(adder(n), x, r) };
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

/// Scaling gate: the `add x 0 = x` proof's size (nodes counted once per allocation) must keep growing
/// by no more than 4.5x per doubling of the width, and stay under a fixed size at n=64. Both were
/// breached by an unshared shift in `cong_n`/`trans_proof` (design doc sections 54-56: 8x per doubling,
/// 1.58M nodes at n=64, against 3.0x and 288k now). A new proof builder that copies where it should
/// share fails here, not months later in a timing. Check-time visit counts are gated by hand with
/// `walk_counts_on_hard_queries` (needs the `record-defeq` feature).
#[test]
fn add_zero_proof_size_scales_gently() {
    let size = |n: usize| tatic::kernel::term_sizes(&add_zero_proof(n, 0).0).0;
    let (s16, s32, s64) = (size(16), size(32), size(64));
    assert!(s32 as f64 / s16 as f64 <= 4.5, "n=16 -> 32: {s16} -> {s32} nodes");
    assert!(s64 as f64 / s32 as f64 <= 4.5, "n=32 -> 64: {s32} -> {s64} nodes");
    assert!(s64 <= 400_000, "n=64: {s64} nodes");
}

/// Size of the generated proof by width, without checking it.
#[test]
#[ignore]
fn proof_size_scaling() {
    for n in [16usize, 32, 64, 128, 256] {
        let (proof, _) = add_zero_proof(n, 0);
        println!("PROOF-SIZE n={n}: dag={}", tatic::kernel::term_sizes(&proof).0);
    }
}

/// Growth of the universal lemma's check time with width (machine load varies; indicative only).
#[test]
#[ignore]
fn add_zero_lemma_scaling() {
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
fn add_zero_lemma_scaling_scoped() {
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
fn add_comm_scaling() {
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
fn add_comm_rejection_probe() {
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
fn add_comm_scaling_scoped() {
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
fn add_shared_zero_is_the_identity_on_a_symbolic_good_vector() {
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
fn add_shared_zero_scaling() {
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
fn replay_defeq_queries() {
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
fn walk_counts_on_hard_queries() {
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
fn whole_check_time() {
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
fn profile_add_zero_n64() {
    let (proof, stmt) = add_zero_proof(64, 0);
    ck("profile n=64", &proof, &stmt);
}

/// As `profile_add_zero_n64`, at n=128.
#[test]
#[ignore]
fn profile_add_zero_n128() {
    let (proof, stmt) = add_zero_proof(128, 0);
    ck("profile n=128", &proof, &stmt);
}

/// As `profile_add_zero_n64`, at n=256.
#[test]
#[ignore]
fn profile_add_zero_n256() {
    let (proof, stmt) = add_zero_proof(256, 0);
    ck("profile n=256", &proof, &stmt);
}

/// As `profile_add_zero_n64`, at n=512.
#[test]
#[ignore]
fn profile_add_zero_n512() {
    let (proof, stmt) = add_zero_proof(512, 0);
    ck("profile n=512", &proof, &stmt);
}

/// Build and check the n=256 / n=512 lemma inside one `InternScope`, for profiling the scoped check
/// alone per width (`SAMPLY.md`; the profiling task passes no environment, so one test per width).
fn profile_scoped(n: usize) {
    let _scope = tatic::kernel::InternScope::enter();
    let (proof, stmt) = add_zero_proof(n, 0);
    ck("profile scoped", &proof, &stmt);
}

/// As `profile_scoped_n512`, on a thread with a 1 GiB stack, so `grow` never needs a new segment.
#[test]
#[ignore]
fn profile_scoped_n512_big_stack() {
    std::thread::Builder::new().stack_size(1 << 30).spawn(|| profile_scoped(512)).unwrap().join().unwrap();
}

#[test]
#[ignore]
fn profile_scoped_n256() {
    profile_scoped(256);
}

#[test]
#[ignore]
fn profile_scoped_n512() {
    profile_scoped(512);
}

/// A large check must not churn stack segments: before `check_in` ran large checks on one big
/// segment, n=256 switched about 11,000 times and n=512 over 65,000 (doc sections 76 and 77), each a
/// Windows fiber. Ignored because n=256 is slow in a debug build; run with `--release`.
#[test]
#[ignore]
fn a_large_check_does_not_churn_stack_segments() {
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
fn intern_lookup_vs_rc_new() {
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
fn table_lookup_cost_by_size() {
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

fn not_(x: Expr) -> Expr {
    xor(x, t())
}
fn mux(c: Expr, x: Expr, y: Expr) -> Expr {
    or(and(c.clone(), x), and(not_(c), y))
}
/// `\a b. a Bool0 (\a_i. b Bool0 (\b_i. and_i xnor(a_i, b_i)))`, closed, of type `Bv_n -> Bv_n -> Bool0`.
fn eq_bv(n: usize) -> Expr {
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
fn wrap_div(n: usize, a: Expr, b: Expr, r: Expr) -> Expr {
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
fn wrap_div_min_proof(n: usize, a: u128, b: u128) -> (Expr, Expr) {
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
fn eq_bv_computes_on_literals() {
    for n in [1usize, 4, 8] {
        let ty = pi(bv_ty(n), pi(bv_ty(n), bool0()));
        ck("eq_bv type", &eq_bv(n), &ty.clone());
        let mask = (1u128 << n) - 1;
        for (x, y) in [(0u128, 0u128), (1, 1), (mask, mask), (0, 1), (1, 0), (mask, 0), (0b101 & mask, 0b100 & mask)] {
            let got = app2(eq_bv(n), lit(n, x), lit(n, y));
            assert!(def_eq(&got, &bit(x == y)), "eq {x} {y} at n={n}");
        }
    }
}

#[test]
fn wrapping_div_min_by_minus_one_is_min() {
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
fn nat_ty() -> Expr {
    pi(sort(0), pi(var(0), pi(arrow(var(1), var(1)), var(2))))
}
fn nat_lit(k: u128) -> Expr {
    let mut body = var(1);
    for _ in 0..k {
        body = app(var(0), body);
    }
    lam(sort(0), lam(var(0), lam(arrow(var(1), var(1)), body)))
}
/// `\a b. \C z s. a C (b C z s) s`
fn nat_add() -> Expr {
    lam(nat_ty(), lam(nat_ty(), lam(sort(0), lam(var(0), lam(arrow(var(1), var(1)),
        app3(var(4), var(2), app3(var(3), var(2), var(1), var(0)), var(0)))))))
}
/// `GoodBv` with the motive in Sort1 (so it can eliminate into `Nat`): `Pi P:(Bv_n -> Sort1). step -> P x`.
fn good_bv1(n: usize) -> Expr {
    lam(bv_ty(n), pi(arrow(bv_ty(n), sort(1)), pi(good_bv_step(n), app(var(1), var(2)))))
}
/// `\x g. g good_bv1 (\a.. ga.. P s. s a.. ga..)`, of type `Pi x. GoodBv x -> GoodBv1 x`: the Sort2
/// witness gives the Sort1 one, by eliminating into `GoodBv1` itself (a Sort2 type).
fn lift_good(n: usize) -> Expr {
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
fn to_n(n: usize) -> Expr {
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
fn good_lit(n: usize, v: u128) -> Expr {
    let bit_good = |b: bool| lam(arrow(bool0(), sort(1)), lam(app(var(0), t()), lam(app(var(1), f()), var(if b { 1 } else { 0 }))));
    let mut args: Vec<Expr> = (0..n).map(|i| bit((v >> i) & 1 == 1)).collect();
    args.extend((0..n).map(|i| bit_good((v >> i) & 1 == 1)));
    lam(arrow(bv_ty(n), sort(2)), lam(good_bv_step(n), apps(var(0), args)))
}

#[test]
fn to_n_computes_on_good_literals() {
    for n in [1usize, 4, 8] {
        let ty = pi(bv_ty(n), arrow(app(good_bv(n), var(0)), nat_ty()));
        let lift_ty = pi(bv_ty(n), arrow(app(good_bv(n), var(0)), app(good_bv1(n), var(0))));
        ck("lift_good type", &lift_good(n), &lift_ty);
        ck("toN type", &to_n(n), &ty);
        let mask = (1u128 << n) - 1;
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
fn sdiv_some(n: usize, a: Expr, b: Expr) -> Expr {
    let min = 1u128 << (n - 1);
    let all = if n == 128 { u128::MAX } else { (1u128 << n) - 1 };
    let overflow = and(app2(eq_bv(n), a, lit(n, min)), app2(eq_bv(n), b.clone(), lit(n, all)));
    not_(or(app2(eq_bv(n), b, lit(n, 0)), overflow))
}

/// D1/D2 on literals: the flag is `false` exactly for `b = 0` and `a = MIN, b = -1`.
#[test]
fn sdiv_flag_matches_the_spec_on_literals() {
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
fn good_bit(b: bool) -> Expr {
    lam(arrow(bool0(), sort(1)), lam(app(var(0), t()), lam(app(var(1), f()), var(if b { 1 } else { 0 }))))
}
/// Closed `Pi a b. GoodBool a -> GoodBool b -> body(a, b)` by case analysis on both; `leaf(va, vb)` proves
/// `body(lit va, lit vb)` (it must be a closed term).
fn lemma2(body: &dyn Fn(Expr, Expr) -> Expr, leaf: &dyn Fn(bool, bool) -> Expr) -> (Expr, Expr) {
    // ctx [a, b, ga, gb]; eliminating `a` under a motive binder puts `b` at var 3
    let elim_b = |va: bool| app3(var(0), lam(bool0(), body(bit(va), var(0))), leaf(va, true), leaf(va, false));
    let proof_body = app3(var(1), lam(bool0(), body(var(0), var(3))), elim_b(true), elim_b(false));
    let proof = lam(bool0(), lam(bool0(), lam(app(good_bool(), var(1)), lam(app(good_bool(), var(1)), proof_body))));
    let ty = pi(bool0(), pi(bool0(), pi(app(good_bool(), var(1)), pi(app(good_bool(), var(1)), body(var(3), var(2))))));
    (proof, ty)
}
fn id_t(x: Expr) -> Expr {
    id(bool0(), x, t())
}
/// `\h. h` against a hypothesis `Id(Bool0, v, true)` whose `v` computes to `false`, or `refl`.
fn hyp_or_refl(h_ty: Expr, trivial: bool) -> Expr {
    lam(h_ty, if trivial { refl(t()) } else { var(0) })
}
/// `(proof, type)` of `Pi c y. Good c -> Good y -> Id(and c y, true) -> Id(c, true)` (`left`) or `-> Id(y, true)`.
fn and_peel(left: bool) -> (Expr, Expr) {
    lemma2(
        &move |c, y| arrow(id_t(and(c.clone(), y.clone())), id_t(if left { c } else { y })),
        &move |a, b| hyp_or_refl(id_t(and(bit(a), bit(b))), if left { a } else { b }),
    )
}
/// `Pi c y. Good c -> Good y -> Good (and c y)`. Not by `lemma2`: `Good` is a Sort2 claim and the bit
/// eliminator reaches only Sort1, so this applies the witnesses to the caller's own motive `P`:
/// `fun c y gc gy P h1 h0 => gc (fun c' => P (and c' y)) (gy (fun y' => P (and true y')) h1 h0) h0`.
fn good_and_lemma() -> (Expr, Expr) {
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
fn bit_from_xnor(l: bool) -> (Expr, Expr) {
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
fn good_xnor_lit(l: bool) -> (Expr, Expr) {
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
fn bit_lemma_hyp(body: impl Fn(Expr) -> Expr, leaf: impl Fn(bool) -> Expr) -> (Expr, Expr) {
    bit_lemma(body(var(0)), leaf(true), leaf(false))
}

/// `(proof, statement)` of `Pi x. GoodBv x -> Id(Bool0, eq_bv x L, true) -> Id(Bv_n, x, L)`, `L = lit(n, l)`.
fn eq_lit_sound(n: usize, l: u128, stated: u128) -> (Expr, Expr) {
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
fn eq_with_a_literal_implies_equality_on_good_vectors() {
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
        let mask = (1u128 << n) - 1;
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

fn min_all(n: usize) -> (u128, u128) {
    (1u128 << (n - 1), if n == 128 { u128::MAX } else { (1u128 << n) - 1 })
}
/// `(proof, statement)` of `Pi a b. Id(b, lit z) -> Id(sdiv_some a b, false)`: true for `z = 0`, false (and
/// rejected) otherwise.
fn sdiv_none_if_zero(n: usize, z: u128) -> (Expr, Expr) {
    // ctx [a, b, h]: a = var 2, b = var 1
    let ff = lam(bv_ty(n), sdiv_some(n, var(3), var(0)));
    let proof = lam(bv_ty(n), lam(bv_ty(n), lam(id(bv_ty(n), var(0), lit(n, z)),
        cong1(&bv_ty(n), &bool0(), &ff, var(1), lit(n, z), var(0)))));
    // statement at ctx [a, b]: Id(b, lit z) -> Id(flag, f)   (arrow: bodies at ctx [a, b])
    let stmt = pi(bv_ty(n), pi(bv_ty(n), arrow(id(bv_ty(n), var(0), lit(n, z)), id(bool0(), sdiv_some(n, var(1), var(0)), f()))));
    (proof, stmt)
}
/// `(proof, statement)` of `Pi a b. Id(a, MIN) -> Id(b, lit w) -> Id(sdiv_some a b, false)`; `w = -1` is the overflow case.
fn sdiv_none_on_overflow(n: usize, w: u128) -> (Expr, Expr) {
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
fn wrap_div_keeps_r(n: usize, claimed: bool) -> (Expr, Expr) {
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
fn sdiv_is_none_on_the_guard_and_wrapper_keeps_r_otherwise() {
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
fn good2(op: &dyn Fn(Expr, Expr) -> Expr, tab: &dyn Fn(bool, bool) -> bool) -> (Expr, Expr) {
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
fn good_add(n: usize) -> (Expr, Expr) {
    good_ripple(n, false)
}
/// `(proof, type)` of `Pi x y. GoodBv x -> GoodBv y -> GoodBv (sub x y)`.
fn good_sub(n: usize) -> (Expr, Expr) {
    good_ripple(n, true)
}
fn good_ripple(n: usize, sub: bool) -> (Expr, Expr) {
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
fn good_vec(n: usize, vec: Expr, bits: &dyn Fn(&[Expr], &[Expr], &[Expr], &[Expr]) -> (Vec<Expr>, Vec<Expr>)) -> (Expr, Expr) {
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
fn add_preserves_goodness() {
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
fn bv_lemma_scaling_h3_d2_good_add() {
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
fn bitwise(n: usize, op: &dyn Fn(Expr, Expr) -> Expr) -> Expr {
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
fn or_bv(n: usize) -> Expr {
    bitwise(n, &|a, b| or(a, b))
}
fn good_or_bv(n: usize) -> (Expr, Expr) {
    let (g_or, _) = good2(&|a, b| or(a, b), &|a, b| a || b);
    good_vec(n, or_bv(n), &move |a, b, ga, gb| {
        let s = (0..n).map(|i| or(a[i].clone(), b[i].clone())).collect();
        let gs = (0..n).map(|i| apps(g_or.clone(), vec![a[i].clone(), b[i].clone(), ga[i].clone(), gb[i].clone()])).collect();
        (s, gs)
    })
}
/// `\P st. st bits.. goods..`: the canonical `GoodBv (mk bits)` from `GoodBool` witnesses.
fn good_tuple(bits: &[Expr], goods: &[Expr]) -> Expr {
    let n = bits.len();
    let sh = |e: &Expr| shift(e, 0, 2);
    lam(arrow(bv_ty(n), sort(2)), lam(good_bv_step(n), apps(var(0), bits.iter().chain(goods).map(sh).collect())))
}

/// `(proof, statement)`: for `a` with free low bits `0..k` (higher bits false) and `b` with free high bits
/// `k..n` (lower bits false), `toN (or a b) = toN a + toN b`, each with its canonical witness.
fn or_disjoint_proof(n: usize, k: usize, stated_sum_with_a_twice: bool) -> (Expr, Expr) {
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
fn or_of_disjoint_vectors_adds_in_to_n() {
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
fn or_disjoint_scaling() {
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
fn lemma_n(k: usize, body: &dyn Fn(&[Expr]) -> Expr, leaf: &dyn Fn(&[bool]) -> Expr) -> (Expr, Expr) {
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
struct TabBdd {
    nodes: Vec<(usize, usize, usize)>,
    root: usize,
}

fn tab_bdd(nv: usize, tab: &dyn Fn(&[bool]) -> bool) -> TabBdd {
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
fn table_app(vars: &[Expr], tab: &dyn Fn(&[bool]) -> bool) -> Expr {
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
fn table_expr(vars: &[Expr], tab: &dyn Fn(&[bool]) -> bool) -> Expr {
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

fn sum3(a: Expr, b: Expr, c: Expr) -> Expr {
    xor(xor(a, b), c)
}
fn maj(a: Expr, b: Expr, c: Expr) -> Expr {
    or(and(a.clone(), b.clone()), and(c, xor(a, b)))
}
/// Table over `[a, b, z, p, q]` (state total `p + 2q`): the output bit (0), the next `p` (1) or next `q` (2).
fn assoc_table(which: usize, v: &[bool]) -> bool {
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
fn assoc_side(left: bool, which: usize, v: &[Expr]) -> Expr {
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
fn assoc_g(which: usize, v: &[Expr]) -> Expr {
    table_expr(v, &|bits| assoc_table(which, bits))
}

/// A `Bool0` expression with its `GoodBool` witness.
#[derive(Clone)]
struct Gb {
    e: Expr,
    g: Expr,
}
struct GoodOps {
    and: Expr,
    or: Expr,
    xor: Expr,
}
impl GoodOps {
    fn new() -> GoodOps {
        GoodOps {
            and: good2(&|a, b| and(a, b), &|a, b| a && b).0,
            or: good2(&|a, b| or(a, b), &|a, b| a || b).0,
            xor: good2(&|a, b| xor(a, b), &|a, b| a != b).0,
        }
    }
    fn go(&self, w: &Expr, e: Expr, x: &Gb, y: &Gb) -> Gb {
        Gb { g: apps(w.clone(), vec![x.e.clone(), y.e.clone(), x.g.clone(), y.g.clone()]), e }
    }
    fn and(&self, x: &Gb, y: &Gb) -> Gb {
        self.go(&self.and, and(x.e.clone(), y.e.clone()), x, y)
    }
    fn or(&self, x: &Gb, y: &Gb) -> Gb {
        self.go(&self.or, or(x.e.clone(), y.e.clone()), x, y)
    }
    fn xor(&self, x: &Gb, y: &Gb) -> Gb {
        self.go(&self.xor, xor(x.e.clone(), y.e.clone()), x, y)
    }
    fn sum3(&self, a: &Gb, b: &Gb, c: &Gb) -> Gb {
        let ab = self.xor(a, b);
        self.xor(&ab, c)
    }
    fn maj(&self, a: &Gb, b: &Gb, c: &Gb) -> Gb {
        let (ab, x) = (self.and(a, b), self.xor(a, b));
        let cx = self.and(c, &x);
        self.or(&ab, &cx)
    }
}

/// `(proof, statement)` of `Pi x y z. GoodBv x -> GoodBv y -> GoodBv z -> Id(Bv_n, add (add x y) z, add x (add y z))`.
/// `wrong` states `add x (add y y)` on the right instead, which the proof must not check against.
fn add_assoc_proof(n: usize, wrong: bool) -> (Expr, Expr) {
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
fn add_is_associative_on_symbolic_good_vectors() {
    for n in [1usize, 2, 4] {
        let (p, s) = add_assoc_proof(n, false);
        ck(&format!("add assoc n={n}"), &p, &s);
        let (p, s) = add_assoc_proof(n, true);
        assert!(check(&Ctx::new(), &p, &s).is_err(), "add (add x y) z = add x (add y y) must be rejected at n={n}");
    }
}

// ---- `add x (xor x -1) = -1` (x + ~x), a carry that stays false (search note section 12).

/// `(proof, statement)` of `Pi x. GoodBv x -> Id(Bv_n, add x (xor x -1), -1)`; `wrong` states `= 0` instead.
fn add_not_proof(n: usize, wrong: bool) -> (Expr, Expr) {
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
    let ones = lit(n, (1u128 << n) - 1);
    let rhs = if wrong { lit(n, 0) } else { ones.clone() };
    let xv = bitwise(n, &|p, q| xor(p, q));
    let claim = |x: Expr| id(bv_ty(n), app2(add(n), x.clone(), app2(xv.clone(), x, ones.clone())), rhs.clone());
    let motive = lam(bv_ty(n), claim(var(0)));
    let proof = lam(bv_ty(n), lam(app(good_bv(n), var(0)), app2(var(0), motive, step)));
    let stmt = pi(bv_ty(n), arrow(app(good_bv(n), var(0)), claim(var(0))));
    (proof, stmt)
}

#[test]
fn add_of_x_and_not_x_is_all_ones() {
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

#[derive(Clone)]
enum Term {
    V(usize),
    Zero,
    Ones,
    Op(usize, Box<Term>, Box<Term>),
}
/// `lt` (index 5) returns a one-bit vector and only appears at the root of a term; `shl1` (index 6) is `a << 1`
/// and ignores its second operand (a delay cell in the machine).
const OPS: [&str; 7] = ["add", "and", "or", "xor", "sub", "lt", "shl1"];
/// How many of `OPS` the miner enumerates: `sub` only with `MINER_SUB=1`.
fn nops() -> usize {
    if std::env::var("MINER_SUB").is_ok() { 5 } else { 4 }
}
/// `\a _. a << 1`, the Church operator of `Term` index 6.
fn shl1_op(n: usize) -> Expr {
    lam(bv_ty(n), lam(bv_ty(n), app(shift_bv(n, 1, true), var(1))))
}
/// `(proof, type)` of `Pi x y. GoodBv x -> GoodBv y -> GoodBv (shl1 x y)`: output bit `i` is input bit `i - 1`, bit 0 false.
fn good_shl1(n: usize) -> (Expr, Expr) {
    good_vec(n, shl1_op(n), &move |a, _b, ga, _gb| {
        let s = (0..n).map(|i| if i == 0 { f() } else { a[i - 1].clone() }).collect();
        let gs = (0..n).map(|i| if i == 0 { good_bit(false) } else { ga[i - 1].clone() }).collect();
        (s, gs)
    })
}
/// The Church operators, indexed as `Term::Op`.
fn ops_for(n: usize) -> [Expr; 7] {
    [add(n), bitwise(n, &|a, b| and(a, b)), bitwise(n, &|a, b| or(a, b)), bitwise(n, &|a, b| xor(a, b)), sub(n), lt_u(n), shl1_op(n)]
}
const VARS: [&str; 8] = ["x", "y", "z", "u", "v", "w", "p", "q"];
impl Term {
    fn show(&self) -> String {
        match self {
            Term::V(i) => VARS[*i].into(),
            Term::Zero => "0".into(),
            Term::Ones => "-1".into(),
            Term::Op(o, a, b) => format!("{}({}, {})", OPS[*o], a.show(), b.show()),
        }
    }
    /// The term as an expression, with `vals[i]` for variable `i`.
    fn eval(&self, ops: &[Expr], n: usize, vals: &[Expr]) -> Expr {
        match self {
            Term::V(i) => vals[*i].clone(),
            Term::Zero => lit(n, 0),
            Term::Ones => lit(n, (1u128 << n) - 1),
            Term::Op(o, a, b) => app2(ops[*o].clone(), a.eval(ops, n, vals), b.eval(ops, n, vals)),
        }
    }
    /// The value on the width-`n` operands `vals`, in plain integers (a cheap screen for false laws).
    fn interp(&self, n: usize, vals: &[u128]) -> u128 {
        let mask = (1u128 << n) - 1;
        match self {
            Term::V(i) => vals[*i],
            Term::Zero => 0,
            Term::Ones => mask,
            Term::Op(o, a, b) => {
                let (x, y) = (a.interp(n, vals), b.interp(n, vals));
                match o {
                    0 => x.wrapping_add(y) & mask,
                    1 => x & y,
                    2 => x | y,
                    3 => x ^ y,
                    5 => (x < y) as u128,
                    6 => (x << 1) & mask,
                    _ => x.wrapping_sub(y) & mask,
                }
            }
        }
    }
    /// Whether `self` and `other` agree on the corners and 200 pseudo-random width-`n` tuples over `k` variables.
    fn plausibly_equals(&self, other: &Term, n: usize, k: usize) -> bool {
        let mask = (1u128 << n) - 1;
        let mut seed = 0x9e37_79b9_7f4a_7c15u128;
        (0..204).all(|i| {
            let vals: Vec<u128> = (0..k)
                .map(|_| {
                    seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                    match i {
                        0 => 0,
                        1 => mask,
                        _ => (seed >> 40) & mask,
                    }
                })
                .collect();
            self.interp(n, &vals) == other.interp(n, &vals)
        })
    }
    fn uses_add(&self) -> bool {
        match self {
            Term::Op(o, a, b) => *o == 0 || *o == 4 || a.uses_add() || b.uses_add(),
            _ => false,
        }
    }
    fn max_var(&self) -> usize {
        match self {
            Term::V(i) => *i,
            Term::Op(_, a, b) => a.max_var().max(b.max_var()),
            _ => 0,
        }
    }
    /// The term's value at one bit position, a `Bool0`, given the variables' bits (`bits[v]`); bitwise ops only.
    fn bit(&self, bits: &[Expr]) -> Expr {
        match self {
            Term::V(i) => bits[*i].clone(),
            Term::Zero => f(),
            Term::Ones => t(),
            Term::Op(o, a, b) => {
                let (x, y) = (a.bit(bits), b.bit(bits));
                match o {
                    1 => and(x, y),
                    2 => or(x, y),
                    3 => xor(x, y),
                    _ => panic!("`add` is not bitwise"),
                }
            }
        }
    }
}

/// Leaves, every operator applied to two leaves, and (with `deep`) every operator applied to such a term
/// and a leaf, in either order.
fn terms(nvars: usize, deep: bool) -> Vec<Term> {
    let mut leaves: Vec<Term> = (0..nvars).map(Term::V).collect();
    leaves.push(Term::Zero);
    leaves.push(Term::Ones);
    let mut level1 = vec![];
    for o in 0..nops() {
        for a in &leaves {
            for b in &leaves {
                level1.push(Term::Op(o, Box::new(a.clone()), Box::new(b.clone())));
            }
        }
    }
    let mut all = leaves.clone();
    all.extend(level1.clone());
    if deep {
        for o in 0..nops() {
            for a in &level1 {
                for b in &leaves {
                    all.push(Term::Op(o, Box::new(a.clone()), Box::new(b.clone())));
                    all.push(Term::Op(o, Box::new(b.clone()), Box::new(a.clone())));
                }
            }
        }
    }
    all
}

type NfCache = std::collections::HashMap<(String, u128), Expr>;

/// The normal form of `t` on the input `tuple`, from the normal forms of its operands: each subterm is
/// normalized once per tuple across all terms, and the operands enter already normal.
fn nf_cached(t: &Term, ops: &[Expr], n: usize, tuple: u128, cache: &mut NfCache) -> Expr {
    let mask = (1u128 << n) - 1;
    let Term::Op(o, a, b) = t else {
        return match t {
            Term::V(i) => lit(n, (tuple >> (n * i)) & mask),
            Term::Zero => lit(n, 0),
            _ => lit(n, mask),
        };
    };
    let key = (t.show(), tuple);
    if let Some(e) = cache.get(&key) {
        return e.clone();
    }
    let (x, y) = (nf_cached(a, ops, n, tuple, cache), nf_cached(b, ops, n, tuple, cache));
    let e = normalize(&app2(ops[*o].clone(), x, y));
    cache.insert(key, e.clone());
    e
}

fn fingerprint(t: &Term, ops: &[Expr], n: usize, tuples: &[u128], cache: &mut NfCache) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    for &tuple in tuples {
        format!("{:?}", nf_cached(t, ops, n, tuple, cache)).hash(&mut h);
    }
    h.finish()
}

/// Generic proof of `t1(x, y) = t2(x, y)` for bitwise terms over two good vectors, with no lemma-specific
/// template: per bit, case analysis on the two `GoodBool` witnesses with `refl` leaves (the kernel decides
/// each leaf), then `cong_n` and the two witness eliminations. A false conjecture fails to check.
fn bitwise_law(n: usize, t1: &Term, t2: &Term) -> (Expr, Expr) {
    bitwise_law_k(n, 2, t1, t2)
}

/// As `bitwise_law`, over `k` good vectors (terms may use variables `0..k`).
fn bitwise_law_k(n: usize, k: usize, t1: &Term, t2: &Term) -> (Expr, Expr) {
    let (bit_law, _) = lemma_n(
        k,
        &|v| id(bool0(), t1.bit(v), t2.bit(v)),
        &|bits| refl(t1.bit(&bits.iter().map(|b| bit(*b)).collect::<Vec<_>>())),
    );
    k_var_law(n, k, t1, t2, &|bits, goods| {
        let (mut s1, mut s2, mut e) = (vec![], vec![], vec![]);
        for i in 0..n {
            let vs: Vec<Expr> = (0..k).map(|v| bits(v, i)).collect();
            s1.push(t1.bit(&vs));
            s2.push(t2.bit(&vs));
            e.push(apps(bit_law.clone(), vs.iter().cloned().chain((0..k).map(|v| goods(v, i))).collect()));
        }
        (s1, s2, e)
    })
}

type BitFn<'a> = &'a dyn Fn(usize) -> Expr;
type VarBitFn<'a> = &'a dyn Fn(usize, usize) -> Expr;
/// The skeleton of two-variable laws: see `k_var_law`; `per_bit(a, ga, b, gb)` gets the bit and witness variables.
fn two_var_law(n: usize, t1: &Term, t2: &Term, per_bit: &dyn Fn(BitFn, BitFn, BitFn, BitFn) -> (Vec<Expr>, Vec<Expr>, Vec<Expr>)) -> (Expr, Expr) {
    k_var_law(n, 2, t1, t2, &|bits, goods| per_bit(&|i| bits(0, i), &|i| goods(0, i), &|i| bits(1, i), &|i| goods(1, i)))
}

/// The skeleton shared by laws `t1 = t2` over `k` vectors with `GoodBv` witnesses: eliminates the `k` witnesses
/// in turn and calls `per_bit(bits, goods)` (`bits(v, i)`, `goods(v, i)`: bit `i` of vector `v` and its `GoodBool`
/// witness, as variables) for the per-bit equalities `(s1, s2, proofs)`; the result is `Pi x_1..x_k.
/// GoodBv x_1 -> .. -> GoodBv x_k -> Id(Bv_n, t1, t2)`.
fn k_var_law(n: usize, k: usize, t1: &Term, t2: &Term, per_bit: &dyn Fn(VarBitFn, VarBitFn) -> (Vec<Expr>, Vec<Expr>, Vec<Expr>)) -> (Expr, Expr) {
    k_var_law_to(n, k, &bv_ty(n), &|args| (t1.eval(&ops_for(n), n, args), t2.eval(&ops_for(n), n, args)), &|bits, goods| {
        let (s1, s2, e) = per_bit(bits, goods);
        let mut fbody = apps(var(0), (0..n).map(|i| var((n + 1 - i) as u32)).collect());
        fbody = lam(sort(1), lam(karrow(n), fbody));
        for _ in 0..n {
            fbody = lam(bool0(), fbody);
        }
        cong_n(&bool0(), &bv_ty(n), &fbody, &s1, &s2, e)
    })
}

/// As `k_var_law` for a claim `Id(ty, l, r)` with `(l, r) = sides(vectors)` (`ty` is `Bv_n`, or `Bv_1` for a root
/// `lt`): `finish(bits, goods)` proves it for the bit variables (the vectors are rebuilt by the witness eliminations).
fn k_var_law_to(n: usize, k: usize, ty: &Expr, sides: &dyn Fn(&[Expr]) -> (Expr, Expr), finish: &dyn Fn(VarBitFn, VarBitFn) -> Expr) -> (Expr, Expr) {
    // ctx: x_0..x_(k-1), g_0..g_(k-1), then level j adds a_j.. (n bits) and their witnesses (n)
    let level = |j: usize| 2 * k + 2 * n * j;
    let depth = |j: usize| 2 * k + 2 * n * (j + 1);
    let at = |d: usize, pos: usize| var((d - 1 - pos) as u32);
    let last = depth(k - 1);
    let done = finish(&|v, i| at(last, level(v) + i), &|v, i| at(last, level(v) + n + i));
    let binders = |mut body: Expr| {
        for _ in 0..n {
            body = lam(app(good_bool(), var(n as u32 - 1)), body);
        }
        for _ in 0..n {
            body = lam(bool0(), body);
        }
        body
    };
    let claim = |args: Vec<Expr>| {
        let (l, r) = sides(&args);
        id(ty.clone(), l, r)
    };
    // the motive for eliminating vector `j` at depth `d` (inside the previous level's binders), under its own binder
    let motive = |j: usize, d: usize| {
        let args = (0..k)
            .map(|v| {
                if v < j {
                    mk(&(0..n).map(|i| shift(&at(d, level(v) + i), 0, 1)).collect::<Vec<_>>())
                } else if v == j {
                    var(0)
                } else {
                    shift(&at(d, v), 0, 1)
                }
            })
            .collect();
        lam(bv_ty(n), claim(args))
    };
    let mut step = binders(done);
    for j in (0..k - 1).rev() {
        step = binders(app2(at(depth(j), k + j + 1), motive(j + 1, depth(j)), step));
    }
    let body = app2(at(2 * k, k), motive(0, 2 * k), step);
    let g = |v: usize| app(good_bv(n), var((k - 1) as u32 + 0 * v as u32));
    let mut proof = body;
    let mut stmt = claim((0..k).map(|v| var((2 * k - 1 - v) as u32)).collect());
    for v in (0..k).rev() {
        proof = lam(g(v), proof);
        stmt = pi(g(v), stmt);
    }
    for _ in 0..k {
        proof = lam(bv_ty(n), proof);
        stmt = pi(bv_ty(n), stmt);
    }
    (proof, stmt)
}

#[test]
fn bitwise_law_proves_true_laws_and_rejects_false_ones() {
    let v = |i: usize| Term::V(i);
    let op = |o: usize, a: Term, b: Term| Term::Op(o, Box::new(a), Box::new(b));
    for n in [1usize, 2, 4] {
        for (name, t1, t2) in [
            ("and x y = and y x", op(1, v(0), v(1)), op(1, v(1), v(0))),
            ("xor x x = 0", op(3, v(0), v(0)), Term::Zero),
            ("or x -1 = -1", op(2, v(0), Term::Ones), Term::Ones),
            ("and x (or x y) = x", op(1, v(0), op(2, v(0), v(1))), v(0)),
        ] {
            let (p, s) = bitwise_law(n, &t1, &t2);
            ck(&format!("{name} at n={n}"), &p, &s);
        }
        for (name, t1, t2) in [("and x y = or x y", op(1, v(0), v(1)), op(2, v(0), v(1))), ("xor x x = -1", op(3, v(0), v(0)), Term::Ones)] {
            let (p, s) = bitwise_law(n, &t1, &t2);
            assert!(check(&Ctx::new(), &p, &s).is_err(), "false law `{name}` must be rejected at n={n}");
        }
    }
}

// ---- Rewriting with proven lemmas (search note section 10). An `add` conjecture is simplified on both sides by
// the library lemmas `add a 0 = a`, `add 0 a = a` and `add a b = add b a` (the last used to order the operands),
// each rewrite justified by `cong_n` on the enclosing operator and chained with `trans_proof`; if the two
// results are then equal, or both add-free, `bitwise_law` closes the gap.

thread_local! {
    /// Lemmas built by `add_tree_law`, keyed on the side machine, encoding tables and lemma tag; shared across conjectures.
    static LEMMAS: std::cell::RefCell<std::collections::HashMap<String, Expr>> = Default::default();
    static CLOSED: std::cell::RefCell<std::collections::HashMap<String, (Expr, Expr)>> = Default::default();
}
/// A closed library term built once per key (the proofs and witnesses the rewriter reuses at every step).
fn memo(key: String, build: impl FnOnce() -> (Expr, Expr)) -> (Expr, Expr) {
    if let Some(v) = CLOSED.with(|c| c.borrow().get(&key).cloned()) {
        return v;
    }
    let v = build();
    CLOSED.with(|c| c.borrow_mut().insert(key, v.clone()));
    v
}

/// Whether the rewriter's rule `name` is switched off by the env var `ABLATE` (comma list: zero, comm, assoc, not, collapse).
fn ablated(name: &str) -> bool {
    std::env::var("ABLATE").is_ok_and(|v| v.split(',').any(|x| x == name))
}

/// `(value, GoodBv witness)` of `t` in context `[x, y, gx, gy]`.
fn witnessed(t: &Term, n: usize, goods: &[(Expr, Expr)]) -> (Expr, Expr) {
    let all = (1u128 << n) - 1;
    match t {
        Term::V(i) => goods[*i].clone(),
        Term::Zero => (lit(n, 0), good_lit(n, 0)),
        Term::Ones => (lit(n, all), good_lit(n, all)),
        Term::Op(o, a, b) => {
            let ((av, aw), (bv, bw)) = (witnessed(a, n, goods), witnessed(b, n, goods));
            let (op, good_op) = match o {
                0 => (add(n), memo(format!("good_add{n}"), || good_add(n)).0),
                4 => (sub(n), memo(format!("good_sub{n}"), || good_sub(n)).0),
                6 => (shl1_op(n), memo(format!("good_shl1{n}"), || good_shl1(n)).0),
                _ => memo(format!("gbit{n}_{o}"), || {
                    let o = *o;
                    let opf = move |p: Expr, q: Expr| match o {
                        1 => and(p, q),
                        2 => or(p, q),
                        _ => xor(p, q),
                    };
                    let (g, _) = match o {
                        1 => good2(&|p, q| and(p, q), &|p, q| p && q),
                        2 => good2(&|p, q| or(p, q), &|p, q| p || q),
                        _ => good2(&|p, q| xor(p, q), &|p, q| p != q),
                    };
                    let vec = bitwise(n, &opf);
                    let (gp, _) = good_vec(n, vec.clone(), &move |a, b, ga, gb| {
                        let s = (0..n).map(|i| opf(a[i].clone(), b[i].clone())).collect();
                        let gs = (0..n).map(|i| apps(g.clone(), vec![a[i].clone(), b[i].clone(), ga[i].clone(), gb[i].clone()])).collect();
                        (s, gs)
                    });
                    (vec, gp)
                }),
            };
            (app2(op.clone(), av.clone(), bv.clone()), apps(good_op, vec![av, bv, aw, bw]))
        }
    }
}

/// A sum of two (atom-abstracted) bitwise operands that a constant carry reduces to 0, -1 or one of its atoms:
/// the rewritten term and the proof from `carry_chain_law` instantiated at the atoms' values and witnesses.
fn chain_step(n: usize, a: &Term, b: &Term, goods: &[(Expr, Expr)]) -> Option<(Term, Expr)> {
    if ablated("chain") {
        return None;
    }
    let mut atoms = vec![];
    let (a1, b1) = (abstract_atoms(a, &mut atoms, 2)?, abstract_atoms(b, &mut atoms, 2)?);
    for cand in [Term::Zero, Term::Ones, Term::V(0), Term::V(1)] {
        if matches!(cand, Term::V(i) if i >= atoms.len()) || find_constant_carry(&a1, &b1, &cand).is_none() {
            continue;
        }
        let law = carry_chain_law(n, &Term::Op(0, Box::new(a1.clone()), Box::new(b1.clone())), &cand)?;
        let w: Vec<(Expr, Expr)> = (0..2).map(|i| atoms.get(i).map_or(goods[0].clone(), |t| witnessed(t, n, goods))).collect();
        let proof = apps(law.0, vec![w[0].0.clone(), w[1].0.clone(), w[0].1.clone(), w[1].1.clone()]);
        let target = if let Term::V(i) = cand { atoms[i].clone() } else { cand };
        return Some((target, proof));
    }
    None
}

/// A sum tree of add-free leaves that the carry-encoding search shows equal to a constant, a variable or one
/// bitwise operation on two of them (so `-1 - x` becomes `x ^ -1`): that value and
/// the proof (`add_tree_law` at the variables' values and witnesses). Ablation name `tree`.
fn tree_step(n: usize, t1: &Term, goods: &[(Expr, Expr)]) -> Option<(Term, Expr)> {
    if ablated("tree") {
        return None;
    }
    let k = goods.len();
    // the constants, the variables, then every operator applied to two of them (a plain-integer screen in
    // `add_tree_law` discards the false candidates cheaply)
    for cand in [Term::Zero, Term::Ones].into_iter().chain((0..k).map(Term::V)).chain(terms(k, false).into_iter().filter(|c| matches!(c, Term::Op(o, ..) if (1..=3).contains(o)))) {
        if let Some(law) = add_tree_law(n, k, t1, &cand) {
            let args = goods.iter().map(|g| g.0.clone()).chain(goods.iter().map(|g| g.1.clone())).collect();
            return Some((cand, apps(law.0, args)));
        }
    }
    None
}

/// A library law used as a left-to-right rewrite rule: `lhs = rhs` over the pattern variables `V(0)..`, each instance
/// proved from the law `add_tree_law` proves once (per width) for the patterns themselves. `name` is the `ABLATE` key.
struct Rule {
    name: &'static str,
    lhs: Term,
    rhs: Term,
}

thread_local! {
    /// Rules added at run time (by the rule miner), after the built-in ones.
    static EXTRA_RULES: std::cell::RefCell<Vec<(Term, Term)>> = Default::default();
}
/// How many more rule applications `rule_step` may make; the rule miner sets it per trial so that a candidate that
/// undoes a built-in rule cannot loop. Soundness is unaffected: a refused step only leaves the term less normalized.
static RULE_BUDGET: std::sync::atomic::AtomicI64 = std::sync::atomic::AtomicI64::new(i64::MAX / 2);

fn rules() -> Vec<Rule> {
    let op = |o: usize, a: Term, b: Term| Term::Op(o, Box::new(a), Box::new(b));
    let v = Term::V;
    let shl = |a: Term| Term::Op(6, Box::new(a), Box::new(Term::Zero));
    let mut all = vec![
        Rule { name: "shldist", lhs: shl(op(0, v(0), v(1))), rhs: op(0, shl(v(0)), shl(v(1))) },
        Rule { name: "shldistsub", lhs: shl(op(4, v(0), v(1))), rhs: op(4, shl(v(0)), shl(v(1))) },
        Rule { name: "shlzero", lhs: shl(Term::Zero), rhs: Term::Zero },
        Rule { name: "double", lhs: op(0, v(0), v(0)), rhs: shl(v(0)) },
        Rule { name: "doublechain", lhs: op(0, v(0), op(0, v(0), v(1))), rhs: op(0, shl(v(0)), v(1)) },
        // mined by `rule_miner` (section 36): cancellation
        Rule { name: "cancelr", lhs: op(4, op(0, v(0), v(1)), v(1)), rhs: v(0) },
        Rule { name: "cancell", lhs: op(4, op(0, v(0), v(1)), v(0)), rhs: v(1) },
        Rule { name: "subdist", lhs: op(4, op(0, v(0), v(1)), op(0, v(2), v(3))), rhs: op(0, op(4, v(0), v(2)), op(4, v(1), v(3))) },
    ];
    EXTRA_RULES.with(|e| all.extend(e.borrow().iter().map(|(l, r)| Rule { name: "mined", lhs: l.clone(), rhs: r.clone() })));
    all
}

/// First-order match of the pattern `p` against `t`, binding pattern variables in `sub` (a repeated variable must see equal terms).
impl Term {
    /// Number of nodes.
    fn size(&self) -> usize {
        match self {
            Term::Op(_, a, b) => 1 + a.size() + b.size(),
            _ => 1,
        }
    }
    /// All subterms (with repeats), the term itself first.
    fn subterms(&self, out: &mut Vec<Term>) {
        out.push(self.clone());
        if let Term::Op(_, a, b) = self {
            a.subterms(out);
            b.subterms(out);
        }
    }
}

fn match_pat(p: &Term, t: &Term, sub: &mut Vec<Option<Term>>) -> bool {
    match (p, t) {
        (Term::V(i), _) => match &sub[*i] {
            Some(b) => b.show() == t.show(),
            None => {
                sub[*i] = Some(t.clone());
                true
            }
        },
        (Term::Zero, Term::Zero) | (Term::Ones, Term::Ones) => true,
        (Term::Op(o, a, b), Term::Op(o2, c, d)) => o == o2 && match_pat(a, c, sub) && match_pat(b, d, sub),
        _ => false,
    }
}

fn subst_pat(p: &Term, sub: &[Option<Term>]) -> Term {
    match p {
        Term::V(i) => sub[*i].clone().expect("bound"),
        Term::Op(o, a, b) => Term::Op(*o, Box::new(subst_pat(a, sub)), Box::new(subst_pat(b, sub))),
        _ => p.clone(),
    }
}

/// Instances of `rule_step` by rule name, for the audit.
static RULE_HITS: std::sync::Mutex<Vec<(&'static str, u64)>> = std::sync::Mutex::new(Vec::new());

/// The first library rule (not ablated) whose left side matches `t`: the rewritten term and the proof.
fn rule_step(n: usize, t: &Term, goods: &[(Expr, Expr)]) -> Option<(Term, Expr)> {
    for r in rules() {
        let k = r.lhs.max_var().max(r.rhs.max_var()) + 1;
        let mut sub = vec![None; k];
        if ablated(r.name) || !match_pat(&r.lhs, t, &mut sub) {
            continue;
        }
        if RULE_BUDGET.fetch_sub(1, std::sync::atomic::Ordering::Relaxed) <= 0 {
            return None;
        }
        let law = memo(format!("rule_{}_{}_{}_{n}", r.name, r.lhs.show(), r.rhs.show()), || add_tree_law(n, k, &r.lhs, &r.rhs).unwrap_or_else(|| panic!("rule {} is not provable", r.name)));
        // a pattern variable the left side does not mention is free in the law: any value serves
        let w: Vec<(Expr, Expr)> = sub.iter().map(|s| s.as_ref().map_or(goods[0].clone(), |t| witnessed(t, n, goods))).collect();
        let args = w.iter().map(|x| x.0.clone()).chain(w.iter().map(|x| x.1.clone())).collect();
        let mut hits = RULE_HITS.lock().unwrap();
        match hits.iter_mut().find(|h| h.0 == r.name) {
            Some(h) => h.1 += 1,
            None => hits.push((r.name, 1)),
        }
        return Some((subst_pat(&r.rhs, &sub), apps(law.0, args)));
    }
    None
}

/// `t` rewritten bottom-up, with a proof of `Id(Bv_n, t, t')` in context `[x, y, gx, gy]`.
fn rewrite(t: &Term, n: usize, ops: &[Expr], goods: &[(Expr, Expr)]) -> (Term, Expr) {
    let vals: Vec<Expr> = goods.iter().map(|g| g.0.clone()).collect();
    let ev = |t: &Term| t.eval(ops, n, &vals);
    let Term::Op(o, a, b) = t else { return (t.clone(), refl(ev(t))) };
    let ((a2, pa), (b2, pb)) = (rewrite(a, n, ops, goods), rewrite(b, n, ops, goods));
    let cong = cong_n(&bv_ty(n), &bv_ty(n), &ops[*o], &[ev(a), ev(b)], &[ev(&a2), ev(&b2)], vec![pa, pb]);
    let t1 = Term::Op(*o, Box::new(a2.clone()), Box::new(b2.clone()));
    if *o == 4 {
        // a difference: the library rules, then the carry-encoding search
        if let Some((target, step)) = rule_step(n, &t1, goods) {
            let (t3, p3) = rewrite(&target, n, ops, goods);
            let first = trans_proof(&bv_ty(n), &ev(t), &ev(&t1), &ev(&target), cong, step);
            return (t3.clone(), trans_proof(&bv_ty(n), &ev(t), &ev(&target), &ev(&t3), first, p3));
        }
        return match tree_step(n, &t1, goods) {
            Some((target, law)) => (target.clone(), trans_proof(&bv_ty(n), &ev(t), &ev(&t1), &ev(&target), cong, law)),
            None => (t1, cong),
        };
    }
    if *o == 6 {
        // a shift: the library rules (`shldist`, ...), else unchanged
        if let Some((target, step)) = rule_step(n, &t1, goods) {
            let (t3, p3) = rewrite(&target, n, ops, goods);
            let first = trans_proof(&bv_ty(n), &ev(t), &ev(&t1), &ev(&target), cong, step);
            return (t3.clone(), trans_proof(&bv_ty(n), &ev(t), &ev(&target), &ev(&t3), first, p3));
        }
        return (t1, cong);
    }
    if *o != 0 {
        // a bitwise node equal to 0, -1 or one of its atoms collapses to it (truth table, then `bitwise_law`)
        let (mut atoms, k) = (vec![], goods.len());
        if let (false, Some(abs)) = (ablated("collapse"), abstract_atoms(&t1, &mut atoms, k)) {
            let truth = |t: &Term| (0..1usize << k).map(|m| normalize(&t.bit(&(0..k).map(|v| bit(m >> v & 1 == 1)).collect::<Vec<_>>()))).collect::<Vec<_>>();
            let want = truth(&abs);
            let cands: Vec<Term> = [Term::Zero, Term::Ones].into_iter().chain((0..k).map(Term::V)).collect();
            if let Some(c) = cands.iter().find(|c| c.max_var() < atoms.len().max(1) && truth(c) == want) {
                let target = if let Term::V(i) = c { atoms[*i].clone() } else { c.clone() };
                if target.show() != t1.show() {
                    let w: Vec<(Expr, Expr)> = (0..k).map(|i| atoms.get(i).map_or(goods[0].clone(), |a| witnessed(a, n, goods))).collect();
                    let args = w.iter().map(|x| x.0.clone()).chain(w.iter().map(|x| x.1.clone())).collect();
                    let law = apps(bitwise_law_k(n, k, &abs, c).0, args);
                    return (target.clone(), trans_proof(&bv_ty(n), &ev(t), &ev(&t1), &ev(&target), cong, law));
                }
            }
        }
        // commutative operands in a fixed order (constants last), by the generic bitwise law
        let key = |t: &Term| match t {
            Term::Zero => "~0".to_string(),
            Term::Ones => "~1".to_string(),
            _ => t.show(),
        };
        if key(&b2) < key(&a2) {
            let t2 = Term::Op(*o, Box::new(b2.clone()), Box::new(a2.clone()));
            let ((av, aw), (bv, bw)) = (witnessed(&a2, n, goods), witnessed(&b2, n, goods));
            let swap = |x: Term, y: Term| Term::Op(*o, Box::new(x), Box::new(y));
            let law = apps(bitwise_law(n, &swap(Term::V(0), Term::V(1)), &swap(Term::V(1), Term::V(0))).0, vec![av, bv, aw, bw]);
            return (t2.clone(), trans_proof(&bv_ty(n), &ev(t), &ev(&t1), &ev(&t2), cong, law));
        }
        return (t1, cong);
    }
    let (av, aw) = witnessed(&a2, n, goods);
    let (bv, bw) = witnessed(&b2, n, goods);
    let assoc = |p: &Term, q: &Term, r: &Term| {
        let ((pv, pw), (qv, qw), (rv, rw)) = (witnessed(p, n, goods), witnessed(q, n, goods), witnessed(r, n, goods));
        apps(memo(format!("assoc{n}"), || add_assoc_proof(n, false)).0, vec![pv, qv, rv, pw, qw, rw])
    };
    let sum = |p: &Term, q: &Term| Term::Op(0, Box::new(p.clone()), Box::new(q.clone()));
    let step = if !ablated("zero") && matches!(b2, Term::Zero) {
        Some((a2.clone(), app2(memo(format!("idr{n}"), || add_identity_proof(n, 0, false)).0, av, aw)))
    } else if !ablated("zero") && matches!(a2, Term::Zero) {
        Some((b2.clone(), app2(memo(format!("idl{n}"), || add_identity_proof(n, 0, true)).0, bv, bw)))
    } else if !ablated("not") && matches!(&b2, Term::Op(3, p, q) if p.show() == a2.show() && matches!(**q, Term::Ones)) {
        // a + ~a = -1
        Some((Term::Ones, app2(memo(format!("not{n}"), || add_not_proof(n, false)).0, av, aw)))
    } else if !ablated("not") && !ablated("comm") && matches!(&a2, Term::Op(3, p, q) if p.show() == b2.show() && matches!(**q, Term::Ones)) {
        // ~b + b = b + ~b = -1
        let lemma = app2(memo(format!("not{n}"), || add_not_proof(n, false)).0, bv.clone(), bw.clone());
        let comm = apps(memo(format!("comm{n}"), || add_comm_proof(n, false)).0, vec![av, bv.clone(), aw, bw]);
        let swapped = witnessed(&Term::Op(0, Box::new(b2.clone()), Box::new(a2.clone())), n, goods).0;
        let ones = witnessed(&Term::Ones, n, goods).0;
        Some((Term::Ones, trans_proof(&bv_ty(n), &ev(&t1), &swapped, &ones, comm, lemma)))
    } else if let Some(r) = rule_step(n, &t1, goods) {
        Some(r)
    } else if let Some(r) = chain_step(n, &a2, &b2, goods) {
        Some(r)
    } else if let Some(r) = tree_step(n, &t1, goods) {
        Some(r)
    } else if let (false, Term::Op(0, p, q)) = (ablated("assoc"), &a2) {
        // (p + q) + r = p + (q + r)
        Some((sum(p, &sum(q, &b2)), assoc(p, q, &b2)))
    } else if let (false, Term::Op(0, bp, bq)) = (ablated("assoc") || ablated("comm"), &b2) {
        if bp.show() < a2.show() {
            // a + (b + c) = (a + b) + c = (b + a) + c = b + (a + c)
            let (a_, b_, c_) = (&a2, &**bp, &**bq);
            let ((av2, aw2), (bv2, bw2), (cv2, _)) = (witnessed(a_, n, goods), witnessed(b_, n, goods), witnessed(c_, n, goods));
            let (ab, ba) = (witnessed(&sum(a_, b_), n, goods).0, witnessed(&sum(b_, a_), n, goods).0);
            let comm = apps(memo(format!("comm{n}"), || add_comm_proof(n, false)).0, vec![av2, bv2, aw2, bw2]);
            let swap = cong_n(&bv_ty(n), &bv_ty(n), &ops[0], &[ab.clone(), cv2.clone()], &[ba.clone(), cv2.clone()], vec![comm, refl(cv2)]);
            let (acc, bc, a_bc) = (witnessed(&sum(&sum(a_, b_), c_), n, goods).0, witnessed(&sum(&sum(b_, a_), c_), n, goods).0, witnessed(&t1, n, goods).0);
            let target = sum(b_, &sum(a_, c_));
            let (to_ab_c, ab_c_to_ba_c, ba_c_to_target) = (sym(&bv_ty(n), &acc, &a_bc, assoc(a_, b_, c_)), swap, assoc(b_, a_, c_));
            let tv = witnessed(&target, n, goods).0;
            let first = trans_proof(&bv_ty(n), &witnessed(&t1, n, goods).0, &acc, &bc, to_ab_c, ab_c_to_ba_c);
            Some((target, trans_proof(&bv_ty(n), &witnessed(&t1, n, goods).0, &bc, &tv, first, ba_c_to_target)))
        } else {
            None
        }
    } else if !ablated("comm") && b2.show() < a2.show() {
        Some((sum(&b2, &a2), apps(memo(format!("comm{n}"), || add_comm_proof(n, false)).0, vec![av, bv, aw, bw])))
    } else {
        None
    };
    match step {
        None => (t1, cong),
        Some((t2, p)) => {
            let (t3, p3) = rewrite(&t2, n, ops, goods);
            let first = trans_proof(&bv_ty(n), &ev(t), &ev(&t1), &ev(&t2), cong, p);
            (t3.clone(), trans_proof(&bv_ty(n), &ev(t), &ev(&t2), &ev(&t3), first, p3))
        }
    }
}

/// `t` with each variable and each `add` subterm replaced by an atom variable (up to `cap`, by `show`).
fn abstract_atoms(t: &Term, atoms: &mut Vec<Term>, cap: usize) -> Option<Term> {
    match t {
        Term::Zero | Term::Ones => Some(t.clone()),
        Term::V(_) | Term::Op(0 | 4 | 6, ..) => {
            let i = match atoms.iter().position(|a| a.show() == t.show()) {
                Some(i) => i,
                None => {
                    atoms.push(t.clone());
                    atoms.len() - 1
                }
            };
            (i < cap).then(|| Term::V(i))
        }
        Term::Op(o, a, b) => Some(Term::Op(*o, Box::new(abstract_atoms(a, atoms, cap)?), Box::new(abstract_atoms(b, atoms, cap)?))),
    }
}

/// How many times `prove_eq` closed a pair with a whole-term machine proof (the rewriting did not finish the job).
static MACHINE_FALLBACKS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// Pairs whose machines have more carries than this try generalizing a shared subterm first.
const GENERALIZE_ABOVE: usize = 3;

/// The subterm (with at least one `add` or `sub`, not a whole side) that occurs in both terms and has the most
/// carries, if any.
fn shared_subterm(a: &Term, b: &Term) -> Option<Term> {
    fn subs(t: &Term, out: &mut Vec<Term>) {
        if let Term::Op(_, x, y) = t {
            out.push(t.clone());
            subs(x, out);
            subs(y, out);
        }
    }
    let (mut sa, mut sb) = (vec![], vec![]);
    subs(a, &mut sa);
    subs(b, &mut sb);
    let in_b: std::collections::HashSet<String> = sb.iter().map(|t| t.show()).collect();
    sa.into_iter()
        .filter(|t| t.uses_add() && t.show() != a.show() && t.show() != b.show() && in_b.contains(&t.show()))
        .max_by_key(|t| Machine::parse(t).map_or(0, |m| m.carries()))
}

/// `t` with every occurrence of the subterm `x` replaced by `with`.
fn replace_term(t: &Term, x: &Term, with: &Term) -> Term {
    if t.show() == x.show() {
        return with.clone();
    }
    match t {
        Term::Op(o, a, b) => Term::Op(*o, Box::new(replace_term(a, x, with)), Box::new(replace_term(b, x, with))),
        _ => t.clone(),
    }
}

/// Proof of `Id(Bv_n, a, b)` in context `[x, y, gx, gy]` for rewritten terms: `refl`; the bitwise law over atoms
/// (when it holds on all four bit values, so the kernel check cannot fail); or, for two sums, `cong_n` on
/// proofs for their operands. `None` otherwise.
fn prove_eq(n: usize, ops: &[Expr], goods: &[(Expr, Expr)], a: &Term, b: &Term) -> Option<Expr> {
    let vals: Vec<Expr> = goods.iter().map(|g| g.0.clone()).collect();
    let ev = |t: &Term| t.eval(ops, n, &vals);
    if a.show() == b.show() {
        return Some(refl(ev(a)));
    }
    let (mut atoms, k) = (vec![], goods.len());
    if let (Some(a1), Some(a2)) = (abstract_atoms(a, &mut atoms, k), abstract_atoms(b, &mut atoms, k)) {
        let holds = (0..1usize << k).all(|m| {
            let bits: Vec<Expr> = (0..k).map(|v| bit(m >> v & 1 == 1)).collect();
            let truth = |t: &Term| normalize(&t.bit(&bits));
            truth(&a1) == truth(&a2)
        });
        if holds {
            let w: Vec<(Expr, Expr)> = (0..k).map(|i| atoms.get(i).map_or(goods[0].clone(), |t| witnessed(t, n, goods))).collect();
            let args = w.iter().map(|x| x.0.clone()).chain(w.iter().map(|x| x.1.clone())).collect();
            return Some(apps(bitwise_law_k(n, k, &a1, &a2).0, args));
        }
    }
    if let (Term::Op(o @ (0 | 4), a1, a2), Term::Op(o2, b1, b2)) = (a, b) {
        if o == o2 {
            if let (Some(p1), Some(p2)) = (prove_eq(n, ops, goods, a1, b1), prove_eq(n, ops, goods, a2, b2)) {
                return Some(cong_n(&bv_ty(n), &bv_ty(n), &ops[*o], &[ev(a1), ev(a2)], &[ev(b1), ev(b2)], vec![p1, p2]));
            }
        }
    }
    // equal bitwise operators: congruence on the operands
    if let (Term::Op(o, a1, a2), Term::Op(o2, b1, b2)) = (a, b) {
        if o == o2 && *o != 0 && *o != 4 {
            if let (Some(p1), Some(p2)) = (prove_eq(n, ops, goods, a1, b1), prove_eq(n, ops, goods, a2, b2)) {
                return Some(cong_n(&bv_ty(n), &bv_ty(n), &ops[*o], &[ev(a1), ev(a2)], &[ev(b1), ev(b2)], vec![p1, p2]));
            }
        }
    }
    // a large pair: a subterm both sides share becomes one more variable (the witness of its value is built by
    // `witnessed`), which takes its carries out of the machine; the proof for the pair over `k + 1` variables
    // is the proof for the original pair, since the extra variable's value is the subterm's
    let cost = |t: &Term| Machine::parse(t).map_or(0, |m| m.carries());
    if cost(a).max(cost(b)) > GENERALIZE_ABOVE && k < VARS.len() {
        if let Some(x) = shared_subterm(a, b) {
            let mut goods2 = goods.to_vec();
            goods2.push(witnessed(&x, n, goods));
            let (a2, b2) = (replace_term(a, &x, &Term::V(k)), replace_term(b, &x, &Term::V(k)));
            if let Some(p) = prove_eq(n, ops, &goods2, &a2, &b2) {
                return Some(p);
            }
        }
    }
    // the carry-encoding proof for the two terms as bit-serial machines, at the variables' values
    let law = add_tree_law(n, k, a, b)?;
    MACHINE_FALLBACKS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let args = goods.iter().map(|g| g.0.clone()).chain(goods.iter().map(|g| g.1.clone())).collect();
    return Some(apps(law.0, args));
}

/// Proof of `t1 = t2` over two good vectors by rewriting both sides and closing with `prove_eq`; `None` when
/// that cannot.
fn rewrite_law(n: usize, k: usize, t1: &Term, t2: &Term) -> Option<(Expr, Expr)> {
    let ops = ops_for(n);
    let goods: Vec<(Expr, Expr)> = (0..k).map(|i| (var((2 * k - 1 - i) as u32), var((k - 1 - i) as u32))).collect();
    let vals: Vec<Expr> = goods.iter().map(|g| g.0.clone()).collect();
    let (r1, p1) = rewrite(t1, n, &ops, &goods);
    let (r2, p2) = rewrite(t2, n, &ops, &goods);
    let ev = |t: &Term| t.eval(&ops, n, &vals);
    let bv = bv_ty(n);
    let mid = prove_eq(n, &ops, &goods, &r1, &r2)?;
    let to_r2 = trans_proof(&bv, &ev(t1), &ev(&r1), &ev(&r2), p1, mid);
    let body = trans_proof(&bv, &ev(t1), &ev(&r2), &ev(t2), to_r2, sym(&bv, &ev(t2), &ev(&r2), p2));
    let (mut proof, mut stmt) = (body, id(bv.clone(), ev(t1), ev(t2)));
    for _ in 0..k {
        let g = app(good_bv(n), var(k as u32 - 1));
        (proof, stmt) = (lam(g.clone(), proof), pi(g, stmt));
    }
    for _ in 0..k {
        (proof, stmt) = (lam(bv.clone(), proof), pi(bv.clone(), stmt));
    }
    Some((proof, stmt))
}

#[test]
fn laws_over_three_vectors_check_and_false_ones_fail() {
    let _scope = tatic::kernel::InternScope::enter();
    let v = |i: usize| Term::V(i);
    let op = |o: usize, a: Term, b: Term| Term::Op(o, Box::new(a), Box::new(b));
    for n in [1usize, 3] {
        // bitwise (x ^ y) ^ z = x ^ (y ^ z)
        let (p, s) = bitwise_law_k(n, 3, &op(3, op(3, v(0), v(1)), v(2)), &op(3, v(0), op(3, v(1), v(2))));
        ck(&format!("xor assoc at n={n}"), &p, &s);
        assert!(check(&Ctx::new(), &bitwise_law_k(n, 3, &op(1, v(0), v(2)), &op(2, v(0), v(2))).0, &bitwise_law_k(n, 3, &op(1, v(0), v(2)), &op(2, v(0), v(2))).1).is_err());
        // add associativity over three vectors, and a non-law
        let (p, s) = rewrite_law(n, 3, &op(0, op(0, v(0), v(1)), v(2)), &op(0, v(0), op(0, v(1), v(2)))).expect("assoc");
        ck(&format!("add assoc at n={n}"), &p, &s);
        let (p, s) = rewrite_law(n, 3, &op(0, op(0, v(2), v(0)), v(1)), &op(0, v(1), op(0, v(0), v(2)))).expect("comm+assoc");
        ck(&format!("add comm assoc at n={n}"), &p, &s);
        assert!(rewrite_law(n, 3, &op(0, v(0), v(2)), &op(0, v(0), v(1))).is_none());
    }
}

#[test]
fn rewrite_law_proves_add_conjectures_from_the_library_lemmas() {
    let v = |i: usize| Term::V(i);
    let op = |o: usize, a: Term, b: Term| Term::Op(o, Box::new(a), Box::new(b));
    let n = 4;
    for (name, t1, t2) in [
        ("or (add x 0) y = or y x", op(2, op(0, v(0), Term::Zero), v(1)), op(2, v(1), v(0))),
        ("xor (add x y) y = xor y (add y x)", op(3, op(0, v(0), v(1)), v(1)), op(3, v(1), op(0, v(1), v(0)))),
        ("add (and x y) y = add y (and y x)", op(0, op(1, v(0), v(1)), v(1)), op(0, v(1), op(1, v(1), v(0)))),
    ] {
        let (p, s) = rewrite_law(n, 2, &t1, &t2).unwrap_or_else(|| panic!("{name}: no rewrite proof"));
        ck(name, &p, &s);
    }
    // associativity instances, including one that needs reordering as well
    for (name, t1, t2) in [
        ("add (add x y) y = add x (add y y)", op(0, op(0, v(0), v(1)), v(1)), op(0, v(0), op(0, v(1), v(1)))),
        ("add (add y y) x = add (add x y) y", op(0, op(0, v(1), v(1)), v(0)), op(0, op(0, v(0), v(1)), v(1))),
    ] {
        let (p, s) = rewrite_law(n, 2, &t1, &t2).unwrap_or_else(|| panic!("{name}: no rewrite proof"));
        ck(name, &p, &s);
    }
    // a false law is refused by the truth-table pre-check
    assert!(rewrite_law(n, 2, &op(0, v(0), v(1)), &op(0, v(0), v(0))).is_none());
}

// ---- Carry-chain builder (search note section 13): `add A B = T` for bitwise A, B, T over x, y, with no
// lemma-specific template. It *discovers* the proof invariant: a constant value R for the carry that is
// inductive (the carry stays R for every pair of operand bits, starting from the initial `false`) and under
// which every sum bit equals the target bit. Both are decided by truth table before anything is built.

/// The constant carry value (as a literal bit) that works for `add a b = t`, if any.
fn find_constant_carry(a: &Term, b: &Term, t: &Term) -> Option<bool> {
    let carry = |x: Expr, y: Expr, c: Expr| or(and(x.clone(), y.clone()), and(c, xor(x, y)));
    [false, true].into_iter().find(|&r| {
        // the initial carry is `false`, so only `false` can be maintained from the start
        !r && (0..4).all(|m| {
            let bits = [bit(m & 1 == 1), bit(m & 2 == 2)];
            let (ab, bb, tb) = (a.bit(&bits), b.bit(&bits), t.bit(&bits));
            normalize(&carry(ab.clone(), bb.clone(), bit(r))) == bit(r) && normalize(&sum3(ab, bb, bit(r))) == normalize(&tb)
        })
    })
}

/// Proof of `t1 = t2` where `t1 = add A B` (bitwise `A`, `B`) and `t2` is bitwise, over two good vectors, by the
/// discovered constant-carry invariant; `None` when no constant carry works.
fn carry_chain_law(n: usize, t1: &Term, t2: &Term) -> Option<(Expr, Expr)> {
    let Term::Op(0, a_term, b_term) = t1 else { return None };
    if a_term.uses_add() || b_term.uses_add() || t2.uses_add() || t1.max_var().max(t2.max_var()) > 1 {
        return None;
    }
    let r = bit(find_constant_carry(a_term, b_term, t2)?);
    let carry = |x: Expr, y: Expr, c: Expr| or(and(x.clone(), y.clone()), and(c, xor(x, y)));
    // per-bit lemmas, by case analysis on the two operand bits
    let (p_carry, _) = lemma2(
        &|x, y| id(bool0(), carry(a_term.bit(&[x.clone(), y.clone()]), b_term.bit(&[x.clone(), y.clone()]), r.clone()), r.clone()),
        &|_, _| refl(r.clone()),
    );
    let (p_sum, _) = lemma2(
        &|x, y| id(bool0(), sum3(a_term.bit(&[x.clone(), y.clone()]), b_term.bit(&[x.clone(), y.clone()]), r.clone()), t2.bit(&[x, y])),
        &|vx, vy| refl(t2.bit(&[bit(vx), bit(vy)])),
    );
    Some(two_var_law(n, t1, t2, &|a, ga, b, gb| {
        let bl = bool0();
        let (ai, bi) = (|i: usize| a_term.bit(&[a(i), b(i)]), |i: usize| b_term.bit(&[a(i), b(i)]));
        let mut c = vec![r.clone()];
        let mut pc: Vec<Option<Expr>> = vec![None];
        let (mut s1, mut s2, mut e) = (vec![], vec![], vec![]);
        for i in 0..n {
            let args = vec![a(i), b(i), ga(i), gb(i)];
            // sum bit: rewrite the carry to R, then the sum lemma
            let s_i = sum3(ai(i), bi(i), c[i].clone());
            let to_target = apps(p_sum.clone(), args.clone());
            e.push(match &pc[i] {
                None => to_target,
                Some(pci) => {
                    let fmap = lam(bl.clone(), sum3(shift(&ai(i), 0, 1), shift(&bi(i), 0, 1), var(0)));
                    let rewritten = cong1(&bl, &bl, &fmap, c[i].clone(), r.clone(), pci.clone());
                    trans_proof(&bl, &s_i, &sum3(ai(i), bi(i), r.clone()), &t2.bit(&[a(i), b(i)]), rewritten, to_target)
                }
            });
            s1.push(s_i);
            s2.push(t2.bit(&[a(i), b(i)]));
            // next carry stays R
            let next = carry(ai(i), bi(i), c[i].clone());
            let stays = apps(p_carry.clone(), args);
            pc.push(Some(match &pc[i] {
                None => stays,
                Some(pci) => {
                    let fmap = lam(bl.clone(), carry(shift(&ai(i), 0, 1), shift(&bi(i), 0, 1), var(0)));
                    let rewritten = cong1(&bl, &bl, &fmap, c[i].clone(), r.clone(), pci.clone());
                    trans_proof(&bl, &next, &carry(ai(i), bi(i), r.clone()), &r, rewritten, stays)
                }
            }));
            c.push(next);
        }
        (s1, s2, e)
    }))
}

#[test]
fn carry_chain_builder_finds_the_constant_carry() {
    let v = |i: usize| Term::V(i);
    let op = |o: usize, a: Term, b: Term| Term::Op(o, Box::new(a), Box::new(b));
    for n in [1usize, 2, 4] {
        for (name, t1, t2) in [
            ("add x (xor x -1) = -1", op(0, v(0), op(3, v(0), Term::Ones)), Term::Ones),
            ("add (xor -1 y) y = -1", op(0, op(3, Term::Ones, v(1)), v(1)), Term::Ones),
            ("add x 0 = x", op(0, v(0), Term::Zero), v(0)),
            ("add (and x 0) y = y", op(0, op(1, v(0), Term::Zero), v(1)), v(1)),
        ] {
            let (p, s) = carry_chain_law(n, &t1, &t2).unwrap_or_else(|| panic!("{name}: no constant carry"));
            ck(&format!("{name} at n={n}"), &p, &s);
        }
        // no constant carry exists for these
        assert!(carry_chain_law(n, &op(0, v(0), v(1)), &op(0, v(1), v(0))).is_none());
        assert!(carry_chain_law(n, &op(0, v(0), Term::Ones), &v(0)).is_none());
    }
}

// ---- Searching for the carry-state encoding (search note sections 14 and 15). A sum tree of `c + 1` leaves (each
// leaf an add-free bitwise term over `k` vectors) is a ripple machine with `c` carries, one per `add` node. Two
// such sums agree if some encoding phi = (phi_1..phi_m) of the carry vector (m Boolean functions of the `c`
// carries) carries enough information: each side's output bit and next phi-values must be functions of (the `k`
// operand bits, phi(carries)), the same functions on both sides. `moore_encoding` computes the coarsest one by partition
// refinement; the proof is the associativity proof with the discovered phi in
// place of the hand-derived (xor, and) -- for a three-leaf sum, the total carry in binary.

/// The value of an add-free bitwise term at one bit position, with its `GoodBool` witness, given the operand bits.
fn term_gb<G: Gates>(g: &G, tm: &Term, u: &[G::S]) -> G::S {
    match tm {
        Term::V(i) => u[*i].clone(),
        Term::Zero => g.konst(false),
        Term::Ones => g.konst(true),
        Term::Op(1, a, b) => g.and(&term_gb(g, a, u), &term_gb(g, b, u)),
        Term::Op(2, a, b) => g.or(&term_gb(g, a, u), &term_gb(g, b, u)),
        Term::Op(3, a, b) => g.xor(&term_gb(g, a, u), &term_gb(g, b, u)),
        Term::Op(..) => panic!("`add` inside a leaf"),
    }
}

#[derive(Clone, Copy, Debug)]
enum Src {
    Leaf(usize),
    Node(usize),
}

/// A sum tree flattened in post-order: `nodes[i]` adds two sources; `root` is the last node, or the only leaf of
/// a bare add-free term (no carries).
struct Machine {
    leaves: Vec<Term>,
    /// `(left, right, op)`, `op` as in `Term::Op`: add (0) and sub (4) nodes carry a bit between positions, the
    /// bitwise ones (1..=3) combine their operands' bits at the same position.
    nodes: Vec<(Src, Src, usize)>,
    root: Src,
}

impl Machine {
    /// A description that determines the machine (for lemma cache keys).
    fn key(&self) -> String {
        format!("{}|{:?}|{:?}", self.leaves.iter().map(|l| l.show()).collect::<Vec<_>>().join(","), self.nodes, self.root)
    }

    /// Any term over variables and constants: the machine computes it one bit position at a time.
    fn parse(t: &Term) -> Option<Machine> {
        // equal subterms are one node (so a chain of delay cells serves every shift of the same operand)
        fn go(t: &Term, m: &mut Machine, seen: &mut std::collections::HashMap<String, Src>) -> Option<Src> {
            match t {
                Term::Op(o, a, b) => {
                    let key = t.show();
                    if let Some(src) = seen.get(&key) {
                        return Some(*src);
                    }
                    let a = go(a, m, seen)?;
                    let b = if *o == 6 { a } else { go(b, m, seen)? };
                    m.nodes.push((a, b, *o));
                    let src = Src::Node(m.nodes.len() - 1);
                    seen.insert(key, src);
                    Some(src)
                }
                _ => {
                    m.leaves.push(t.clone());
                    Some(Src::Leaf(m.leaves.len() - 1))
                }
            }
        }
        let mut m = Machine { leaves: vec![], nodes: vec![], root: Src::Leaf(0) };
        m.root = go(t, &mut m, &mut Default::default())?;
        Some(m)
    }

    /// The number of carries: one per add or sub node.
    fn carries(&self) -> usize {
        self.nodes.iter().filter(|n| matches!(n.2, 0 | 4 | 5 | 6)).count()
    }

    /// Whether the root is `lt`: the result is the last carry after the final position, not a vector.
    fn last(&self) -> bool {
        matches!(self.root, Src::Node(i) if self.nodes[i].2 == 5)
    }

    /// One position: `(output bit, next carries)` from the operand bits `u` and the carries `s`.
    fn step<G: Gates>(&self, g: &G, u: &[G::S], s: &[G::S]) -> (G::S, Vec<G::S>) {
        let leaf: Vec<G::S> = self.leaves.iter().map(|l| term_gb(g, l, u)).collect();
        let (mut val, mut next): (Vec<G::S>, Vec<G::S>) = (vec![], vec![]);
        let ones = g.konst(true);
        for (a, b, o) in self.nodes.iter() {
            let src = |s: &Src| match s {
                Src::Leaf(j) => leaf[*j].clone(),
                Src::Node(j) => val[*j].clone(),
            };
            let (x, y) = (src(a), src(b));
            let v = match o {
                1 => g.and(&x, &y),
                2 => g.or(&x, &y),
                3 => g.xor(&x, &y),
                6 => {
                    // a delay cell: the output is last position's operand bit
                    next.push(x.clone());
                    s[next.len() - 1].clone()
                }
                _ => {
                    let c = &s[next.len()];
                    // a subtractor's borrow is maj(~a, b, s)
                    next.push(if *o >= 4 { g.maj(&g.xor(&x, &ones), &y, c) } else { g.maj(&x, &y, c) });
                    g.sum3(&x, &y, c)
                }
            };
            val.push(v);
        }
        let out = match self.root {
            Src::Leaf(j) => leaf[j].clone(),
            Src::Node(j) => val[j].clone(),
        };
        (out, next)
    }
}

struct Encoding {
    /// `phi[side][j][s]`, `s` the side's carries as a number (first carry most significant).
    phi: [Vec<Vec<bool>>; 2],
    /// `g[0]` output, `g[1 + j]` next `phi_j`, indexed by (the `k` operand bits, then the `m` phi values), first most significant.
    g: Vec<Vec<bool>>,
}

/// The number with bits `bits`, first most significant.
fn index_of(bits: &[bool]) -> usize {
    bits.iter().fold(0, |a, b| a * 2 + *b as usize)
}

/// Each machine's (out, next carries) on all assignments of (operand bits, carries), computed once by the kernel.
fn raw_table(mach: &Machine, k: usize, gops: &GoodOps) -> Vec<Vec<bool>> {
    let c = mach.carries();
    (0..1usize << (k + c))
        .map(|r| {
            let bitgb = |pos: usize| Gb { e: bit(r >> (k + c - 1 - pos) & 1 == 1), g: f() };
            let u: Vec<Gb> = (0..k).map(bitgb).collect();
            let s: Vec<Gb> = (k..k + c).map(bitgb).collect();
            let (o, next) = mach.step(gops, &u, &s);
            let out = !mach.last() && normalize(&o.e) == t();
            std::iter::once(out).chain(next.iter().map(|g| normalize(&g.e) == t())).collect()
        })
        .collect()
}

type Reach = [Vec<bool>; 2];

/// The carry vectors one machine can reach from all-false by some input sequence (a vector as `index_of` reads it).
fn reachable(raw: &[Vec<bool>]) -> Vec<bool> {
    let c = raw[0].len() - 1;
    let mut seen = vec![false; 1 << c];
    seen[0] = true;
    let mut stack = vec![0usize];
    while let Some(s) = stack.pop() {
        for u in 0..raw.len() >> c {
            let next = index_of(&raw[u << c | s][1..]);
            if !seen[next] {
                seen[next] = true;
                stack.push(next);
            }
        }
    }
    seen
}

/// The functions `g` for which both machines factor through the encodings `phi` (one set per side), if any.
fn try_encoding(raw: &[Vec<Vec<bool>>; 2], k: usize, phi: &[Vec<Vec<bool>>; 2], reach: Option<&Reach>) -> Option<Vec<Vec<bool>>> {
    let m = phi[0].len();
    let mut g: Vec<Vec<Option<bool>>> = vec![vec![None; 1 << (k + m)]; 1 + m];
    for side in 0..2 {
        let c = raw[side][0].len() - 1;
        let ph = |s: usize| -> Vec<bool> { phi[side].iter().map(|t| t[s]).collect() };
        for (r, row) in raw[side].iter().enumerate() {
            let (u, s) = (r >> c, r & ((1 << c) - 1));
            if reach.is_some_and(|rc| !rc[side][s]) {
                continue;
            }
            let key = u << m | index_of(&ph(s));
            for (j, v) in std::iter::once(row[0]).chain(ph(index_of(&row[1..]))).enumerate() {
                match g[j][key] {
                    Some(old) if old != v => return None,
                    _ => g[j][key] = Some(v),
                }
            }
        }
    }
    Some(g.into_iter().map(|t| t.into_iter().map(|v| v.unwrap_or(false)).collect()).collect())
}

/// The coarsest consistent encoding, by Moore partition refinement over the carry vectors of both machines (all of
/// them, or only the `reach`able ones): two vectors share a class iff no input sequence tells them apart (the same
/// outputs, and with a root `lt` the same final bit). The class number, in binary, is the phi value. `None` when the
/// two start states (all-false) differ, i.e. the terms differ at some width.
fn moore_encoding(m1: &Machine, m2: &Machine, k: usize, gops: &GoodOps, reach: Option<&Reach>) -> Option<Encoding> {
    let raw = [raw_table(m1, k, gops), raw_table(m2, k, gops)];
    let cs = [m1.carries(), m2.carries()];
    let last = m1.last();
    let live = |side: usize, s: usize| reach.is_none_or(|rc| rc[side][s]);
    // class[side][s]; unreachable vectors stay in class 0 and are never looked at
    let mut class: [Vec<usize>; 2] = [0, 1].map(|side| (0..1usize << cs[side]).map(|s| if last && live(side, s) { s & 1 } else { 0 }).collect());
    let mut count = 0;
    loop {
        let mut ids: std::collections::HashMap<Vec<(usize, bool, usize)>, usize> = Default::default();
        let mut next: [Vec<usize>; 2] = [vec![0; class[0].len()], vec![0; class[1].len()]];
        for side in 0..2 {
            for s in (0..1usize << cs[side]).filter(|s| live(side, *s)) {
                let sig: Vec<(usize, bool, usize)> = std::iter::once((class[side][s], false, 0))
                    .chain((0..1usize << k).map(|u| {
                        let row = &raw[side][u << cs[side] | s];
                        (usize::MAX, row[0], class[side][index_of(&row[1..])])
                    }))
                    .collect();
                let fresh = ids.len();
                next[side][s] = *ids.entry(sig).or_insert(fresh);
            }
        }
        let done = ids.len() == count;
        count = ids.len();
        class = next;
        if done {
            break;
        }
    }
    if class[0][0] != class[1][0] {
        return None;
    }
    let m = (count.max(2) - 1).ilog2() as usize + 1;
    let phi: [Vec<Vec<bool>>; 2] = [0, 1].map(|side| (0..m).map(|j| class[side].iter().map(|c| c >> (m - 1 - j) & 1 == 1).collect()).collect());
    try_encoding(&raw, k, &phi, reach).map(|g| Encoding { phi, g })
}

/// `Id(Bool0, a, b)` from `h : Id(Bool0, false, true)`, for any Boolean `a`, `b`: congruence of `\c. mux c a b`.
fn absurd_id(h: Expr, a: &Expr, b: &Expr) -> Expr {
    let bl = bool0();
    let fmap = lam(bl.clone(), mux(var(0), shift(a, 0, 1), shift(b, 0, 1)));
    let p = cong1(&bl, &bl, &fmap, f(), t(), h);
    sym(&bl, &app(fmap.clone(), f()), &app(fmap, t()), p)
}

/// Nanoseconds spent in `add_tree_law`'s encoding searches: [all-states hit, all-states miss, reachable retry].
static LEMMA_HITS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static PROF: [std::sync::atomic::AtomicU64; 3] = [std::sync::atomic::AtomicU64::new(0), std::sync::atomic::AtomicU64::new(0), std::sync::atomic::AtomicU64::new(0)];

/// One line of machine state to print with every timing (LONG_RUNS.md): Defender real-time protection and total CPU
/// load over two seconds, read through PowerShell; "unavailable" off Windows.
fn machine_state() -> String {
    let script = r"'RTP=' + (Get-MpComputerStatus).RealTimeProtectionEnabled + ' CPU=' + [int](Get-Counter '\Processor(_Total)\% Processor Time' -SampleInterval 2 -MaxSamples 2).CounterSamples[-1].CookedValue + '%'";
    std::process::Command::new("powershell")
        .args(["-NoProfile", "-Command", script])
        .output()
        .ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .map_or_else(|| "machine state unavailable".to_string(), |t| t.trim().to_string())
}

/// The most carries per side `add_tree_law` takes on (unguarded lemmas are decision diagrams, guarded ones case trees over `k + carries` bits); env `CARRY_CAP`.
fn carry_cap() -> usize {
    std::env::var("CARRY_CAP").ok().and_then(|v| v.parse().ok()).unwrap_or(10)
}

/// Proof of `t1 = t2` for two sum trees of add-free leaves over `k` good vectors, with a carry encoding: found by
/// `moore_encoding` (first over all carry states, then over the reachable ones); `None` when there is none.
fn add_tree_law(n: usize, k: usize, t1: &Term, t2: &Term) -> Option<(Expr, Expr)> {
    if !t1.plausibly_equals(t2, n, k) {
        return None;
    }
    let (m1, m2) = (Machine::parse(t1)?, Machine::parse(t2)?);
    let last = m1.last();
    if last != m2.last() {
        return None;
    }
    let cs = [m1.carries(), m2.carries()];
    if cs[0].max(cs[1]) > carry_cap() {
        return None;
    }
    if cs[0] + cs[1] == 0 {
        return None;
    }
    let gops = GoodOps::new();
    let attempt = |reach: Option<&Reach>| {
        moore_encoding(&m1, &m2, k, &gops, reach)
    };
    // first over all carry states; failing that, over the reachable ones, with the lemmas conditional on an invariant
    let t_all = Instant::now();
    let first = attempt(None);
    PROF[if first.is_some() { 0 } else { 1 }].fetch_add(t_all.elapsed().as_nanos() as u64, std::sync::atomic::Ordering::Relaxed);
    let (enc, inv): (Encoding, Option<Reach>) = match first {
        Some(e) => (e, None),
        None => {
            // guarded lemmas are still case trees over k + c bits, so they keep the old cap
            if cs[0].max(cs[1]) > 6 {
                return None;
            }
            let t_reach = Instant::now();
            let r = [reachable(&raw_table(&m1, k, &gops)), reachable(&raw_table(&m2, k, &gops))];
            if r.iter().all(|v| v.iter().all(|x| *x)) {
                return None;
            }
            let second = attempt(Some(&r));
            PROF[2].fetch_add(t_reach.elapsed().as_nanos() as u64, std::sync::atomic::Ordering::Relaxed);
            (second?, Some(r))
        }
    };
    let m = enc.phi[0].len();
    // with a root `lt`: the final result as a function `dec` of the phi values
    let mut dec = vec![false; 1 << m];
    for side in 0..2 {
        for s in 0..1usize << cs[side] {
            if inv.as_ref().is_none_or(|r| r[side][s]) {
                dec[index_of(&(0..m).map(|j| enc.phi[side][j][s]).collect::<Vec<_>>())] = s & 1 == 1;
            }
        }
    }
    let machines = [m1, m2];
    let phi_expr = |side: usize, j: usize, s: &[Expr]| table_app(s, &|b| enc.phi[side][j][index_of(b)]);
    let g_expr = |j: usize, v: &[Expr]| table_app(v, &|b| enc.g[j][index_of(b)]);
    // F_j of a side at symbolic (operand bits, carries): j = 0 output, 1..=m the next phi values
    let side_f = |side: usize, j: usize, v: &[Expr]| -> Expr {
        let dummy: Vec<Gb> = v.iter().map(|e| Gb { e: e.clone(), g: f() }).collect();
        let (o, next) = machines[side].step(&gops, &dummy[..k], &dummy[k..]);
        match j {
            0 => o.e,
            _ => phi_expr(side, j - 1, &next.iter().map(|g| g.e.clone()).collect::<Vec<_>>()),
        }
    };
    // the same functions over diagram signals (F_j of a side, and G_j at the operand bits and the phi values)
    let phi_sig = |g: &DdGates, side: usize, j: usize, s: &[Sig]| g.table(s, &|b| enc.phi[side][j][index_of(b)]);
    let side_sig = |g: &DdGates, side: usize, j: usize, v: &[Sig]| -> Sig {
        let (o, next) = machines[side].step(g, &v[..k], &v[k..]);
        match j {
            0 => o,
            _ => phi_sig(g, side, j - 1, &next),
        }
    };
    let inv_expr = |side: usize, v: &[Expr]| table_app(v, &|b| inv.as_ref().unwrap()[side][index_of(b)]);
    // `Id(a, b)` for the `nv` bits `v` by case analysis; the carries are `v[off..]`. Over the reachable states only
    // (with `inv`), the lemma takes `Id(I(carries), true)` and the unreachable cases are absurd.
    // diagrams pay off only once the case tree is big (2^nv leaves); below that their per-node proofs cost more
    let dd_min: usize = std::env::var("DDMIN").ok().and_then(|v| v.parse().ok()).unwrap_or(9);
    let use_dd = |nv: usize| inv.is_none() && std::env::var("NOBDD").is_err() && nv >= dd_min;
    let guarded = |side: usize, nv: usize, off: usize, tag: &str, ab: &dyn Fn(&[Expr]) -> (Expr, Expr), dd: &dyn Fn(&DdGates, &[Sig]) -> (Sig, Sig)| -> Expr {
        let key = format!("{}|{k}|{nv}|{tag}|{:?}|{:?}", machines[side].key(), inv.as_ref().map(|r| &r[side]), enc.phi[side]);
        if let Some(e) = LEMMAS.with(|c| c.borrow().get(&key).cloned()) {
            LEMMA_HITS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            return e;
        }
        let hty = |v: &[Expr]| id(bool0(), inv_expr(side, &v[off..]), t());
        if inv.is_some() && std::env::var("GUARDTRACE").is_ok() {
            eprintln!("GUARDED lemma nv={nv} tag={tag}");
        }
        if use_dd(nv) {
            if let Some(e) = lemma_dd(nv, dd) {
                LEMMAS.with(|c| c.borrow_mut().insert(key, e.clone()));
                return e;
            }
        }
        let e = lemma_n(
            nv,
            &|v| {
                let (a, b) = ab(v);
                let inner = id(bool0(), a, b);
                if inv.is_some() { pi(hty(v), shift(&inner, 0, 1)) } else { inner }
            },
            &|bits| {
                let lits: Vec<Expr> = bits.iter().map(|b| bit(*b)).collect();
                let (a, b) = ab(&lits);
                match &inv {
                    None => refl(a),
                    Some(r) => lam(hty(&lits), if r[side][index_of(&bits[off..])] { refl(a) } else { absurd_id(var(0), &a, &b) }),
                }
            },
        )
        .0;
        LEMMAS.with(|c| c.borrow_mut().insert(key, e.clone()));
        e
    };
    // lemmas Id(F_j, G_j(operand bits, phi(carries))) by case analysis on the k + c bits
    let lemmas: Vec<Vec<Expr>> = (0..2)
        .map(|side| {
            (0..=m)
                .map(|j| {
                    if last && j == 0 {
                        return t();
                    }
                    guarded(side, k + cs[side], k, &format!("F{j}|{:?}", enc.g[j]), &|v| {
                        let key: Vec<Expr> = v[..k].iter().cloned().chain((0..m).map(|q| phi_expr(side, q, &v[k..]))).collect();
                        (side_f(side, j, v), g_expr(j, &key))
                    }, &|g, v| {
                        let key: Vec<Sig> = v[..k].iter().cloned().chain((0..m).map(|q| phi_sig(g, side, q, &v[k..]))).collect();
                        (side_sig(g, side, j, v), g.table(&key, &|b| enc.g[j][index_of(b)]))
                    })
                })
                .collect()
        })
        .collect();
    // the invariant is preserved by a step
    let pres: Vec<Expr> = (0..2)
        .map(|side| {
            if inv.is_none() {
                return t();
            }
            guarded(side, k + cs[side], k, "P", &|v| {
                let dummy: Vec<Gb> = v.iter().map(|e| Gb { e: e.clone(), g: f() }).collect();
                let next = machines[side].step(&gops, &dummy[..k], &dummy[k..]).1;
                (inv_expr(side, &next.iter().map(|g| g.e.clone()).collect::<Vec<_>>()), t())
            }, &|_, v| (v[0].clone(), v[0].clone()))
        })
        .collect();
    let dec_expr = |v: &[Expr]| table_app(v, &|b| dec[index_of(b)]);
    // the last carry is a function of the phi values: Id(carry_last, dec(phi(carries))) by cases
    let dlemmas: Vec<Expr> = (0..2)
        .map(|side| {
            if !last {
                return t();
            }
            guarded(side, cs[side], 0, &format!("D|{dec:?}"), &|v| (v[cs[side] - 1].clone(), dec_expr(&(0..m).map(|q| phi_expr(side, q, v)).collect::<Vec<_>>())), &|g, v| {
                (v[cs[side] - 1].clone(), g.table(&(0..m).map(|q| phi_sig(g, side, q, v)).collect::<Vec<_>>(), &|b| dec[index_of(b)]))
            })
        })
        .collect();
    let core = |bits: VarBitFn, goods: VarBitFn| {
        let bl = bool0();
        let tr = |x: &Expr, y: &Expr, w: &Expr, p: Expr, q: Expr| trans_proof(&bl, x, y, w, p, q);
        let zero = Gb { e: f(), g: good_bit(false) };
        let mut st: Vec<Vec<Gb>> = (0..2).map(|side| vec![zero.clone(); cs[side]]).collect();
        // the initial phi values agree by evaluation (both are the constant false)
        let mut ip: Vec<Expr> = (0..m).map(|j| refl(phi_expr(0, j, &vec![f(); cs[0]]))).collect();
        // the invariant holds at the all-false state (it is reachable)
        let mut hy: Vec<Expr> = vec![refl(t()), refl(t())];
        let (mut s1, mut s2, mut e) = (vec![], vec![], vec![]);
        for i in 0..n {
            let ug: Vec<Gb> = (0..k).map(|v| Gb { e: bits(v, i), g: goods(v, i) }).collect();
            let ub: Vec<Expr> = ug.iter().map(|g| g.e.clone()).collect();
            let sx = |side: usize| -> Vec<Expr> { st[side].iter().map(|g| g.e.clone()).collect() };
            let vs = |side: usize| -> Vec<Expr> { ub.iter().cloned().chain(sx(side)).collect() };
            let pq = |side: usize| -> Vec<Expr> { (0..m).map(|j| phi_expr(side, j, &sx(side))).collect() };
            let key = |p: &[Expr]| -> Vec<Expr> { ub.iter().cloned().chain(p.iter().cloned()).collect() };
            let eq = |j: usize| {
                let (fl, fr) = (side_f(0, j, &vs(0)), side_f(1, j, &vs(1)));
                let (pl, pr) = (pq(0), pq(1));
                let (gl, gr) = (g_expr(j, &key(&pl)), g_expr(j, &key(&pr)));
                let inst = |side: usize| {
                    let args = vs(side).into_iter().chain(ug.iter().map(|g| g.g.clone())).chain(st[side].iter().map(|g| g.g.clone()));
                    let mut args: Vec<Expr> = args.collect();
                    if inv.is_some() {
                        args.push(hy[side].clone());
                    }
                    apps(lemmas[side][j].clone(), args)
                };
                let mut fmap = g_expr(j, &ub.iter().map(|e| shift(e, 0, m as i32)).chain((0..m).map(|q| var((m - 1 - q) as u32))).collect::<Vec<_>>());
                for _ in 0..m {
                    fmap = lam(bl.clone(), fmap);
                }
                let link = cong_n(&bl, &bl, &fmap, &pl, &pr, ip.clone());
                let back = sym(&bl, &fr, &gr, inst(1));
                let mid = tr(&gl, &gr, &fr, link, back);
                (fl.clone(), fr.clone(), tr(&fl, &gl, &fr, inst(0), mid))
            };
            let first = last as usize;
            let proofs: Vec<(Expr, Expr, Expr)> = (first..=m).map(eq).collect();
            if !last {
                s1.push(proofs[0].0.clone());
                s2.push(proofs[0].1.clone());
                e.push(proofs[0].2.clone());
            }
            ip = proofs[1 - first..].iter().map(|p| p.2.clone()).collect();
            if inv.is_some() {
                for side in 0..2 {
                    let args = vs(side).into_iter().chain(ug.iter().map(|g| g.g.clone())).chain(st[side].iter().map(|g| g.g.clone())).chain([hy[side].clone()]);
                    hy[side] = apps(pres[side].clone(), args.collect());
                }
            }
            for side in 0..2 {
                st[side] = machines[side].step(&gops, &ug, &st[side]).1;
            }
        }
        (s1, s2, e, st, ip, hy)
    };
    if !last {
        return Some(k_var_law(n, k, t1, t2, &|bits, goods| {
            let (s1, s2, e, ..) = core(bits, goods);
            (s1, s2, e)
        }));
    }
    Some(k_var_law_to(n, k, &bv_ty(1), &|args| (t1.eval(&ops_for(n), n, args), t2.eval(&ops_for(n), n, args)), &|bits, goods| {
        let (.., st, ip, hy) = core(bits, goods);
        let bl = bool0();
        let sx = |side: usize| -> Vec<Expr> { st[side].iter().map(|g| g.e.clone()).collect() };
        let pq = |side: usize| -> Vec<Expr> { (0..m).map(|j| phi_expr(side, j, &sx(side))).collect() };
        let (pl, pr) = (pq(0), pq(1));
        let end = |side: usize| st[side][cs[side] - 1].e.clone();
        let inst = |side: usize| {
            let mut args: Vec<Expr> = sx(side).into_iter().chain(st[side].iter().map(|g| g.g.clone())).collect();
            if inv.is_some() {
                args.push(hy[side].clone());
            }
            apps(dlemmas[side].clone(), args)
        };
        let (dl, dr) = (dec_expr(&pl), dec_expr(&pr));
        let mut fmap = dec_expr(&(0..m).map(|q| var((m - 1 - q) as u32)).collect::<Vec<_>>());
        for _ in 0..m {
            fmap = lam(bl.clone(), fmap);
        }
        let link = cong_n(&bl, &bl, &fmap, &pl, &pr, ip);
        let back = sym(&bl, &end(1), &dr, inst(1));
        let mid = trans_proof(&bl, &dl, &dr, &end(1), link, back);
        let whole = trans_proof(&bl, &end(0), &dl, &end(1), inst(0), mid);
        let fbody = lam(bl.clone(), lam(sort(1), lam(karrow(1), app(var(0), var(2)))));
        cong_n(&bl, &bv_ty(1), &fbody, &[end(0)], &[end(1)], vec![whole])
    }))
}

#[test]
fn state_encoding_search_proves_three_leaf_sum_laws() {
    let _scope = tatic::kernel::InternScope::enter();
    let v = |i: usize| Term::V(i);
    let op = |a: Term, b: Term| Term::Op(0, Box::new(a), Box::new(b));
    for n in [1usize, 2, 4] {
        for (name, t1, t2) in [
            ("add (add x y) y = add x (add y y)", op(op(v(0), v(1)), v(1)), op(v(0), op(v(1), v(1)))),
            ("add (add y y) -1 = add y (add y -1)", op(op(v(1), v(1)), Term::Ones), op(v(1), op(v(1), Term::Ones))),
            ("add (add x -1) -1 = add x (add -1 -1)", op(op(v(0), Term::Ones), Term::Ones), op(v(0), op(Term::Ones, Term::Ones))),
        ] {
            if n == 1 {
                let e = moore_encoding(&Machine::parse(&t1).unwrap(), &Machine::parse(&t2).unwrap(), 2, &GoodOps::new(), None).unwrap();
                println!("ENCODING {name}: {} phi bits, phi1 {:?}", e.phi[0].len(), e.phi[0]);
            }
            let (p, s) = add_tree_law(n, 2, &t1, &t2).unwrap_or_else(|| panic!("{name}: no encoding"));
            ck(&format!("{name} at n={n}"), &p, &s);
        }
        // a false law has no encoding
        assert!(add_tree_law(n, 2, &op(op(v(0), v(1)), v(1)), &op(v(0), op(v(0), v(0)))).is_none());
    }
}

#[test]
fn state_encoding_search_handles_bitwise_leaves_three_vectors_and_four_leaves() {
    let _scope = tatic::kernel::InternScope::enter();
    let v = |i: usize| Term::V(i);
    let op = |o: usize, a: Term, b: Term| Term::Op(o, Box::new(a), Box::new(b));
    let add = |a: Term, b: Term| op(0, a, b);
    for n in [1usize, 2, 4] {
        // x & y + x | y = x + y: the leaves are bitwise terms
        let t1 = add(op(1, v(0), v(1)), op(2, v(0), v(1)));
        let t2 = add(v(0), v(1));
        let (p, s) = add_tree_law(n, 2, &t1, &t2).expect("and+or");
        ck(&format!("and+or at n={n}"), &p, &s);
        // associativity over three vectors, found by search
        let (p, s) = add_tree_law(n, 3, &add(add(v(0), v(1)), v(2)), &add(v(0), add(v(1), v(2)))).expect("assoc3");
        ck(&format!("assoc over x y z at n={n}"), &p, &s);
        // four leaves (three carries, two-bit total carry): (((x+y)+z)+x) = (x+(y+(z+x)))
        let l = add(add(add(v(0), v(1)), v(2)), v(0));
        let r = add(v(0), add(v(1), add(v(2), v(0))));
        let (p, s) = add_tree_law(n, 3, &l, &r).expect("four leaves");
        ck(&format!("four leaves at n={n}"), &p, &s);
        // false laws have no encoding
        assert!(add_tree_law(n, 3, &l, &add(v(0), add(v(1), add(v(2), v(2))))).is_none());
        assert!(add_tree_law(n, 2, &t1, &add(v(0), v(0))).is_none());
    }
}

#[test]
fn symmetric_encoding_handles_unequal_carry_counts_bare_leaves_and_five_leaves() {
    let _scope = tatic::kernel::InternScope::enter();
    let v = |i: usize| Term::V(i);
    let op = |o: usize, a: Term, b: Term| Term::Op(o, Box::new(a), Box::new(b));
    let add = |a: Term, b: Term| op(0, a, b);
    for n in [1usize, 2, 4] {
        // one add against two: the zero leaf adds a carry that never fires
        let (p, s) = add_tree_law(n, 2, &add(v(1), Term::Ones), &add(Term::Ones, add(v(1), Term::Zero))).expect("unequal counts");
        ck(&format!("y + -1 = -1 + (y + 0) at n={n}"), &p, &s);
        // a bare leaf is a sum with no carries
        let (p, s) = add_tree_law(n, 2, &v(1), &add(v(1), Term::Zero)).expect("bare leaf");
        ck(&format!("y = y + 0 at n={n}"), &p, &s);
        let (p, s) = add_tree_law(n, 2, &op(3, v(0), Term::Ones), &add(op(3, v(0), Term::Ones), Term::Zero)).expect("bare bitwise leaf");
        ck(&format!("x^-1 = (x^-1) + 0 at n={n}"), &p, &s);
        assert!(add_tree_law(n, 2, &v(1), &add(v(1), Term::Ones)).is_none());
        // five leaves, four carries
        let l = add(add(add(add(v(0), v(1)), v(2)), v(0)), v(1));
        let r = add(v(0), add(v(1), add(v(2), add(v(0), v(1)))));
        let (p, s) = add_tree_law(n, 3, &l, &r).expect("five leaves");
        ck(&format!("five leaves at n={n}"), &p, &s);
        assert!(add_tree_law(n, 3, &l, &add(v(0), add(v(1), add(v(2), add(v(0), v(0)))))).is_none());
        assert!(add_tree_law(n, 2, &add(v(1), Term::Ones), &add(v(0), add(v(1), Term::Zero))).is_none());
    }
}

/// Build and check time of the carry-encoding proof by number of carries (n = 4, three operands).
#[test]
#[ignore]
fn tree_proof_cost_by_carries() {
    let v = |i: usize| Term::V(i);
    let add = |a: Term, b: Term| Term::Op(0, Box::new(a), Box::new(b));
    let leaves = [v(0), v(1), v(2), v(0), v(1), v(2), v(0)];
    for n in [4usize] {
        for c in 2..=6usize {
            let left = leaves[1..=c].iter().fold(leaves[0].clone(), |a, b| add(a, b.clone()));
            let right = leaves[..c].iter().rev().fold(leaves[c].clone(), |a, b| add(b.clone(), a));
            let _scope = tatic::kernel::InternScope::enter();
            let t0 = Instant::now();
            let (p, s) = add_tree_law(n, 3, &left, &right).expect("encoding");
            let built = t0.elapsed();
            let t1 = Instant::now();
            let ok = check(&Ctx::new(), &p, &s).is_ok();
            println!("TREECOST n={n} carries={c}: build {built:?}, check {:?}, ok {ok}", t1.elapsed());
        }
    }
}

#[test]
fn sub_computes_is_good_and_its_laws_are_found_by_the_encoding_search() {
    let _scope = tatic::kernel::InternScope::enter();
    // computes: a - b mod 2^n on all pairs at n = 3
    let n = 3;
    for a in 0..8u128 {
        for b in 0..8u128 {
            let e = app2(sub(n), lit(n, a), lit(n, b));
            assert_eq!(normalize(&e), normalize(&lit(n, a.wrapping_sub(b) & 7)), "{a} - {b}");
        }
    }
    let (p, s) = good_sub(2);
    ck("good_sub n=2", &p, &s);
    let v = |i: usize| Term::V(i);
    let op = |o: usize, a: Term, b: Term| Term::Op(o, Box::new(a), Box::new(b));
    for n in [1usize, 2, 4] {
        for (name, k, l, r) in [
            ("x - x = 0", 2, op(4, v(0), v(0)), Term::Zero),
            ("x - 0 = x", 2, op(4, v(0), Term::Zero), v(0)),
            ("(x + y) - y = x", 2, op(4, op(0, v(0), v(1)), v(1)), v(0)),
            ("(x - y) + y = x", 2, op(0, op(4, v(0), v(1)), v(1)), v(0)),
            ("(x - y) - z = x - (y + z)", 3, op(4, op(4, v(0), v(1)), v(2)), op(4, v(0), op(0, v(1), v(2)))),
            ("0 - x = ~(x + -1)", 2, op(4, Term::Zero, v(0)), op(3, op(0, v(0), Term::Ones), Term::Ones)),
            ("~(x + y) = ~x - y", 2, op(3, op(0, v(0), v(1)), Term::Ones), op(4, op(3, v(0), Term::Ones), v(1))),
            ("(x & y) + (x | y) = x + y, bitwise nodes inside the machine", 2, op(0, op(1, v(0), v(1)), op(2, v(0), v(1))), op(0, v(0), v(1))),
            ("x - (y - z) = (x - y) + z", 3, op(4, v(0), op(4, v(1), v(2))), op(0, op(4, v(0), v(1)), v(2))),
        ] {
            let (p, s) = add_tree_law(n, k, &l, &r).unwrap_or_else(|| panic!("{name}: no encoding"));
            ck(&format!("{name} at n={n}"), &p, &s);
        }
        // false laws have none
        assert!(add_tree_law(n, 2, &op(4, v(0), v(1)), &op(4, v(1), v(0))).is_none());
        assert!(add_tree_law(n, 2, &op(4, v(0), v(1)), &op(0, v(0), v(1))).is_none() || n == 1);
    }
}

/// Time of the kernel evaluation of one machine on every (operand bits, carries) assignment.
#[test]
#[ignore]
fn raw_table_probe() {
    let v = |i: usize| Term::V(i);
    let add = |a: Term, b: Term| Term::Op(0, Box::new(a), Box::new(b));
    let leaves = [v(0), v(1), v(2), v(0), v(1), v(2)];
    let gops = GoodOps::new();
    for c in 2..=5usize {
        let left = leaves[1..=c].iter().fold(leaves[0].clone(), |a, b| add(a, b.clone()));
        let m = Machine::parse(&left).unwrap();
        let t0 = Instant::now();
        let raw = raw_table(&m, 3, &gops);
        println!("PROBE raw_table carries={c}: {} rows in {:?}", raw.len(), t0.elapsed());
    }
}

/// Check time of a case-analysis lemma whose body is the machine's output against itself (c = 3..5, k = 3).
#[test]
#[ignore]
fn machine_lemma_probe() {
    let v = |i: usize| Term::V(i);
    let add = |a: Term, b: Term| Term::Op(0, Box::new(a), Box::new(b));
    let leaves = [v(0), v(1), v(2), v(0), v(1), v(2)];
    let gops = GoodOps::new();
    for c in 3..=5usize {
        let _scope = std::env::var("NO_SCOPE").is_err().then(tatic::kernel::InternScope::enter);
        let left = leaves[1..=c].iter().fold(leaves[0].clone(), |a, b| add(a, b.clone()));
        let m = Machine::parse(&left).unwrap();
        for (what, pick) in [("out", 0usize), ("next carry 0", 1), ("table of next carries", 2)] {
            let f_of = |vv: &[Expr]| -> Expr {
                let dummy: Vec<Gb> = vv.iter().map(|e| Gb { e: e.clone(), g: f() }).collect();
                let (o, next) = m.step(&gops, &dummy[..3], &dummy[3..]);
                match pick {
                    0 => o.e,
                    1 => next[0].e.clone(),
                    _ => table_app(&next.iter().map(|g| g.e.clone()).collect::<Vec<_>>(), &|b| b.iter().filter(|x| **x).count() % 2 == 1),
                }
            };
            let (p, ty) = lemma_n(3 + c, &|vv| id(bool0(), f_of(vv), f_of(vv)), &|b| refl(f_of(&b.iter().map(|x| bit(*x)).collect::<Vec<_>>())));
            let t0 = Instant::now();
            let ok = check(&Ctx::new(), &p, &ty).is_ok();
            println!("PROBE carries={c} {what}: check {:?} ok {ok}", t0.elapsed());
        }
    }
}

/// Where the per-lemma time goes: the case split alone (trivial leaves) against a real machine lemma.
#[test]
#[ignore]
fn lemma_overhead_probe() {
    for vars in [5usize, 6, 7, 8] {
        let (p, ty) = lemma_n(vars, &|v| id(bool0(), v[0].clone(), v[0].clone()), &|b| refl(bit(b[0])));
        let t0 = Instant::now();
        let ok = check(&Ctx::new(), &p, &ty).is_ok();
        println!("PROBE trivial lemma over {vars} bits: check {:?} ok {ok}", t0.elapsed());
    }
}

/// Mine at width `MINER_N` (default 4) over `MINER_VARS` variables (default 2), `MINER_DEEP=1` for terms two
/// operators deep. Prints the classes, then tries every conjecture over x, y with the generic builder.
#[test]
#[ignore]
fn conjecture_miner() {
    let _scope = tatic::kernel::InternScope::enter();
    let env = |k: &str, d: usize| std::env::var(k).ok().and_then(|v| v.parse().ok()).unwrap_or(d);
    let (n, nvars, deep) = (env("MINER_N", 4), env("MINER_VARS", 2), env("MINER_DEEP", 0) == 1);
    let ops = ops_for(n);
    let ts = terms(nvars, deep);
    let t0 = Instant::now();
    let mut classes: std::collections::BTreeMap<u64, Vec<usize>> = Default::default();
    let mut cache = NfCache::default();
    // all input tuples, or `MINER_SAMPLE` of them (a fixed pseudo-random subset plus the all-zero and all-one
    // tuples): a class may then hold a false equality, which no proof builder or kernel check will accept
    let total = 1u128 << (n * nvars);
    let sample = env("MINER_SAMPLE", 0) as u128;
    let tuples: Vec<u128> = if sample == 0 || sample >= total {
        (0..total).collect()
    } else {
        let mut x = 0x9e3779b97f4a7c15u128;
        let mut v = vec![0, total - 1];
        for _ in 0..sample {
            x = x.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            v.push((x >> 40) % total);
        }
        v.sort();
        v.dedup();
        v
    };
    for (i, t) in ts.iter().enumerate() {
        classes.entry(fingerprint(t, &ops, n, &tuples, &mut cache)).or_default().push(i);
    }
    let conjectures: usize = classes.values().map(|c| c.len() - 1).sum();
    println!("MINER n={n} vars={nvars} deep={deep}: {} terms, {} classes, {conjectures} conjectures, run in {:?}", ts.len(), classes.len(), t0.elapsed());
    let show = std::env::var("MINER_SHOW").is_ok();
    // Every conjecture (class representative = shortest term) over x, y, by what can check it.
    let (mut by_builder, mut rejected, mut needs_add, mut needs_z, mut by_third) = (0, vec![], vec![], 0, (0usize, 0usize));
    let (mut by_rewrite, mut rewrite_bugs, mut by_chain, mut by_tree) = (0, vec![], 0, 0);
    let t1 = Instant::now();
    for c in classes.values().filter(|c| c.len() > 1) {
        let mut members: Vec<&Term> = c.iter().map(|&i| &ts[i]).collect();
        members.sort_by_key(|t| t.show().len());
        for other in &members[1..] {
            let law = format!("{} = {}", members[0].show(), other.show());
            if show {
                println!("  CONJ: {law}");
            }
            let k = (members[0].max_var().max(other.max_var()) + 1).max(2);
            if k > 2 {
                by_third.0 += 1;
            }
            if members[0].uses_add() || other.uses_add() {
                match rewrite_law(n, k, members[0], other) {
                    Some((p, s)) if k > 2 && check(&Ctx::new(), &p, &s).is_ok() => by_third.1 += 1,
                    _ if k > 2 => match add_tree_law(n, k, members[0], other) {
                        Some((p, s)) if check(&Ctx::new(), &p, &s).is_ok() => by_third.1 += 1,
                        _ => needs_z += 1,
                    },
                    Some((p, s)) if check(&Ctx::new(), &p, &s).is_ok() => by_rewrite += 1,
                    Some(_) => rewrite_bugs.push(law),
                    None => {
                        // the generic carry-chain builder, in either orientation
                        let chain = carry_chain_law(n, members[0], other).or_else(|| carry_chain_law(n, other, members[0]));
                        match chain {
                            Some((p, s)) if check(&Ctx::new(), &p, &s).is_ok() => by_chain += 1,
                            _ => match add_tree_law(n, 2, members[0], other) {
                                Some((p, s)) if check(&Ctx::new(), &p, &s).is_ok() => by_tree += 1,
                                _ => needs_add.push(law),
                            },
                        }
                    }
                }
            } else {
                let (p, s) = bitwise_law_k(n, k, members[0], other);
                if check(&Ctx::new(), &p, &s).is_ok() {
                    by_builder += 1;
                    by_third.1 += (k > 2) as usize;
                } else {
                    rejected.push(law);
                }
            }
        }
    }
    println!("MINER generic builder: {by_builder} proved, {} rejected {rejected:?}, in {:?}", rejected.len(), t1.elapsed());
    println!("MINER carry-chain builder: {by_chain} proved, state-encoding search: {by_tree} proved");
    println!("MINER rewrite: {by_rewrite} proved, {} failed to check {:?}", rewrite_bugs.len(), &rewrite_bugs[..rewrite_bugs.len().min(5)]);
    println!("MINER third variable: {} conjectures, {} proved, {needs_z} unproved", by_third.0, by_third.1);
    println!("MINER no builder: {} still need `add`", needs_add.len());
    for law in needs_add.iter().take(12) {
        println!("  needs add: {law}");
    }
    // Known library lemmas: does the miner conjecture them, and does the template proof check?
    let v = |i: usize| Term::V(i);
    let op = |o: usize, a: Term, b: Term| Term::Op(o, Box::new(a), Box::new(b));
    let same = |a: &Term, b: &Term| {
        classes.values().any(|c| c.iter().any(|&i| ts[i].show() == a.show()) && c.iter().any(|&i| ts[i].show() == b.show()))
    };
    let (p0, s0) = add_zero_proof(n, 0);
    let (p1, s1) = add_identity_proof(n, 0, true);
    let (p2, s2) = add_comm_proof(n, false);
    for (name, mined, proved) in [
        ("add x 0 = x", same(&op(0, v(0), Term::Zero), &v(0)), check(&Ctx::new(), &p0, &s0).is_ok()),
        ("add 0 x = x", same(&op(0, Term::Zero, v(0)), &v(0)), check(&Ctx::new(), &p1, &s1).is_ok()),
        ("add x y = add y x", same(&op(0, v(0), v(1)), &op(0, v(1), v(0))), check(&Ctx::new(), &p2, &s2).is_ok()),
    ] {
        println!("MINER known lemma {name}: conjectured {mined}, template proof checks {proved}");
        assert!(mined && proved, "{name}");
    }
    if deep && nvars >= 3 {
        let assoc = same(&op(0, op(0, v(0), v(1)), v(2)), &op(0, v(0), op(0, v(1), v(2))));
        println!("MINER add associativity conjectured: {assoc}");
    }
}

// ---- Comparison (search note section 20): `lt a b` is the final borrow of the chain for `a - b`, a `Bool0` result.

/// The terms `lt` is mined over: the leaves and every operator applied to two leaves.
fn lt_pool(nvars: usize) -> Vec<Term> {
    let mut leaves: Vec<Term> = (0..nvars).map(Term::V).collect();
    leaves.extend([Term::Zero, Term::Ones]);
    let mut pool = leaves.clone();
    for o in 0..5 {
        for a in &leaves {
            for b in &leaves {
                pool.push(Term::Op(o, Box::new(a.clone()), Box::new(b.clone())));
            }
        }
    }
    pool
}

#[test]
fn lt_computes_and_its_laws_are_found_by_the_encoding_search() {
    let _scope = tatic::kernel::InternScope::enter();
    let n = 4usize;
    // `lt_u` computes `a < b`
    let ops = ops_for(n);
    for (a, b) in [(0u128, 0u128), (3, 5), (5, 3), (7, 7), (0, 15), (15, 0), (8, 9)] {
        let e = app2(ops[5].clone(), lit(n, a), lit(n, b));
        assert_eq!(normalize(&e), normalize(&lit(1, (a < b) as u128)), "lt {a} {b}");
    }
    let v = |i: usize| Box::new(Term::V(i));
    let lt = |a: Term, b: Term| Term::Op(5, Box::new(a), Box::new(b));
    let op = |o: usize, a: Term, b: Term| Term::Op(o, Box::new(a), Box::new(b));
    // lt x x = lt y y; and an operand-order law with a carry on both sides
    let laws = [
        ("lt x x = lt y y", lt(Term::V(0), Term::V(0)), lt(Term::V(1), Term::V(1))),
        ("lt (and x y) (or x y) = lt (and y x) (or y x)", lt(op(1, *v(0), *v(1)), op(2, *v(0), *v(1))), lt(op(1, *v(1), *v(0)), op(2, *v(1), *v(0)))),
    ];
    for (name, t1, t2) in &laws {
        let (p, s) = add_tree_law(n, 2, t1, t2).unwrap_or_else(|| panic!("no proof: {name}"));
        ck(name, &p, &s);
    }
    // these hold only on the reachable carry states (the borrow of `x - 0` never becomes 1, the borrow of `x + y < x`
    // equals the add's carry): proved with lemmas conditional on a reachability invariant
    for (name, t1, t2) in [
        ("lt x 0 = lt y 0", lt(Term::V(0), Term::Zero), lt(Term::V(1), Term::Zero)),
        ("lt (x+y) x = lt (x+y) y", lt(op(0, *v(0), *v(1)), Term::V(0)), lt(op(0, *v(0), *v(1)), Term::V(1))),
    ] {
        let (p, s) = add_tree_law(n, 2, &t1, &t2).unwrap_or_else(|| panic!("no proof: {name}"));
        ck(name, &p, &s);
    }
    // false laws are not proved: by the plausibility screen, and a wrong proof would not check
    assert!(add_tree_law(n, 2, &lt(Term::V(0), Term::V(1)), &lt(Term::V(1), Term::V(0))).is_none());
    assert!(add_tree_law(n, 2, &lt(Term::V(0), Term::V(1)), &lt(Term::V(0), op(0, *v(1), Term::Ones))).is_none());
}

/// All `lt` pairs over the pool that agree on every width-4 input, grouped by behaviour; each conjecture is
/// built and kernel-checked.
#[test]
#[ignore]
fn lt_conjecture_miner() {
    let _scope = tatic::kernel::InternScope::enter();
    println!("LTMINER machine at start: {}", machine_state());
    let n = 4usize;
    let env = |k: &str, d: usize| std::env::var(k).ok().and_then(|v| v.parse().ok()).unwrap_or(d);
    let nv = env("LTMINER_VARS", 2);
    let cap = env("LTMINER_MAX", 0);
    let pool = lt_pool(nv);
    let mut groups: std::collections::HashMap<Vec<u128>, Vec<Term>> = Default::default();
    for a in &pool {
        for b in &pool {
            let t = Term::Op(5, Box::new(a.clone()), Box::new(b.clone()));
            let sig: Vec<u128> = (0..1u128 << (n * nv)).map(|i| t.interp(n, &(0..nv).map(|v| i >> (n * v) & 15).collect::<Vec<_>>())).collect();
            groups.entry(sig).or_default().push(t);
        }
    }
    let (mut total, mut proved, mut none) = (0, 0, 0);
    let t0 = Instant::now();
    let (mut t_law, mut t_ck) = (std::time::Duration::ZERO, std::time::Duration::ZERO);
    let mut conj: Vec<(Term, Term)> = groups.values().filter(|g| g.len() > 1).flat_map(|g| g[1..].iter().map(|t2| (g[0].clone(), t2.clone()))).collect();
    conj.sort_by_key(|(a, b)| (a.show(), b.show()));
    if cap > 0 && conj.len() > cap {
        let stride = conj.len() / cap;
        conj = conj.into_iter().step_by(stride).take(cap).collect();
    }
    {
        for (g0, t2) in &conj {
            let g = [g0.clone()];
            total += 1;
            let tl = Instant::now();
            let law = add_tree_law(n, nv, &g[0], t2);
            t_law += tl.elapsed();
            match law {
                Some((p, s)) => {
                    let tc = Instant::now();
                    ck(&format!("{} = {}", g[0].show(), t2.show()), &p, &s);
                    t_ck += tc.elapsed();
                    proved += 1;
                }
                None => {
                    none += 1;
                    // the groups are by behaviour at width 4; a law that fails at another width cannot have a proof for all widths
                    let generic = (1..=6).all(|w| g[0].plausibly_equals(t2, w, nv));
                    println!("LTMINER no proof ({}): {} = {}", if generic { "holds at widths 1..6" } else { "width-specific" }, g[0].show(), t2.show());
                }
            }
        }
    }
    let pf = |i: usize| std::time::Duration::from_nanos(PROF[i].load(std::sync::atomic::Ordering::Relaxed));
    println!("LTMINER time: add_tree_law {t_law:?} (all-states search: hit {:?}, miss {:?}; reachable retry {:?}), kernel check {t_ck:?}, lemma cache hits {}", pf(0), pf(1), pf(2), LEMMA_HITS.load(std::sync::atomic::Ordering::Relaxed));
    println!("LTMINER machine at end: {}", machine_state());
    println!("LTMINER {} groups, {total} conjectures, {proved} proved, {none} without a proof, {:?}", groups.len(), t0.elapsed());
}

// ---- Constant shifts (search note section 20). A shift reads another position, so it is not a carry machine; it
// is a rewiring of leaves. Laws over bitwise terms with constant shifts are proved per position: each position's
// equality is case analysis over the (variable, source position) bits it reads.

/// `x << k` (`left`) or `x >> k` as a vector operation: output bit `i` is input bit `i - k` (or `i + k`), else false.
fn shift_bv(n: usize, k: usize, left: bool) -> Expr {
    let d = 3 + n; // depth at the innermost body: a C kk a0..
    let v = |pos: usize| var((d - 1 - pos) as u32);
    let outs: Vec<Expr> = (0..n).map(|i| shift_src(n, k, left, i).map_or_else(f, |j| v(3 + j))).collect();
    let mut body = apps(v(2), outs);
    for _ in 0..n {
        body = lam(bool0(), body);
    }
    lam(bv_ty(n), lam(sort(1), lam(karrow(n), app2(var(2), var(1), body))))
}

/// The input position that output position `i` of a shift reads, if any.
fn shift_src(n: usize, k: usize, left: bool, i: usize) -> Option<usize> {
    if left { i.checked_sub(k) } else { Some(i + k).filter(|j| *j < n) }
}

/// Bitwise terms with constant shifts.
#[derive(Clone, Debug)]
enum STerm {
    V(usize),
    Zero,
    Ones,
    /// `(op, a, b)` with `op` 1 and, 2 or, 3 xor
    Bit(usize, Box<STerm>, Box<STerm>),
    /// `(amount, left?, a)`
    Shift(usize, bool, Box<STerm>),
}

type BitOp = fn(Expr, Expr) -> Expr;
const BIT_OPS: [BitOp; 3] = [and, or, xor];

impl STerm {
    fn show(&self) -> String {
        match self {
            STerm::V(i) => VARS[*i].into(),
            STerm::Zero => "0".into(),
            STerm::Ones => "-1".into(),
            STerm::Bit(o, a, b) => format!("{}({}, {})", OPS[*o], a.show(), b.show()),
            STerm::Shift(k, left, a) => format!("{}{k}({})", if *left { "shl" } else { "shr" }, a.show()),
        }
    }
    fn eval(&self, n: usize, vals: &[Expr]) -> Expr {
        match self {
            STerm::V(i) => vals[*i].clone(),
            STerm::Zero => lit(n, 0),
            STerm::Ones => lit(n, (1u128 << n) - 1),
            STerm::Bit(o, a, b) => {
                let op = BIT_OPS[*o - 1];
                app2(bitwise(n, &|x, y| op(x, y)), a.eval(n, vals), b.eval(n, vals))
            }
            STerm::Shift(k, left, a) => app(shift_bv(n, *k, *left), a.eval(n, vals)),
        }
    }
    fn interp(&self, n: usize, vals: &[u128]) -> u128 {
        let mask = (1u128 << n) - 1;
        match self {
            STerm::V(i) => vals[*i],
            STerm::Zero => 0,
            STerm::Ones => mask,
            STerm::Bit(o, a, b) => {
                let (x, y) = (a.interp(n, vals), b.interp(n, vals));
                [x & y, x | y, x ^ y][*o - 1]
            }
            STerm::Shift(k, left, a) => {
                let x = a.interp(n, vals);
                if *left { (x << k) & mask } else { x >> k }
            }
        }
    }
    /// Bit `i` of the term given the bits `bit(v, j)` of the variables.
    fn bit_at(&self, n: usize, i: usize, bit: &dyn Fn(usize, usize) -> Expr) -> Expr {
        match self {
            STerm::V(v) => bit(*v, i),
            STerm::Zero => f(),
            STerm::Ones => t(),
            STerm::Bit(o, a, b) => BIT_OPS[*o - 1](a.bit_at(n, i, bit), b.bit_at(n, i, bit)),
            STerm::Shift(k, left, a) => shift_src(n, *k, *left, i).map_or_else(f, |j| a.bit_at(n, j, bit)),
        }
    }
    /// The (variable, position) bits read at position `i`.
    fn atoms(&self, n: usize, i: usize, out: &mut Vec<(usize, usize)>) {
        match self {
            STerm::V(v) => out.push((*v, i)),
            STerm::Zero | STerm::Ones => {}
            STerm::Bit(_, a, b) => {
                a.atoms(n, i, out);
                b.atoms(n, i, out);
            }
            STerm::Shift(k, left, a) => {
                if let Some(j) = shift_src(n, *k, *left, i) {
                    a.atoms(n, j, out);
                }
            }
        }
    }
}

/// Proof of `t1 = t2` for shift terms over `k` good vectors: per position, case analysis over the bits both sides read.
fn shift_law(n: usize, k: usize, t1: &STerm, t2: &STerm) -> (Expr, Expr) {
    let sides = |args: &[Expr]| (t1.eval(n, args), t2.eval(n, args));
    k_var_law_to(n, k, &bv_ty(n), &sides, &|bits, goods| {
        let (mut s1, mut s2, mut e) = (vec![], vec![], vec![]);
        for i in 0..n {
            let mut atoms = vec![];
            t1.atoms(n, i, &mut atoms);
            t2.atoms(n, i, &mut atoms);
            atoms.sort();
            atoms.dedup();
            let at = |vals: &[Expr]| {
                let lookup = |v: usize, j: usize| vals[atoms.iter().position(|a| *a == (v, j)).unwrap()].clone();
                (t1.bit_at(n, i, &lookup), t2.bit_at(n, i, &lookup))
            };
            let (lemma, _) = lemma_n(
                atoms.len(),
                &|vals| {
                    let (a, b) = at(vals);
                    id(bool0(), a, b)
                },
                &|bs| refl(at(&bs.iter().map(|b| bit(*b)).collect::<Vec<_>>()).0),
            );
            let bit_vars: Vec<Expr> = atoms.iter().map(|(v, j)| bits(*v, *j)).collect();
            let args: Vec<Expr> = bit_vars.iter().cloned().chain(atoms.iter().map(|(v, j)| goods(*v, *j))).collect();
            let (a, b) = at(&bit_vars);
            s1.push(a);
            s2.push(b);
            e.push(apps(lemma, args));
        }
        let mut fbody = apps(var(0), (0..n).map(|i| var((n + 1 - i) as u32)).collect());
        fbody = lam(sort(1), lam(karrow(n), fbody));
        for _ in 0..n {
            fbody = lam(bool0(), fbody);
        }
        cong_n(&bool0(), &bv_ty(n), &fbody, &s1, &s2, e)
    })
}

#[test]
fn shift_ops_compute_and_shift_laws_check_and_false_ones_fail() {
    let _scope = tatic::kernel::InternScope::enter();
    let v = |i: usize| STerm::V(i);
    let sh = |k: usize, left: bool, a: STerm| STerm::Shift(k, left, Box::new(a));
    let bw = |o: usize, a: STerm, b: STerm| STerm::Bit(o, Box::new(a), Box::new(b));
    for n in [1usize, 2, 4] {
        // the Church shifts compute
        for x in 0..1u128 << n {
            for (k, left) in [(0usize, true), (1, true), (2, false), (3, true)] {
                let want = if left { (x << k) & ((1 << n) - 1) } else { x >> k };
                assert_eq!(normalize(&app(shift_bv(n, k, left), lit(n, x))), normalize(&lit(n, want)), "n={n} x={x} k={k} left={left}");
            }
        }
        let laws = [
            ("shl1 (and x y) = and (shl1 x) (shl1 y)", sh(1, true, bw(1, v(0), v(1))), bw(1, sh(1, true, v(0)), sh(1, true, v(1)))),
            ("shl1 (shl1 x) = shl2 x", sh(1, true, sh(1, true, v(0))), sh(2, true, v(0))),
            ("shr1 (shl1 x) = and x (shr1 (shl1 -1))", sh(1, false, sh(1, true, v(0))), bw(1, v(0), sh(1, false, sh(1, true, STerm::Ones)))),
            ("xor (shl1 x) (shl1 x) = 0", bw(3, sh(1, true, v(0)), sh(1, true, v(0))), STerm::Zero),
            ("shl0 x = x", sh(0, true, v(0)), v(0)),
            ("shl n x = 0", sh(n, true, v(0)), STerm::Zero),
        ];
        for (name, t1, t2) in &laws {
            let (p, s) = shift_law(n, 2, t1, t2);
            ck(&format!("{name}, n={n}"), &p, &s);
        }
        // false laws do not check (skipped when the two sides happen to agree at this width)
        for (t1, t2) in [(sh(1, true, v(0)), v(0)), (sh(1, true, v(0)), sh(1, false, v(0))), (sh(1, false, sh(1, true, v(0))), v(0))] {
            if (0..1u128 << n).all(|x| t1.interp(n, &[x, 0]) == t2.interp(n, &[x, 0])) {
                continue;
            }
            let (p, s) = shift_law(n, 2, &t1, &t2);
            assert!(check(&Ctx::new(), &p, &s).is_err(), "false law checked: {} = {}, n={n}", t1.show(), t2.show());
        }
    }
}

/// Every pair of shift terms over the pool that agree on all width-4 inputs, grouped by behaviour; each conjecture is
/// built and kernel-checked.
#[test]
#[ignore]
fn shift_conjecture_miner() {
    let _scope = tatic::kernel::InternScope::enter();
    let n = 4usize;
    let leaves = [STerm::V(0), STerm::V(1), STerm::Zero, STerm::Ones];
    let mut base: Vec<STerm> = leaves.to_vec();
    for a in &leaves {
        for (k, left) in [(1, true), (2, true), (1, false), (2, false)] {
            base.push(STerm::Shift(k, left, Box::new(a.clone())));
        }
    }
    let mut pool = base.clone();
    for o in 1..=3 {
        for a in &base {
            for b in &base {
                pool.push(STerm::Bit(o, Box::new(a.clone()), Box::new(b.clone())));
            }
        }
    }
    let level1: Vec<STerm> = pool[base.len()..].to_vec();
    for a in &level1 {
        for (k, left) in [(1, true), (1, false), (2, true)] {
            pool.push(STerm::Shift(k, left, Box::new(a.clone())));
        }
    }
    let mut groups: std::collections::HashMap<Vec<u128>, Vec<STerm>> = Default::default();
    for t in &pool {
        let sig: Vec<u128> = (0..256u128).map(|i| t.interp(n, &[i & 15, i >> 4])).collect();
        groups.entry(sig).or_default().push(t.clone());
    }
    let (mut total, t0) = (0, Instant::now());
    for g in groups.values().filter(|g| g.len() > 1) {
        for t2 in &g[1..] {
            total += 1;
            let (p, s) = shift_law(n, 2, &g[0], t2);
            ck(&format!("{} = {}", g[0].show(), t2.show()), &p, &s);
        }
    }
    println!("SHIFTMINER {} terms, {} groups, {total} conjectures proved and checked, 0 rejected, {:?}", pool.len(), groups.len(), t0.elapsed());
}

#[test]
fn shared_subterms_are_generalized_so_large_sums_stay_provable() {
    let _scope = tatic::kernel::InternScope::enter();
    let v = |i: usize| Term::V(i);
    let add = |a: Term, b: Term| Term::Op(0, Box::new(a), Box::new(b));
    let s = add(add(v(0), v(1)), v(2)); // two carries
    // 8 carries on each side before sharing equal subterms (6 after), so `rewrite_law` generalizes S to a variable
    let t1 = add(s.clone(), add(s.clone(), s.clone()));
    let t2 = add(add(s.clone(), s.clone()), s.clone());
    let (p, st) = rewrite_law(2, 3, &t1, &t2).expect("generalized");
    ck("add S (add S S) = add (add S S) S", &p, &st);
    // not equal: no proof
    assert!(rewrite_law(2, 3, &t1, &add(add(s.clone(), s.clone()), v(0))).is_none());
}

// ---- Left shifts inside machines (search note section 21): `shl1 a` is a delay cell, a carry whose next value is
// the operand's bit and whose output is the previous one, so sums with shifts are ordinary machines.

#[test]
fn shifts_inside_sums_are_machines_and_their_laws_check() {
    let _scope = tatic::kernel::InternScope::enter();
    let v = |i: usize| Term::V(i);
    let op = |o: usize, a: Term, b: Term| Term::Op(o, Box::new(a), Box::new(b));
    let shl = |a: Term| op(6, a, Term::Zero);
    let n = 4usize;
    let laws = [
        ("shl1 x = add x x", shl(v(0)), op(0, v(0), v(0))),
        ("shl1 (add x y) = add (shl1 x) (shl1 y)", shl(op(0, v(0), v(1))), op(0, shl(v(0)), shl(v(1)))),
        ("shl1 (sub x y) = sub (shl1 x) (shl1 y)", shl(op(4, v(0), v(1))), op(4, shl(v(0)), shl(v(1)))),
        ("shl1 (shl1 x) = add (add x x) (add x x)", shl(shl(v(0))), op(0, op(0, v(0), v(0)), op(0, v(0), v(0)))),
        ("add x (shl1 x) = add (shl1 x) x", op(0, v(0), shl(v(0))), op(0, shl(v(0)), v(0))),
        ("add (shl1 x) y = add y (shl1 x)", op(0, shl(v(0)), v(1)), op(0, v(1), shl(v(0)))),
        ("shl1 (xor x y) = xor (shl1 x) (shl1 y)", shl(op(3, v(0), v(1))), op(3, shl(v(0)), shl(v(1)))),
    ];
    for (name, t1, t2) in &laws {
        let (p, s) = add_tree_law(n, 2, t1, t2).unwrap_or_else(|| panic!("no proof: {name}"));
        ck(name, &p, &s);
    }
    // false laws get no proof
    assert!(add_tree_law(n, 2, &shl(v(0)), &v(0)).is_none());
    assert!(add_tree_law(n, 2, &shl(v(0)), &op(0, v(0), v(1))).is_none());
}

/// The equal pairs of the `shl1` pool over `nv` variables at width 4 (leaves, shifted leaves, every operator on two of
/// them, and shifts of those), each group's first term paired with the others.
fn shl_conjectures(nv: usize) -> Vec<(Term, Term)> {
    let n = 4usize;
    let b = |o: usize, a: &Term, c: &Term| Term::Op(o, Box::new(a.clone()), Box::new(c.clone()));
    let shl = |a: &Term| b(6, a, &Term::Zero);
    let leaves: Vec<Term> = (0..nv).map(Term::V).chain([Term::Zero, Term::Ones]).collect();
    let mut base: Vec<Term> = leaves.to_vec();
    base.extend(leaves.iter().map(&shl));
    let sh: Vec<Term> = leaves.iter().map(&shl).collect();
    base.extend(sh.iter().map(&shl));
    let mut level1 = vec![];
    for o in 0..5 {
        for x in &base {
            for y in &base {
                level1.push(b(o, x, y));
            }
        }
    }
    let mut pool = base.clone();
    pool.extend(level1.iter().cloned());
    pool.extend(level1.iter().map(&shl));
    let mut groups: std::collections::HashMap<Vec<u128>, Vec<Term>> = Default::default();
    for t in &pool {
        let sig: Vec<u128> = (0..1u128 << (n * nv)).map(|i| t.interp(n, &(0..nv).map(|v| i >> (n * v) & 15).collect::<Vec<_>>())).collect();
        groups.entry(sig).or_default().push(t.clone());
    }
    let mut conj: Vec<(Term, Term)> = groups.values().filter(|g| g.len() > 1).flat_map(|g| g[1..].iter().map(|t2| (g[0].clone(), t2.clone()))).collect();
    conj.sort_by_key(|(a, b)| (a.show(), b.show()));
    conj
}

/// Pairs over a pool with `shl1` that agree on all width-4 inputs; each is built and kernel-checked.
#[test]
#[ignore]
fn shl_conjecture_miner() {
    let _scope = tatic::kernel::InternScope::enter();
    println!("SHLMINER machine at start: {}", machine_state());
    let n = 4usize;
    let env = |k: &str, d: usize| std::env::var(k).ok().and_then(|v| v.parse().ok()).unwrap_or(d);
    let (nv, cap) = (env("SHLMINER_VARS", 2), env("SHLMINER_MAX", 0));
    let b = |o: usize, a: &Term, c: &Term| Term::Op(o, Box::new(a.clone()), Box::new(c.clone()));
    let shl = |a: &Term| b(6, a, &Term::Zero);
    let mut conj = shl_conjectures(nv);
    if cap > 0 && conj.len() > cap {
        let stride = conj.len() / cap;
        conj = conj.into_iter().step_by(stride).take(cap).collect();
    }
    let (mut total, mut proved, mut generic_none, mut t_none, mut carry_free, mut skipped, t0) = (0, 0, 0, 0, 0, 0, Instant::now());
    for (g0, t2) in &conj {
        let g = [g0.clone()];
        {
            let big = [&g[0], t2].iter().any(|t| Machine::parse(t).is_some_and(|m| m.carries() > carry_cap()));
            if big {
                skipped += 1; // beyond the carry cap of add_tree_law
                continue;
            }
            total += 1;
            match add_tree_law(n, nv, &g[0], t2) {
                Some((p, s)) => {
                    ck(&format!("{} = {}", g[0].show(), t2.show()), &p, &s);
                    proved += 1;
                }
                None if [&g[0], t2].iter().all(|t| Machine::parse(t).is_none_or(|m| m.carries() == 0)) => carry_free += 1, // `bitwise_law` territory
                None => {
                    // a law that fails at another width cannot have a proof for all widths
                    let generic = (1..=6).all(|w| g[0].plausibly_equals(t2, w, nv));
                    t_none += 1;
                    if generic {
                        generic_none += 1;
                        if generic_none <= 12 {
                            println!("SHLMINER no proof, holds at widths 1..6: {} = {}", g[0].show(), t2.show());
                        }
                    }
                }
            }
        }
    }
    println!("SHLMINER machine at end: {}", machine_state());
    println!("SHLMINER {} listed conjectures ({} after the cap), {total} conjectures within the carry cap ({skipped} bigger ones skipped): {proved} proved and checked, {carry_free} carry-free (bitwise laws), {t_none} without a proof ({generic_none} hold at widths 1..6), {:?}", conj.len(), conj.len(), t0.elapsed());
}

/// `c * t` (mod 2^n) as shift-and-add: the sum of `shl1^i t` over the set bits `i` of `c`.
fn mul_const(c: u32, t: &Term) -> Term {
    let shl = |a: Term, k: u32| (0..k).fold(a, |acc, _| Term::Op(6, Box::new(acc), Box::new(Term::Zero)));
    let mut parts = (0..32).filter(|i| c >> i & 1 == 1).map(|i| shl(t.clone(), i));
    let first = parts.next().expect("c is nonzero");
    parts.fold(first, |acc, p| Term::Op(0, Box::new(acc), Box::new(p)))
}

#[test]
fn multiplication_by_constants_as_shift_and_add_machines() {
    let _scope = tatic::kernel::InternScope::enter();
    let v = |i: usize| Term::V(i);
    let op = |o: usize, a: Term, b: Term| Term::Op(o, Box::new(a), Box::new(b));
    let shl = |a: Term| op(6, a, Term::Zero);
    let n = 4usize;
    let laws = [
        ("3x = x + 2x, written both ways", mul_const(3, &v(0)), op(0, shl(v(0)), v(0))),
        ("2x = x + x", mul_const(2, &v(0)), op(0, v(0), v(0))),
        ("6x = 2 * 3x", mul_const(6, &v(0)), shl(mul_const(3, &v(0)))),
        ("5x = 4x + x", mul_const(5, &v(0)), op(0, v(0), shl(shl(v(0))))),
        ("7x = 8x - x", mul_const(7, &v(0)), op(4, shl(shl(shl(v(0)))), v(0))),
        ("3 (x + y) = 3x + 3y", mul_const(3, &op(0, v(0), v(1))), op(0, mul_const(3, &v(0)), mul_const(3, &v(1)))),
        ("3 (x - y) = 3x - 3y", mul_const(3, &op(4, v(0), v(1))), op(4, mul_const(3, &v(0)), mul_const(3, &v(1)))),
        ("(x + y) + 2 (x + y) = 3x + 3y", op(0, op(0, v(0), v(1)), shl(op(0, v(0), v(1)))), op(0, mul_const(3, &v(0)), mul_const(3, &v(1)))),
    ];
    for (name, t1, t2) in &laws {
        assert!((1..=6).all(|w| t1.plausibly_equals(t2, w, 2)), "{name} is not a law");
        let t0 = Instant::now();
        let (p, s) = add_tree_law(n, 2, t1, t2).unwrap_or_else(|| panic!("no proof: {name}"));
        let built = t0.elapsed();
        ck(name, &p, &s);
        println!("MUL {name}: build {built:?}, total {:?}", t0.elapsed());
    }
    // false: 3x is not 4x - 2
    assert!(add_tree_law(n, 2, &mul_const(3, &v(0)), &mul_const(5, &v(0))).is_none());
}

/// Constant-multiplication laws (`(a + b) x`, `(a b) x`, `a (x + y)`, `(2^j - 1) x`) for constants up to `MULMINER_MAX`
/// (default 7), each proved by `add_tree_law` and kernel-checked; prints carries per side and cost, so the carry cap
/// (env `CARRY_CAP`, default 10) can be probed.
/// The constant-multiplication laws over constants up to `max`: sums, products, differences, distribution over `x+y`, `x-y`.
fn mul_laws(max: u32) -> Vec<(String, Term, Term)> {
    let (x, y) = (Term::V(0), Term::V(1));
    let add = |a: Term, b: Term| Term::Op(0, Box::new(a), Box::new(b));
    let mut laws: Vec<(String, Term, Term)> = vec![];
    for a in 1..=max {
        for b in a..=max {
            laws.push((format!("({a}+{b})x = {a}x + {b}x"), mul_const(a + b, &x), add(mul_const(a, &x), mul_const(b, &x))));
            laws.push((format!("({a}*{b})x = {a}({b}x)"), mul_const(a * b, &x), mul_const(a, &mul_const(b, &x))));
            if b > a {
                let sub = |l: Term, r: Term| Term::Op(4, Box::new(l), Box::new(r));
                laws.push((format!("({b}-{a})x = {b}x - {a}x"), mul_const(b - a, &x), sub(mul_const(b, &x), mul_const(a, &x))));
            }
        }
        let sub = |l: Term, r: Term| Term::Op(4, Box::new(l), Box::new(r));
        laws.push((format!("{a}(x-y) = {a}x - {a}y"), mul_const(a, &sub(x.clone(), y.clone())), sub(mul_const(a, &x), mul_const(a, &y))));
        laws.push((format!("{a}(x+y) = {a}x + {a}y"), mul_const(a, &add(x.clone(), y.clone())), add(mul_const(a, &x), mul_const(a, &y))));
    }
    laws
}

#[test]
#[ignore]
fn mul_conjecture_miner() {
    let _scope = tatic::kernel::InternScope::enter();
    println!("MULMINER machine at start: {}", machine_state());
    let env = |k: &str, d: u32| std::env::var(k).ok().and_then(|v| v.parse().ok()).unwrap_or(d);
    let max = env("MULMINER_MAX", 7);
    let n = 4usize;
    let only = std::env::var("MULMINER_ONLY").unwrap_or_default();
    let mut laws = mul_laws(max);
    laws.retain(|l| l.0.contains(&only));
    let (mut proved, mut none, mut capped, t0) = (0, 0, 0, Instant::now());
    for (name, t1, t2) in &laws {
        let cs = [t1, t2].map(|t| Machine::parse(t).map_or(0, |m| m.carries()));
        if !(1..=6).all(|w| t1.plausibly_equals(t2, w, 2)) {
            continue;
        }
        let t = Instant::now();
        match add_tree_law(n, 2, t1, t2) {
            Some((p, s)) => {
                let built = t.elapsed();
                ck(name, &p, &s);
                proved += 1;
                println!("MULMINER {name}: carries {cs:?}, build {built:?}, total {:?}", t.elapsed());
            }
            None if cs[0].max(cs[1]) > carry_cap() => {
                capped += 1;
                println!("MULMINER {name}: carries {cs:?} over the cap");
            }
            None => {
                none += 1;
                println!("MULMINER {name}: carries {cs:?}, NO PROOF though it holds at widths 1..6");
            }
        }
    }
    println!("MULMINER machine at end: {}", machine_state());
    println!("MULMINER {} laws, {proved} proved and checked, {capped} over the carry cap, {none} unproved within it, {:?}", laws.len(), t0.elapsed());
}

/// Ablation audit (search note section 32): for each mul law, what a lemma-finding search would have to invent. The
/// proof's lemmas `Id(F_j, G_j(bits, phi(carries)))` are decided by the diagram prover once the midpoint (the phi
/// encodings and the tables `g`) is given, and the midpoint is the coarsest bisimulation, found by `moore_encoding`.
/// Prints per law: carries per side, states, classes, phi bits, table bits of `g`, the Moore time, the total time.
#[test]
#[ignore]
fn ablation_audit() {
    let _scope = tatic::kernel::InternScope::enter();
    println!("AUDIT machine at start: {}", machine_state());
    let max = std::env::var("MULMINER_MAX").ok().and_then(|v| v.parse().ok()).unwrap_or(7);
    let gops = GoodOps::new();
    let (mut n_laws, mut moore_ns, mut total_ns) = (0, 0u128, 0u128);
    for (name, t1, t2) in mul_laws(max) {
        let (Some(m1), Some(m2)) = (Machine::parse(&t1), Machine::parse(&t2)) else { continue };
        if !(1..=6).all(|w| t1.plausibly_equals(&t2, w, 2)) || m1.carries().max(m2.carries()) > carry_cap() {
            continue;
        }
        let t = Instant::now();
        let Some(enc) = moore_encoding(&m1, &m2, 2, &gops, None) else { continue };
        let moore = t.elapsed();
        let t = Instant::now();
        let proved = add_tree_law(4, 2, &t1, &t2).is_some();
        let total = t.elapsed();
        let m = enc.phi[0].len();
        let classes = (0..2).map(|s| enc.phi[s][0].len()).collect::<Vec<_>>();
        let gbits = (1 + m) << (2 + m);
        n_laws += 1;
        moore_ns += moore.as_nanos();
        total_ns += total.as_nanos();
        println!("AUDIT {name}: carries [{}, {}], states {classes:?}, phi bits {m}, g bits {gbits}, moore {moore:?}, proof {total:?}, proved {proved}", m1.carries(), m2.carries());
    }
    println!("AUDIT machine at end: {}", machine_state());
    println!("AUDIT {n_laws} laws, Moore {:.1}s of {:.1}s proof time", moore_ns as f64 / 1e9, total_ns as f64 / 1e9);
}

// ---- Proof-producing decision diagrams (search note section 29). Each lemma over `nv` bits used to be a full case
// tree (2^nv leaves). Here every signal carries a reduced ordered decision diagram node `n` and a kernel proof
// `Id(e, C(n))` that its gate expression equals the node's canonical term `C(n)` (nested `mux` over the bit variables),
// built gate by gate: `op(C(a), C(b)) = C(apply(op, a, b))` is proved by recursion on the diagrams (Harrison's BDD rule
// for HOL, 1995), each step an instance of a closed lemma, memoized per node pair. Two signals have the same node iff
// they are the same Boolean function, so an equality lemma is `trans` of one proof with the `sym` of the other.

/// The binary gates of a diagram: 0 and, 1 or, 2 xor.
fn bop(op: usize, a: Expr, b: Expr) -> Expr {
    match op {
        0 => and(a, b),
        1 => or(a, b),
        _ => xor(a, b),
    }
}
fn bop_val(op: usize, a: bool, b: bool) -> bool {
    match op {
        0 => a && b,
        1 => a || b,
        _ => a != b,
    }
}
fn bop_fn(op: usize) -> Expr {
    match op {
        0 => and_(),
        1 => or_(),
        _ => xor_(),
    }
}

/// The closed lemmas the diagram's steps instantiate (each `Pi bits. GoodBool bits -> Id(Bool0, l, r)`), over bits in
/// the order given: `same[op]`: `op (mux v a b) (mux v c d) = mux v (op a c) (op b d)` (`v a b c d`); `skipl[op]`:
/// `op (mux v a b) y = mux v (op a y) (op b y)` (`v a b y`); `skipr[op]`: `op x (mux v c d) = mux v (op x c) (op x d)`
/// (`v x c d`); `red`: `mux v x x = x` (`v x`); `var`: `v = mux v true false` (`v`).
struct DdLemmas {
    same: Vec<Expr>,
    skipl: Vec<Expr>,
    skipr: Vec<Expr>,
    red: Expr,
    var: Expr,
}

thread_local! {
    static DD_LEMMAS: std::cell::RefCell<Option<std::rc::Rc<DdLemmas>>> = Default::default();
}

/// `Id(Bool0, lhs, rhs)` over `k` bits by case analysis (each leaf is `refl`, checked by evaluation).
fn eq_lemma(k: usize, lhs: &dyn Fn(&[Expr]) -> Expr, rhs: &dyn Fn(&[Expr]) -> Expr) -> Expr {
    lemma_n(k, &|v| id(bool0(), lhs(v), rhs(v)), &|bits| refl(lhs(&bits.iter().map(|b| bit(*b)).collect::<Vec<_>>()))).0
}

fn dd_lemmas() -> std::rc::Rc<DdLemmas> {
    if let Some(l) = DD_LEMMAS.with(|c| c.borrow().clone()) {
        return l;
    }
    let mut same = vec![];
    let mut skipl = vec![];
    let mut skipr = vec![];
    for op in 0..3 {
        same.push(eq_lemma(
            5,
            &move |v| bop(op, mux(v[0].clone(), v[1].clone(), v[2].clone()), mux(v[0].clone(), v[3].clone(), v[4].clone())),
            &move |v| mux(v[0].clone(), bop(op, v[1].clone(), v[3].clone()), bop(op, v[2].clone(), v[4].clone())),
        ));
        skipl.push(eq_lemma(
            4,
            &move |v| bop(op, mux(v[0].clone(), v[1].clone(), v[2].clone()), v[3].clone()),
            &move |v| mux(v[0].clone(), bop(op, v[1].clone(), v[3].clone()), bop(op, v[2].clone(), v[3].clone())),
        ));
        skipr.push(eq_lemma(
            4,
            &move |v| bop(op, v[1].clone(), mux(v[0].clone(), v[2].clone(), v[3].clone())),
            &move |v| mux(v[0].clone(), bop(op, v[1].clone(), v[2].clone()), bop(op, v[1].clone(), v[3].clone())),
        ));
    }
    let red = eq_lemma(2, &|v| mux(v[0].clone(), v[1].clone(), v[1].clone()), &|v| v[1].clone());
    let var = eq_lemma(1, &|v| v[0].clone(), &|v| mux(v[0].clone(), t(), f()));
    let l = std::rc::Rc::new(DdLemmas { same, skipl, skipr, red, var });
    DD_LEMMAS.with(|c| *c.borrow_mut() = Some(l.clone()));
    l
}

/// A Boolean expression `e`, its diagram node `n`, and `p : Id(Bool0, e, C(n))`.
#[derive(Clone)]
struct Sig {
    e: Expr,
    n: usize,
    p: Expr,
}

/// The diagram under construction for one lemma: bit variable `i` is `vars[i]` with witness `goods[i]`.
struct Dd {
    lem: std::rc::Rc<DdLemmas>,
    vars: Vec<Expr>,
    goods: Vec<Expr>,
    gops: GoodOps,
    /// `(variable, hi, lo)`, node id = index + 2 (0 is false, 1 is true).
    nodes: Vec<(usize, usize, usize)>,
    unique: std::collections::HashMap<(usize, usize, usize), usize>,
    canon: std::collections::HashMap<usize, (Expr, Expr)>,
    applied: std::collections::HashMap<(usize, usize, usize), (usize, Expr)>,
}

impl Dd {
    fn mk(&mut self, var: usize, hi: usize, lo: usize) -> usize {
        if hi == lo {
            return hi;
        }
        if let Some(n) = self.unique.get(&(var, hi, lo)) {
            return *n;
        }
        self.nodes.push((var, hi, lo));
        let n = self.nodes.len() + 1;
        self.unique.insert((var, hi, lo), n);
        n
    }
    fn var_of(&self, n: usize) -> usize {
        if n < 2 { usize::MAX } else { self.nodes[n - 2].0 }
    }
    /// The canonical term of node `n` and its `GoodBool` witness.
    fn canon(&mut self, n: usize) -> (Expr, Expr) {
        if n < 2 {
            return (bit(n == 1), good_bit(n == 1));
        }
        if let Some(c) = self.canon.get(&n) {
            return c.clone();
        }
        let (v, hi, lo) = self.nodes[n - 2];
        let (ch, gh) = self.canon(hi);
        let (cl, gl) = self.canon(lo);
        let c = Gb { e: self.vars[v].clone(), g: self.goods[v].clone() };
        let one = Gb { e: t(), g: good_bit(true) };
        let not_c = self.gops.xor(&c, &one);
        let a1 = self.gops.and(&c, &Gb { e: ch, g: gh });
        let a2 = self.gops.and(&not_c, &Gb { e: cl, g: gl });
        let r = self.gops.or(&a1, &a2);
        self.canon.insert(n, (r.e.clone(), r.g.clone()));
        (r.e, r.g)
    }
    /// The node of `op(a, b)` and a proof of `Id(Bool0, op(C(a), C(b)), C(node))`.
    fn apply(&mut self, op: usize, a: usize, b: usize) -> (usize, Expr) {
        if let Some(r) = self.applied.get(&(op, a, b)) {
            return r.clone();
        }
        let (ca, ga) = self.canon(a);
        let (cb, gb) = self.canon(b);
        let res = if a < 2 && b < 2 {
            (bop_val(op, a == 1, b == 1) as usize, refl(bop(op, ca, cb)))
        } else {
            let (va, vb) = (self.var_of(a), self.var_of(b));
            let m = va.min(vb);
            let (ah, al) = if va == m { (self.nodes[a - 2].1, self.nodes[a - 2].2) } else { (a, a) };
            let (bh, bl) = if vb == m { (self.nodes[b - 2].1, self.nodes[b - 2].2) } else { (b, b) };
            let (rh, ph) = self.apply(op, ah, bh);
            let (rl, pl) = self.apply(op, al, bl);
            let r = self.mk(m, rh, rl);
            let (v, gv) = (self.vars[m].clone(), self.goods[m].clone());
            let ((cah, gah), (cal, gal), (cbh, gbh), (cbl, gbl)) = (self.canon(ah), self.canon(al), self.canon(bh), self.canon(bl));
            let ((crh, grh), (crl, _)) = (self.canon(rh), self.canon(rl));
            let step1 = if va == m && vb == m {
                apps(self.lem.same[op].clone(), vec![v.clone(), cah.clone(), cal.clone(), cbh.clone(), cbl.clone(), gv.clone(), gah, gal, gbh, gbl])
            } else if va == m {
                apps(self.lem.skipl[op].clone(), vec![v.clone(), cah.clone(), cal.clone(), cb.clone(), gv.clone(), gah, gal, gb])
            } else {
                apps(self.lem.skipr[op].clone(), vec![v.clone(), ca.clone(), cbh.clone(), cbl.clone(), gv.clone(), ga, gbh, gbl])
            };
            let (xh, xl) = (bop(op, cah, cbh), bop(op, cal, cbl));
            let mid = mux(v.clone(), xh.clone(), xl.clone());
            let target = mux(v.clone(), crh.clone(), crl.clone());
            let fm = lam(bool0(), lam(bool0(), mux(shift(&v, 0, 2), var(1), var(0))));
            let step2 = cong_n(&bool0(), &bool0(), &fm, &[xh, xl], &[crh.clone(), crl.clone()], vec![ph, pl]);
            let lhs = bop(op, ca, cb);
            let p12 = trans_proof(&bool0(), &lhs, &mid, &target, step1, step2);
            if rh == rl {
                let red = apps(self.lem.red.clone(), vec![v, crh.clone(), gv, grh]);
                (r, trans_proof(&bool0(), &lhs, &target, &crh, p12, red))
            } else {
                (r, p12)
            }
        };
        self.applied.insert((op, a, b), res.clone());
        res
    }
}

/// The gate operations shared by the proof-term builder (`GoodOps`, over `Gb`) and the diagram (`DdGates`, over `Sig`).
trait Gates {
    type S: Clone;
    fn and(&self, x: &Self::S, y: &Self::S) -> Self::S;
    fn or(&self, x: &Self::S, y: &Self::S) -> Self::S;
    fn xor(&self, x: &Self::S, y: &Self::S) -> Self::S;
    fn konst(&self, b: bool) -> Self::S;
    /// The truth table `tab` over the signals `vars`.
    fn table(&self, vars: &[Self::S], tab: &dyn Fn(&[bool]) -> bool) -> Self::S;
    fn sum3(&self, a: &Self::S, b: &Self::S, c: &Self::S) -> Self::S {
        let ab = self.xor(a, b);
        self.xor(&ab, c)
    }
    fn maj(&self, a: &Self::S, b: &Self::S, c: &Self::S) -> Self::S {
        let (ab, x) = (self.and(a, b), self.xor(a, b));
        let cx = self.and(c, &x);
        self.or(&ab, &cx)
    }
}

impl Gates for GoodOps {
    type S = Gb;
    fn and(&self, x: &Gb, y: &Gb) -> Gb {
        GoodOps::and(self, x, y)
    }
    fn or(&self, x: &Gb, y: &Gb) -> Gb {
        GoodOps::or(self, x, y)
    }
    fn xor(&self, x: &Gb, y: &Gb) -> Gb {
        GoodOps::xor(self, x, y)
    }
    fn konst(&self, b: bool) -> Gb {
        Gb { e: bit(b), g: good_bit(b) }
    }
    /// The witness is a placeholder: claims built this way are only stated, never proved through it.
    fn table(&self, vars: &[Gb], tab: &dyn Fn(&[bool]) -> bool) -> Gb {
        Gb { e: table_app(&vars.iter().map(|g| g.e.clone()).collect::<Vec<_>>(), tab), g: f() }
    }
}

struct DdGates {
    dd: std::cell::RefCell<Dd>,
}

impl DdGates {
    fn new(vars: Vec<Expr>, goods: Vec<Expr>) -> DdGates {
        DdGates {
            dd: std::cell::RefCell::new(Dd {
                lem: dd_lemmas(),
                vars,
                goods,
                gops: GoodOps::new(),
                nodes: vec![],
                unique: Default::default(),
                canon: Default::default(),
                applied: Default::default(),
            }),
        }
    }
    fn var_sig(&self, i: usize) -> Sig {
        let mut dd = self.dd.borrow_mut();
        let n = dd.mk(i, 1, 0);
        let (v, gv) = (dd.vars[i].clone(), dd.goods[i].clone());
        Sig { e: v.clone(), n, p: apps(dd.lem.var.clone(), vec![v, gv]) }
    }
    fn gate(&self, op: usize, x: &Sig, y: &Sig) -> Sig {
        let mut dd = self.dd.borrow_mut();
        let (r, pr) = dd.apply(op, x.n, y.n);
        let (cx, cy, cr) = (dd.canon(x.n).0, dd.canon(y.n).0, dd.canon(r).0);
        let congp = cong_n(&bool0(), &bool0(), &bop_fn(op), &[x.e.clone(), y.e.clone()], &[cx.clone(), cy.clone()], vec![x.p.clone(), y.p.clone()]);
        let p = trans_proof(&bool0(), &bop(op, x.e.clone(), y.e.clone()), &bop(op, cx, cy), &cr, congp, pr);
        Sig { e: bop(op, x.e.clone(), y.e.clone()), n: r, p }
    }
    /// `Id(Bool0, a.e, b.e)` when both signals are the same function.
    fn equate(&self, a: &Sig, b: &Sig) -> Option<Expr> {
        if a.n != b.n {
            return None;
        }
        let c = self.dd.borrow_mut().canon(a.n).0;
        Some(trans_proof(&bool0(), &a.e, &c, &b.e, a.p.clone(), sym(&bool0(), &b.e, &c, b.p.clone())))
    }
}

impl Gates for DdGates {
    type S = Sig;
    fn and(&self, x: &Sig, y: &Sig) -> Sig {
        self.gate(0, x, y)
    }
    fn or(&self, x: &Sig, y: &Sig) -> Sig {
        self.gate(1, x, y)
    }
    fn xor(&self, x: &Sig, y: &Sig) -> Sig {
        self.gate(2, x, y)
    }
    fn konst(&self, b: bool) -> Sig {
        Sig { e: bit(b), n: b as usize, p: refl(bit(b)) }
    }
    /// The table's own reduced diagram, composed along its nodes (each node a `mux` of the signal at its level), so the
    /// expression is the body of `table_app` instantiated; `e` is stated in `table_app` form (the same term up to beta).
    fn table(&self, vars: &[Sig], tab: &dyn Fn(&[bool]) -> bool) -> Sig {
        let d = tab_bdd(vars.len(), tab);
        let one = self.konst(true);
        let mut sigs: Vec<Sig> = vec![self.konst(false), one.clone()];
        for &(level, hi, lo) in &d.nodes {
            let c = &vars[level];
            let not_c = self.xor(c, &one);
            let (a1, a2) = (self.and(c, &sigs[hi]), self.and(&not_c, &sigs[lo]));
            let s = self.or(&a1, &a2);
            sigs.push(s);
        }
        let mut s = sigs[d.root].clone();
        s.e = table_app(&vars.iter().map(|v| v.e.clone()).collect::<Vec<_>>(), tab);
        s
    }
}

/// Closed `Pi bits. GoodBool bits -> Id(Bool0, a, b)` for the two signals `build` makes from the bit variables, by
/// diagrams instead of a case tree; `None` when they are different functions. Same shape as `lemma_n`'s proof.
fn lemma_dd(nv: usize, build: &dyn Fn(&DdGates, &[Sig]) -> (Sig, Sig)) -> Option<Expr> {
    let vars: Vec<Expr> = (0..nv).map(|m| var((2 * nv - 1 - m) as u32)).collect();
    let goods: Vec<Expr> = (0..nv).map(|m| var((nv - 1 - m) as u32)).collect();
    let g = DdGates::new(vars, goods);
    let inputs: Vec<Sig> = (0..nv).map(|i| g.var_sig(i)).collect();
    let (a, b) = build(&g, &inputs);
    let mut proof = g.equate(&a, &b)?;
    for _ in 0..nv {
        proof = lam(app(good_bool(), var(nv as u32 - 1)), proof);
    }
    for _ in 0..nv {
        proof = lam(bool0(), proof);
    }
    Some(proof)
}

#[test]
fn decision_diagram_proofs_check_and_beat_the_case_tree() {
    let _scope = tatic::kernel::InternScope::enter();
    // associativity of xor over 3 bits, against `lemma_n`'s statement
    let sides = |g: &DdGates, v: &[Sig]| (g.xor(&g.xor(&v[0], &v[1]), &v[2]), g.xor(&v[0], &g.xor(&v[1], &v[2])));
    let (pn, ty) = lemma_n(
        3,
        &|v| id(bool0(), xor(xor(v[0].clone(), v[1].clone()), v[2].clone()), xor(v[0].clone(), xor(v[1].clone(), v[2].clone()))),
        &|bits| {
            let l = |i: usize| bit(bits[i]);
            refl(xor(xor(l(0), l(1)), l(2)))
        },
    );
    ck("case tree", &pn, &ty);
    let pd = lemma_dd(3, &sides).expect("same function");
    ck("diagram", &pd, &ty);
    // a false equation has no diagram proof
    assert!(lemma_dd(2, &|g, v| (g.and(&v[0], &v[1]), g.or(&v[0], &v[1]))).is_none());
    // a chain of 14 bits in two association orders: 2^14 case-tree leaves, a few dozen diagram nodes
    let nv = 14;
    let chain = |g: &DdGates, v: &[Sig]| {
        let left = v[1..].iter().fold(v[0].clone(), |a, b| g.xor(&a, b));
        let right = v[..nv - 1].iter().rev().fold(v[nv - 1].clone(), |a, b| g.xor(b, &a));
        (left, right)
    };
    let t0 = Instant::now();
    let pd = lemma_dd(nv, &chain).expect("parity chains agree");
    let built = t0.elapsed();
    let vv = |m: usize| var((2 * nv - 1 - m) as u32);
    let left = (1..nv).fold(vv(0), |a, i| xor(a, vv(i)));
    let right = (0..nv - 1).rev().fold(vv(nv - 1), |a, i| xor(vv(i), a));
    let mut ty = id(bool0(), left, right);
    for _ in 0..nv {
        ty = pi(app(good_bool(), var(nv as u32 - 1)), ty);
    }
    for _ in 0..nv {
        ty = pi(bool0(), ty);
    }
    let t1 = Instant::now();
    ck("parity chains", &pd, &ty);
    println!("DD 14-bit parity chains: build {built:?}, check {:?}", t1.elapsed());
}

/// Rewriting with the library rules over every constant-multiplication law (search note section 35): per law the
/// carries of the target machines, whether a whole-term machine proof was still needed, build and check times; the
/// totals show what the rules buy. `ABLATE=shldist,shldistsub,double,doublechain` (any subset) removes rules.
#[test]
#[ignore]
fn rewrite_rules_over_the_mul_laws() {
    let _scope = tatic::kernel::InternScope::enter();
    println!("RULES machine at start: {}", machine_state());
    let max = std::env::var("MULMINER_MAX").ok().and_then(|v| v.parse().ok()).unwrap_or(7);
    let (mut proved, mut none, mut machine_free, mut over_cap, t0) = (0, 0, 0, 0, Instant::now());
    for (name, t1, t2) in mul_laws(max) {
        if !(1..=6).all(|w| t1.plausibly_equals(&t2, w, 2)) {
            continue;
        }
        let cs = [&t1, &t2].map(|t| Machine::parse(t).map_or(0, |m| m.carries()));
        let before = MACHINE_FALLBACKS.load(std::sync::atomic::Ordering::Relaxed);
        let t = Instant::now();
        let r = rewrite_law(4, 2, &t1, &t2);
        let built = t.elapsed();
        let fell = MACHINE_FALLBACKS.load(std::sync::atomic::Ordering::Relaxed) - before;
        match r {
            Some((p, s)) => {
                let t = Instant::now();
                ck(&name, &p, &s);
                proved += 1;
                machine_free += (fell == 0) as u32;
                over_cap += (cs[0].max(cs[1]) > carry_cap()) as u32;
                println!("RULES {name}: carries {cs:?}, machine proofs used {fell}, build {built:?}, check {:?}", t.elapsed());
            }
            None => {
                none += 1;
                println!("RULES {name}: carries {cs:?}, no proof, {built:?}");
            }
        }
    }
    println!("RULES machine at end: {}", machine_state());
    println!("RULES rule instances: {:?}", RULE_HITS.lock().unwrap());
    println!("RULES {proved} proved ({machine_free} with no whole-term machine proof, {over_cap} beyond the carry cap), {none} not, {:?}", t0.elapsed());
}

/// Rule miner (search note section 36): candidate rules are the equal pairs of the `shl1` pool (two variables, width 4,
/// the shl miner's pool), oriented to a strictly smaller right side and proved by `add_tree_law`. The targets are the
/// mul laws that still needed a whole-term machine proof under the built-in rules (the "stragglers"). A candidate is
/// tried on the stragglers whose normalized terms contain an instance of its left side; it scores by the machine
/// proofs it removes. Env: `MULMINER_MAX` (default 7), `RULEMINER_TRIALS` (candidate cap, default 400).
#[test]
#[ignore]
fn rule_miner() {
    let _scope = tatic::kernel::InternScope::enter();
    println!("RULEMINER machine at start: {}", machine_state());
    let env = |k: &str, d: usize| std::env::var(k).ok().and_then(|v| v.parse().ok()).unwrap_or(d);
    let (max, trials) = (env("MULMINER_MAX", 7) as u32, env("RULEMINER_TRIALS", 400));
    let (n, nv) = (4usize, 2usize);
    let ops = ops_for(n);
    let goods: Vec<(Expr, Expr)> = (0..2).map(|i| (var((3 - i) as u32), var((1 - i) as u32))).collect();
    let fallbacks = || MACHINE_FALLBACKS.load(std::sync::atomic::Ordering::Relaxed);
    // stragglers under the built-in rules
    let mut stragglers: Vec<(String, Term, Term, [Term; 2], u64, std::time::Duration)> = vec![];
    let family = std::env::var("RULEMINER_FAMILY").unwrap_or_else(|_| "mul".into());
    let laws: Vec<(String, Term, Term)> = if family == "shl" {
        let conj = shl_conjectures(2);
        let stride = (conj.len() / env("RULEMINER_LAWS", 250)).max(1);
        conj.into_iter().step_by(stride).map(|(a, b)| (format!("{} = {}", a.show(), b.show()), a, b)).collect()
    } else {
        mul_laws(max)
    };
    for (name, t1, t2) in laws.iter().cloned() {
        if !(1..=6).all(|w| t1.plausibly_equals(&t2, w, 2)) || [&t1, &t2].iter().any(|t| Machine::parse(t).is_some_and(|m| m.carries() > carry_cap())) {
            continue;
        }
        let before = fallbacks();
        let t = Instant::now();
        let r = rewrite_law(n, 2, &t1, &t2);
        let took = t.elapsed();
        let fell = fallbacks() - before;
        if r.is_some() && fell > 0 {
            let normal = [rewrite(&t1, n, &ops, &goods).0, rewrite(&t2, n, &ops, &goods).0];
            println!("RULEMINER straggler {name}: {} = {} ({fell} machine proofs, {took:?})", normal[0].show(), normal[1].show());
            stragglers.push((name, t1, t2, normal, fell, took));
        }
    }
    let base_time: f64 = stragglers.iter().map(|s| s.5.as_secs_f64()).sum();
    println!("RULEMINER {family}: {} stragglers of {} laws, {:.1}s base", stragglers.len(), laws.len(), base_time);
    // goal-directed candidates: abstract each arithmetic subterm of a straggler's normalized terms into a pattern over
    // at most two variables (cutting subterms into variables), and look for a smaller term over the same variables
    // with the same values at width 4 (a pool of all terms up to RULEMINER_SIZE nodes, indexed by value)
    let psize = env("RULEMINER_SIZE", 5);
    let mut by_size: Vec<Vec<Term>> = vec![vec![]; psize + 1];
    by_size[1] = vec![Term::V(0), Term::V(1), Term::Zero, Term::Ones];
    for sz in 2..=psize {
        let mut level = vec![];
        for x in &by_size[sz - 1] {
            level.push(Term::Op(6, Box::new(x.clone()), Box::new(Term::Zero)));
        }
        for i in 1..sz - 1 {
            for l in &by_size[i] {
                for r in &by_size[sz - 1 - i] {
                    for o in [0usize, 1, 2, 3, 4] {
                        level.push(Term::Op(o, Box::new(l.clone()), Box::new(r.clone())));
                    }
                }
            }
        }
        by_size[sz] = level;
    }
    let sig = |t: &Term| -> Vec<u128> { (0..256u128).map(|i| t.interp(n, &[i & 15, i >> 4])).collect() };
    let mut index: std::collections::HashMap<Vec<u128>, Vec<Term>> = Default::default();
    for t in by_size.iter().flatten() {
        index.entry(sig(t)).or_default().push(t.clone());
    }
    println!("RULEMINER pool of {} terms, {} distinct functions", by_size.iter().map(|v| v.len()).sum::<usize>(), index.len());
    /// The patterns obtained from `t` by cutting subterms into variables: (pattern, cut subterms in variable order).
    fn abstractions(t: &Term, cap: usize) -> Vec<(Term, Vec<Term>)> {
        let mut out = vec![];
        if !matches!(t, Term::Zero | Term::Ones) {
            out.push((Term::V(0), vec![t.clone()]));
        } else {
            out.push((t.clone(), vec![]));
        }
        if let Term::Op(o, a, b) = t {
            for (pa, ca) in abstractions(a, cap) {
                for (pb, cb) in abstractions(b, cap) {
                    // renumber the right pattern's variables after the left's, merging equal cut subterms
                    let mut cuts = ca.clone();
                    let mut map = vec![];
                    for c in &cb {
                        let at = cuts.iter().position(|x| x.show() == c.show()).unwrap_or_else(|| {
                            cuts.push(c.clone());
                            cuts.len() - 1
                        });
                        map.push(at);
                    }
                    if cuts.len() > cap {
                        continue;
                    }
                    fn renum(p: &Term, map: &[usize]) -> Term {
                        match p {
                            Term::V(i) => Term::V(map[*i]),
                            Term::Op(o, a, b) => Term::Op(*o, Box::new(renum(a, map)), Box::new(renum(b, map))),
                            _ => p.clone(),
                        }
                    }
                    out.push((Term::Op(*o, Box::new(pa.clone()), Box::new(renum(&pb, &map))), cuts));
                }
            }
        }
        out.retain(|(_, c)| c.len() <= cap);
        out
    }
    // RULEMINER_ANY=1: also abstract subterms without add/sub (constant folding inside shifts and bitwise nodes)
    let any_op = env("RULEMINER_ANY", 0) == 1;
    let mut seen_pat: std::collections::HashSet<String> = Default::default();
    let mut cands: Vec<(Term, Term)> = vec![];
    for st in &stragglers {
        let mut subs = vec![];
        st.3[0].subterms(&mut subs);
        st.3[1].subterms(&mut subs);
        for sub in subs.iter().filter(|t| (any_op || t.uses_add()) && t.size() >= if any_op { 2 } else { 3 }) {
            for (pat, _) in abstractions(sub, 2) {
                let Term::Op(..) = pat else { continue };
                if !seen_pat.insert(pat.show()) || pat.size() > 9 {
                    continue;
                }
                let Some(group) = index.get(&sig(&pat)) else { continue };
                let uses = |t: &Term, v: usize| t.show().contains(VARS[v]);
                for r in group.iter().filter(|r| r.size() < pat.size() && (0..2).all(|v| !uses(r, v) || uses(&pat, v))) {
                    cands.push((pat.clone(), r.clone()));
                }
            }
        }
    }
    // cross-side candidates: a subterm of one normalized side and a subterm of the other with the same value, both
    // abstracted by the same cuts (up to four variables): the rule `abstract(s) -> abstract(s')`
    let cross_cap = env("RULEMINER_VARS", 4);
    for st in &stragglers {
        let (mut sl, mut sr) = (vec![], vec![]);
        st.3[0].subterms(&mut sl);
        st.3[1].subterms(&mut sr);
        for (xs, ys) in [(&sl, &sr), (&sr, &sl)] {
            for x in xs.iter().filter(|t| t.uses_add() && t.size() >= 3 && t.size() <= 13) {
                for y in ys.iter().filter(|t| t.size() <= 13 && t.show() != x.show()) {
                    if !(1..=4).all(|w| x.plausibly_equals(y, w, 2)) {
                        continue;
                    }
                    for (pat, cuts) in abstractions(x, cross_cap) {
                        let Term::Op(..) = pat else { continue };
                        if cuts.len() <= 2 || pat.size() > 13 {
                            continue; // up to two variables is the pool route's job
                        }
                        // express y with the same cuts, through placeholders V(4+j)
                        let mut yy = y.clone();
                        for (j, c) in cuts.iter().enumerate() {
                            yy = replace_term(&yy, c, &Term::V(4 + j));
                        }
                        fn bare(t: &Term) -> bool {
                            match t {
                                Term::V(i) => *i >= 4,
                                Term::Op(_, a, b) => bare(a) && bare(b),
                                _ => true,
                            }
                        }
                        fn renum(t: &Term) -> Term {
                            match t {
                                Term::V(i) => Term::V(i - 4),
                                Term::Op(o, a, b) => Term::Op(*o, Box::new(renum(a)), Box::new(renum(b))),
                                _ => t.clone(),
                            }
                        }
                        if bare(&yy) && yy.size() < pat.size() + 4 && seen_pat.insert(format!("{} => {}", pat.show(), renum(&yy).show())) {
                            cands.push((pat.clone(), renum(&yy)));
                        }
                    }
                }
            }
        }
    }
    // per left side, the smallest right side only
    cands.sort_by_key(|(l, r)| (l.size(), l.show(), r.size(), r.show()));
    cands.dedup_by_key(|(l, _)| l.show());
    println!("RULEMINER {} oriented candidates (one per left side)", cands.len());
    // keep candidates whose left side matches a subterm of some straggler's normalized terms
    let applicable = |l: &Term| {
        stragglers.iter().any(|s| {
            let mut subs = vec![];
            s.3[0].subterms(&mut subs);
            s.3[1].subterms(&mut subs);
            subs.iter().any(|t| match_pat(l, t, &mut vec![None; 8]))
        })
    };
    let cands: Vec<(Term, Term)> = cands.into_iter().filter(|(l, _)| applicable(l)).take(trials).collect();
    println!("RULEMINER {} applicable candidates (cap {trials})", cands.len());
    let mut results = vec![];
    for (l, r) in &cands {
        // the candidate must itself be provable
        let t = Instant::now();
        if add_tree_law(n, l.max_var().max(r.max_var()) + 1, l, r).is_none() {
            continue;
        }
        EXTRA_RULES.with(|e| *e.borrow_mut() = vec![(l.clone(), r.clone())]);
        let (mut removed, mut time) = (0u64, 0f64);
        let mut fixed = vec![false; stragglers.len()];
        for (si, s) in stragglers.iter().enumerate() {
            RULE_BUDGET.store(200, std::sync::atomic::Ordering::Relaxed);
            let before = fallbacks();
            let t = Instant::now();
            let ok = rewrite_law(n, 2, &s.1, &s.2).is_some();
            time += t.elapsed().as_secs_f64();
            fixed[si] = ok && fallbacks() - before < s.4;
            removed += fixed[si] as u64;
        }
        EXTRA_RULES.with(|e| e.borrow_mut().clear());
        RULE_BUDGET.store(i64::MAX / 2, std::sync::atomic::Ordering::Relaxed);
        let _ = t;
        results.push((removed, time, l.show(), r.show(), fixed));
    }
    results.sort_by(|a, b| b.0.cmp(&a.0).then(a.1.partial_cmp(&b.1).unwrap()));
    for (removed, time, l, r, _) in results.iter().take(10) {
        println!("RULEMINER helps {removed} of {} stragglers ({time:.1}s total): {l} -> {r}", stragglers.len());
    }
    // greedy cover: the rule fixing most still-unfixed stragglers, until none adds one
    let mut covered = vec![false; stragglers.len()];
    loop {
        let gain = |f: &Vec<bool>| f.iter().zip(&covered).filter(|(a, c)| **a && !**c).count();
        let Some(best) = results.iter().max_by_key(|r| gain(&r.4)).filter(|r| gain(&r.4) > 0) else { break };
        println!("RULEMINER chosen (+{}): {} -> {}", gain(&best.4), best.2, best.3);
        for (c, f) in covered.iter_mut().zip(&best.4) {
            *c |= *f;
        }
    }
    println!("RULEMINER {} of {} stragglers covered by the chosen rules", covered.iter().filter(|c| **c).count(), stragglers.len());
    for (st, c) in stragglers.iter().zip(&covered) {
        if !c {
            println!("RULEMINER uncovered: {}", st.0);
        }
    }
    println!("RULEMINER machine at end: {}", machine_state());
}
