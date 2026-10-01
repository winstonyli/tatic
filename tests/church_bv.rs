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
    let cond = and(app2(eq_bv(n), a, lit(n, min)), app2(eq_bv(n), b, lit(n, all)));
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
