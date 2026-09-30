// A fixed-width bit-vector as a Church-encoded n-ary tuple of Church Bools, with an
// unrolled ripple-carry `add`, on the unchanged kernel (public API only).
use std::time::Instant;
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
