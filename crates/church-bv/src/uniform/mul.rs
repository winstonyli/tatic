// Spike (2026-11-01, task u3; builds on `width.rs`): the multiplier through the stream route, a second, nested induction.
//
// Stage A, the definition. Shift-and-add: `acc_0 = 0`, `acc_(j+1) = acc_j + (y_j ? x << j : 0)`, with the stream adder of
// `width.rs` and the stream shift `shl` below. The kernel has no cumulativity, and that fixes the shape:
//   * the stream adder `sumbit(k, ..)` reads its operands at `Nat_k` and is indexed by `Nat_(k+1)` (its count), so
//     `add : Bits(k) -> Bits(k) -> Bits(k+1)` raises the index level by one. No term lowers a stream's level: that would need
//     `Nat_k -> Nat_(k+1)` (`embed` goes the other way, `Nat_(k+1) -> Nat_k`; `i C z s` for `i : Nat_k` needs `C : Sort k`).
//   * so one Church `Nat` fold cannot carry the accumulator: its state `Bits(k)` would have to be the adder's output `Bits(k+1)`
//     (test `a_single_nested_fold_is_ill_typed` shows the kernel's message; `src/wnat.rs` lifts this with a W-built index). The outer loop over the multiplier's bit
//     positions is therefore UNROLLED in the meta-language: m multiplier bits are m adders, `acc_j : Bits(k0 + j)`, and the final
//     stream is indexed by `Nat_(k0 + m)`. The law is uniform in the OUTPUT POSITION (and in the multiplicand stream), not in the
//     multiplier's width: the level of the statement grows with m.
//   * `shl : Bits(k) -> Bits(k+1)` (a delay: the fold over the count carries (position, x at the previous position)); `x << j` is
//     `shl` applied j times, `Bits(k0 + j)`, which is exactly the level `acc_j` and the adder at step j expect.
//   * the partial product is `y_j & x_shifted`, the mask FIRST (`and(y_j, bit)`), so `y_j = false` makes it the zero stream by
//     computation (`and ff b` reduces to `ff` for any `b`), with no goodness hypothesis on the shifted stream.
use crate::encoding;
use super::width::T::*;
use super::width::*;
use std::time::Instant;
use tatic_kernel::{self as kernel, Ctx, Expr};

// ---------- stage A: the stream multiplier ----------
/// One step of the shift's fold: (position, x at the previous position) -> (position + 1, x at this position).
pub(crate) fn shl_step(k: u32, x: T) -> T {
    lm("u", state(k), pair_s(k, ap(succ(k), fst(k, v("u"))), ap(x, fst(k, v("u")))))
}
/// The shift's fold over the count `n`, starting from (zero, `fill`).
pub(crate) fn shl_state(k: u32, x: T, fill: bool, n: T) -> T {
    ap3(n, state(k), pair_s(k, zero(k), if fill { tt() } else { ff() }), shl_step(k, x))
}
/// `Bits(k) -> Bits(k+1)`: bit N of the result is `x (N-1)`, and the fill bit at N = 0 (false for the real shift; `fill = true`
/// is the mutant the shift tests use). The fold over the count carries (position, the value `x` had at the position before).
pub(crate) fn shl_fill(k: u32, x: T, fill: bool) -> T {
    lm("N", nat(k + 1), snd(k, shl_state(k, x, fill, v("N"))))
}
pub(crate) fn shl(k: u32, x: T) -> T {
    shl_fill(k, x, false)
}
/// `x << j`, in `Bits(k0 + j)`.
pub(crate) fn shl_n(k0: u32, j: usize, x: T, fill: bool) -> T {
    (0..j).fold(x, |e, i| shl_fill(k0 + i as u32, e, fill))
}
/// The partial product stream at level `l`: `i -> and(yb, sh i)`.
pub(crate) fn tm(l: u32, yb: T, sh: T) -> T {
    lm("i", nat(l), and2(yb, ap(sh, v("i"))))
}
/// The sum stream, `Bits(k+1)`.
pub(crate) fn add_stream(k: u32, a: T, c: T) -> T {
    lm("N", nat(k + 1), sumbit(k, a, c, v("N")))
}
/// `\x. acc_j x` as a CLOSED kernel term, `Bits(k0) -> Bits(k0 + j)`. `acc_j` mentions `acc_(j-1)` three times (the adder reads
/// each operand in its step and again in its sum), so spelling it as a meta-level tree is 3^j in size and exhausted 8 GB at
/// j = 5; the closed `Expr` handle is shared, and each level is applied to `x` instead.
pub(crate) fn acc_fn(k0: u32, ys: &[T], j: usize, fill: bool) -> Expr {
    if j == 0 {
        return ex(&lm("x", bits(k0), zs(k0)));
    }
    let l = k0 + (j - 1) as u32;
    let prev = K(acc_fn(k0, ys, j - 1, fill));
    ex(&lm("x", bits(k0), add_stream(l, ap(prev, v("x")), tm(l, ys[j - 1].clone(), shl_n(k0, j - 1, v("x"), fill)))))
}
/// `acc_j x`, in `Bits(k0 + j)`.
pub(crate) fn acc_upto(k0: u32, ys: &[T], x: T, j: usize) -> T {
    acc_upto_fill(k0, ys, x, j, false)
}
pub(crate) fn acc_upto_fill(k0: u32, ys: &[T], x: T, j: usize, fill: bool) -> T {
    ap(K(acc_fn(k0, ys, j, fill)), x)
}
/// The stream product of `x : Bits(k0)` and the multiplier bits `ys` (meta-level bools), in `Bits(k0 + ys.len())`.
pub(crate) fn mul_stream(k0: u32, ys: &[T], x: T) -> T {
    acc_upto(k0, ys, x, ys.len())
}
/// `mul_stream` with the shift's fill bit chosen (the mutation tests of `shift.rs`).
pub(crate) fn mul_stream_fill(k0: u32, ys: &[T], x: T, fill: bool) -> T {
    ap(K(acc_fn(k0, ys, ys.len(), fill)), x)
}
pub(crate) fn bit_of(y: u128, j: usize) -> T {
    if (y >> j) & 1 == 1 { tt() } else { ff() }
}
pub(crate) fn ybits(m: usize, y: u128) -> Vec<T> {
    (0..m).map(|j| bit_of(y, j)).collect()
}

#[test]
fn stream_multiplier_is_well_typed_at_every_level() {
    for k0 in [1u32, 2] {
        for m in 1..=3usize {
            let f = lm("x", bits(k0), mul_stream(k0, &ybits(m, 0), v("x")));
            let ty = kernel::typecheck(&ex(&f)).unwrap_or_else(|e| panic!("k0={k0} m={m}: {e}"));
            let want = ex(&arr(bits(k0), bits(k0 + m as u32)));
            assert!(kernel::def_eq(&ty, &want), "k0={k0} m={m}: type is not Bits(k0) -> Bits(k0+m)");
        }
    }
}

/// The product bits of the streams on concrete numbers: positions 0 .. 2m+1 of x*y (exact, the streams do not truncate).
#[test]
fn stream_multiplier_computes_products() {
    let (k0, m) = (1u32, 3usize);
    let xs_of = |x: u128| ap(lookup(m), tuple(&(0..m).map(|i| bit_of(x, i)).collect::<Vec<_>>()));
    for (x, y) in [(5u128, 3u128), (7, 7), (6, 5), (3, 0), (0, 7), (7, 1), (4, 6), (1, 1)] {
        let prod = mul_stream(k0, &ybits(m, y), xs_of(x));
        for p in 0..2 * m + 2 {
            let got = ex(&ap(prod.clone(), numeral(k0 + m as u32, p)));
            assert!(kernel::def_eq(&got, &ex(&bit_of(x * y, p))), "{x} * {y}: bit {p} of {}", x * y);
        }
    }
}

/// The single-fold definition one would like (outer fold over the count, state = (position, accumulator stream)) does not
/// typecheck: the step returns `Bits(k+1)` where the state wants `Bits(k)`. The kernel's message is printed. This is a limit of
/// Church numerals only: `src/wnat.rs` writes the same fold over a W-built index.
#[test]
fn a_single_nested_fold_is_ill_typed() {
    let k = 1u32;
    // state := Sigma(_:Nat_k, Bits(k)) : Sort(k+1); step (p, acc) = (succ p, add acc x)
    let st = Sig("_s", b(nat(k)), b(bits(k)));
    let pr = |a: T, c: T| Pair("_k", b(bits(k)), b(a), b(c));
    let fst_ = |u: T| SigRec(b(lm("_s", st.clone(), nat(k))), b(lm("a", nat(k), lm("b", bits(k), v("a")))), b(u));
    let snd_ = |u: T| SigRec(b(lm("_s", st.clone(), bits(k))), b(lm("a", nat(k), lm("b", bits(k), v("b")))), b(u));
    let stp = lm("u", st.clone(), pr(ap(succ(k), fst_(v("u"))), add_stream(k, snd_(v("u")), v("x"))));
    let fold = lm("x", bits(k), lm("N", nat(k + 1), ap3(v("N"), st.clone(), pr(zero(k), zs(k)), stp)));
    let r = kernel::typecheck(&ex(&fold));
    let m = r.expect_err("the single fold typechecked");
    println!("[single nested fold] REJECTED: {}", m.chars().take(300).collect::<String>());
    // the same step with the adder's output forced down a level cannot be written: the lowering Nat_k -> Nat_(k+1) is
    // `i Nat_(k+1) zero succ`, whose C must live in Sort k
    let lower = lm("i", nat(k), ap3(v("i"), nat(k + 1), zero(k + 1), succ(k + 1)));
    let m2 = kernel::typecheck(&ex(&lower)).expect_err("a level-lowering map typechecked");
    println!("[Nat_k -> Nat_(k+1)] REJECTED: {}", m2.chars().take(300).collect::<String>());
}

// ---------- stage B: the adder keeps a known stream ----------
// `Good_k i` for `i : Nat_k`: the induction witness with motives in Sort k (`good1 (k-1)`).
pub(crate) fn gk(k: u32, i: T) -> T {
    ap(good1(k - 1), i)
}
/// `Pi N:Nat_(k+1). Good_(k+1) N -> Good_k (embed N)`: the numerals the fold reads are good.
pub(crate) fn ge_proof(k: u32) -> T {
    lm("N", nat(k + 1), lm("g", ap(good1(k), v("N")),
        ap3(v("g"), lm("M", nat(k + 1), gk(k, embed(k, v("M")))), gzero(k),
            lm("m", nat(k + 1), lm("ih", gk(k, embed(k, v("m"))), gsucc(k, embed(k, v("m")), v("ih")))))))
}
// non-dependent pairs
pub(crate) fn sig2(a: T, c: T) -> T {
    Sig("_p", b(a), b(c))
}
pub(crate) fn mk2(_a_ty: T, c_ty: T, a: T, c: T) -> T {
    Pair("_p", b(c_ty), b(a), b(c))
}
pub(crate) fn pr1(a_ty: T, c_ty: T, p: T) -> T {
    SigRec(b(lm("_s", sig2(a_ty.clone(), c_ty.clone()), a_ty.clone())), b(lm("a", a_ty, lm("b", c_ty, v("a")))), b(p))
}
pub(crate) fn pr2(a_ty: T, c_ty: T, p: T) -> T {
    SigRec(b(lm("_s", sig2(a_ty.clone(), c_ty.clone()), c_ty.clone())), b(lm("a", a_ty, lm("b", c_ty, v("b")))), b(p))
}

/// The adder keeps a stream that is known pointwise (at good positions) to be `sw`, when the other operand is the zero stream:
/// `Pi N:Nat_(k+1). Good N -> Pi su sw:Bits(k). (Pi i:Nat_k. Good_k i -> GoodBool (sw i)) -> (Pi i:Nat_k. Good_k i -> su i = sw i)
///    -> sumbit(su, zs, N) = sw (embed N)`   (`zero_right`), or with `sumbit(zs, su, N)` (the zero operand first).
fn y_stmt(k: u32, zero_right: bool) -> T {
    let (a, c) = if zero_right { (v("su"), zs(k)) } else { (zs(k), v("su")) };
    pi_("N", nat(k + 1), arr(ap(good1(k), v("N")), pi_("su", bits(k), pi_("sw", bits(k),
        arr(pi_("i", nat(k), arr(gk(k, v("i")), ap(goodbool(), ap(v("sw"), v("i"))))),
        arr(pi_("i", nat(k), arr(gk(k, v("i")), idt(bool0(), ap(v("su"), v("i")), ap(v("sw"), v("i"))))),
            idt(bool0(), sumbit(k, a, c, v("N")), ap(v("sw"), embed(k, v("N"))))))))))
}
/// The induction behind the carry lemmas Y (zero right) and Z (`shift.rs`, zero left): with `g : Good N` free, a
/// proof of `Sigma (Good_k (embed N)) (st(maj, a, c, N) = (embed N, false))`, given `to_false(em, ge_m)`, a proof of
/// `maj(a em, c em, false) = false` from the goodness `ge_m` of `em = embed m` (the zero operand makes the carry stay false).
pub(crate) fn carry_false(k: u32, a: &T, c: &T, to_false: &dyn Fn(T, T) -> T) -> T {
    let stn = |m: T| st(k, maj, a.clone(), c.clone(), m);
    let target = |m: T| pair_s(k, embed(k, m), ff());
    let eq_ty = |m: T| idt(state(k), stn(m.clone()), target(m));
    let gty = |m: T| gk(k, embed(k, m));
    let pmf = |m: T| sig2(gty(m.clone()), eq_ty(m));
    let em = embed(k, v("m"));
    let ge_m = pr1(gty(v("m")), eq_ty(v("m")), v("ih"));
    let eq_m = pr2(gty(v("m")), eq_ty(v("m")), v("ih"));
    let h = rew(bool0(), maj(ap(a.clone(), em.clone()), ap(c.clone(), em.clone()), ff()), ff(), to_false(em.clone(), ge_m.clone()),
        lm("t", bool0(), idt(state(k), pair_s(k, ap(succ(k), em.clone()), v("t")), pair_s(k, ap(succ(k), em.clone()), ff()))),
        rfl(pair_s(k, ap(succ(k), em.clone()), ff())));
    let eq_new = rew(state(k), stn(v("m")), target(v("m")), eq_m,
        lm("t", state(k), idt(state(k), ap(step(k, maj, a.clone(), c.clone()), v("t")), pair_s(k, ap(succ(k), em.clone()), ff()))), h);
    let sm = ap(succ(k + 1), v("m"));
    let step_ = lm("m", nat(k + 1), lm("ih", pmf(v("m")),
        mk2(gty(sm.clone()), eq_ty(sm), gsucc(k, em, ge_m), eq_new)));
    let z = zero(k + 1);
    let base = mk2(gty(z.clone()), eq_ty(z), gzero(k), rfl(pair_s(k, zero(k), ff())));
    ap3(v("g"), lm("M", nat(k + 1), pmf(v("M"))), base, step_)
}
pub(crate) fn y_proof(k: u32, zero_right: bool) -> T {
    let (a, c) = if zero_right { (v("su"), zs(k)) } else { (zs(k), v("su")) };
    let stn = |m: T| st(k, maj, a.clone(), c.clone(), m);
    let target = |m: T| pair_s(k, embed(k, m), ff());
    let e = |m: T| embed(k, m);
    let eq_ty = |m: T| idt(state(k), stn(m.clone()), target(m));
    let gty = |m: T| gk(k, e(m));
    let zsl = |p: T| ap(zs(k), p); // reduces to ff
    // the carry stays false: right-zero needs the known stream's goodness; left-zero is by computation
    let (eq_n, ge_n) = if zero_right {
        let pn = carry_false(k, &a, &c, &|em, ge_m| rew(bool0(), ap(v("su"), em.clone()), ap(v("sw"), em.clone()), ap2(v("hu"), em.clone(), ge_m.clone()),
            lm("b", bool0(), idt(bool0(), maj(v("b"), zsl(em.clone()), ff()), ff())),
            cases1(ap2(v("gw"), em.clone(), ge_m), &|bb| maj(bb, zsl(em.clone()), ff()), &|_| ff())));
        (pr2(gty(v("N")), eq_ty(v("N")), pn.clone()), pr1(gty(v("N")), eq_ty(v("N")), pn))
    } else {
        let em = e(v("m"));
        let eq_new = rew(state(k), stn(v("m")), target(v("m")), v("ih"),
            lm("t", state(k), idt(state(k), ap(step(k, maj, a.clone(), c.clone()), v("t")), pair_s(k, ap(succ(k), em.clone()), ff()))),
            rfl(pair_s(k, ap(succ(k), em), ff())));
        let pn = ap3(v("g"), lm("M", nat(k + 1), eq_ty(v("M"))), rfl(pair_s(k, zero(k), ff())),
            lm("m", nat(k + 1), lm("ih", eq_ty(v("m")), eq_new)));
        (pn, ap2(ge_proof(k), v("N"), v("g")))
    };
    let en = e(v("N"));
    let f = |bb: T| if zero_right { xor(xor(bb, zsl(en.clone())), ff()) } else { xor(xor(zsl(en.clone()), bb), ff()) };
    let leaf = rew(bool0(), ap(v("su"), en.clone()), ap(v("sw"), en.clone()), ap2(v("hu"), en.clone(), ge_n.clone()),
        lm("b", bool0(), idt(bool0(), f(v("b")), ap(v("sw"), en.clone()))),
        cases1(ap2(v("gw"), en.clone(), ge_n), &|bb| f(bb), &|bb| bb));
    let fin = rew(state(k), stn(v("N")), target(v("N")), eq_n,
        lm("t", state(k), idt(bool0(), sumfn(k, a.clone(), c.clone(), v("t")), ap(v("sw"), en.clone()))), leaf);
    lm("N", nat(k + 1), lm("g", ap(good1(k), v("N")), lm("su", bits(k), lm("sw", bits(k),
        lm("gw", pi_("i", nat(k), arr(gk(k, v("i")), ap(goodbool(), ap(v("sw"), v("i"))))),
        lm("hu", pi_("i", nat(k), arr(gk(k, v("i")), idt(bool0(), ap(v("su"), v("i")), ap(v("sw"), v("i"))))), fin))))))
}

#[test]
fn the_good_embed_lemma_and_the_adder_lemmas_check_at_every_level() {
    for k in 1..=4u32 {
        let ge_ty = pi_("N", nat(k + 1), arr(ap(good1(k), v("N")), gk(k, embed(k, v("N")))));
        super::width::run(&format!("good embed k={k}"), &ge_ty, &ge_proof(k)).unwrap();
        for zr in [true, false] {
            super::width::run(&format!("Y k={k} zero_right={zr}"), &y_stmt(k, zr), &y_proof(k, zr)).unwrap();
        }
    }
}

// ---------- the multiplier laws, uniformly in the output position ----------
#[derive(Clone, Copy, PartialEq, Debug)]
pub(crate) enum Law {
    /// `mul x 0 = 0`
    Zero,
    /// `mul x 1 = x`
    One,
}
pub(crate) fn law_y(law: Law, m: usize) -> Vec<T> {
    ybits(m, if law == Law::One { 1 } else { 0 })
}
/// `t : Nat_(k0+m)` lowered to `Nat_k0`.
pub(crate) fn lower(k0: u32, m: usize, t: T) -> T {
    (0..m).rev().fold(t, |t, j| embed(k0 + j as u32, t))
}
/// `Pi x:Bits(k0). [(Pi i. GoodBool (x i)) ->] Pi N:Nat_(k0+m). Good N -> Id(Bool0, mul_stream x N, rhs)`, where `rhs` is false
/// (`Zero`) or `x` read at the lowered position (`One`).
fn mul_stmt(k0: u32, m: usize, law: Law, ys: &[T], rhs_override: Option<T>) -> T {
    let kn = k0 + m as u32;
    let rhs = rhs_override.unwrap_or_else(|| if law == Law::One { ap(v("x"), lower(k0, m, v("N"))) } else { ff() });
    let core = pi_("N", nat(kn), arr(ap(good1(kn - 1), v("N")), idt(bool0(), ap(mul_stream(k0, ys, v("x")), v("N")), rhs)));
    let core = if law == Law::One { arr(pi_("i", nat(k0), ap(goodbool(), ap(v("x"), v("i")))), core) } else { core };
    pi_("x", bits(k0), core)
}
/// `w_j := x` lowered j levels: `w_0 = w0`, `w_(j+1) = \i:Nat_(k0+j+1). w_j (embed i)`.
fn wchain(k0: u32, j: usize, w0: T) -> T {
    (0..j).fold(w0, |w, i| lm("i", nat(k0 + i as u32 + 1), ap(w, embed(k0 + i as u32, v("i")))))
}
pub(crate) fn mul_proof(k0: u32, m: usize, law: Law) -> T {
    let ys = law_y(law, m);
    let x = v("x");
    let (w0, gw0) = match law {
        Law::Zero => (zs(k0), lm("i", nat(k0), goodff())),
        Law::One => (x.clone(), v("gx")),
    };
    // h = H_j : Pi i:Nat_(k0+j). Good_(k0+j) i -> Id(acc_j i, w_j i)
    let mut h = lm("i", nat(k0), lm("g0", gk(k0, v("i")), rfl(ff())));
    for j in 0..m {
        let kj = k0 + j as u32;
        let (wj, gwj) = (wchain(k0, j, w0.clone()), wchain(k0, j, gw0.clone()));
        let (zero_right, su, hu) = if law == Law::One && j == 0 {
            // acc_0 = 0 is the left operand; the unknown is the partial product y_0 & x, equal to x at good positions
            let t0 = tm(k0, ys[0].clone(), x.clone());
            let hu0 = lm("i", nat(k0), lm("g0", gk(k0, v("i")),
                cases1(ap(v("gx"), v("i")), &|bb| and2(ys[0].clone(), bb), &|bb| bb)));
            (false, t0, hu0)
        } else {
            (true, acc_upto(k0, &ys, x.clone(), j), h)
        };
        let y = K(ex(&y_proof(kj, zero_right)));
        h = lm("N", nat(kj + 1), lm("g", ap(good1(kj), v("N")),
            ap(ap(ap(ap(ap2(y, v("N"), v("g")), su), wj), lm("gi", nat(kj), lm("gg", gk(kj, v("gi")), ap(gwj, v("gi"))))), hu)));
    }
    let core = lm("x", bits(k0), h);
    if law == Law::One {
        lm("x", bits(k0), lm("gx", pi_("i", nat(k0), ap(goodbool(), ap(v("x"), v("i")))), h_of(&core)))
    } else {
        core
    }
}
/// The body of `\x. h`.
fn h_of(t: &T) -> T {
    match t {
        Lm(_, _, body) => (**body).clone(),
        _ => unreachable!(),
    }
}

#[test]
fn mul_zero_and_mul_one_hold_uniformly_in_the_position() {
    for law in [Law::Zero, Law::One] {
        for (k0, m) in [(1u32, 1usize), (1, 2), (1, 3), (2, 2), (2, 3)] {
            let ys = law_y(law, m);
            super::width::run(&format!("{law:?} k0={k0} m={m}"), &mul_stmt(k0, m, law, &ys, None), &mul_proof(k0, m, law)).unwrap();
        }
    }
}

#[test]
fn mul_uniform_rejects_wrong_statements() {
    for (k0, m) in [(1u32, 2usize), (1, 3), (2, 2)] {
        let rej = |name: &str, stmt: T, proof: &T| {
            let r = kernel::check(&Ctx::new(), &ex(proof), &ex(&stmt));
            let msg = r.expect_err(&format!("k0={k0} m={m}: {name} was accepted"));
            println!("[uniform wrong k0={k0} m={m} {name}] REJECTED: {}", msg.chars().take(120).collect::<String>());
        };
        let (pz, p1) = (mul_proof(k0, m, Law::Zero), mul_proof(k0, m, Law::One));
        // mul x 0 = 1 (a true bit), and = x
        rej("mul x 0 = true", mul_stmt(k0, m, Law::Zero, &law_y(Law::Zero, m), Some(tt())), &pz);
        // the multiplier 1 against the zero law's proof, and 2 against the one law's proof
        rej("mul x 1 = 0 by the zero proof", mul_stmt(k0, m, Law::Zero, &ybits(m, 1), None), &pz);
        rej("mul x 1 = 0", mul_stmt(k0, m, Law::One, &law_y(Law::One, m), Some(ff())), &p1);
        rej("mul x 2 = x", mul_stmt(k0, m, Law::One, &ybits(m, 2), None), &p1);
        rej("mul x 3 = x", mul_stmt(k0, m, Law::One, &ybits(m, 3), None), &p1);
        // the lemma with a false right-hand side
        let bad_y = pi_("N", nat(k0 + 1), arr(ap(good1(k0), v("N")), pi_("su", bits(k0), pi_("sw", bits(k0),
            arr(pi_("i", nat(k0), arr(gk(k0, v("i")), ap(goodbool(), ap(v("sw"), v("i"))))),
            arr(pi_("i", nat(k0), arr(gk(k0, v("i")), idt(bool0(), ap(v("su"), v("i")), ap(v("sw"), v("i"))))),
                idt(bool0(), sumbit(k0, v("su"), zs(k0), v("N")), tt())))))));
        rej("lemma Y with rhs true", bad_y, &y_proof(k0, true));
    }
}

// ---------- stage C: the fixed-width multiplier, and the bridge ----------
// `mul(n)` is the unrolled shift-and-add circuit, built only from the encoding's `add(n)` and `bitwise(n, and)` and a shift of the
// n-bit tuple (`shl_bv`, defined here):
//   mul x y := \C k. y C (\y_0 .. y_(n-1). acc_n C k)
//   acc_0 = lit 0,  acc_(j+1) = add acc_j (bitwise_and (rep y_j) (shl_bv^j x)),  rep b = the tuple of n copies of b
// i.e. exactly `acc_upto` with tuples for streams (mask first, as in `tm`). Bit i of acc_j is the stream circuit's bit i, so the
// bridge needs no equality between circuits: `mul(n) (mk a..) (lit v)` and the stream product at the numeral i are convertible
// (the adder's bits are `encoding::ripple`'s, and `shl_bv^j` at i is `a_(i-j)` or false, as the stream `shl` reads it).
/// `\x:Bv_n. \C k. x C (\a_0..a_(n-1). k false a_0 .. a_(n-2))`
pub(crate) fn shl_bv(n: usize, fill: bool) -> T {
    let call = (0..n - 1).fold(ap(v("k"), if fill { tt() } else { ff() }), |f, j| ap(f, v(AN(j))));
    let body = (0..n).rev().fold(call, |body, j| lm(AN(j), bool0(), body));
    lm("x", bvt(n), lm("C", s(1), lm("k", arrows(n, v("C")), ap2(v("x"), v("C"), body))))
}
pub(crate) fn rep(n: usize, bit: T) -> T {
    tuple(&vec![bit; n])
}
pub(crate) fn band(n: usize, p: T, q: T) -> T {
    ap2(K(encoding::bitwise(n, &|a, c| encoding::and(a, c))), p, q)
}
pub(crate) fn mul_bv(n: usize) -> Expr {
    mul_bv_fill(n, false)
}
/// `mul_bv` with the shift's fill bit chosen (`true` is the mutant of the shift tests).
pub(crate) fn mul_bv_fill(n: usize, fill: bool) -> Expr {
    let mut acc = K(encoding::lit(n, 0));
    for j in 0..n {
        let sh = (0..j).fold(v("x"), |e, _| ap(shl_bv(n, fill), e));
        acc = ap2(K(encoding::add(n)), acc, band(n, rep(n, v(YB(j))), sh));
    }
    let body = (0..n).rev().fold(ap2(acc, v("C"), v("k")), |body, j| lm(YB(j), bool0(), body));
    ex(&lm("x", bvt(n), lm("y", bvt(n), lm("C", s(1), lm("k", arrows(n, v("C")), ap2(v("y"), v("C"), body))))))
}

#[derive(Clone, Copy)]
enum Rhs {
    Lit(u128),
    X,
}
/// `Pi x:Bv_n. GoodBv x -> Id(Bv_n, mul x (lit ylit), rhs)`
fn bridge_stmt(n: usize, ylit: u128, rhs: Rhs) -> Expr {
    let bv = K(encoding::bv_ty(n));
    let r = match rhs {
        Rhs::Lit(c) => K(encoding::lit(n, c)),
        Rhs::X => v("x"),
    };
    ex(&pi_("x", bv.clone(), arr(ap(K(encoding::good_bv(n)), v("x")),
        idt(bv, ap2(K(mul_bv(n)), v("x"), K(encoding::lit(n, ylit))), r))))
}
/// The proof, from the uniform theorem of `law` at k0 = 2 (the lookup returns `W`, see `width::bridge_add_zero`).
pub(crate) fn bridge_proof(n: usize, law: Law) -> Expr {
    let (k0, kn) = (2u32, 2 + n as u32);
    let (xs, gxs) = (stream(XN, n), wstream(XN, n));
    let uni = K(ex(&mul_proof(k0, n, law)));
    let prod = mul_stream(k0, &law_y(law, n), xs.clone());
    let target = |i: usize| if law == Law::Zero { ff() } else { v(AN(i)) };
    let l_i = |i: usize| ap(prod.clone(), numeral(kn, i));
    let e_i = |i: usize| {
        let t = if law == Law::One { ap2(uni.clone(), xs.clone(), gxs.clone()) } else { ap(uni.clone(), xs.clone()) };
        ap2(t, numeral(kn, i), goodnum(kn - 1, i as u32))
    };
    let g = tuple_chain(n, &l_i, &target, &e_i);
    let bv = K(encoding::bv_ty(n));
    let rhs_of = |x: T| if law == Law::Zero { K(encoding::lit(n, 0)) } else { x };
    let ylit = if law == Law::One { 1 } else { 0 };
    let motive = lm("x", bv.clone(), idt(bv.clone(), ap2(K(mul_bv(n)), v("x"), K(encoding::lit(n, ylit))), rhs_of(v("x"))));
    ex(&lm("x", bv, lm("gb", ap(K(encoding::good_bv(n)), v("x")), ap2(v("gb"), motive, lam_bits(XN, n, g)))))
}
fn bridge_rhs(law: Law) -> Rhs {
    if law == Law::One { Rhs::X } else { Rhs::Lit(0) }
}
fn bridge_ylit(law: Law) -> u128 {
    if law == Law::One { 1 } else { 0 }
}

/// `mul(n)` is a multiplier: on closed literals it computes the product mod 2^n.
#[test]
fn mul_bv_multiplies_literals() {
    for n in 1..=3usize {
        let m = 1u128 << n;
        for x in 0..m {
            for y in 0..m {
                let got = ex(&ap2(K(mul_bv(n)), K(encoding::lit(n, x)), K(encoding::lit(n, y))));
                assert!(kernel::def_eq(&got, &encoding::lit(n, (x * y) % m)), "n={n}: {x} * {y}");
            }
        }
    }
}

#[test]
fn bridge_checks_for_small_n() {
    for law in [Law::Zero, Law::One] {
        for n in 1..=3usize {
            let (pf, stmt) = (bridge_proof(n, law), bridge_stmt(n, bridge_ylit(law), bridge_rhs(law)));
            let (r, ms) = timed_check(&pf, &stmt);
            println!("[bridge {law:?} n={n}] {} in {ms:.2} ms", if r.is_ok() { "ACCEPTED" } else { "REJECTED" });
            r.unwrap_or_else(|m| panic!("{law:?} n={n}: {}", m.chars().take(900).collect::<String>()));
        }
    }
}

#[test]
fn bridge_rejects_wrong_statements() {
    for n in 1..=3usize {
        for law in [Law::Zero, Law::One] {
            let pf = bridge_proof(n, law);
            let mut wrong: Vec<(String, Expr)> = vec![];
            if law == Law::Zero {
                wrong.push(("mul x 0 = 1".into(), bridge_stmt(n, 0, Rhs::Lit(1))));
                wrong.push(("mul x 0 = all ones".into(), bridge_stmt(n, 0, Rhs::Lit(encoding::low_bits(n)))));
                wrong.push(("mul x 0 = x".into(), bridge_stmt(n, 0, Rhs::X)));
                wrong.push(("mul x 1 = 0".into(), bridge_stmt(n, 1, Rhs::Lit(0))));
            } else {
                wrong.push(("mul x 1 = 0".into(), bridge_stmt(n, 1, Rhs::Lit(0))));
                wrong.push(("mul x 0 = x".into(), bridge_stmt(n, 0, Rhs::X)));
                if n >= 2 {
                    wrong.push(("mul x 2 = x".into(), bridge_stmt(n, 2, Rhs::X)));
                    wrong.push(("mul x 3 = x".into(), bridge_stmt(n, 3, Rhs::X)));
                }
            }
            for (name, stmt) in wrong {
                // the wrong statement is well-typed, so the rejection is a proof mismatch, not an ill-formed statement
                kernel::typecheck(&stmt).unwrap_or_else(|e| panic!("{name} is ill-typed: {e}"));
                let (r, _) = timed_check(&pf, &stmt);
                let m = r.expect_err(&format!("{law:?} n={n}: {name} was accepted"));
                if n == 2 {
                    println!("[bridge wrong {law:?} n={n} {name}] REJECTED: {}", m.chars().take(100).collect::<String>());
                }
            }
        }
        // the one-law proof does not prove the zero law's statement and vice versa
        let (p1, p0) = (bridge_proof(n, Law::One), bridge_proof(n, Law::Zero));
        assert!(timed_check(&p1, &bridge_stmt(n, 0, Rhs::Lit(0))).0.is_err(), "n={n}: one-proof proved mul x 0 = 0");
        assert!(timed_check(&p0, &bridge_stmt(n, 1, Rhs::X)).0.is_err(), "n={n}: zero-proof proved mul x 1 = x");
    }
}

// ---------- the per-width baselines ----------
// Zero: `mul x 0 = 0` is a computation once the `GoodBv` step opens `x`: the step is `refl`. (Without opening, `x` is a stuck
// variable.) One: nested case splits on the bits a_0 .. a_j for output bit j (2^(j+1) leaves), built here, not in the encoding.
pub(crate) fn proj_bit(n: usize, j: usize, t: T) -> T {
    ap2(t, bool0(), (0..n).rev().fold(v(AN(j)), |body, i| lm(AN(i), bool0(), body)))
}
fn direct_bit(n: usize, j: usize, idx: usize, bits: &[T]) -> T {
    let lhs = |bs: &[T]| proj_bit(n, j, ap2(K(mul_bv(n)), tuple(bs), K(encoding::lit(n, 1))));
    if idx > j {
        return rfl(bits[j].clone());
    }
    let with = |bb: T| {
        let mut b2 = bits.to_vec();
        b2[idx] = bb;
        b2
    };
    let motive_body = |bb: T| {
        let b2 = with(bb);
        idt(bool0(), lhs(&b2), b2[j].clone())
    };
    ap3(v(GN(idx)), lm("$b", bool0(), motive_body(v("$b"))), direct_bit(n, j, idx + 1, &with(tt())), direct_bit(n, j, idx + 1, &with(ff())))
}
fn baseline_proof(n: usize, law: Law) -> Expr {
    let bv = K(encoding::bv_ty(n));
    let motive = |x: T| idt(bv.clone(), ap2(K(mul_bv(n)), x.clone(), K(encoding::lit(n, bridge_ylit(law)))), if law == Law::Zero { K(encoding::lit(n, 0)) } else { x });
    let step = if law == Law::Zero {
        rfl(K(encoding::lit(n, 0)))
    } else {
        let a: Vec<T> = (0..n).map(|i| v(AN(i))).collect();
        let lhs = |i: usize| proj_bit(n, i, ap2(K(mul_bv(n)), tuple(&a), K(encoding::lit(n, 1))));
        tuple_chain(n, &lhs, &|i| a[i].clone(), &|j| direct_bit(n, j, 0, &a))
    };
    ex(&lm("x", bv.clone(), lm("gb", ap(K(encoding::good_bv(n)), v("x")), ap2(v("gb"), lm("x", bv.clone(), motive(v("x"))), lam_bits(XN, n, step)))))
}

#[test]
fn baselines_check_for_small_n() {
    for law in [Law::Zero, Law::One] {
        for n in 1..=4usize {
            let (pf, stmt) = (baseline_proof(n, law), bridge_stmt(n, bridge_ylit(law), bridge_rhs(law)));
            let (r, ms) = timed_check(&pf, &stmt);
            println!("[baseline {law:?} n={n}] {} in {ms:.2} ms", if r.is_ok() { "ACCEPTED" } else { "REJECTED" });
            r.unwrap_or_else(|m| panic!("baseline {law:?} n={n}: {}", m.chars().take(900).collect::<String>()));
        }
    }
}

#[test]
#[ignore]
fn bridge_scaling() {
    for law in [Law::Zero, Law::One] {
        for n in [1usize, 2, 3, 4, 5, 6] {
            let t0 = Instant::now();
            let (pf, stmt) = (bridge_proof(n, law), bridge_stmt(n, bridge_ylit(law), bridge_rhs(law)));
            let built = t0.elapsed().as_secs_f64() * 1e3;
            let (r, ms) = timed_check(&pf, &stmt);
            let t1 = Instant::now();
            let bp = baseline_proof(n, law);
            let bbuilt = t1.elapsed().as_secs_f64() * 1e3;
            let (r2, ms2) = timed_check(&bp, &stmt);
            println!("MUL {law:?} n={n}: bridge built {built:.1} ms, check {ms:.2} ms ({}); baseline built {bbuilt:.1} ms, check {ms2:.2} ms ({})",
                if r.is_ok() { "accepted" } else { "REJECTED" }, if r2.is_ok() { "accepted" } else { "REJECTED" });
        }
    }
}
