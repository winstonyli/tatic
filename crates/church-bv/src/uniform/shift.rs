// Spike (2026-11-01, task y2; builds on `width.rs` and `mul.rs`): a stream-route law that really uses the shift.
//
// `mul.rs` proves `mul x 0 = 0` and `mul x 1 = x`; in both every shifted partial product is masked by a zero multiplier
// bit, so no proof ever observes `shl` / `shl_bv` (flipping `shl_bv`'s fill bit left every bridge test passing). Here the
// multiplier is the literal 2: `mul x 2 = x + x`, uniformly in the output position, with the multiplier bits unrolled in the
// meta-language as in `mul.rs` (m adders, the statement's level grows with m). The proof has four parts:
//   * `J` (joint induction): the shift's fold and the adder's fold `x + x` run in step. `AD M = SH M` as states, together with
//     `GoodBool (snd (SH M))` (the adder step needs the carry known: `maj(a, a, c) = a` is by computation only once `c` is a
//     known bit, because `or(.., and(c, ff))` is stuck on a symbolic `c`). `SH M`'s second component is `x` at the previous
//     position, so its goodness needs no transport.
//   * `S`: from `J`, `shl x M = (x + x) M` at good positions ("doubling is the shift").
//   * `Z`: an adder whose left operand is pointwise the zero stream keeps its carry false, with the other operand arbitrary
//     (the mirror of lemma Y of `mul.rs`, which has the zero operand on the right or literally `zs`). It gives
//     `acc_2 N = shl x (embed N)`: the first partial product is masked by `y_0 = 0`, the second is the shifted stream.
//   * the multiplier bits 2, 3, .. are 0: the existing lemma Y keeps the known stream `shl x` (lowered), which needs
//     `GoodBool` of its bits at good positions only (Y's hypothesis `gw` was made conditional on `Good_k i` for this).
// The fill bit of the shift is a parameter (`fill = false` is the real shift) so the mutation tests can flip it in the stream
// construction and in the fixed-width `shl_bv`.
use tatic_wasm::encoding;
use super::mul::*;
use super::width::T::*;
use super::width::*;
use std::time::Instant;
use tatic_kernel::{self as kernel, Expr};

fn ap4(f: T, a: T, c: T, d: T, e: T) -> T {
    ap(ap3(f, a, c, d), e)
}
fn ap5(f: T, a: T, c: T, d: T, e: T, g: T) -> T {
    ap(ap4(f, a, c, d, e), g)
}
/// `a = c` and `c = d` give `a = d` (rewrite `a` to `c` in `Id(_, d)`).
fn trans_b(a: T, c: T, d: T, p1: T, p2: T) -> T {
    rew(bool0(), a, c, p1, lm("t", bool0(), idt(bool0(), v("t"), d)), p2)
}

// ---------- J: the shift's fold and the adder `x + x` in step ----------
fn ad(k: u32, m: T) -> T {
    st(k, maj, v("x"), v("x"), m)
}
fn sh(k: u32, fill: bool, m: T) -> T {
    shl_state(k, v("x"), fill, m)
}
fn ja(k: u32, fill: bool, m: T) -> T {
    ap(goodbool(), snd(k, sh(k, fill, m)))
}
fn jb(k: u32, fill: bool, m: T) -> T {
    idt(state(k), ad(k, m.clone()), sh(k, fill, m))
}
fn gx_ty(k: u32) -> T {
    pi_("i", nat(k), ap(goodbool(), ap(v("x"), v("i"))))
}
/// `Pi x gx. Pi M:Nat_(k+1). Good M -> Sigma(GoodBool (snd (SH M)), Id(state, AD M, SH M))`.
pub(crate) fn j_stmt(k: u32, fill: bool) -> T {
    let m = || v("M");
    pi_("x", bits(k), pi_("gx", gx_ty(k), pi_("M", nat(k + 1),
        arr(ap(good1(k), m()), sig2(ja(k, fill, m()), jb(k, fill, m()))))))
}
pub(crate) fn j_proof(k: u32, fill: bool) -> T {
    let pmf = |m: T| sig2(ja(k, fill, m.clone()), jb(k, fill, m));
    let um = sh(k, fill, v("m"));
    let fu = fst(k, um.clone());
    let gm = pr1(ja(k, fill, v("m")), jb(k, fill, v("m")), v("ih"));
    let eqm = pr2(ja(k, fill, v("m")), jb(k, fill, v("m")), v("ih"));
    // the step maps agree on the state `SH m`: x(p) = maj(x p, x p, c) once x p and c are known bits
    // (the case split is on a Bool0 equality, whose sort is 1; a state equality would not fit the witness's motive)
    let xp = ap(v("x"), fu.clone());
    let hb = cases2(ap(v("gx"), fu.clone()), gm, snd(k, um.clone()), bool0(),
        &|aa, cc| maj(aa.clone(), aa, cc), &|aa, _| aa);
    let h = rew(bool0(), maj(xp.clone(), xp.clone(), snd(k, um.clone())), xp.clone(), hb,
        lm("t", bool0(), idt(state(k), pair_s(ap(succ(k), fu.clone()), v("t")), pair_s(ap(succ(k), fu.clone()), xp.clone()))),
        rfl(pair_s(ap(succ(k), fu.clone()), xp)));
    let eq_new = rew(state(k), ad(k, v("m")), um.clone(), eqm,
        lm("t", state(k), idt(state(k), ap(step(k, maj, v("x"), v("x")), v("t")), ap(shl_step(k, v("x")), um.clone()))), h);
    let sm = ap(succ(k + 1), v("m"));
    let gnew = ap(v("gx"), fu);
    let step_ = lm("m", nat(k + 1), lm("ih", pmf(v("m")), mk2(ja(k, fill, sm.clone()), jb(k, fill, sm), gnew, eq_new)));
    let z = zero(k + 1);
    let base = mk2(ja(k, fill, z.clone()), jb(k, fill, z), goodff(), rfl(pair_s(zero(k), ff())));
    let pn = ap3(v("g"), lm("M", nat(k + 1), pmf(v("M"))), base, step_);
    lm("x", bits(k), lm("gx", gx_ty(k), lm("M", nat(k + 1), lm("g", ap(good1(k), v("M")), pn))))
}

// ---------- S: shl x = x + x at good positions ----------
pub(crate) fn s_stmt(k: u32, fill: bool) -> T {
    pi_("x", bits(k), pi_("gx", gx_ty(k), pi_("M", nat(k + 1), arr(ap(good1(k), v("M")),
        idt(bool0(), ap(shl_fill(k, v("x"), fill), v("M")), sumbit(k, v("x"), v("x"), v("M")))))))
}
pub(crate) fn s_proof(k: u32, fill: bool) -> T {
    let m = v("M");
    let jm = ap4(K(ex(&j_proof(k, fill))), v("x"), v("gx"), m.clone(), v("g"));
    let gs = pr1(ja(k, fill, m.clone()), jb(k, fill, m.clone()), jm.clone());
    let eq = pr2(ja(k, fill, m.clone()), jb(k, fill, m.clone()), jm);
    let shm = sh(k, fill, m.clone());
    // x p, q known: q = xor(xor(x p, x p), q)
    let h = cases2(ap(v("gx"), fst(k, shm.clone())), gs, snd(k, shm.clone()), bool0(),
        &|_, cc| cc, &|aa, cc| xor(xor(aa.clone(), aa), cc));
    let fin = rew(state(k), ad(k, m.clone()), shm.clone(), eq,
        lm("t", state(k), idt(bool0(), snd(k, shm), sumfn(k, v("x"), v("x"), v("t")))), h);
    lm("x", bits(k), lm("gx", gx_ty(k), lm("M", nat(k + 1), lm("g", ap(good1(k), m), fin))))
}

// ---------- Z: a pointwise-zero left operand keeps the carry false ----------
pub(crate) fn z_stmt(k: u32) -> T {
    pi_("N", nat(k + 1), arr(ap(good1(k), v("N")), pi_("za", bits(k), pi_("zc", bits(k),
        arr(pi_("i", nat(k), arr(gk(k, v("i")), idt(bool0(), ap(v("za"), v("i")), ff()))),
            idt(state(k), st(k, maj, v("za"), v("zc"), v("N")), pair_s(embed(k, v("N")), ff())))))))
}
pub(crate) fn z_proof(k: u32) -> T {
    let eq_ty = |m: T| idt(state(k), st(k, maj, v("za"), v("zc"), m.clone()), pair_s(embed(k, m), ff()));
    let gty = |m: T| gk(k, embed(k, m));
    // a (embed m) = false, so maj(a, c, false) = false whatever c is
    let pn = carry_false(k, &v("za"), &v("zc"), &|em, ge_m| rew(bool0(), ap(v("za"), em.clone()), ff(), ap2(v("hu"), em.clone(), ge_m),
        lm("b", bool0(), idt(bool0(), maj(v("b"), ap(v("zc"), em.clone()), ff()), ff())),
        rfl(ff())));
    lm("N", nat(k + 1), lm("g", ap(good1(k), v("N")), lm("za", bits(k), lm("zc", bits(k),
        lm("hu", pi_("i", nat(k), arr(gk(k, v("i")), idt(bool0(), ap(v("za"), v("i")), ff()))),
            pr2(gty(v("N")), eq_ty(v("N")), pn))))))
}

// ---------- the law: mul x 2 = x + x, uniformly in the output position ----------
/// `t : Nat_(k0+m)` lowered to `Nat_(k0+1)` (the index of `x + x`).
fn l1(k0: u32, m: usize, t: T) -> T {
    (1..m).rev().fold(t, |t, j| embed(k0 + j as u32, t))
}
/// `g : Good t` for the lowering of `t` (`l1`).
fn l1_good(k0: u32, m: usize, t: T, g: T) -> T {
    let (mut t, mut g) = (t, g);
    for j in (1..m).rev() {
        let l = k0 + j as u32;
        g = ap2(ge_proof(l), t.clone(), g);
        t = embed(l, t);
    }
    g
}
/// `Pi x gx. Pi N:Nat_(k0+m). Good N -> Id(Bool0, mul_stream x N, rhs)`, the multiplier the literal `ylit` on m bits and
/// `rhs` the sum stream `x + x` read at the lowered position unless overridden.
pub(crate) fn shift_stmt(k0: u32, m: usize, ylit: u128, fill: bool, rhs_override: Option<T>) -> T {
    let ys = ybits(m, ylit);
    let kn = k0 + m as u32;
    let rhs = rhs_override.unwrap_or_else(|| sumbit(k0, v("x"), v("x"), l1(k0, m, v("N"))));
    pi_("x", bits(k0), pi_("gx", gx_ty(k0), pi_("N", nat(kn),
        arr(ap(good1(kn - 1), v("N")), idt(bool0(), ap(mul_stream_fill(k0, &ys, v("x"), fill), v("N")), rhs)))))
}
/// The proof of `shift_stmt(k0, m, 2, fill, None)`, m >= 2.
pub(crate) fn shift_proof(k0: u32, m: usize, fill: bool) -> T {
    assert!(m >= 2);
    let ys = ybits(m, 2);
    let (x, k1) = (v("x"), k0 + 1);
    let shl_x = |p: T| ap(shl_fill(k0, v("x"), fill), p);
    let jlem = K(ex(&j_proof(k0, fill)));
    let jsig = |e: T, ge: T| ap4(jlem.clone(), v("x"), v("gx"), e, ge);
    let good_shl = |e: T, ge: T| pr1(ja(k0, fill, e.clone()), jb(k0, fill, e.clone()), jsig(e, ge));
    // H_2 : Pi N:Nat_(k0+2). Good N -> Id(acc_2 N, shl x (embed N)), by Z and the first partial product being zero
    let a = acc_upto_fill(k0, &ys, x.clone(), 1, fill);
    let c = tm(k1, ys[1].clone(), shl_fill(k0, x.clone(), fill));
    let hu1 = ap(K(ex(&mul_proof(k0, 1, Law::Zero))), x.clone());
    let e = embed(k1, v("N"));
    let ge = ap2(ge_proof(k1), v("N"), v("g"));
    let eqz = ap5(K(ex(&z_proof(k1))), v("N"), v("g"), a.clone(), c.clone(), hu1.clone());
    let gs = good_shl(e.clone(), ge.clone());
    let h2 = cases1(gs, &|s_| xor(xor(ff(), and2(tt(), s_)), ff()), &|s_| s_);
    let h1 = rew(bool0(), ap(a.clone(), e.clone()), ff(), ap2(hu1, e.clone(), ge),
        lm("t", bool0(), idt(bool0(), xor(xor(v("t"), ap(c.clone(), e.clone())), ff()), shl_x(e.clone()))), h2);
    let fin2 = rew(state(k1), st(k1, maj, a.clone(), c.clone(), v("N")), pair_s(e.clone(), ff()), eqz,
        lm("t", state(k1), idt(bool0(), sumfn(k1, a, c, v("t")), shl_x(e.clone()))), h1);
    let mut h = lm("N", nat(k1 + 1), lm("g", ap(good1(k1), v("N")), fin2));
    // w_2 = shl x lowered, with its conditional goodness
    let mut wj = lm("i", nat(k1 + 1), shl_x(embed(k1, v("i"))));
    let mut gwj = {
        let ei = embed(k1, v("i"));
        lm("i", nat(k1 + 1), lm("gi", gk(k1 + 1, v("i")), good_shl(ei, ap2(ge_proof(k1), v("i"), v("gi")))))
    };
    // multiplier bits 2 .. m-1 are zero: the zero operand leaves the known stream alone (lemma Y)
    for j in 2..m {
        let kj = k0 + j as u32;
        let su = acc_upto_fill(k0, &ys, x.clone(), j, fill);
        let y = K(ex(&y_proof(kj, true)));
        h = lm("N", nat(kj + 1), lm("g", ap(good1(kj), v("N")), ap4(ap2(y, v("N"), v("g")), su, wj.clone(), gwj.clone(), h.clone())));
        wj = lm("i", nat(kj + 1), ap(wj, embed(kj, v("i"))));
        gwj = lm("i", nat(kj + 1), lm("gi", gk(kj + 1, v("i")), ap2(gwj, embed(kj, v("i")), ap2(ge_proof(kj), v("i"), v("gi")))));
    }
    // N -> M = lowered; acc_m N = shl x M (h), shl x M = (x + x) M (S)
    let n = v("N");
    let mm = l1(k0, m, n.clone());
    let gm = l1_good(k0, m, n.clone(), v("g"));
    let p1 = ap2(h, n.clone(), v("g"));
    let p2 = ap4(K(ex(&s_proof(k0, fill))), v("x"), v("gx"), mm.clone(), gm);
    let lhs = ap(mul_stream_fill(k0, &ys, v("x"), fill), n);
    let fin = trans_b(lhs, shl_x(mm.clone()), sumbit(k0, v("x"), v("x"), mm), p1, p2);
    lm("x", bits(k0), lm("gx", gx_ty(k0), lm("N", nat(k0 + m as u32), lm("g", ap(good1(k0 + m as u32 - 1), v("N")), fin))))
}

// ---------- tests: the lemmas and the uniform law ----------
#[test]
fn shift_lemmas_check_at_every_level() {
    for k in 1..=4u32 {
        run(&format!("J k={k}"), &j_stmt(k, false), &j_proof(k, false)).unwrap();
        run(&format!("S k={k}"), &s_stmt(k, false), &s_proof(k, false)).unwrap();
        run(&format!("Z k={k}"), &z_stmt(k), &z_proof(k)).unwrap();
    }
}

/// The streams on concrete numbers: `mul x 2` is `x + x` (and the product `2x`) bit by bit, and flipping the fill bit shows.
#[test]
fn stream_shift_computes() {
    let (k0, m) = (1u32, 3usize);
    let xs_of = |x: u128| ap(lookup(m), tuple(&(0..m).map(|i| bit_of(x, i)).collect::<Vec<_>>()));
    for x in 0..(1u128 << m) {
        let prod = mul_stream_fill(k0, &ybits(m, 2), xs_of(x), false);
        let mutant = mul_stream_fill(k0, &ybits(m, 2), xs_of(x), true);
        for p in 0..2 * m + 1 {
            let got = ex(&ap(prod.clone(), numeral(k0 + m as u32, p)));
            assert!(kernel::def_eq(&got, &ex(&bit_of(2 * x, p))), "2 * {x}: bit {p}");
            // the sum stream x + x at the same position
            let sum = ex(&sumbit(k0, xs_of(x), xs_of(x), numeral(k0 + 1, p)));
            assert!(kernel::def_eq(&sum, &ex(&bit_of(2 * x, p))), "{x} + {x}: bit {p}");
        }
        // the mutant: bit 0 is the fill bit
        assert!(kernel::def_eq(&ex(&ap(mutant, numeral(k0 + m as u32, 0))), &ex(&tt())), "mutant bit 0 of 2 * {x}");
    }
}

#[test]
fn mul_two_is_add_x_x_uniformly_in_the_position() {
    for (k0, m) in [(1u32, 2usize), (1, 3), (2, 2), (2, 3), (2, 4), (3, 3)] {
        run(&format!("mul x 2 = x + x, k0={k0} m={m}"), &shift_stmt(k0, m, 2, false, None), &shift_proof(k0, m, false)).unwrap();
    }
}

#[test]
fn shift_uniform_rejects_wrong_statements() {
    for (k0, m) in [(1u32, 2usize), (1, 3), (2, 2), (2, 3)] {
        let pf = shift_proof(k0, m, false);
        let flip = |t: T| xor(t, tt());
        let lowered_x = |n: T| ap(v("x"), (0..m).rev().fold(n, |t, j| embed(k0 + j as u32, t)));
        let wrong: Vec<(&str, T)> = vec![
            ("mul x 3 = x + x", shift_stmt(k0, m, 3, false, None)),
            ("mul x 1 = x + x", shift_stmt(k0, m, 1, false, None)),
            ("mul x 0 = x + x", shift_stmt(k0, m, 0, false, None)),
            ("mul x 2 = x", shift_stmt(k0, m, 2, false, Some(lowered_x(v("N"))))),
            ("mul x 2 = 0", shift_stmt(k0, m, 2, false, Some(ff()))),
            ("mul x 2 = not (x + x)", shift_stmt(k0, m, 2, false, Some(flip(sumbit(k0, v("x"), v("x"), l1(k0, m, v("N"))))))),
            ("mul x 2 = (x + x) read one position lower", shift_stmt(k0, m, 2, false,
                Some(sumbit(k0, v("x"), v("x"), l1(k0, m, ap(succ(k0 + m as u32), v("N"))))))),
        ];
        for (name, stmt) in wrong {
            // well-typed and false: the rejection is a proof mismatch
            kernel::typecheck(&ex(&stmt)).unwrap_or_else(|e| panic!("{name} is ill-typed: {e}"));
            let r = kernel::check(&kernel::Ctx::new(), &ex(&pf), &ex(&stmt));
            let msg = r.expect_err(&format!("k0={k0} m={m}: {name} was accepted"));
            println!("[uniform wrong k0={k0} m={m} {name}] REJECTED: {}", msg.chars().take(100).collect::<String>());
        }
        // the lemma with a false statement: shl x = x (not x + x)
        let s_bad = pi_("x", bits(k0), pi_("gx", gx_ty(k0), pi_("M", nat(k0 + 1), arr(ap(good1(k0), v("M")),
            idt(bool0(), ap(shl_fill(k0, v("x"), false), v("M")), ap(v("x"), embed(k0, v("M"))))))));
        assert!(run("S with shl x = x", &s_bad, &s_proof(k0, false)).is_err());
    }
}

// ---------- the mutation gate, at the stream level ----------
/// The fill bit of the stream shift flipped (false -> true) in the whole construction, the proof skeleton unchanged: the
/// uniform law no longer checks, and the kernel says where.
#[test]
fn mutating_the_stream_shifts_fill_bit_is_rejected() {
    for (k0, m) in [(1u32, 2usize), (2, 2), (2, 3)] {
        // the statement and the proof both built with the mutant; and the unmutated proof against the mutant's statement
        for (name, stmt, pf) in [
            ("mutant statement, mutant proof", shift_stmt(k0, m, 2, true, None), shift_proof(k0, m, true)),
            ("mutant statement, real proof", shift_stmt(k0, m, 2, true, None), shift_proof(k0, m, false)),
        ] {
            kernel::typecheck(&ex(&stmt)).unwrap_or_else(|e| panic!("mutant statement is ill-typed: {e}"));
            let r = kernel::check(&kernel::Ctx::new(), &ex(&pf), &ex(&stmt));
            let msg = r.expect_err(&format!("k0={k0} m={m}: {name} was accepted"));
            println!("[stream mutant k0={k0} m={m} {name}] REJECTED: {}", msg.chars().take(160).collect::<String>());
        }
        // the lemmas the law is built from, mutated: J and S are the ones that observe the fill bit
        assert!(run("J fill=true", &j_stmt(k0, true), &j_proof(k0, true)).is_err());
        assert!(run("S fill=true", &s_stmt(k0, true), &s_proof(k0, true)).is_err());
        // the mutated shift is another function: the real S proof does not prove S for it
        assert!(run("S real proof, mutant statement", &s_stmt(k0, true), &s_proof(k0, false)).is_err());
    }
}

// ---------- the bridge to Bv_n ----------
#[derive(Clone, Copy)]
enum ShRhs {
    /// `add x x`
    AddXX,
    X,
    Lit(u128),
    /// `add x x` with bit 0 flipped
    Flip0,
    /// `shl_bv` with fill bit true applied to x
    ShlOnes,
}
/// `\C k. t C (\b_0..b_(n-1). k (not b_0) b_1 .. b_(n-1))`
fn flip0(n: usize, t: T) -> T {
    let call = (1..n).fold(ap(v("k"), xor(v(AN(0)), tt())), |f, j| ap(f, v(AN(j))));
    let body = (0..n).rev().fold(call, |body, j| lm(AN(j), bool0(), body));
    lm("C", s(1), lm("k", arrows(n, v("C")), ap2(t, v("C"), body)))
}
/// `Pi x:Bv_n. GoodBv x -> Id(Bv_n, mul x (lit ylit), rhs)`, the multiplier built with the shift's fill bit `lhs_fill`.
fn bridge_stmt(n: usize, lhs_fill: bool, ylit: u128, rhs: ShRhs) -> Expr {
    let bv = K(encoding::bv_ty(n));
    let xx = ap2(K(encoding::add(n)), v("x"), v("x"));
    let r = match rhs {
        ShRhs::AddXX => xx,
        ShRhs::X => v("x"),
        ShRhs::Lit(c) => K(encoding::lit(n, c)),
        ShRhs::Flip0 => flip0(n, xx),
        ShRhs::ShlOnes => ap(shl_bv(n, true), v("x")),
    };
    ex(&pi_("x", bv.clone(), arr(ap(K(encoding::good_bv(n)), v("x")),
        idt(bv, ap2(K(mul_bv_fill(n, lhs_fill)), v("x"), K(encoding::lit(n, ylit))), r))))
}
/// The proof, from the uniform theorem at k0 = 2 (`fill` is the stream shift's fill bit, false for the real one).
fn bridge_proof(n: usize, fill: bool) -> Expr {
    let (k0, kn) = (2u32, 2 + n as u32);
    let (xs, gxs) = (stream(XN, n), wstream(XN, n));
    let uni = K(ex(&shift_proof(k0, n, fill)));
    let prod = mul_stream_fill(k0, &ybits(n, 2), xs.clone(), fill);
    let l_i = |i: usize| ap(prod.clone(), numeral(kn, i));
    let r_i = |i: usize| sumbit(k0, xs.clone(), xs.clone(), numeral(k0 + 1, i));
    let e_i = |i: usize| ap2(ap2(uni.clone(), xs.clone(), gxs.clone()), numeral(kn, i), goodnum(kn - 1, i as u32));
    let g = tuple_chain(n, &l_i, &r_i, &e_i);
    let bv = K(encoding::bv_ty(n));
    let xx = ap2(K(encoding::add(n)), v("x"), v("x"));
    let motive = lm("x", bv.clone(), idt(bv.clone(), ap2(K(mul_bv_fill(n, fill)), v("x"), K(encoding::lit(n, 2))), xx));
    ex(&lm("x", bv, lm("gb", ap(K(encoding::good_bv(n)), v("x")), ap2(v("gb"), motive, lam_bits(XN, n, g)))))
}

/// `mul(n)` multiplies by 2 as `x + x` on closed literals (the definitions agree before any proof).
#[test]
fn mul_bv_two_is_add_on_literals() {
    for n in 2..=4usize {
        let m = 1u128 << n;
        for x in 0..m {
            let got = ex(&ap2(K(mul_bv_fill(n, false)), K(encoding::lit(n, x)), K(encoding::lit(n, 2))));
            let sum = ex(&ap2(K(encoding::add(n)), K(encoding::lit(n, x)), K(encoding::lit(n, x))));
            assert!(kernel::def_eq(&got, &sum), "n={n}: 2 * {x}");
            // the mutant differs on literals (the computation test catches the flip)
            let bad = ex(&ap2(K(mul_bv_fill(n, true)), K(encoding::lit(n, x)), K(encoding::lit(n, 2))));
            assert!(!kernel::def_eq(&bad, &sum), "n={n}: the mutant agrees on {x}");
        }
    }
}

#[test]
fn bridge_checks_for_small_n() {
    for n in 2..=4usize {
        let (pf, stmt) = (bridge_proof(n, false), bridge_stmt(n, false, 2, ShRhs::AddXX));
        let (r, ms) = timed_check(&pf, &stmt);
        println!("[bridge mul x 2 = x + x n={n}] {} in {ms:.2} ms", if r.is_ok() { "ACCEPTED" } else { "REJECTED" });
        r.unwrap_or_else(|m| panic!("n={n}: {}", m.chars().take(900).collect::<String>()));
    }
}

#[test]
fn bridge_rejects_wrong_statements() {
    for n in 2..=4usize {
        let pf = bridge_proof(n, false);
        let wrong: Vec<(&str, Expr)> = vec![
            ("mul x 2 = x", bridge_stmt(n, false, 2, ShRhs::X)),
            ("mul x 2 = 0", bridge_stmt(n, false, 2, ShRhs::Lit(0))),
            ("mul x 2 = (x + x) with bit 0 flipped", bridge_stmt(n, false, 2, ShRhs::Flip0)),
            ("mul x 2 = shl with ones", bridge_stmt(n, false, 2, ShRhs::ShlOnes)),
            ("mul x 1 = x + x", bridge_stmt(n, false, 1, ShRhs::AddXX)),
            ("mul x 3 = x + x", bridge_stmt(n, false, 3, ShRhs::AddXX)),
            ("mul x 0 = x + x", bridge_stmt(n, false, 0, ShRhs::AddXX)),
        ];
        for (name, stmt) in wrong {
            kernel::typecheck(&stmt).unwrap_or_else(|e| panic!("{name} is ill-typed: {e}"));
            let (r, _) = timed_check(&pf, &stmt);
            let msg = r.expect_err(&format!("n={n}: {name} was accepted"));
            if n == 2 {
                println!("[bridge wrong n={n} {name}] REJECTED: {}", msg.chars().take(100).collect::<String>());
            }
        }
    }
}

// ---------- the mutation gate, at the bridge ----------
/// The reviewer's finding on `mul.rs`: with `shl_bv`'s fill bit flipped the old bridges (`mul x 0 = 0`, `mul x 1 = x`)
/// still check, because a zero multiplier bit masks every shifted partial product. This law observes the shift: the same flip
/// is rejected by the bridge check itself (the kernel's conversion of the statement's `mul` against the proof's stream bits),
/// not only by the computation test.
#[test]
fn flipping_shl_bvs_fill_bit_is_caught_by_the_bridge_check() {
    for n in 2..=4usize {
        // (1) the old laws do not see it
        for (name, ylit, rhs, law) in [("mul x 0 = 0", 0u128, ShRhs::Lit(0), Law::Zero), ("mul x 1 = x", 1, ShRhs::X, Law::One)] {
            let stmt = bridge_stmt(n, true, ylit, rhs);
            let (r, _) = timed_check(&super::mul::bridge_proof(n, law), &stmt);
            assert!(r.is_ok(), "n={n}: the old bridge {name} noticed the mutant: {}", r.unwrap_err().chars().take(300).collect::<String>());
            println!("[mutant n={n}] old bridge `{name}` with shl_bv fill=true: still ACCEPTED");
        }
        // (2) the new law does: the real proof against the mutant multiplier's statement
        let stmt = bridge_stmt(n, true, 2, ShRhs::AddXX);
        kernel::typecheck(&stmt).unwrap_or_else(|e| panic!("mutant statement is ill-typed: {e}"));
        let (r, _) = timed_check(&bridge_proof(n, false), &stmt);
        let msg = r.expect_err(&format!("n={n}: the mutant statement was accepted"));
        println!("[mutant n={n}] mul x 2 = x + x with shl_bv fill=true: REJECTED by the bridge check: {}", msg.chars().take(140).collect::<String>());
        // (3) the whole construction mutated (stream shift and fixed-width shift): rejected too
        let (r2, _) = timed_check(&bridge_proof(n, true), &stmt);
        assert!(r2.is_err(), "n={n}: the fully mutated bridge was accepted");
    }
}

// ---------- the per-width baseline ----------
// `mul x 2 = x + x` for one width, no uniform theorem: the `GoodBv` step opens x into variables a_0 .. a_(n-1), and output bit j
// is a case split on a_0 .. a_j (2^(j+1) leaves, each closed by refl: the multiplier's bit j reads a_0 .. a_(j-1) and the
// adder's a_0 .. a_j), as the One baseline of `mul.rs`.
fn direct_bit(n: usize, j: usize, idx: usize, bits: &[T]) -> T {
    let lhs = |bs: &[T]| proj_bit(n, j, ap2(K(mul_bv_fill(n, false)), tuple(bs), K(encoding::lit(n, 2))));
    let rhs = |bs: &[T]| proj_bit(n, j, ap2(K(encoding::add(n)), tuple(bs), tuple(bs)));
    if idx > j {
        return rfl(lhs(bits));
    }
    let with = |bb: T| {
        let mut b2 = bits.to_vec();
        b2[idx] = bb;
        b2
    };
    let motive_body = |bb: T| {
        let b2 = with(bb);
        idt(bool0(), lhs(&b2), rhs(&b2))
    };
    ap3(v(GN(idx)), lm("$b", bool0(), motive_body(v("$b"))), direct_bit(n, j, idx + 1, &with(tt())), direct_bit(n, j, idx + 1, &with(ff())))
}
fn baseline_proof(n: usize) -> Expr {
    let bv = K(encoding::bv_ty(n));
    let a: Vec<T> = (0..n).map(|i| v(AN(i))).collect();
    let lhs = |i: usize| proj_bit(n, i, ap2(K(mul_bv_fill(n, false)), tuple(&a), K(encoding::lit(n, 2))));
    let rhs = |i: usize| proj_bit(n, i, ap2(K(encoding::add(n)), tuple(&a), tuple(&a)));
    let step = tuple_chain(n, &lhs, &rhs, &|j| direct_bit(n, j, 0, &a));
    let xx = |x: T| ap2(K(encoding::add(n)), x.clone(), x);
    let motive = lm("x", bv.clone(), idt(bv.clone(), ap2(K(mul_bv_fill(n, false)), v("x"), K(encoding::lit(n, 2))), xx(v("x"))));
    ex(&lm("x", bv, lm("gb", ap(K(encoding::good_bv(n)), v("x")), ap2(v("gb"), motive, lam_bits(XN, n, step)))))
}

#[test]
fn baselines_check_for_small_n() {
    for n in 2..=4usize {
        let (pf, stmt) = (baseline_proof(n), bridge_stmt(n, false, 2, ShRhs::AddXX));
        let (r, ms) = timed_check(&pf, &stmt);
        println!("[baseline mul x 2 = x + x n={n}] {} in {ms:.2} ms", if r.is_ok() { "ACCEPTED" } else { "REJECTED" });
        r.unwrap_or_else(|m| panic!("baseline n={n}: {}", m.chars().take(900).collect::<String>()));
    }
}

#[test]
#[ignore]
fn bridge_scaling() {
    for n in [2usize, 3, 4, 5, 6] {
        let t0 = Instant::now();
        let (pf, stmt) = (bridge_proof(n, false), bridge_stmt(n, false, 2, ShRhs::AddXX));
        let built = t0.elapsed().as_secs_f64() * 1e3;
        let (r, ms) = timed_check(&pf, &stmt);
        let t1 = Instant::now();
        let bp = baseline_proof(n);
        let bbuilt = t1.elapsed().as_secs_f64() * 1e3;
        let (r2, ms2) = timed_check(&bp, &stmt);
        println!("SHIFT n={n}: bridge built {built:.1} ms, check {ms:.2} ms ({}); baseline built {bbuilt:.1} ms, check {ms2:.2} ms ({})",
            if r.is_ok() { "accepted" } else { "REJECTED" }, if r2.is_ok() { "accepted" } else { "REJECTED" });
    }
}
