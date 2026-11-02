// Spike (2026-11-01, task z3; builds on `uniform_width.rs`, `uniform_mul.rs`): a stream-route law with a SYMBOLIC multiplier,
//     Pi y:Bv_n. GoodBv y -> Id(Bv_n, mul(n) (lit 1) y, y)        (`mul(n) x y`: the multiplicand FIRST, the multiplier `y` second)
//
// Until now the multiplier bits were meta-level literals (`ybits`); here they are the bit variables `a_j` of the `GoodBv` step.
// The partial product `and(y_j, x << j)` is then stuck on `y_j` (no computation removes it, `and a ff` is `a C ff ff`), and every
// fact about it needs a case split on the witness `ga_j`.
//
// The multiplicand is the closed one-hot stream `e_0` (the literal 1), so `x << j` is the one-hot stream `e_j`, a CLOSED term whose
// value at a numeral the kernel computes. The proof is therefore positionwise at numerals (not uniform in the position):
//   * `acc_j` is the stream accumulator of `uniform_mul.rs` with the multiplier bits as ARGUMENTS of a closed term
//     (`acc_sym(j) = \y_0..y_(j-1). \x. acc_j`), so it can be applied to the variables `a_j` and still be shared (a meta-level tree
//     over `a_j` is 3^j in size, the reason `acc_fn` is closed).
//   * the claim is `E(j, q) : acc_j (numeral q) = (a_q if q < j else false)`, for each stage j and each q < n.
//   * the adder's state at a numeral is walked one step at a time (`L1`: from `st N = (e, false)` and `maj(su e, sv e, false) = false`
//     to `st (succ N) = (succ e, false)`; `CF(j, q)` is q applications of it), and the sum bit is read from the state (`L2`).
//     The two operands of every addition have disjoint support, so the carry stays false: that is the `maj` fact `h(j, p)`.
//     Only `p < j` needs case splits (on `ga_p` and `ga_j`): there `acc_j p = a_p` is symbolic and `y_j & e_j(p) = a_j & ff`;
//     at `p >= j` the first operand is `ff` and `maj(ff, _, ff) = ff` is by computation.
//   * the bridge is the one of `uniform_mul.rs` (a `tuple_chain` of the bit equalities), with no stream read off the tuple: the
//     multiplier bits are the variables themselves and the multiplicand is closed, so the index level can be k0 = 1.
// What this is NOT: the hinted lemma "disjoint add" with a `Pi i. Good i ->` hypothesis. That would need `e_j` and the truncated
// multiplier stream at a SYMBOLIC good position i (position tracking of `shl`, then an induction on i generalised over the tuple that
// the `lookup` reads), which is not built here. See `docs/tier-cycle.md` (the lead records it).
use super::encoding;
use super::uniform_mul::*;
use super::uniform_width::T::*;
use super::uniform_width::*;
use std::time::Instant;
use tatic::kernel::{self, Expr};

/// The level of the streams' index at stage 0. `x = e_0` reads `Bool0` out of `Nat_1`, so k0 = 1 is enough.
pub(crate) const K0: u32 = 1;

/// The one-hot stream `e_0` (the literal 1) in `Bits(K0)`: `i -> i Bool0 tt (\_. ff)`.
fn x_one() -> T {
    lm("i", nat(K0), ap3(v("i"), bool0(), tt(), lm("_", bool0(), ff())))
}
fn y(j: usize) -> T {
    v(AN(j))
}
/// `acc_sym(j) : Bool0^j -> Bits(K0) -> Bits(K0 + j)`, CLOSED: `\y_0..y_(j-1). \x. acc_j` (the shift's fill bit is `fill`).
pub(crate) fn acc_sym(j: usize, fill: bool) -> Expr {
    let mut body = lm("x", bits(K0), acc_body(j, fill));
    for i in (0..j).rev() {
        body = lm(YB(i), bool0(), body);
    }
    ex(&body)
}
fn acc_body(j: usize, fill: bool) -> T {
    if j == 0 {
        return zs(K0);
    }
    let l = K0 + (j - 1) as u32;
    let prev = ap((0..j - 1).fold(K(acc_sym(j - 1, fill)), |f, i| ap(f, v(YB(i)))), v("x"));
    add_stream(l, prev, tm(l, v(YB(j - 1)), shl_n(K0, j - 1, v("x"), fill)))
}
pub(crate) fn apn(f: T, args: &[T]) -> T {
    args.iter().fold(f, |f, a| ap(f, a.clone()))
}
/// `acc_j` applied to the multiplier bits `ys` and the multiplicand `x`: a stream in `Bits(K0 + j)`.
pub(crate) fn big_a(acc: &[Expr], j: usize, ys: &[T], x: &T) -> T {
    ap(apn(K(acc[j]), &ys[..j]), x.clone())
}
/// The j-th partial product stream, `y_j & (x << j)`, in `Bits(K0 + j)`.
fn big_t(j: usize, x: &T, fill: bool) -> T {
    tm(K0 + j as u32, y(j), shl_n(K0, j, x.clone(), fill))
}
/// The value `acc_j` has at position p: the multiplier's bit p below j, zero from j on.
fn val(j: usize, p: usize) -> T {
    if p < j { y(p) } else { ff() }
}

// ---------- the two step lemmas, at level k ----------
/// `L1 : Pi su sv:Bits(k). Pi N:Nat_(k+1). Pi e:Nat_k. Id(state, st N, (e, ff)) -> Id(Bool0, maj(su e, sv e, ff), ff)
///        -> Id(state, st (succ N), (succ e, ff))`   (the carry stays false for one more position)
fn l1_proof(k: u32) -> T {
    let e = || v("e");
    let m_ = || maj(ap(v("su"), e()), ap(v("sv"), e()), ff());
    let stn = |n: T| st(k, maj, v("su"), v("sv"), n);
    let nxt = || pair_s(k, ap(succ(k), e()), ff());
    let hm = rew(bool0(), m_(), ff(), v("hm"),
        lm("t", bool0(), idt(state(k), pair_s(k, ap(succ(k), e()), v("t")), nxt())), rfl(nxt()));
    let fin = rew(state(k), stn(v("N")), pair_s(k, e(), ff()), v("eq"),
        lm("t", state(k), idt(state(k), ap(step(k, maj, v("su"), v("sv")), v("t")), nxt())), hm);
    lm("su", bits(k), lm("sv", bits(k), lm("N", nat(k + 1), lm("e", nat(k),
        lm("eq", idt(state(k), stn(v("N")), pair_s(k, e(), ff())),
            lm("hm", idt(bool0(), m_(), ff()), fin))))))
}
/// `L2 : Pi su sv N e. Id(state, st N, (e, ff)) -> Pi r:Bool0. Id(Bool0, xor(xor(su e, sv e), ff), r) -> Id(Bool0, sumbit(su, sv, N), r)`
fn l2_proof(k: u32) -> T {
    let e = || v("e");
    let fin = rew(state(k), st(k, maj, v("su"), v("sv"), v("N")), pair_s(k, e(), ff()), v("eq"),
        lm("t", state(k), idt(bool0(), sumfn(k, v("su"), v("sv"), v("t")), v("r"))), v("hh"));
    lm("su", bits(k), lm("sv", bits(k), lm("N", nat(k + 1), lm("e", nat(k),
        lm("eq", idt(state(k), st(k, maj, v("su"), v("sv"), v("N")), pair_s(k, e(), ff())),
            lm("r", bool0(), lm("hh", idt(bool0(), xor(xor(ap(v("su"), e()), ap(v("sv"), e())), ff()), v("r")), fin)))))))
}

// ---------- the equalities E(j, q) ----------
/// `E[j][q] : Id(Bool0, acc_j (numeral q), val(j, q))` for j in 0..=n, q in 0..n, as open terms over `a_i`, `ga_i`.
fn eq_table(n: usize, fill: bool) -> Vec<Vec<T>> {
    let x = K(ex(&x_one()));
    let acc: Vec<Expr> = (0..=n).map(|j| acc_sym(j, fill)).collect();
    let ys: Vec<T> = (0..n).map(y).collect();
    let mut e: Vec<Vec<T>> = vec![(0..n).map(|_| rfl(ff())).collect()];
    for j in 0..n {
        let kj = K0 + j as u32;
        let (su, sv) = (big_a(&acc, j, &ys, &x), big_t(j, &x, fill));
        let (l1, l2) = (K(ex(&l1_proof(kj))), K(ex(&l2_proof(kj))));
        // h(j, p) : maj(acc_j p, t_j p, ff) = ff
        let h = |p: usize| -> T {
            let num = numeral(kj, p);
            let body = if p < j {
                // acc_j p = a_p (symbolic) and t_j p = a_j & ff
                cases2(v(GN(p)), v(GN(j)), y(j), bool0(), &|a, c| maj(a, and2(c, ff()), ff()), &|_, _| ff())
            } else {
                rfl(ff())
            };
            rew(bool0(), ap(su.clone(), num.clone()), val(j, p), e[j][p].clone(),
                lm("b", bool0(), idt(bool0(), maj(v("b"), ap(sv.clone(), num), ff()), ff())), body)
        };
        // CF(j, q) : st (numeral q) = (numeral q, ff)
        let mut cf = vec![rfl(pair_s(kj, zero(kj), ff()))];
        for q in 0..n.saturating_sub(1) {
            let next = apn(l1.clone(), &[su.clone(), sv.clone(), numeral(kj + 1, q), numeral(kj, q), cf[q].clone(), h(q)]);
            cf.push(next);
        }
        let mut row = vec![];
        for q in 0..n {
            let num = numeral(kj, q);
            let svq = ap(sv.clone(), num.clone());
            // xor(xor(acc_j q, t_j q), ff) = val(j + 1, q), with acc_j q = val(j, q)
            let body = if q < j {
                cases2(v(GN(q)), v(GN(j)), y(j), bool0(), &|a, c| xor(xor(a, and2(c, ff())), ff()), &|a, _| a)
            } else if q == j {
                cases1(v(GN(j)), &|b| xor(xor(ff(), and2(b, tt())), ff()), &|b| b)
            } else {
                cases1(v(GN(j)), &|b| xor(xor(ff(), and2(b, ff())), ff()), &|_| ff())
            };
            let vnew = val(j + 1, q);
            let h2 = rew(bool0(), ap(su.clone(), num.clone()), val(j, q), e[j][q].clone(),
                lm("b", bool0(), idt(bool0(), xor(xor(v("b"), svq), ff()), vnew.clone())), body);
            row.push(apn(l2.clone(), &[su.clone(), sv.clone(), numeral(kj + 1, q), num, cf[q].clone(), vnew, h2]));
        }
        e.push(row);
    }
    e
}

// ---------- the bridge to Bv_n ----------
#[derive(Clone, Copy, Debug)]
pub(crate) enum Rhs {
    Y,
    Lit(u128),
    /// every bit negated
    NotY,
    /// bit 0 negated
    Flip0,
}
/// `\C k. t C (\a_0..a_(n-1). k f_0(a_0) .. f_(n-1)(a_(n-1)))`
fn map_bits(n: usize, t: T, f: &dyn Fn(usize, T) -> T) -> T {
    let call = (0..n).fold(v("k"), |g, j| ap(g, f(j, v(AN(j)))));
    let body = (0..n).rev().fold(call, |body, j| lm(AN(j), bool0(), body));
    lm("C", s(1), lm("k", arrows(n, v("C")), ap2(t, v("C"), body)))
}
pub(crate) fn mul_y(n: usize, fill: bool, xlit: u128) -> T {
    ap2(K(mul_bv_fill(n, fill)), K(encoding::lit(n, xlit)), v("y"))
}
/// `Pi y:Bv_n. GoodBv y -> Id(Bv_n, mul(n) (lit xlit) y, rhs)`, the `mul` built with the shift's fill bit `fill`.
pub(crate) fn bridge_stmt(n: usize, fill: bool, xlit: u128, rhs: Rhs) -> Expr {
    let bv = K(encoding::bv_ty(n));
    let r = match rhs {
        Rhs::Y => v("y"),
        Rhs::Lit(c) => K(encoding::lit(n, c)),
        Rhs::NotY => map_bits(n, v("y"), &|_, a| xor(a, tt())),
        Rhs::Flip0 => map_bits(n, v("y"), &|j, a| if j == 0 { xor(a, tt()) } else { a }),
    };
    ex(&pi_("y", bv.clone(), arr(ap(K(encoding::good_bv(n)), v("y")), idt(bv, mul_y(n, fill, xlit), r))))
}
/// The proof of `bridge_stmt(n, fill, 1, Y)`; `fill` is the shift's fill bit in the stream construction and in `mul(n)`.
fn bridge_proof(n: usize, fill: bool) -> Expr {
    let kn = K0 + n as u32;
    let e = eq_table(n, fill);
    let x = K(ex(&x_one()));
    let acc: Vec<Expr> = (0..=n).map(|j| acc_sym(j, fill)).collect();
    let ys: Vec<T> = (0..n).map(y).collect();
    let prod = big_a(&acc, n, &ys, &x);
    let g = tuple_chain(n, &|i| ap(prod.clone(), numeral(kn, i)), &|i| y(i), &|i| e[n][i].clone());
    let bv = K(encoding::bv_ty(n));
    let motive = lm("y", bv.clone(), idt(bv.clone(), mul_y(n, fill, 1), v("y")));
    ex(&lm("y", bv, lm("gb", ap(K(encoding::good_bv(n)), v("y")), ap2(v("gb"), motive, lam_bits(XN, n, g)))))
}

// ---------- tests ----------
#[test]
fn the_symbolic_accumulator_is_well_typed_and_multiplies() {
    for j in 0..=4usize {
        let f = acc_sym(j, false);
        let ty = kernel::typecheck(&f).unwrap_or_else(|m| panic!("acc_sym({j}): {m}"));
        let want = (0..j).rev().fold(arr(bits(K0), bits(K0 + j as u32)), |t, _| arr(bool0(), t));
        assert!(kernel::def_eq(&ty, &ex(&want)), "acc_sym({j}) has the wrong type");
    }
    // with literal multiplier bits it is the product of the one-hot stream 1 and y: bit p of y (p < m), zero above
    let m = 4usize;
    let ys_of = |yv: u128| -> Vec<T> { ybits(m, yv) };
    for yv in 0..(1u128 << m) {
        let ys = ys_of(yv);
        let prod = ap(apn(K(acc_sym(m, false)), &ys), K(ex(&x_one())));
        for p in 0..m + 2 {
            let got = ex(&ap(prod.clone(), numeral(K0 + m as u32, p)));
            assert!(kernel::def_eq(&got, &ex(&bit_of(yv, p))), "1 * {yv}: bit {p}");
        }
    }
}

#[test]
fn the_step_lemmas_are_well_typed_at_every_level() {
    for k in 1..=4u32 {
        kernel::typecheck(&ex(&l1_proof(k))).unwrap_or_else(|m| panic!("L1 k={k}: {m}"));
        kernel::typecheck(&ex(&l2_proof(k))).unwrap_or_else(|m| panic!("L2 k={k}: {m}"));
    }
}

#[test]
fn bridge_checks_for_small_n() {
    for n in 1..=4usize {
        let (pf, stmt) = (bridge_proof(n, false), bridge_stmt(n, false, 1, Rhs::Y));
        let (r, ms) = timed_check(&pf, &stmt);
        println!("[symmul bridge mul 1 y = y n={n}] {} in {ms:.2} ms", if r.is_ok() { "ACCEPTED" } else { "REJECTED" });
        r.unwrap_or_else(|m| panic!("n={n}: {}", m.chars().take(900).collect::<String>()));
    }
}

#[test]
fn bridge_rejects_wrong_statements() {
    for n in 1..=4usize {
        let pf = bridge_proof(n, false);
        let mut wrong: Vec<(&str, Expr)> = vec![
            ("mul 1 y = 0", bridge_stmt(n, false, 1, Rhs::Lit(0))),
            ("mul 1 y = not y", bridge_stmt(n, false, 1, Rhs::NotY)),
            ("mul 1 y = y with bit 0 flipped", bridge_stmt(n, false, 1, Rhs::Flip0)),
            ("mul 0 y = y", bridge_stmt(n, false, 0, Rhs::Y)),
        ];
        if n >= 2 {
            wrong.push(("mul 2 y = y", bridge_stmt(n, false, 2, Rhs::Y)));
            wrong.push(("mul 3 y = y", bridge_stmt(n, false, 3, Rhs::Y)));
        }
        for (name, stmt) in wrong {
            // well-typed and false: the rejection is a proof mismatch, not an ill-formed statement
            kernel::typecheck(&stmt).unwrap_or_else(|e| panic!("{name} is ill-typed: {e}"));
            let (r, _) = timed_check(&pf, &stmt);
            let m = r.expect_err(&format!("n={n}: {name} was accepted"));
            if n == 2 {
                println!("[symmul wrong n={n} {name}] REJECTED: {}", m.chars().take(100).collect::<String>());
            }
        }
    }
}

/// Flipping the shift's fill bit. With the multiplicand the literal 1, the shift is exercised at every multiplier bit j >= 1 (the
/// partial product `y_j & (1 << j)` is not masked by a literal zero), so for n >= 2 the real proof does not check against the
/// mutant `mul(n)`, and neither does the proof built with the mutant stream shift. At n = 1 there is no shift (j = 0 only): the
/// mutant is the same function and the proof is accepted.
#[test]
fn flipping_the_shifts_fill_bit_is_caught_by_this_bridge_for_n_at_least_2() {
    for n in 1..=4usize {
        let stmt = bridge_stmt(n, true, 1, Rhs::Y);
        kernel::typecheck(&stmt).unwrap_or_else(|e| panic!("mutant statement is ill-typed: {e}"));
        let (r, _) = timed_check(&bridge_proof(n, false), &stmt);
        let (r2, _) = timed_check(&bridge_proof(n, true), &stmt);
        if n == 1 {
            assert!(r.is_ok() && r2.is_ok(), "n=1 has no shift: the mutant is the same function");
            println!("[symmul mutant n=1] fill=true is the same function (no shift at n=1): ACCEPTED, as it must be");
        } else {
            let m = r.expect_err(&format!("n={n}: the real proof accepted the mutant mul"));
            println!("[symmul mutant n={n}] real proof vs shl_bv fill=true: REJECTED: {}", m.chars().take(140).collect::<String>());
            let m2 = r2.expect_err(&format!("n={n}: the fully mutated proof was accepted"));
            println!("[symmul mutant n={n}] mutant stream shift too: REJECTED: {}", m2.chars().take(140).collect::<String>());
        }
    }
}

// ---------- the per-width baseline ----------
// Output bit j of `mul 1 y` depends on a_0 .. a_(n-1) syntactically: the partial products of the higher multiplier bits are
// `a_m C ff ff`, which no computation removes. So every output bit splits on ALL n bits: 2^n leaves per bit (closed by refl).
fn direct_bit(n: usize, j: usize, idx: usize, bits: &[T]) -> T {
    let lhs = |bs: &[T]| proj_bit(n, j, ap2(K(mul_bv_fill(n, false)), K(encoding::lit(n, 1)), tuple(bs)));
    if idx == n {
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
pub(crate) fn baseline_proof(n: usize) -> Expr {
    let bv = K(encoding::bv_ty(n));
    let a: Vec<T> = (0..n).map(y).collect();
    let lhs = |i: usize| proj_bit(n, i, ap2(K(mul_bv_fill(n, false)), K(encoding::lit(n, 1)), tuple(&a)));
    let step = tuple_chain(n, &lhs, &|i| a[i].clone(), &|j| direct_bit(n, j, 0, &a));
    let motive = lm("y", bv.clone(), idt(bv.clone(), mul_y(n, false, 1), v("y")));
    ex(&lm("y", bv, lm("gb", ap(K(encoding::good_bv(n)), v("y")), ap2(v("gb"), motive, lam_bits(XN, n, step)))))
}

#[test]
fn baselines_check_for_small_n() {
    for n in 1..=4usize {
        let (pf, stmt) = (baseline_proof(n), bridge_stmt(n, false, 1, Rhs::Y));
        let (r, ms) = timed_check(&pf, &stmt);
        println!("[symmul baseline mul 1 y = y n={n}] {} in {ms:.2} ms", if r.is_ok() { "ACCEPTED" } else { "REJECTED" });
        r.unwrap_or_else(|m| panic!("baseline n={n}: {}", m.chars().take(900).collect::<String>()));
    }
}

/// Run by exact name. n = 7 peaked at 4288 MB (build 4.4 s); n = 8 hit the 8 GB wrapper cap (the proof term, a tree over the
/// `E(j, q)` table, grows about 4x per bit), so the list stops at 6.
#[test]
#[ignore]
fn symmul_scaling() {
    for n in [2usize, 4, 6] {
        let t0 = Instant::now();
        let (pf, stmt) = (bridge_proof(n, false), bridge_stmt(n, false, 1, Rhs::Y));
        let built = t0.elapsed().as_secs_f64() * 1e3;
        let (r, ms) = timed_check(&pf, &stmt);
        let t1 = Instant::now();
        let bp = baseline_proof(n);
        let bbuilt = t1.elapsed().as_secs_f64() * 1e3;
        let (r2, ms2) = timed_check(&bp, &stmt);
        println!("SYMMUL n={n}: bridge built {built:.1} ms, check {ms:.2} ms ({}); baseline built {bbuilt:.1} ms, check {ms2:.2} ms ({})",
            if r.is_ok() { "accepted" } else { "REJECTED" }, if r2.is_ok() { "accepted" } else { "REJECTED" });
    }
}
