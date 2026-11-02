// Spike (2026-11-01; builds on `uniform_mul.rs`, `uniform_symmul_stream.rs`): `mul 1 y = y` with a SYMBOLIC multiplier, bridged
// STAGE BY STAGE at the `Bv_n` level, so that the kernel never has to convert the statement's whole fixed-width `mul(n)` against a
// differently shaped term.
//     Pi y:Bv_n. GoodBv y -> Id(Bv_n, mul(n) (lit 1) y, y)         (`bridge_stmt`; `mul(n) x y`: the multiplicand FIRST)
//
// This module holds the statement (`bridge_stmt`, `Rhs`, the negative variants), the stage-wise proof and a per-width baseline (the
// reference for the scaling comparison). The stream theorem uniform in the position, a standalone result, is in
// `uniform_symmul_stream.rs`; this bridge does not use it, only its case-split hypotheses (`hyps_c`, `hyps_x`).
//
// `mul(n) x y` unrolls to `ACC_n` with `ACC_0 = lit 0` and `ACC_(j+1) = add ACC_j (and (rep y_j) (shl^j x))`. Here:
//   * `ACC_j` is a CLOSED handle `\y_0..y_(j-1). ..` (`acc_table`), whose body applies the previous handle: conversion of a stage's
//     statement against its proof's type is one beta step (the same `add` application on both sides), it never unfolds the stages below.
//   * `S_j : Pi a_0..a_(j-1) ga_0..ga_(j-1). Id(Bv_n, ACC_j a.., T_j)` with the target tuple `T_j = (a_0..a_(j-1), ff..ff)`.
//     `S_0` is `refl`; `S_(j+1)` rewrites `ACC_j a..` to `T_j` (by `S_j`, a `Bv_n` equality) inside `add _ P_j` and finishes with the
//     stage lemma `L_j : Id(Bv_n, add T_j P_j, T_(j+1))`, `P_j = and (rep a_j) (shl^j (lit 1))`.
//   * `L_j` is proved directly at the Bv level for the symbolic bits (no stream, no induction): `tuple_chain` over the n output bits,
//     each `xor(xor(u_i, w_i), c_i) = T_(j+1)_i` with `u_i`, `w_i` the bits of the two operands and `c_i` the ripple carry
//     (`encoding::ripple`'s circuit, as `maj`). The carry is shown `ff` by a chain `E_(i+1)` of rewrites, one case split (on the
//     witnesses of `a_i` and `a_j`) per position `i < j`; the sum bits are then the case splits of `uniform_symmul_stream.rs`
//     (`hyps_c`, `hyps_x`). A case split on a `GoodBool` witness admits `Sort1` motives only, so every split is on a `Bool0` equality
//     and the `Bv_n` equality is assembled with `rew`.
//   * the bridge is `gb motive (\a.. ga.. . S_n a.. ga..)`; the one conversion left is `mul(n) (lit 1) (tuple a)` against `ACC_n a..`
//     (the same terms, one inline, one through handles).
//   * the baseline proves the same statement per width: output bit j of `mul 1 y` depends on a_0 .. a_(n-1) syntactically (the partial
//     products of the higher multiplier bits are `a_m C ff ff`, which no computation removes), so every output bit splits on ALL n
//     bits: 2^n leaves per bit, each closed by refl.
//
// Result (one run each on a shared machine, CPU load 30-80%; `symmul_scaling`, raw rows under `claude-runs/tatic`, runs
// `2026-11-01-opaque-*`): the end-to-end check is polynomial. Bridge check in ms: n = 4: 2.3-3.0; n = 6: 6.6-7.0; n = 7: 9.9;
// n = 8: 10.0-10.2; then 16.8, 43, 133, 211, 382 for n = 10, 12, 16, 20, 24 (roughly n^3). The comparisons with the baseline and
// with the bridges this module replaced are in `docs/tier-cycle.md` ("Laws uniform in the width").
// Each stage `S_j` checks in time about linear in j (n = 24: 3 ms for S_1, 115 for S_12, 306 for S_24), and the one remaining
// conversion `mul(n) (lit 1) (tuple a) == ACC_n a..` takes 3.1 ms at n = 8, 40 at 16, 163 at 24 (also polynomial, about 40% of the
// bridge at n = 24). Peak commit: 257 MB at n = 8, 640 MB at n = 24.
// What it costs: the BUILD is larger, not smaller: 291 ms at n = 8, then 663, 1550, 4806, 10129, 20358 ms for n = 10, 12, 16, 20, 24
// (the `tuple_chain` and `E_i` terms are built as trees, then hashed). The term's unfolded size still grows
// (199117, 800851, 2224525 nodes for n = 4, 6, 8: about 2x per bit) and its distinct nodes are about quadratic (2026, 3951, 6644,
// 10177 for n = 4, 6, 8, 10). The stream theorem's machinery (Good positions, lemmas D, Psh) is not used: the stage lemma is a
// direct Bv-level add of two explicit tuples, ~1 ms to check at n = 4.
// Not built: the second route of the task (the stage's add through the stream adder at numerals); the direct one is cheap, so
// there is nothing to compare it against here.
use super::encoding;
use super::uniform_mul::{band, mul_bv_fill, proj_bit, rep, shl_bv};
use super::uniform_symmul_stream::{apn, hyps_c, hyps_x, yv};
use super::uniform_width::T::*;
use super::uniform_width::*;
use std::time::Instant;
use tatic::kernel::{self, Expr};

// ---------- the statement ----------
#[derive(Clone, Copy, Debug)]
enum Rhs {
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
fn mul_y(n: usize, fill: bool, xlit: u128) -> T {
    ap2(K(mul_bv_fill(n, fill)), K(encoding::lit(n, xlit)), v("y"))
}
/// `Pi y:Bv_n. GoodBv y -> Id(Bv_n, mul(n) (lit xlit) y, rhs)`, the `mul` built with the shift's fill bit `fill`.
fn bridge_stmt(n: usize, fill: bool, xlit: u128, rhs: Rhs) -> Expr {
    let bv = K(encoding::bv_ty(n));
    let r = match rhs {
        Rhs::Y => v("y"),
        Rhs::Lit(c) => K(encoding::lit(n, c)),
        Rhs::NotY => map_bits(n, v("y"), &|_, a| xor(a, tt())),
        Rhs::Flip0 => map_bits(n, v("y"), &|j, a| if j == 0 { xor(a, tt()) } else { a }),
    };
    ex(&pi_("y", bv.clone(), arr(ap(K(encoding::good_bv(n)), v("y")), idt(bv, mul_y(n, fill, xlit), r))))
}

// ---------- the stage-wise proof ----------
fn bvk(n: usize) -> T {
    K(encoding::bv_ty(n))
}
/// `shl^j (lit 1)`, the multiplicand shifted j places (a closed term the kernel computes).
fn one_j(n: usize, fill: bool, j: usize) -> T {
    (0..j).fold(K(encoding::lit(n, 1)), |e, _| ap(shl_bv(n, fill), e))
}
/// The j-th partial product, `and (rep y) (shl^j (lit 1))`.
fn pp(n: usize, fill: bool, j: usize, y: T) -> T {
    band(n, rep(n, y), one_j(n, fill, j))
}
/// `T_j = (a_0..a_(j-1), ff..ff)` as a tuple term.
fn t_j(n: usize, j: usize) -> T {
    tuple(&(0..n).map(|m| if m < j { yv(m) } else { ff() }).collect::<Vec<_>>())
}

/// The closed handles `ACC_j : Bool0^j -> Bv_n` for j in 0..=n (`ACC_0 = lit 0`).
fn acc_table(n: usize, fill: bool) -> Vec<Expr> {
    let mut acc: Vec<Expr> = vec![encoding::lit(n, 0)];
    for j in 1..=n {
        let prev = (0..j - 1).fold(K(acc[j - 1]), |f, i| ap(f, v(YB(i))));
        let body = ap2(K(encoding::add(n)), prev, pp(n, fill, j - 1, v(YB(j - 1))));
        acc.push(ex(&(0..j).rev().fold(body, |b, i| lm(YB(i), bool0(), b))));
    }
    acc
}
fn acc_at(acc: &[Expr], j: usize) -> T {
    apn(K(acc[j]), &(0..j).map(yv).collect::<Vec<_>>())
}
/// `Pi a_0..a_(j-1). Pi ga_0..ga_(j-1). body`
fn pi_bits(j: usize, mut body: T) -> T {
    for m in (0..j).rev() {
        body = pi_(GN(m), ap(goodbool(), yv(m)), body);
    }
    for m in (0..j).rev() {
        body = pi_(AN(m), bool0(), body);
    }
    body
}
/// The statement of `S_j`.
fn stage_stmt(n: usize, j: usize, acc: &[Expr]) -> Expr {
    ex(&pi_bits(j, idt(bvk(n), acc_at(acc, j), t_j(n, j))))
}

/// The bits of the two operands of stage j's addition and the ripple carries: `T_j` (bit i is `a_i` below j, else ff) plus
/// `P_j` (bit i is `a_j & e_i`, with `e_i` the one-hot bit of `shl^j 1`), `carry[i+1] = maj(u_i, w_i, carry[i])`.
fn operand_bits(n: usize, j: usize) -> (Vec<T>, Vec<T>, Vec<T>) {
    let u: Vec<T> = (0..n).map(|i| if i < j { yv(i) } else { ff() }).collect();
    let w: Vec<T> = (0..n).map(|i| and2(yv(j), if i == j { tt() } else { ff() })).collect();
    let mut carry = vec![ff()];
    for i in 0..n {
        carry.push(maj(u[i].clone(), w[i].clone(), carry[i].clone()));
    }
    (u, w, carry)
}
/// `L_j : Id(Bv_n, add T_j P_j, T_(j+1))`, over the variables `a_0..a_j` and witnesses `ga_0..ga_j`.
fn stage_lemma(n: usize, j: usize) -> T {
    let (u, w, carry) = operand_bits(n, j);
    let (hc, hx) = (hyps_c(n, j), hyps_x(n, j));
    // E_i : Id(Bool0, carry_i, ff)
    let mut e = vec![rfl(ff())];
    for i in 0..n {
        let fam = lm("t", bool0(), idt(bool0(), maj(u[i].clone(), w[i].clone(), v("t")), ff()));
        e.push(rew(bool0(), carry[i].clone(), ff(), e[i].clone(), fam, hc[i].clone()));
    }
    let rhs = |i: usize| if i <= j { yv(i) } else { ff() };
    let lhs = |i: usize| xor(xor(u[i].clone(), w[i].clone()), carry[i].clone());
    let eq = |i: usize| {
        let fam = lm("t", bool0(), idt(bool0(), xor(xor(u[i].clone(), w[i].clone()), v("t")), rhs(i)));
        rew(bool0(), carry[i].clone(), ff(), e[i].clone(), fam, hx[i].clone())
    };
    tuple_chain(n, &lhs, &rhs, &eq)
}
/// `S_(j+1)` from `S_j`: rewrite `ACC_j a..` to `T_j` inside `add _ P_j`, then `L_j`.
fn next_stage(n: usize, j: usize, fill: bool, acc: &[Expr], s_j: Expr) -> Expr {
    let prev_args: Vec<T> = (0..j).map(yv).chain((0..j).map(|m| v(GN(m)))).collect();
    let acc_j = acc_at(acc, j);
    let fam = lm("t", bvk(n), idt(bvk(n), ap2(K(encoding::add(n)), v("t"), pp(n, fill, j, yv(j))), t_j(n, j + 1)));
    let body = rew(bvk(n), acc_j, t_j(n, j), apn(K(s_j), &prev_args), fam, stage_lemma(n, j));
    ex(&lam_bits(XN, j + 1, body))
}
/// `S_0 .. S_n` over the handles `acc`.
fn stages(n: usize, fill: bool, acc: &[Expr]) -> Vec<Expr> {
    let mut s_tab = vec![ex(&rfl(t_j(n, 0)))];
    for j in 0..n {
        let nxt = next_stage(n, j, fill, acc, s_tab[j]);
        s_tab.push(nxt);
    }
    s_tab
}

/// The proof of `bridge_stmt(n, fill, 1, Rhs::Y)`; `fill` is the shift's fill bit in the handles and in `mul(n)`.
fn bridge_proof(n: usize, fill: bool) -> Expr {
    let s_tab = stages(n, fill, &acc_table(n, fill));
    let args: Vec<T> = (0..n).map(yv).chain((0..n).map(|m| v(GN(m)))).collect();
    let g = apn(K(s_tab[n]), &args);
    let bv = bvk(n);
    let motive = lm("y", bv.clone(), idt(bv.clone(), mul_y(n, fill, 1), v("y")));
    ex(&lm("y", bv, lm("gb", ap(K(encoding::good_bv(n)), v("y")), ap2(v("gb"), motive, lam_bits(XN, n, g)))))
}

// ---------- the per-width baseline ----------
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
fn baseline_proof(n: usize) -> Expr {
    let bv = bvk(n);
    let a: Vec<T> = (0..n).map(yv).collect();
    let lhs = |i: usize| proj_bit(n, i, ap2(K(mul_bv_fill(n, false)), K(encoding::lit(n, 1)), tuple(&a)));
    let step = tuple_chain(n, &lhs, &|i| a[i].clone(), &|j| direct_bit(n, j, 0, &a));
    let motive = lm("y", bv.clone(), idt(bv.clone(), mul_y(n, false, 1), v("y")));
    ex(&lm("y", bv, lm("gb", ap(K(encoding::good_bv(n)), v("y")), ap2(v("gb"), motive, lam_bits(XN, n, step)))))
}

// ---------- tests ----------
fn chk(name: &str, pf: &Expr, stmt: &Expr) -> f64 {
    let (r, ms) = timed_check(pf, stmt);
    println!("[{name}] {} in {ms:.2} ms", if r.is_ok() { "ACCEPTED" } else { "REJECTED" });
    r.unwrap_or_else(|m| panic!("{name}: {}", m.chars().take(1500).collect::<String>()));
    ms
}

#[test]
fn the_handles_are_well_typed_and_multiply() {
    for n in 1..=3usize {
        for (j, h) in acc_table(n, false).iter().enumerate() {
            kernel::typecheck(h).unwrap_or_else(|m| panic!("ACC_{j} n={n}: {m}"));
        }
    }
}

#[test]
fn every_stage_checks() {
    for n in 1..=4usize {
        let acc = acc_table(n, false);
        let s_tab = stages(n, false, &acc);
        for j in 0..=n {
            chk(&format!("opaque S_{j} n={n}"), &s_tab[j], &stage_stmt(n, j, &acc));
        }
    }
}

#[test]
fn bridge_checks_for_small_n() {
    for n in 1..=4usize {
        chk(&format!("symmul bridge mul 1 y = y n={n}"), &bridge_proof(n, false), &bridge_stmt(n, false, 1, Rhs::Y));
    }
}

#[test]
fn baselines_check_for_small_n() {
    for n in 1..=4usize {
        chk(&format!("symmul baseline mul 1 y = y n={n}"), &baseline_proof(n), &bridge_stmt(n, false, 1, Rhs::Y));
    }
}

#[test]
fn stage_lemma_rejects_a_wrong_target() {
    // S_j against a statement whose target tuple is wrong (T_(j+1) with bit 0 flipped / the wrong accumulator) is rejected
    let n = 3usize;
    let acc = acc_table(n, false);
    let s_tab = stages(n, false, &acc);
    for j in 1..=n {
        let flipped = ex(&pi_bits(j, idt(bvk(n), acc_at(&acc, j), tuple(&(0..n).map(|m| if m == 0 { xor(yv(0), tt()) } else if m < j { yv(m) } else { ff() }).collect::<Vec<_>>()))));
        kernel::typecheck(&flipped).unwrap_or_else(|e| panic!("flipped S_{j} is ill-typed: {e}"));
        let (r, _) = timed_check(&s_tab[j], &flipped);
        r.expect_err(&format!("S_{j} was accepted against a flipped target"));
        // the previous stage's statement is also not S_j's
        let wrong = stage_stmt(n, j - 1, &acc);
        let (r, _) = timed_check(&s_tab[j], &wrong);
        r.expect_err(&format!("S_{j} was accepted against the statement of S_{}", j - 1));
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

/// The shift's fill bit flipped, in the statement's `mul(n)` and/or in the proof's handles. At n = 1 there is no shift and the
/// mutant is the same function; from n = 2 the stage lemma (built for `fill = false`'s one-hot bits) and the final conversion see it.
#[test]
fn flipping_the_shifts_fill_bit_is_caught_for_n_at_least_2() {
    for n in 1..=4usize {
        let stmt = bridge_stmt(n, true, 1, Rhs::Y);
        kernel::typecheck(&stmt).unwrap_or_else(|e| panic!("mutant statement is ill-typed: {e}"));
        let (r, _) = timed_check(&bridge_proof(n, false), &stmt);
        let (r2, _) = timed_check(&bridge_proof(n, true), &stmt);
        if n == 1 {
            assert!(r.is_ok() && r2.is_ok(), "n=1 has no shift: the mutant is the same function");
        } else {
            let m = r.expect_err(&format!("n={n}: the real proof accepted the mutant mul"));
            println!("[symmul mutant n={n}] real proof vs shl_bv fill=true: REJECTED: {}", m.chars().take(140).collect::<String>());
            let m2 = r2.expect_err(&format!("n={n}: the fully mutated proof was accepted"));
            println!("[symmul mutant n={n}] mutant handles too: REJECTED: {}", m2.chars().take(140).collect::<String>());
        }
    }
}

/// The mutation is rejected by a STAGE (the lemma `L_j` is about the one-hot partial product), not only by the final conversion:
/// with the mutated handles, `S_1` (no shift) still checks and every `S_(j+1)` with j >= 1 does not.
#[test]
fn the_mutated_handles_fail_at_the_stage_that_shifts() {
    let n = 4usize;
    let acc = acc_table(n, true);
    let s_tab = stages(n, true, &acc);
    for j in 1..=n {
        let (r, _) = timed_check(&s_tab[j], &stage_stmt(n, j, &acc));
        if j == 1 {
            r.expect("S_1 has no shift and must still check");
        } else {
            r.expect_err(&format!("S_{j} checked with the fill bit flipped"));
        }
    }
}

fn ns_from_env(default: &[usize]) -> Vec<usize> {
    std::env::var("SYMMUL_NS").ok().map(|s| s.split(',').filter_map(|t| t.parse().ok()).collect()).unwrap_or_else(|| default.to_vec())
}

/// Run by exact name; `SYMMUL_NS=4,6,8` picks the widths. Prints the build time, every stage's check time (each against its own
/// statement), the end-to-end bridge check, and the time of the single conversion `mul(n) (lit 1) (tuple a) == ACC_n a..`.
/// With `SYMMUL_BASE=1` it also builds and checks the per-width baseline (2^n leaves per output bit) for the same n.
/// The peak memory of a run is in the wrapper's `run.json`, not printed here.
#[test]
#[ignore]
fn symmul_scaling() {
    for n in ns_from_env(&[2, 4]) {
        let t0 = Instant::now();
        let acc = acc_table(n, false);
        let s_tab = stages(n, false, &acc);
        let pf = bridge_proof(n, false);
        let built = t0.elapsed().as_secs_f64() * 1e3;
        let per_stage: Vec<String> = (1..=n).map(|j| format!("S_{j} {:.2}", timed_check(&s_tab[j], &stage_stmt(n, j, &acc)).1)).collect();
        let stmt = bridge_stmt(n, false, 1, Rhs::Y);
        let (r, ms) = timed_check(&pf, &stmt);
        // the one remaining conversion, closed over the bits
        let a: Vec<T> = (0..n).map(yv).collect();
        let abits = |body: T| (0..n).rev().fold(body, |b, j| lm(AN(j), bool0(), b));
        let l = ex(&abits(ap2(K(mul_bv_fill(n, false)), K(encoding::lit(n, 1)), tuple(&a))));
        let rr = ex(&abits(acc_at(&acc, n)));
        let t1 = Instant::now();
        let same = kernel::def_eq(&l, &rr);
        let conv = t1.elapsed().as_secs_f64() * 1e3;
        println!("SYMMUL n={n}: built {built:.1} ms; stage checks: {}; bridge check {ms:.2} ms ({}); final conversion {conv:.2} ms ({}); distinct/unfolded {:?}",
            per_stage.join(", "), if r.is_ok() { "accepted" } else { "REJECTED" }, if same { "equal" } else { "NOT EQUAL" }, kernel::term_sizes(&pf));
        if std::env::var("SYMMUL_BASE").is_ok() {
            let t3 = Instant::now();
            let base = baseline_proof(n);
            let base_built = t3.elapsed().as_secs_f64() * 1e3;
            let (r3, ms3) = timed_check(&base, &stmt);
            println!("SYMMUL_BASE n={n}: per-width baseline built {base_built:.1} ms, check {ms3:.2} ms ({}); stage-wise bridge built {built:.1} ms, check {ms:.2} ms", if r3.is_ok() { "accepted" } else { "REJECTED" });
        }
    }
}

/// The header's size claims are the measured ones: distinct nodes about quadratic, unfolded size about 2x per bit.
#[test]
fn header_size_claims_are_the_measured_ones() {
    let sizes: Vec<(usize, u128)> = (2..=6usize).map(|n| kernel::term_sizes(&bridge_proof(n, false))).collect();
    println!("[symmul sizes] (distinct, unfolded) for n=2..6: {sizes:?}");
    for w in sizes.windows(2) {
        assert!(w[1].0 < w[0].0 * 2, "distinct nodes grew by 2x or more in one bit: {sizes:?}");
        assert!(w[1].1 < w[0].1 * 4, "unfolded size grew by 4x or more in one bit: {sizes:?}");
    }
    let src = include_str!("uniform_symmul.rs");
    let header: String = src.lines().take_while(|l| l.starts_with("//")).collect::<Vec<_>>().join("\n");
    for phrase in ["polynomial", "docs/tier-cycle.md", "BUILD is larger", "Not built"] {
        assert!(header.contains(phrase), "the header must say: {phrase}");
    }
}
