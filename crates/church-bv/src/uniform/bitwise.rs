// Spike (2026-11-01, task u2; builds on `width.rs`): the bitwise and `lt` laws through the stream route, bridged to the
// encoding's own `Bv_n` statements.
//
// Bitwise operators are pointwise, so their uniform laws need no fold and no induction: `Pi x.. gx.. i. Id(Bool0, L(x i..), R(x i..))`
// for streams indexed by `Nat_k`, proved by a case split on the `GoodBool` witnesses at the position `i`. One table row
// (`Law`) states a law once, bit-level and as a fixed-width vector statement built only from `encoding::bitwise`, `lit`,
// `bv_ty` and `good_bv`; the uniform theorem, its bridge to `Bv_n` and the per-width baseline are all derived from the row.
// `lt` is a borrow chain (a fold like the adder, `encoding::ripple_carry`'s borrow) and needs the `Good1` induction.
// No per-width `Id` proof of any of these laws exists in `encoding.rs`; the statements are built from its definitions, and the
// `direct` baseline here (the same chain with the per-bit case split at the variables) is built in this file, not the encoding's.
use tatic_wasm::encoding;
use super::width::T::*;
use super::width::*;
use std::time::Instant;
use tatic_kernel::Expr;

// (the name sets `XN`, `YN` and the stream readers `stream`, `wstream` are `width`'s)

// ---------- bit-level gates ----------
/// Exactly `encoding::not_` (one gate).
fn not_t(a: T) -> T {
    ap(lm("a", bool0(), lm("C", s(0), lm("t", v("C"), lm("f", v("C"), ap3(v("a"), v("C"), v("f"), v("t")))))), a)
}

// ---------- fixed-width vector operations, from the encoding ----------
#[derive(Clone, Copy)]
enum Op {
    And,
    Or,
    Xor,
    NotL,
}
fn bw(n: usize, op: Op, x: T, y: T) -> T {
    let k = match op {
        Op::And => encoding::bitwise(n, &|a, b| encoding::and(a, b)),
        Op::Or => encoding::bitwise(n, &|a, b| encoding::or(a, b)),
        Op::Xor => encoding::bitwise(n, &|a, b| encoding::xor(a, b)),
        Op::NotL => encoding::bitwise(n, &|a, _| encoding::not_(a)),
    };
    ap2(K(k), x, y)
}
fn notv(n: usize, u: T) -> T {
    bw(n, Op::NotL, u.clone(), u)
}
fn lit(n: usize, x: u128) -> T {
    K(encoding::lit(n, x))
}

/// One law: `lhs = rhs` bitwise, over the bits `[x_i]` or `[x_i, y_i]`, and as a statement about `Bv_n` vectors.
struct Law {
    name: &'static str,
    arity: usize,
    lhs: fn(&[T]) -> T,
    rhs: fn(&[T]) -> T,
    vlhs: fn(usize, T, T) -> T,
    vrhs: fn(usize, T, T) -> T,
    /// a false right-hand side, bit-level and as a vector
    bad_bit: fn(&[T]) -> T,
    bad_vec: fn(usize, T, T) -> T,
}

const LAWS: [Law; 4] = [
    // x xor x = 0: one witness, the case split closes both branches by computation
    Law {
        name: "xor x x = 0",
        arity: 1,
        lhs: |b| xor(b[0].clone(), b[0].clone()),
        rhs: |_| ff(),
        vlhs: |n, x, _| bw(n, Op::Xor, x.clone(), x),
        vrhs: |n, _, _| lit(n, 0),
        bad_bit: |_| tt(),
        bad_vec: |n, _, _| lit(n, encoding::low_bits(n)),
    },
    // and x y = and y x: two witnesses
    Law {
        name: "and x y = and y x",
        arity: 2,
        lhs: |b| and2(b[0].clone(), b[1].clone()),
        rhs: |b| and2(b[1].clone(), b[0].clone()),
        vlhs: |n, x, y| bw(n, Op::And, x, y),
        vrhs: |n, x, y| bw(n, Op::And, y, x),
        bad_bit: |b| or2(b[1].clone(), b[0].clone()),
        bad_vec: |n, x, y| bw(n, Op::Or, y, x),
    },
    // absorption: and x (or x y) = x: two operators composed
    Law {
        name: "and x (or x y) = x",
        arity: 2,
        lhs: |b| and2(b[0].clone(), or2(b[0].clone(), b[1].clone())),
        rhs: |b| b[0].clone(),
        vlhs: |n, x, y| bw(n, Op::And, x.clone(), bw(n, Op::Or, x, y)),
        vrhs: |_, x, _| x,
        bad_bit: |b| b[1].clone(),
        bad_vec: |_, _, y| y,
    },
    // De Morgan: or (not x) (not y) = not (and x y): three operators, `not` is the encoding's one-gate `not_` on the first operand
    Law {
        name: "or (not x) (not y) = not (and x y)",
        arity: 2,
        lhs: |b| or2(not_t(b[0].clone()), not_t(b[1].clone())),
        rhs: |b| not_t(and2(b[0].clone(), b[1].clone())),
        vlhs: |n, x, y| bw(n, Op::Or, notv(n, x), notv(n, y)),
        vrhs: |n, x, y| notv(n, bw(n, Op::And, x, y)),
        bad_bit: |b| not_t(or2(b[0].clone(), b[1].clone())),
        bad_vec: |n, x, y| notv(n, bw(n, Op::Or, x, y)),
    },
];

// ---------- the uniform theorem of a law ----------
fn gbits(k: u32, s_: &'static str) -> T {
    pi_("i", nat(k), ap(goodbool(), ap(v(s_), v("i"))))
}
fn xy_bits(arity: usize) -> Vec<T> {
    let xi = ap(v("x"), v("i"));
    if arity == 1 { vec![xi] } else { vec![xi, ap(v("y"), v("i"))] }
}
/// `Pi x [y]. (Pi i. GoodBool (x i)) -> [..y..] -> Pi i:Nat_k. Id(Bool0, L, R)`; `wrong` swaps in the false right-hand side.
fn uni_stmt(law: &Law, k: u32, wrong: bool) -> T {
    let bs = xy_bits(law.arity);
    let r = if wrong { (law.bad_bit)(&bs) } else { (law.rhs)(&bs) };
    let body = pi_("i", nat(k), idt(bool0(), (law.lhs)(&bs), r));
    if law.arity == 1 {
        pi_("x", bits(k), arr(gbits(k, "x"), body))
    } else {
        pi_("x", bits(k), pi_("y", bits(k), arr(gbits(k, "x"), arr(gbits(k, "y"), body))))
    }
}
fn uni_proof(law: &Law, k: u32) -> T {
    let (l, r) = (law.lhs, law.rhs);
    let leaf = if law.arity == 1 {
        cases1(ap(v("gx"), v("i")), &|b| l(&[b]), &|b| r(&[b]))
    } else {
        cases2(ap(v("gx"), v("i")), ap(v("gy"), v("i")), ap(v("y"), v("i")), bool0(),
            &|a, c| l(&[a, c]), &|a, c| r(&[a, c]))
    };
    let inner = lm("i", nat(k), leaf);
    if law.arity == 1 {
        lm("x", bits(k), lm("gx", gbits(k, "x"), inner))
    } else {
        lm("x", bits(k), lm("y", bits(k), lm("gx", gbits(k, "x"), lm("gy", gbits(k, "y"), inner))))
    }
}

#[test]
fn bitwise_uniform_theorems_check_at_every_level() {
    for law in &LAWS {
        for k in 0..=3u32 {
            let (r, ms) = timed_check(&ex(&uni_proof(law, k)), &ex(&uni_stmt(law, k, false)));
            println!("[uniform {} k={k}] {} in {ms:.2} ms", law.name, if r.is_ok() { "ACCEPTED" } else { "REJECTED" });
            r.unwrap_or_else(|m| panic!("{} k={k}: {m}", law.name));
        }
    }
}

#[test]
fn bitwise_uniform_rejects_false_laws() {
    for law in &LAWS {
        let (r, _) = timed_check(&ex(&uni_proof(law, 1)), &ex(&uni_stmt(law, 1, true)));
        let m = r.expect_err(&format!("{}: the false right-hand side was accepted", law.name));
        println!("[uniform wrong {}] REJECTED: {}", law.name, m.chars().take(160).collect::<String>());
    }
}

// ---------- the bridge of a law to `Bv_n` ----------
#[derive(Clone, Copy, PartialEq)]
enum Mode {
    /// each bit by the uniform theorem at the numeral `i`
    Uniform,
    /// each bit by the per-bit case split at the variables (no streams): the baseline, built here
    Direct,
}

/// `(proof, statement)` of `Pi x [y]. GoodBv x -> [GoodBv y ->] Id(Bv_n, vlhs, vrhs)`; `wrong` states the false right-hand side.
fn bridge(law: &Law, n: usize, mode: Mode, wrong: bool) -> (Expr, Expr) {
    let a1 = law.arity == 1;
    let bv = K(encoding::bv_ty(n));
    let good = |s_: &'static str| ap(K(encoding::good_bv(n)), v(s_));
    let vr = |x: T, y: T| if wrong { (law.bad_vec)(n, x, y) } else { (law.vrhs)(n, x, y) };
    let body = |x: T, y: T| idt(bv.clone(), (law.vlhs)(n, x.clone(), y.clone()), vr(x, y));
    let stmt = if a1 {
        pi_("x", bv.clone(), arr(good("x"), body(v("x"), v("x"))))
    } else {
        pi_("x", bv.clone(), pi_("y", bv.clone(), arr(good("x"), arr(good("y"), body(v("x"), v("y"))))))
    };
    // the per-position bits and the proof of lhs_j = rhs_j
    let bits_at = |j: usize| if a1 { vec![v(AN(j))] } else { vec![v(AN(j)), v(CN(j))] };
    let lhs_j = |j: usize| (law.lhs)(&bits_at(j));
    let rhs_j = |j: usize| (law.rhs)(&bits_at(j));
    let (l, r) = (law.lhs, law.rhs);
    let eq_j = |j: usize| match mode {
        Mode::Direct => {
            if a1 {
                cases1(v(GN(j)), &|b| l(&[b]), &|b| r(&[b]))
            } else {
                cases2(v(GN(j)), v(GC(j)), v(CN(j)), bool0(), &|a, c| l(&[a, c]), &|a, c| r(&[a, c]))
            }
        }
        Mode::Uniform => {
            let mut t = ap(uni_proof(law, 2), stream(XN, n));
            if !a1 {
                t = ap(t, stream(YN, n));
            }
            t = ap(t, wstream(XN, n));
            if !a1 {
                t = ap(t, wstream(YN, n));
            }
            ap(t, numeral(2, j))
        }
    };
    let g = tuple_chain(n, &lhs_j, &rhs_j, &eq_j);
    let vl_true = |x: T, y: T| idt(bv.clone(), (law.vlhs)(n, x.clone(), y.clone()), (law.vrhs)(n, x, y));
    let proof = if a1 {
        let motive = lm("x", bv.clone(), vl_true(v("x"), v("x")));
        lm("x", bv.clone(), lm("gb", good("x"), ap2(v("gb"), motive, lam_bits(XN, n, g))))
    } else {
        let mk_a = tuple_of(n, &|i| v(AN(i)));
        let motive_y = lm("y", bv.clone(), vl_true(mk_a, v("y")));
        let step_x = lam_bits(XN, n, ap2(v("gy"), motive_y, lam_bits(YN, n, g)));
        let motive_x = lm("x", bv.clone(), vl_true(v("x"), v("y")));
        lm("x", bv.clone(), lm("y", bv.clone(), lm("gx", good("x"), lm("gy", good("y"),
            ap2(v("gx"), motive_x, step_x)))))
    };
    (ex(&proof), ex(&stmt))
}

#[test]
fn bitwise_bridge_checks_for_small_n() {
    for law in &LAWS {
        for n in [1usize, 2, 3] {
            for mode in [Mode::Uniform, Mode::Direct] {
                let (pf, stmt) = bridge(law, n, mode, false);
                let (r, ms) = timed_check(&pf, &stmt);
                println!("[bridge {} n={n} {}] {} in {ms:.2} ms", law.name, if mode == Mode::Uniform { "uniform" } else { "direct" },
                    if r.is_ok() { "ACCEPTED" } else { "REJECTED" });
                r.unwrap_or_else(|m| panic!("{} n={n}: {}", law.name, m.chars().take(900).collect::<String>()));
            }
        }
    }
}

#[test]
fn bitwise_bridge_rejects_wrong_statements() {
    for law in &LAWS {
        for n in [1usize, 2, 3] {
            for mode in [Mode::Uniform, Mode::Direct] {
                let (pf, _) = bridge(law, n, mode, false);
                let (_, wrong) = bridge(law, n, mode, true);
                let (r, _) = timed_check(&pf, &wrong);
                let m = r.expect_err(&format!("{} n={n}: the false statement was accepted", law.name));
                if n == 2 {
                    println!("[bridge wrong {}] REJECTED: {}", law.name, m.chars().take(160).collect::<String>());
                }
            }
        }
    }
}

#[test]
#[ignore]
fn bitwise_bridge_scaling() {
    for law in &LAWS {
        for n in [4usize, 8, 16, 24, 32] {
            for mode in [Mode::Uniform, Mode::Direct] {
                let t0 = Instant::now();
                let (pf, stmt) = bridge(law, n, mode, false);
                let built = t0.elapsed().as_secs_f64() * 1e3;
                let (r, ms) = timed_check(&pf, &stmt);
                println!("BITWISE {} n={n} {}: built {built:.1} ms, check {ms:.2} ms, {}", law.name,
                    if mode == Mode::Uniform { "uniform" } else { "direct " },
                    if r.is_ok() { "accepted".to_string() } else { format!("REJECTED {}", r.unwrap_err().chars().take(200).collect::<String>()) });
            }
        }
    }
}

// ---------- lt: the borrow chain ----------
/// The next borrow, in the circuit `encoding::ripple_carry(sub = true, ..)` uses.
fn borrow(a: T, b: T, c: T) -> T {
    let na = xor(a, tt());
    or2(and2(na.clone(), b.clone()), and2(c, xor(na, b)))
}

#[derive(Clone, Copy, PartialEq)]
enum Lt {
    /// `lt x x = 0`
    SelfLt,
    /// `lt x 0 = 0`
    Zero,
}
impl Lt {
    fn name(self) -> &'static str {
        match self {
            Lt::SelfLt => "lt x x = 0",
            Lt::Zero => "lt x 0 = 0",
        }
    }
    fn y(self, k: u32) -> T {
        match self {
            Lt::SelfLt => v("x"),
            Lt::Zero => zs(k),
        }
    }
    /// the `y` bit when the `x` bit is `b`
    fn ybit(self, b: T) -> T {
        match self {
            Lt::SelfLt => b,
            Lt::Zero => ff(),
        }
    }
}

/// `Pi N. Good1 N -> Pi x. (Pi i. GoodBool (x i)) -> Id(Bool0, borrow after N steps of x against y, 0)`; `wrong` states `1`.
fn lt_stmt(which: Lt, k: u32, wrong: bool) -> T {
    let r = if wrong { tt() } else { ff() };
    pi_("N", nat(k + 1), arr(ap(good1(k), v("N")), pi_("x", bits(k), arr(gbits(k, "x"),
        idt(bool0(), snd(k, st(k, borrow, v("x"), which.y(k), v("N"))), r)))))
}
/// One induction on the count, as `proof_b`: `st M = (embed M, false)`, then `snd`.
fn lt_proof(which: Lt, k: u32) -> T {
    let y = which.y(k);
    let stx = |m: T| st(k, borrow, v("x"), y.clone(), m);
    let target = |m: T| pair_s(embed(k, m), ff());
    let pm = lm("M", nat(k + 1), idt(state(k), stx(v("M")), target(v("M"))));
    let em = embed(k, v("m"));
    let to_false = cases1(ap(v("gx"), em.clone()), &|bb| borrow(bb.clone(), which.ybit(bb), ff()), &|_| ff());
    let h = rew(bool0(), borrow(ap(v("x"), em.clone()), ap(y.clone(), em.clone()), ff()), ff(), to_false,
        lm("t", bool0(), idt(state(k), pair_s(ap(succ(k), em.clone()), v("t")), pair_s(ap(succ(k), em.clone()), ff()))),
        rfl(pair_s(ap(succ(k), em.clone()), ff())));
    let step_ = lm("m", nat(k + 1), lm("ih", idt(state(k), stx(v("m")), target(v("m"))),
        rew(state(k), stx(v("m")), target(v("m")), v("ih"),
            lm("t", state(k), idt(state(k), ap(step(k, borrow, v("x"), y.clone()), v("t")), pair_s(ap(succ(k), em), ff()))),
            h)));
    let pn = ap3(v("g"), pm, rfl(pair_s(zero(k), ff())), step_);
    let fin = rew(state(k), stx(v("N")), target(v("N")), pn,
        lm("t", state(k), idt(bool0(), snd(k, v("t")), ff())), rfl(ff()));
    lm("N", nat(k + 1), lm("g", ap(good1(k), v("N")), lm("x", bits(k), lm("gx", gbits(k, "x"), fin))))
}

#[test]
fn lt_uniform_theorems_check_at_every_level() {
    for which in [Lt::SelfLt, Lt::Zero] {
        for k in 0..=3u32 {
            let (r, ms) = timed_check(&ex(&lt_proof(which, k)), &ex(&lt_stmt(which, k, false)));
            println!("[uniform {} k={k}] {} in {ms:.2} ms", which.name(), if r.is_ok() { "ACCEPTED" } else { "REJECTED" });
            r.unwrap_or_else(|m| panic!("{} k={k}: {m}", which.name()));
        }
    }
}

#[test]
fn lt_uniform_rejects_false_laws() {
    for which in [Lt::SelfLt, Lt::Zero] {
        let (r, _) = timed_check(&ex(&lt_proof(which, 1)), &ex(&lt_stmt(which, 1, true)));
        let m = r.expect_err("lt = 1 was accepted");
        println!("[uniform wrong {}] REJECTED: {}", which.name(), m.chars().take(160).collect::<String>());
    }
    // the skeleton of `lt x x` against `lt x 0` (a different chain) must not pass either way
    assert!(timed_check(&ex(&lt_proof(Lt::SelfLt, 1)), &ex(&lt_stmt(Lt::Zero, 1, true))).0.is_err());
    // and a law that is false: the borrow of `x` against `1`s is not always 0 (lt 0 1 = 1)
    let ones = lm("i", nat(1), tt());
    let bad = pi_("N", nat(2), arr(ap(good1(1), v("N")), pi_("x", bits(1), arr(gbits(1, "x"),
        idt(bool0(), snd(1, st(1, borrow, v("x"), ones, v("N"))), ff())))));
    assert!(timed_check(&ex(&lt_proof(Lt::Zero, 1)), &ex(&bad)).0.is_err(), "lt x 1s = 0 was accepted");
}

#[derive(Clone, Copy, PartialEq)]
enum LtWrong {
    None,
    /// claims `lt = 1`
    Rhs1,
    /// `lt x 1` instead of `lt x 0` (false at x = 0)
    Operand1,
    /// `lt 0 x` instead of `lt x 0` (false at x != 0), `Zero` only
    Swap,
}
/// `(proof, statement)` of `Pi x:Bv_n. GoodBv x -> Id(Bv_1, lt_u x x, lit 1 0)` (or `lt_u x (lit n 0)`), from the uniform theorem.
fn lt_bridge(which: Lt, n: usize, wrong: LtWrong) -> (Expr, Expr) {
    let k = 2;
    let bv = K(encoding::bv_ty(n));
    let bv1 = K(encoding::bv_ty(1));
    let (xs, gxs) = (stream(XN, n), wstream(XN, n));
    let ys = match which {
        Lt::SelfLt => xs.clone(),
        Lt::Zero => zs(k),
    };
    let lt_vec = |x: T, w: LtWrong| {
        let l = K(encoding::lt_u(n));
        match (which, w) {
            (Lt::SelfLt, LtWrong::Operand1) => ap2(l, x, lit(n, 1)),
            (Lt::SelfLt, _) => ap2(l, x.clone(), x),
            (Lt::Zero, LtWrong::Operand1) => ap2(l, x, lit(n, 1)),
            (Lt::Zero, LtWrong::Swap) => ap2(l, lit(n, 0), x),
            (Lt::Zero, _) => ap2(l, x, lit(n, 0)),
        }
    };
    let rhs = lit(1, if wrong == LtWrong::Rhs1 { 1 } else { 0 });
    let good = ap(K(encoding::good_bv(n)), v("x"));
    let stmt = pi_("x", bv.clone(), arr(good.clone(), idt(bv1.clone(), lt_vec(v("x"), wrong), rhs)));
    let e = ap(ap(ap(ap(lt_proof(which, k), numeral(k + 1, n)), goodnum(k, n as u32)), xs.clone()), gxs);
    let bnd = snd(k, st(k, borrow, xs, ys, numeral(k + 1, n)));
    let fam = lm("t", bool0(), idt(bv1.clone(), tuple(&[v("t")]), tuple(&[ff()])));
    let g = rew(bool0(), bnd, ff(), e, fam, rfl(tuple(&[ff()])));
    let motive = lm("x", bv.clone(), idt(bv1, lt_vec(v("x"), LtWrong::None), lit(1, 0)));
    let proof = lm("x", bv, lm("gb", good, ap2(v("gb"), motive, lam_bits(XN, n, g))));
    (ex(&proof), ex(&stmt))
}

#[test]
fn lt_bridge_checks_for_small_n() {
    for which in [Lt::SelfLt, Lt::Zero] {
        for n in [1usize, 2, 3] {
            let (pf, stmt) = lt_bridge(which, n, LtWrong::None);
            let (r, ms) = timed_check(&pf, &stmt);
            println!("[bridge {} n={n}] {} in {ms:.2} ms", which.name(), if r.is_ok() { "ACCEPTED" } else { "REJECTED" });
            r.unwrap_or_else(|m| panic!("{} n={n}: {}", which.name(), m.chars().take(900).collect::<String>()));
        }
    }
}

#[test]
fn lt_bridge_rejects_wrong_statements() {
    for which in [Lt::SelfLt, Lt::Zero] {
        for n in [1usize, 2, 3] {
            let (pf, _) = lt_bridge(which, n, LtWrong::None);
            let mut wrongs = vec![LtWrong::Rhs1, LtWrong::Operand1];
            if which == Lt::Zero {
                wrongs.push(LtWrong::Swap);
            }
            for w in wrongs {
                let (_, wrong) = lt_bridge(which, n, w);
                let (r, _) = timed_check(&pf, &wrong);
                let m = r.expect_err(&format!("{} n={n}: a false statement was accepted", which.name()));
                if n == 2 {
                    println!("[bridge wrong {}] REJECTED: {}", which.name(), m.chars().take(160).collect::<String>());
                }
            }
        }
    }
}

#[test]
#[ignore]
fn lt_bridge_scaling() {
    for which in [Lt::SelfLt, Lt::Zero] {
        for n in [4usize, 8, 16, 24, 32] {
            let t0 = Instant::now();
            let (pf, stmt) = lt_bridge(which, n, LtWrong::None);
            let built = t0.elapsed().as_secs_f64() * 1e3;
            let (r, ms) = timed_check(&pf, &stmt);
            println!("LT {} n={n}: built {built:.1} ms, check {ms:.2} ms, no per-width proof exists, {}", which.name(),
                if r.is_ok() { "accepted".to_string() } else { format!("REJECTED {}", r.unwrap_err().chars().take(200).collect::<String>()) });
        }
    }
}
