// Spike (2026-11-07, o1): is the level wall of `mul.rs#a_single_nested_fold_is_ill_typed` a property of the kernel, or only of
// Church numerals? The stream adder raises its level because a Church `Nat_k` folds only into `Sort k`, so a fold whose state is
// a stream has no fixed point. `WRec`'s motive is unrestricted, so an index built as a W-type can fold into its own stream type.
//
// The index. A bare Church tag gives a `WRec` step no way to use `f : B(a) -> N`, since a Church bool has no dependent case; the
// tag therefore carries its own witness:
//   Maybe X := Pi C:Sort1. (X -> C) -> C -> C                                  : Sort2
//   Tag     := Sigma X:Sort1. Sigma m:Maybe X. GoodMaybe m                     : Sort2
//   N       := W(Tag, fst)                                                     : Sort2
//   Bits    := N -> Bool0                                                      : Sort2
// so `add : Bits -> Bits -> Bits` raises no level, and a multiplier fold is one `WRec`. `Empty` and `Unit` are derived (`empty` is
// `W(unit, \_. unit)`), so no postulate enters. The position is the tree itself: no position in the state, no `embed`.
//
// The tree is not canonical: `nothing` under an inhabited `X` is a second zero, and `X` may branch, so `succ` is not injective
// and there is no general induction `Pi Q. Q zero -> .. -> Pi n. Q n`. A proof splits a tag only through `GoodMaybe`, whose motive
// sits in `Sort1` and sees `m` but not its witness, so `ind` below takes the statement in reduced form, with the tag's `m`
// abstracted. That covers exactly the statements that read a tree through its tag, which is all a stream function can do.
use super::mul::bit_of;
use super::width::T::*;
use super::width::*;
use tatic_kernel::{self as kernel, Ctx};

// ---------- the index ----------
fn unit() -> T {
    idt(bool0(), tt(), tt())
}
fn star() -> T {
    rfl(tt())
}
fn empty() -> T {
    W("_u", b(unit()), b(unit()))
}
fn maybe(x: T) -> T {
    pi_("$C", s(1), arr(arr(x, v("$C")), arr(v("$C"), v("$C"))))
}
fn just(x: T, a: T) -> T {
    lm("$C", s(1), lm("$j", arr(x, v("$C")), lm("$e", v("$C"), ap(v("$j"), a))))
}
fn nothing(x: T) -> T {
    lm("$C", s(1), lm("$j", arr(x, v("$C")), lm("$e", v("$C"), v("$e"))))
}
fn goodmaybe(x: T, m: T) -> T {
    pi_("$P", arr(maybe(x.clone()), s(1)), arr(pi_("$a", x.clone(), ap(v("$P"), just(x.clone(), v("$a")))),
        arr(ap(v("$P"), nothing(x)), ap(v("$P"), m))))
}
/// The `GoodMaybe` witness of `just` or `nothing`: `pick` is the branch's own hypothesis.
fn good_case(x: T, pick: T) -> T {
    lm("$P", arr(maybe(x.clone()), s(1)), lm("$hj", pi_("$a", x.clone(), ap(v("$P"), just(x.clone(), v("$a")))),
        lm("$hn", ap(v("$P"), nothing(x)), pick)))
}
fn tag_inner(x: T) -> T {
    Sig("$m", b(maybe(x.clone())), b(goodmaybe(x, v("$m"))))
}
fn tag_ty() -> T {
    K(ex(&Sig("X", b(s(1)), b(tag_inner(v("X"))))))
}
fn tag_mk(x: T, m: T, g: T) -> T {
    Pair("X", b(tag_inner(v("X"))), b(x.clone()), b(Pair("$m", b(goodmaybe(x, v("$m"))), b(m), b(g))))
}
fn tag_x(t: T) -> T {
    SigRec(b(lm("_t", tag_ty(), s(1))), b(lm("X", s(1), lm("r", tag_inner(v("X")), v("X")))), b(t))
}
fn tag_m(t: T) -> T {
    let inner = SigRec(b(lm("_r", tag_inner(v("X")), maybe(v("X")))),
        b(lm("m", maybe(v("X")), lm("g", goodmaybe(v("X"), v("m")), v("m")))), b(v("r")));
    SigRec(b(lm("_t", tag_ty(), maybe(tag_x(v("_t"))))), b(lm("X", s(1), lm("r", tag_inner(v("X")), inner))), b(t))
}
fn nw() -> T {
    K(ex(&W("t", b(tag_ty()), b(tag_x(v("t"))))))
}
fn bw() -> T {
    arr(nw(), bool0())
}
/// `empty -> N`, by `WRec`: the one child of a tree of `empty` is the recursive answer.
fn absurd(e: T) -> T {
    WRec("_u", b(lm("_n", empty(), nw())), b(unit()),
        b(lm("a", unit(), lm("f", arr(unit(), empty()), lm("ih", arr(unit(), nw()), ap(v("ih"), v("a")))))), b(e))
}
fn zero_w() -> T {
    let e = empty();
    Sup(b(tag_mk(e.clone(), nothing(e.clone()), good_case(e.clone(), v("$hn")))), b(lm("e", e, absurd(v("e")))))
}
fn succ_w(n: T) -> T {
    let tag = tag_mk(unit(), just(unit(), star()), good_case(unit(), ap(v("$hj"), star())));
    Sup(b(tag), b(lm("_", unit(), n)))
}
fn num(j: usize) -> T {
    (0..j).fold(zero_w(), |e, _| succ_w(e))
}

// ---------- streams ----------
/// Non-dependent recursion on `n` into `res`, whose `body` reads `$t`, `$f` and `$ih`.
fn rec_w(res: T, n: T, body: T) -> T {
    WRec("$t", b(lm("_n", nw(), res.clone())), b(tag_x(v("$t"))), b(lm("$t", tag_ty(), lm("$f", arr(tag_x(v("$t")), nw()),
        lm("$ih", arr(tag_x(v("$t")), res), body)))), b(n))
}
/// The tag's case split at the leaf, in a `rec_w` body: `k` on the witness, else `z`.
fn sel(k: &dyn Fn(T) -> T, z: T) -> T {
    ap3(tag_m(v("$t")), bool0(), lm("$w", tag_x(v("$t")), k(v("$w"))), z)
}
fn carry_fn() -> T {
    K(ex(&lm("x", bw(), lm("y", bw(), lm("i", nw(), rec_w(bool0(), v("i"), sel(&|w| {
        let p = ap(v("$f"), w.clone());
        maj(ap(v("x"), p.clone()), ap(v("y"), p), ap(v("$ih"), w))
    }, ff())))))))
}
fn carry(a: T, c: T, i: T) -> T {
    ap3(carry_fn(), a, c, i)
}
fn add_fn() -> T {
    K(ex(&lm("x", bw(), lm("y", bw(), lm("i", nw(), xor(xor(ap(v("x"), v("i")), ap(v("y"), v("i"))), carry(v("x"), v("y"), v("i"))))))))
}
fn add(a: T, c: T) -> T {
    ap2(add_fn(), a, c)
}
/// Bit `i` of the shift: `x (i - 1)`, and `fill` at 0 (false for the real shift; true is the mutant).
fn shl_fn(fill: bool) -> T {
    K(ex(&lm("x", bw(), lm("i", nw(), rec_w(bool0(), v("i"), sel(&|w| ap(v("x"), ap(v("$f"), w)), if fill { tt() } else { ff() }))))))
}
fn shl(a: T) -> T {
    ap(shl_fn(false), a)
}
fn shr(y: T) -> T {
    lm("$i", nw(), ap(y, succ_w(v("$i"))))
}
fn zw() -> T {
    lm("$i", nw(), ff())
}
/// The partial product, `j -> and(x j, z)`: the operand first, so `x j = false` makes it false by computation.
fn tmask(x: T, z: T) -> T {
    lm("$j", nw(), and2(ap(x, v("$j")), z))
}
/// Horner on the multiplier: `mul (succ p) x y = (x & y_0) + shl (mul p x (shr y))`, one fold whose motive is a stream function.
fn mul_fn(fill: bool) -> T {
    let res = arr(bw(), arr(bw(), bw()));
    let body = lm("x", bw(), lm("y", bw(), lm("i", nw(), sel(&|w| {
        let tail = ap2(ap(v("$ih"), w), v("x"), shr(v("y")));
        ap(ap2(add_fn(), tmask(v("x"), ap(v("y"), zero_w())), ap(shl_fn(fill), tail)), v("i"))
    }, ff()))));
    K(ex(&lm("m", nw(), rec_w(res, v("m"), body))))
}
fn mul(m: T, x: T, y: T) -> T {
    ap3(mul_fn(false), m, x, y)
}
/// The stream of the low `nb` bits of `val`, as a chain of closed tag cases.
fn stream_of(val: u128, nb: usize) -> T {
    (0..nb).rev().fold(zw(), |tail, j| {
        let tail = K(ex(&tail));
        K(ex(&lm("i", nw(), rec_w(bool0(), v("i"), sel(&|w| ap(tail.clone(), ap(v("$f"), w)), bit_of(val, j))))))
    })
}

// ---------- proofs ----------
fn eqb(a: T, c: T) -> T {
    idt(bool0(), a, c)
}
/// Pointwise equality of two streams.
fn ptw(a: T, c: T) -> T {
    pi_("$i", nw(), eqb(ap(a, v("$i")), ap(c, v("$i"))))
}
fn sym(l: T, r: T, p: T) -> T {
    rew(bool0(), l, r.clone(), p, lm("t", bool0(), eqb(r.clone(), v("t"))), rfl(r))
}
fn trans(l: T, m: T, r: T, p: T, q: T) -> T {
    rew(bool0(), l, m, p, lm("t", bool0(), eqb(v("t"), r)), q)
}
/// `f l1 l2 l3 = f r1 r2 r3`, from `(l, r, l = r)` for each argument.
fn cong3(f: &dyn Fn(T, T, T) -> T, e1: (T, T, T), e2: (T, T, T), e3: (T, T, T)) -> T {
    let ((l1, r1, p1), (l2, r2, p2), (l3, r3, p3)) = (e1, e2, e3);
    let rhs = f(r1.clone(), r2.clone(), r3.clone());
    let h3 = rew(bool0(), l3.clone(), r3, p3, lm("t", bool0(), eqb(f(r1.clone(), r2.clone(), v("t")), rhs.clone())), rfl(rhs.clone()));
    let h2 = rew(bool0(), l2.clone(), r2, p2, lm("t", bool0(), eqb(f(r1.clone(), v("t"), l3.clone()), rhs.clone())), h3);
    rew(bool0(), l1, r1, p1, lm("t", bool0(), eqb(f(v("t"), l2, l3), rhs)), h2)
}
fn xor3(a: T, c: T, d: T) -> T {
    xor(xor(a, c), d)
}
/// The tag case of a reduced statement, at the abstracted `m`.
fn selm(m: T, k: &dyn Fn(T) -> T, z: T) -> T {
    ap3(m, bool0(), lm("$w", v("X"), k(v("$w"))), z)
}
fn fw(w: &T) -> T {
    ap(v("$f"), w.clone())
}
/// Induction on `target` for `motive`. Inside, `X`, `$f` and `$ih` are bound; `pre` wraps the lambdas that bring the statement down
/// to `Sort1`; `pred m` is that statement reduced at the tag's `m`; `hj w` proves it at `just w`, `hn` at `nothing`.
fn ind(motive: &dyn Fn(T) -> T, target: T, pre: &dyn Fn(T) -> T, pred: &dyn Fn(T) -> T, hj: &dyn Fn(T) -> T, hn: T) -> T {
    let goal = |tag: T| pi_("$f", arr(tag_x(tag.clone()), nw()),
        pi_("$ih", pi_("$w", tag_x(tag.clone()), motive(ap(v("$f"), v("$w")))), motive(Sup(b(tag), b(v("$f"))))));
    let split = ap3(v("g"), lm("$mm", maybe(v("X")), pred(v("$mm"))), lm("$w", v("X"), hj(v("$w"))), hn);
    let leaf = lm("m", maybe(v("X")), lm("g", goodmaybe(v("X"), v("m")),
        lm("$f", arr(v("X"), nw()), lm("$ih", pi_("$w", v("X"), motive(ap(v("$f"), v("$w")))), pre(split)))));
    let pack = |r: T| Pair("X", b(tag_inner(v("X"))), b(v("X")), b(r));
    let by_r = SigRec(b(lm("_r", tag_inner(v("X")), goal(pack(v("_r"))))), b(leaf), b(v("r")));
    let step = lm("$t", tag_ty(), SigRec(b(lm("_t", tag_ty(), goal(v("_t")))), b(lm("X", s(1), lm("r", tag_inner(v("X")), by_r))), b(v("$t"))));
    WRec("$t", b(lm("$n", nw(), motive(v("$n")))), b(tag_x(v("$t"))), b(step), b(target))
}
fn noop(t: T) -> T {
    t
}
fn carry_at(a: &T, c: &T, w: &T) -> T {
    let p = fw(w);
    maj(ap(a.clone(), p.clone()), ap(c.clone(), p.clone()), carry(a.clone(), c.clone(), p))
}

/// `Pi a a2 c c2. a ~ a2 -> c ~ c2 -> Pi n. carry a c n = carry a2 c2 n`
fn carry_cong() -> T {
    let (a, a2, c, c2) = (v("a"), v("a2"), v("c"), v("c2"));
    let pred = |m: T| eqb(selm(m.clone(), &|w| carry_at(&a, &c, &w), ff()), selm(m, &|w| carry_at(&a2, &c2, &w), ff()));
    let hj = |w: T| {
        let p = fw(&w);
        cong3(&maj, (ap(a.clone(), p.clone()), ap(a2.clone(), p.clone()), ap(v("ha"), p.clone())),
            (ap(c.clone(), p.clone()), ap(c2.clone(), p.clone()), ap(v("hc"), p.clone())),
            (carry(a.clone(), c.clone(), p.clone()), carry(a2.clone(), c2.clone(), p), ap(v("$ih"), w)))
    };
    let body = ind(&|n| eqb(carry(a.clone(), c.clone(), n.clone()), carry(a2.clone(), c2.clone(), n)), v("n"), &noop, &pred, &hj, rfl(ff()));
    K(ex(&lm("a", bw(), lm("a2", bw(), lm("c", bw(), lm("c2", bw(), lm("ha", ptw(a.clone(), a2.clone()), lm("hc", ptw(c.clone(), c2.clone()),
        lm("n", nw(), body)))))))))
}
/// `Pi a a2 c c2. a ~ a2 -> c ~ c2 -> Pi i. add a c i = add a2 c2 i`
fn add_cong() -> T {
    let (a, a2, c, c2, i) = (v("a"), v("a2"), v("c"), v("c2"), v("i"));
    let ce = ap(ap2(ap(ap3(carry_cong(), a.clone(), a2.clone(), c.clone()), c2.clone()), v("ha"), v("hc")), i.clone());
    let body = cong3(&xor3, (ap(a.clone(), i.clone()), ap(a2.clone(), i.clone()), ap(v("ha"), i.clone())),
        (ap(c.clone(), i.clone()), ap(c2.clone(), i.clone()), ap(v("hc"), i.clone())),
        (carry(a.clone(), c.clone(), i.clone()), carry(a2.clone(), c2.clone(), i), ce));
    K(ex(&lm("a", bw(), lm("a2", bw(), lm("c", bw(), lm("c2", bw(), lm("ha", ptw(a.clone(), a2.clone()), lm("hc", ptw(c, c2),
        lm("i", nw(), body)))))))))
}
fn add_cong_at(a: T, a2: T, c: T, c2: T, ha: T, hc: T, i: T) -> T {
    ap(ap2(ap(ap3(add_cong(), a, a2, c), c2), ha, hc), i)
}
/// `Pi a a2. a ~ a2 -> Pi n. shl a n = shl a2 n`
fn shl_cong() -> T {
    let (a, a2) = (v("a"), v("a2"));
    let pred = |m: T| eqb(selm(m.clone(), &|w| ap(a.clone(), fw(&w)), ff()), selm(m, &|w| ap(a2.clone(), fw(&w)), ff()));
    let body = ind(&|n| eqb(ap(shl(a.clone()), n.clone()), ap(shl(a2.clone()), n)), v("n"), &noop, &pred, &|w| ap(v("ha"), fw(&w)), rfl(ff()));
    K(ex(&lm("a", bw(), lm("a2", bw(), lm("ha", ptw(a.clone(), a2.clone()), lm("n", nw(), body))))))
}
/// `Pi a. (Pi i. a i = false) -> Pi n. shl a n = false`
fn shl_false() -> T {
    let a = v("a");
    let pred = |m: T| eqb(selm(m, &|w| ap(a.clone(), fw(&w)), ff()), ff());
    let body = ind(&|n| eqb(ap(shl(a.clone()), n), ff()), v("n"), &noop, &pred, &|w| ap(v("ha"), fw(&w)), rfl(ff()));
    K(ex(&lm("a", bw(), lm("ha", ptw(a.clone(), zw()), lm("n", nw(), body)))))
}
/// `Pi n. carry zs zs n = false`
fn carry_zero() -> T {
    let z = zw();
    let pred = |m: T| eqb(selm(m, &|w| carry_at(&z, &z, &w), ff()), ff());
    let hj = |w: T| {
        let p = fw(&w);
        rew(bool0(), carry(z.clone(), z.clone(), p.clone()), ff(), ap(v("$ih"), w),
            lm("t", bool0(), eqb(maj(ap(z.clone(), p.clone()), ap(z.clone(), p), v("t")), ff())), rfl(ff()))
    };
    let body = ind(&|n| eqb(carry(z.clone(), z.clone(), n), ff()), v("n"), &noop, &pred, &hj, rfl(ff()));
    K(ex(&lm("n", nw(), body)))
}
/// `Pi i. add zs zs i = false`
fn add_zero() -> T {
    let (z, i) = (zw(), v("i"));
    let body = rew(bool0(), carry(z.clone(), z.clone(), i.clone()), ff(), ap(carry_zero(), i.clone()),
        lm("t", bool0(), eqb(xor3(ap(z.clone(), i.clone()), ap(z.clone(), i), v("t")), ff())), rfl(ff()));
    K(ex(&lm("i", nw(), body)))
}

// stage 3
fn stmt_zero_mul(rhs: T) -> T {
    pi_("m", nw(), pi_("y", bw(), pi_("i", nw(), eqb(ap(mul(v("m"), zw(), v("y")), v("i")), rhs))))
}
fn proof_zero_mul() -> T {
    let (y, i, z) = (v("y"), v("i"), zw());
    let y0 = ap(y.clone(), zero_w());
    let a = tmask(z.clone(), y0);
    let m_at = |w: &T, yy: T| mul(fw(w), z.clone(), yy);
    let pred = |m: T| eqb(selm(m, &|w| ap(add(a.clone(), shl(m_at(&w, shr(y.clone())))), i.clone()), ff()), ff());
    let hj = |w: T| {
        let tail = m_at(&w, shr(y.clone()));
        // shl tail ~ zs, because the tail is false everywhere by the induction hypothesis
        let hc = lm("$q", nw(), ap2(ap(shl_false(), tail.clone()), ap(ap(v("$ih"), w.clone()), shr(y.clone())), v("$q")));
        let ha = lm("$q", nw(), rfl(ff()));
        let e = add_cong_at(a.clone(), z.clone(), shl(tail.clone()), z.clone(), ha, hc, i.clone());
        trans(ap(add(a.clone(), shl(tail)), i.clone()), ap(add(z.clone(), z.clone()), i.clone()), ff(), e, ap(add_zero(), i.clone()))
    };
    let body = ind(&|n| pi_("y", bw(), pi_("i", nw(), eqb(ap(mul(n, z.clone(), v("y")), v("i")), ff()))), v("m"),
        &|t| lm("y", bw(), lm("i", nw(), t)), &pred, &hj, rfl(ff()));
    lm("m", nw(), body)
}

// stage 4a: commutativity of the stream adder, real carries, goodness needed
fn good_stream(a: T) -> T {
    pi_("$i", nw(), ap(goodbool(), ap(a, v("$i"))))
}
fn stmt_add_comm(rhs: &dyn Fn(T, T) -> T) -> T {
    pi_("x", bw(), pi_("y", bw(), arr(good_stream(v("x")), arr(good_stream(v("y")),
        pi_("i", nw(), eqb(ap(add(v("x"), v("y")), v("i")), ap(rhs(v("x"), v("y")), v("i"))))))))
}
fn proof_add_comm() -> T {
    let (x, y) = (v("x"), v("y"));
    let pred = |m: T| eqb(selm(m.clone(), &|w| carry_at(&x, &y, &w), ff()), selm(m, &|w| carry_at(&y, &x, &w), ff()));
    let hj = |w: T| {
        let p = fw(&w);
        let r = carry(y.clone(), x.clone(), p.clone());
        let (xp, yp) = (ap(x.clone(), p.clone()), ap(y.clone(), p.clone()));
        let leaf = cases2(ap(v("gx"), p.clone()), ap(v("gy"), p.clone()), yp.clone(), bool0(),
            &|a, c| maj(a, c, r.clone()), &|a, c| maj(c, a, r.clone()));
        rew(bool0(), carry(x.clone(), y.clone(), p), r.clone(), ap(v("$ih"), w),
            lm("t", bool0(), eqb(maj(xp.clone(), yp.clone(), v("t")), maj(yp.clone(), xp.clone(), r.clone()))), leaf)
    };
    let ce = ind(&|n| eqb(carry(x.clone(), y.clone(), n.clone()), carry(y.clone(), x.clone(), n)), v("i"), &noop, &pred, &hj, rfl(ff()));
    let i = v("i");
    let r = carry(y.clone(), x.clone(), i.clone());
    let (xi, yi) = (ap(x.clone(), i.clone()), ap(y.clone(), i.clone()));
    let leaf = cases2(ap(v("gx"), i.clone()), ap(v("gy"), i.clone()), yi.clone(), bool0(),
        &|a, c| xor3(a, c, r.clone()), &|a, c| xor3(c, a, r.clone()));
    let fin = rew(bool0(), carry(x.clone(), y.clone(), i), r.clone(), ce,
        lm("t", bool0(), eqb(xor3(xi.clone(), yi.clone(), v("t")), xor3(yi, xi, r.clone()))), leaf);
    lm("x", bw(), lm("y", bw(), lm("gx", good_stream(x.clone()), lm("gy", good_stream(y.clone()), lm("i", nw(), fin)))))
}

// stage 4b: the shift law, with the multiplier's width, multiplicand and multiplier bits all symbolic
/// `Pi a c n. carry (shl a) (shl c) (succ n) = carry a c n`: the carry of the delayed operands is the carry, delayed.
fn carry_shl() -> T {
    let (a, c) = (v("a"), v("c"));
    let (sa, sc) = (shl(a.clone()), shl(c.clone()));
    let pred = |m: T| eqb(
        maj(selm(m.clone(), &|w| ap(a.clone(), fw(&w)), ff()), selm(m.clone(), &|w| ap(c.clone(), fw(&w)), ff()),
            selm(m.clone(), &|w| carry_at(&sa, &sc, &w), ff())),
        selm(m, &|w| carry_at(&a, &c, &w), ff()));
    let hj = |w: T| {
        let p = fw(&w);
        let (ap_, cp) = (ap(a.clone(), p.clone()), ap(c.clone(), p.clone()));
        let r = carry(a.clone(), c.clone(), p.clone());
        rew(bool0(), carry(sa.clone(), sc.clone(), succ_w(p)), r.clone(), ap(v("$ih"), w),
            lm("t", bool0(), eqb(maj(ap_.clone(), cp.clone(), v("t")), maj(ap_.clone(), cp.clone(), r.clone()))),
            rfl(maj(ap_.clone(), cp.clone(), r.clone())))
    };
    let body = ind(&|n| eqb(carry(sa.clone(), sc.clone(), succ_w(n.clone())), carry(a.clone(), c.clone(), n)), v("n"), &noop, &pred, &hj, rfl(ff()));
    K(ex(&lm("a", bw(), lm("c", bw(), lm("n", nw(), body)))))
}
/// `Pi a c n. shl (add a c) n = add (shl a) (shl c) n`
fn shl_add() -> T {
    let (a, c) = (v("a"), v("c"));
    let (sa, sc) = (shl(a.clone()), shl(c.clone()));
    let pred = |m: T| eqb(selm(m.clone(), &|w| ap(add(a.clone(), c.clone()), fw(&w)), ff()),
        xor3(selm(m.clone(), &|w| ap(a.clone(), fw(&w)), ff()), selm(m.clone(), &|w| ap(c.clone(), fw(&w)), ff()),
            selm(m, &|w| carry_at(&sa, &sc, &w), ff())));
    let hj = |w: T| {
        let p = fw(&w);
        let (ap_, cp) = (ap(a.clone(), p.clone()), ap(c.clone(), p.clone()));
        let r = carry(a.clone(), c.clone(), p.clone());
        rew(bool0(), carry(sa.clone(), sc.clone(), succ_w(p.clone())), r.clone(), ap3(carry_shl(), a.clone(), c.clone(), p),
            lm("t", bool0(), eqb(xor3(ap_.clone(), cp.clone(), r.clone()), xor3(ap_.clone(), cp.clone(), v("t")))),
            rfl(xor3(ap_.clone(), cp.clone(), r.clone())))
    };
    let body = ind(&|n| eqb(ap(shl(add(a.clone(), c.clone())), n.clone()), ap(add(sa.clone(), sc.clone()), n)), v("n"), &noop, &pred, &hj, rfl(ff()));
    K(ex(&lm("a", bw(), lm("c", bw(), lm("n", nw(), body)))))
}
/// `Pi x z n. tmask (shl x) z n = shl (tmask x z) n`
fn tmask_shl() -> T {
    let (x, z) = (v("x"), v("z"));
    let pred = |m: T| eqb(and2(selm(m.clone(), &|w| ap(x.clone(), fw(&w)), ff()), z.clone()),
        selm(m, &|w| and2(ap(x.clone(), fw(&w)), z.clone()), ff()));
    let hj = |w: T| rfl(and2(ap(x.clone(), fw(&w)), z.clone()));
    let body = ind(&|n| eqb(ap(tmask(shl(x.clone()), z.clone()), n.clone()), ap(shl(tmask(x.clone(), z.clone())), n)),
        v("n"), &noop, &pred, &hj, rfl(ff()));
    K(ex(&lm("x", bw(), lm("z", bool0(), lm("n", nw(), body)))))
}
fn stmt_mul_shl(fill: bool, rhs: &dyn Fn(T) -> T) -> T {
    let mf = |x: T| ap3(mul_fn(fill), v("m"), x, v("y"));
    pi_("m", nw(), pi_("x", bw(), pi_("y", bw(), pi_("i", nw(),
        eqb(ap(mf(ap(shl_fn(fill), v("x"))), v("i")), ap(rhs(mf(v("x"))), v("i")))))))
}
fn proof_mul_shl() -> T {
    let (x, y, i) = (v("x"), v("y"), v("i"));
    let y0 = ap(y.clone(), zero_w());
    let (a2, a) = (tmask(shl(x.clone()), y0.clone()), tmask(x.clone(), y0));
    let sy = shr(y.clone());
    let tail2 = |w: &T| mul(fw(w), shl(x.clone()), sy.clone());
    let tail = |w: &T| mul(fw(w), x.clone(), sy.clone());
    let pred = |m: T| {
        let lhs = selm(m.clone(), &|w| ap(add(a2.clone(), shl(tail2(&w))), i.clone()), ff());
        let stream = lm("$s", nw(), selm(m, &|w| ap(add(a.clone(), shl(tail(&w))), v("$s")), ff()));
        eqb(lhs, ap(shl(stream), i.clone()))
    };
    let hj = |w: T| {
        let (t2, t) = (tail2(&w), tail(&w));
        // the induction hypothesis at `shr y`: tail2 ~ shl tail
        let ih_at = lm("$q", nw(), ap3(ap(v("$ih"), w.clone()), x.clone(), sy.clone(), v("$q")));
        let hb = lm("$r", nw(), ap(ap3(shl_cong(), t2.clone(), shl(t.clone()), ih_at), v("$r")));
        let ha = lm("$r", nw(), ap3(tmask_shl(), x.clone(), ap(y.clone(), zero_w()), v("$r")));
        let (sa, sb) = (shl(a.clone()), shl(shl(t.clone())));
        let e1 = add_cong_at(a2.clone(), sa.clone(), shl(t2.clone()), sb.clone(), ha, hb, i.clone());
        let mid = ap(add(sa, sb), i.clone());
        let top = ap(shl(add(a.clone(), shl(t.clone()))), i.clone());
        let e2 = ap3(shl_add(), a.clone(), shl(t), i.clone());
        trans(ap(add(a2.clone(), shl(t2)), i.clone()), mid.clone(), top.clone(), e1, sym(top, mid, e2))
    };
    let hn = sym(ap(shl(zw()), i.clone()), ff(), ap2(ap(shl_false(), zw()), lm("$q", nw(), rfl(ff())), i.clone()));
    let body = ind(&|n| pi_("x", bw(), pi_("y", bw(), pi_("i", nw(),
            eqb(ap(mul(n.clone(), shl(v("x")), v("y")), v("i")), ap(shl(mul(n, v("x"), v("y"))), v("i")))))),
        v("m"), &|t| lm("x", bw(), lm("y", bw(), lm("i", nw(), t))), &pred, &hj, hn);
    lm("m", nw(), body)
}

// ---------- stage 1: the types ----------
#[test]
fn w_index_stage1_the_fold_types_with_no_level_raise() {
    for (name, t, sort) in [("unit", unit(), 1), ("empty", empty(), 1), ("tag", tag_ty(), 2), ("N", nw(), 2), ("Bits", bw(), 2)] {
        let ty = kernel::typecheck(&ex(&t)).unwrap_or_else(|e| panic!("{name}: {e}"));
        assert!(kernel::def_eq(&ty, &kernel::sort(sort)), "{name} is not in Sort{sort}");
    }
    let bb = arr(bw(), arr(bw(), bw()));
    for (name, t, want) in [("zero", zero_w(), nw()), ("one", num(1), nw()), ("add", add_fn(), bb.clone()),
        ("shl", shl_fn(false), arr(bw(), bw())), ("mul", mul_fn(false), arr(nw(), bb))] {
        let ty = kernel::typecheck(&ex(&t)).unwrap_or_else(|e| panic!("{name}: {}", e.chars().take(600).collect::<String>()));
        assert!(kernel::def_eq(&ty, &ex(&want)), "{name} has the wrong type");
    }
}

// ---------- stage 2: closed products compute ----------
fn product_bit_is(fill: bool, nb: usize, x: u128, y: u128, p: usize, want: T) -> bool {
    let prod = ap3(mul_fn(fill), num(nb), stream_of(x, nb), stream_of(y, nb));
    kernel::def_eq(&ex(&ap(prod, num(p))), &ex(&want))
}
#[test]
fn w_index_stage2_closed_products_compute() {
    let nb = 3;
    for (x, y) in [(5u128, 3u128), (7, 7), (6, 5), (3, 0), (0, 7), (7, 1), (4, 6), (1, 1)] {
        for p in 0..2 * nb + 2 {
            assert!(product_bit_is(false, nb, x, y, p, bit_of(x * y, p)), "{x} * {y}: bit {p}");
        }
    }
}
#[test]
fn w_index_stage2_the_fill_bit_mutant_computes_wrong_products() {
    let nb = 3;
    let wrong = [(5u128, 3u128), (7, 7), (3, 0), (1, 1)].iter().filter(|&&(x, y)| {
        (0..2 * nb + 2).any(|p| !product_bit_is(true, nb, x, y, p, bit_of(x * y, p)))
    }).count();
    assert_eq!(wrong, 4, "the mutant must miss every product");
}

// ---------- stages 3 and 4: laws at a symbolic position, count and operands ----------
#[test]
fn w_index_stage3_zero_times_y() {
    run("zero mul y = 0, m symbolic", &stmt_zero_mul(ff()), &proof_zero_mul()).unwrap();
    assert!(run("control: mul m zs y i = true", &stmt_zero_mul(tt()), &proof_zero_mul()).is_err());
}
#[test]
fn w_index_stage4a_add_commutes() {
    run("add x y = add y x", &stmt_add_comm(&|x, y| add(y, x)), &proof_add_comm()).unwrap();
    assert!(run("control: add x y = add y y", &stmt_add_comm(&|_, y| add(y.clone(), y)), &proof_add_comm()).is_err());
}
#[test]
fn w_index_stage4b_the_shift_law() {
    run("mul m (shl x) y = shl (mul m x y)", &stmt_mul_shl(false, &shl), &proof_mul_shl()).unwrap();
    assert!(run("control: mul m (shl x) y = mul m x y", &stmt_mul_shl(false, &noop), &proof_mul_shl()).is_err());
    let filled = |t: T| ap(shl_fn(true), t);
    assert!(run("control: the fill-bit mutant", &stmt_mul_shl(true, &filled), &proof_mul_shl()).is_err());
}
/// The symbolic theorem, read at closed numbers, says what the product says: its two sides reduce to bit `p` of `2xy`.
#[test]
fn w_index_stage4b_instantiates_to_true_products() {
    let nb = 3;
    for (x, y) in [(5u128, 3u128), (7, 7), (6, 5), (3, 0)] {
        for p in 0..2 * nb + 3 {
            let at = ap(ap3(proof_mul_shl(), num(nb), stream_of(x, nb), stream_of(y, nb)), num(p));
            let bit = bit_of(2 * x * y, p);
            kernel::check(&Ctx::new(), &ex(&at), &ex(&eqb(bit.clone(), bit))).unwrap_or_else(|e| panic!("{x} {y} bit {p}: {}", e.chars().take(300).collect::<String>()));
            let flip = if (2 * x * y >> p) & 1 == 1 { ff() } else { tt() };
            assert!(kernel::check(&Ctx::new(), &ex(&at), &ex(&eqb(flip.clone(), flip))).is_err(), "{x} {y} bit {p}: the wrong bit passed");
        }
    }
}
