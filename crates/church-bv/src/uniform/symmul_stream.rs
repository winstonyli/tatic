// Spike (2026-11-01, task a1; builds on `mul.rs`, `shift.rs`): the stream form of `mul 1 y = y` with a SYMBOLIC
// multiplier, UNIFORM IN THE POSITION, a standalone result: it is NOT bridged to `Bv_n` (the bridge of `mul 1 y = y` is the
// stage-wise one of `symmul.rs`, which does not use this theorem; it shares only `hyps_c` and `hyps_x`).
// For the multiplier bits `a_0..a_(n-1)` (variables with `GoodBool` witnesses `ga_m`, as the `GoodBv` step binds them) and the
// one-hot multiplicand `e_0`, the theorem is
//     Pi i:Nat_(K0+n). Good i -> Id(Bool0, acc_n i, look(a_0..a_(n-1)) (lower i))
// where `look(t) p = t Bool0 (p (Bool^n -> Bool0) proj0 rot)` is the lookup of `width.rs` (tuple `t` read at the Nat_1
// position `p`, false past the end) and `lower` is the chain of `embed`s down to Nat_1. It is proved for EVERY good position,
// with no per-position case tree. The older positionwise route (the proof a tree over the positions, at numerals) and the bridge of
// this theorem to `Bv_n` are gone; their measurements are in `docs/tier-cycle/` ("Laws uniform in the width").
//
// Cost, as measured by the ignored `symmul_uniform_stage_scaling` (per-stage check times, no bridge): the stream theorem H_n checks
// in 7.4, 9.2, 18.7 ms for n = 4, 6, 8. Sizes count DISTINCT nodes, i.e. they hold only because the kernel shares subterms (the
// stages are handles): H_n has 1821, 2858, 3986, 5233, 6554 distinct nodes for n = 2..6 (about quadratic), but its fully unfolded
// tree is 1.9e6, 1.5e7, 1.1e8, 8.1e8, 5.6e9 nodes, about 7-8x per bit. Anything that unfolds the term (printing it, a checker
// without sharing) sees the exponential size.
//
// Pieces (all closed terms, shared by the later stages as handles; the per-stage terms are O(n) in distinct nodes, O(n^2) over all stages):
//   * `acc_sym`: the stream accumulator of `mul.rs` with the multiplier bits as arguments of a closed term.
//   * `Z0`:  look(0..0) p = false (an induction whose step is the identity: the shifted zero tuple is the zero tuple).
//   * `D`:   a pointwise lemma for the lookup. For `f(u, w)` with `f(ff, ff) = ff` (hypothesis `hp`) and tuples `a, c, r` with
//            `f(a_m, c_m) = r_m` for each m < n:  f(look a p, look c p) = look r p at every good p (or `= ff` when `f(a_m, c_m) = ff`).
//            The induction on p generalises over the tuples (the motive is a Pi over 3n bit variables and n equalities, Sort1,
//            which fits the Good_1 motive); the step is the lookup's own shift: look(t)(succ p) is look(t_1..t_(n-1), ff)(p) by
//            computation, and `hp` closes the padding hypothesis. Two instances: the carry `maj(u, b & w, ff)` stays false
//            (`Dc`, no r), and the sum bit `xor(xor(u, b & w), ff)` is the lookup of the new tuple (`Dx`).
//   * `Psh`: the stream shift transports a lookup: if `x i = look(c)(lower i)` at good i then `shl x M = look(shr c)(lower M)` at
//            good M, with `shr c = (ff, c_0..c_(n-2))` (needs `c_(n-1) = ff`). A joint induction on the shift's fold, the state
//            equality `SH M = (embed M, look(shr c)(lower M))` together with `Good (embed M)` (as the carry lemmas of
//            `mul.rs`), so the step may use the hypothesis at `embed M`.
//   * stage `H_j`: `acc_j i = look(A_j)(lower i)` at good i, `A_j = (a_0..a_(j-1), ff..ff)`. The step is the carry lemma
//            `carry_false` of `mul.rs` (its `to_false` from `Dc`), then the sum bit from `Dx`. Each stage's hypotheses of
//            D are n constant-size proofs (case splits on the witnesses of a_m and a_j), so the stage is O(n).
// The multiplicand is the stream `e_0 := look(1,0,..,0)`, convertible at every numeral to the old `i Bool0 tt (\_. ff)` (a lemma
// `i Bool0 tt (\_. ff) = look(1,0,..)(i)` would need `Z0` inside an induction step that has no goodness of `m`).
use super::mul::*;
use super::width::T::*;
use super::width::*;
use tatic_kernel::{self as kernel, Expr};

/// The level of the streams' index at stage 0. `x = e_0` reads `Bool0` out of `Nat_1`, so k0 = 1 is enough.
const K0: u32 = 1;

/// A leaked `&'static str` name `<p><i>` (the binder names the term builder wants).
fn nm(p: &str, i: usize) -> &'static str {
    Box::leak(format!("{p}{i}").into_boxed_str())
}
/// The multiplier bit variable `a_j`.
pub(crate) fn yv(j: usize) -> T {
    v(AN(j))
}
pub(crate) fn apn(f: T, args: &[T]) -> T {
    args.iter().fold(f, |f, a| ap(f, a.clone()))
}

// ---------- the stream accumulator with the multiplier bits as arguments ----------
/// `acc_sym(j) : Bool0^j -> Bits(K0) -> Bits(K0 + j)`, CLOSED: `\y_0..y_(j-1). \x. acc_j` (the shift's fill bit is `fill`): the
/// stream accumulator of `mul.rs` with the multiplier bits as ARGUMENTS of a closed term, so it can be applied to the
/// variables `a_j` and still be shared (a meta-level tree over `a_j` is 3^j in size, the reason `acc_fn` is closed).
fn acc_sym(j: usize, fill: bool) -> Expr {
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
/// `acc_j` applied to the multiplier bits `ys` and the multiplicand `x`: a stream in `Bits(K0 + j)`.
fn big_a(acc: &[Expr], j: usize, ys: &[T], x: &T) -> T {
    ap(apn(K(acc[j]), &ys[..j]), x.clone())
}

// ---------- tuples (meta-level lists of n bits) ----------
fn zeros(n: usize) -> Vec<T> {
    vec![ff(); n]
}
/// `A_s = (a_0, .., a_(s-1), ff, .., ff)`
fn a_tuple(n: usize, s: usize) -> Vec<T> {
    (0..n).map(|m| if m < s { yv(m) } else { ff() }).collect()
}
/// the one-hot tuple, `tt` at index s
fn oh(n: usize, s: usize) -> Vec<T> {
    (0..n).map(|m| if m == s { tt() } else { ff() }).collect()
}
/// `(ff, c_0, .., c_(n-2))`
fn shr(c: &[T]) -> Vec<T> {
    let mut r = vec![ff()];
    r.extend_from_slice(&c[..c.len() - 1]);
    r
}
/// the tuple `t` read at the Nat_1 position `p`
fn look(n: usize, t: &[T], p: T) -> T {
    ap2(lookup(n), tuple(t), p)
}
/// `t : Nat_k` lowered to Nat_K0
fn low(k: u32, t: T) -> T {
    lower(K0, (k - K0) as usize, t)
}
/// `g : Good_k t` gives `Good_K0 (low t)`.
fn low_good(k: u32, t: T, g: T) -> T {
    let (mut t, mut g) = (t, g);
    for l in (K0..k).rev() {
        g = ap2(K(ex(&ge_proof(l))), t.clone(), g);
        t = embed(l, t);
    }
    g
}

// ---------- Z0 ----------
fn z0_stmt(n: usize) -> T {
    pi_("i", nat(K0), arr(gk(K0, v("i")), idt(bool0(), look(n, &zeros(n), v("i")), ff())))
}
fn z0_proof(n: usize) -> T {
    let pm = |m: T| idt(bool0(), look(n, &zeros(n), m), ff());
    lm("i", nat(K0), lm("g", gk(K0, v("i")),
        ap3(v("g"), lm("M", nat(K0), pm(v("M"))), rfl(ff()), lm("m", nat(K0), lm("ih", pm(v("m")), v("ih"))))))
}

// ---------- D: the pointwise lookup lemma ----------
/// `(statement, proof)` of `Pi b hp p. Good p -> Pi da dc [dr] dh. f(look da p, look dc p) = look dr p` (`= ff` without r).
fn d_lemma(n: usize, f: &dyn Fn(T, T) -> T, with_r: bool) -> (T, T) {
    let da: Vec<T> = (0..n).map(|i| v(nm("da", i))).collect();
    let dc: Vec<T> = (0..n).map(|i| v(nm("dc", i))).collect();
    let dr: Vec<T> = (0..n).map(|i| v(nm("dr", i))).collect();
    let rhs = |m: usize| if with_r { dr[m].clone() } else { ff() };
    let concl = |p: T| {
        idt(bool0(), f(look(n, &da, p.clone()), look(n, &dc, p.clone())), if with_r { look(n, &dr, p) } else { ff() })
    };
    let pt = |p: T| {
        let mut t = concl(p);
        for m in (0..n).rev() {
            t = pi_(nm("dh", m), idt(bool0(), f(da[m].clone(), dc[m].clone()), rhs(m)), t);
        }
        if with_r {
            for m in (0..n).rev() {
                t = pi_(nm("dr", m), bool0(), t);
            }
        }
        for m in (0..n).rev() {
            t = pi_(nm("dc", m), bool0(), t);
        }
        for m in (0..n).rev() {
            t = pi_(nm("da", m), bool0(), t);
        }
        t
    };
    let hp_ty = idt(bool0(), f(ff(), ff()), ff());
    let stmt = pi_("b", bool0(), pi_("hp", hp_ty.clone(), pi_("p", nat(K0), arr(gk(K0, v("p")), pt(v("p"))))));
    // the proof: lambdas over the same binders
    let lam_all = |body: T| {
        let mut t = body;
        for m in (0..n).rev() {
            t = lm(nm("dh", m), idt(bool0(), f(da[m].clone(), dc[m].clone()), rhs(m)), t);
        }
        if with_r {
            for m in (0..n).rev() {
                t = lm(nm("dr", m), bool0(), t);
            }
        }
        for m in (0..n).rev() {
            t = lm(nm("dc", m), bool0(), t);
        }
        for m in (0..n).rev() {
            t = lm(nm("da", m), bool0(), t);
        }
        t
    };
    let base = lam_all(v(nm("dh", 0)));
    // the step: instantiate the hypothesis at the shifted tuples
    let mut args: Vec<T> = vec![];
    args.extend((1..n).map(|m| da[m].clone()));
    args.push(ff());
    args.extend((1..n).map(|m| dc[m].clone()));
    args.push(ff());
    if with_r {
        args.extend((1..n).map(|m| dr[m].clone()));
        args.push(ff());
    }
    args.extend((1..n).map(|m| v(nm("dh", m))));
    args.push(v("hp"));
    let step = lm("m", nat(K0), lm("ih", pt(v("m")), lam_all(apn(v("ih"), &args))));
    let pn = ap3(v("g"), lm("M", nat(K0), pt(v("M"))), base, step);
    let proof = lm("b", bool0(), lm("hp", hp_ty, lm("p", nat(K0), lm("g", gk(K0, v("p")), pn))));
    (stmt, proof)
}
fn f_x(u: T, w: T) -> T {
    xor(xor(u, and2(v("b"), w)), ff())
}
fn f_c(u: T, w: T) -> T {
    maj(u, and2(v("b"), w), ff())
}
/// applying a D lemma: `lem b hp p gp a.. c.. [r..] hyps..`
fn d_app(lem: Expr, b: T, hp: T, p: T, gp: T, a: &[T], c: &[T], r: Option<&[T]>, hyps: Vec<T>) -> T {
    let mut args = vec![b, hp, p, gp];
    args.extend_from_slice(a);
    args.extend_from_slice(c);
    if let Some(r) = r {
        args.extend_from_slice(r);
    }
    args.extend(hyps);
    apn(K(lem), &args)
}

// ---------- Psh: the shift transports a lookup ----------
fn psh(n: usize, k: u32, c: &[T], fill: bool) -> (T, T) {
    let cp = shr(c);
    let sh_m = |m: T| shl_state(k, v("x"), fill, m);
    let tgt = |m: T| pair_s(embed(k, m.clone()), look(n, &cp, low(k + 1, m)));
    let eq_ty = |m: T| idt(state(k), sh_m(m.clone()), tgt(m));
    let gty = |m: T| gk(k, embed(k, m));
    let pmf = |m: T| sig2(gty(m.clone()), eq_ty(m));
    let hx_ty = pi_("i", nat(k), arr(gk(k, v("i")), idt(bool0(), ap(v("x"), v("i")), look(n, c, low(k, v("i"))))));
    let stmt = pi_("x", bits(k), pi_("hx", hx_ty.clone(), pi_("M", nat(k + 1), arr(ap(good1(k), v("M")),
        idt(bool0(), ap(shl_fill(k, v("x"), fill), v("M")), look(n, &cp, low(k + 1, v("M"))))))));
    let em = embed(k, v("m"));
    let ge_m = pr1(gty(v("m")), eq_ty(v("m")), v("ih"));
    let eq_m = pr2(gty(v("m")), eq_ty(v("m")), v("ih"));
    let sm = ap(succ(k + 1), v("m"));
    let hx_em = ap2(v("hx"), em.clone(), ge_m.clone());
    let h = rew(bool0(), ap(v("x"), em.clone()), look(n, c, low(k, em.clone())), hx_em,
        lm("b", bool0(), idt(state(k), pair_s(ap(succ(k), em.clone()), v("b")), tgt(sm.clone()))), rfl(tgt(sm.clone())));
    let eq_new = rew(state(k), sh_m(v("m")), tgt(v("m")), eq_m,
        lm("t", state(k), idt(state(k), ap(shl_step(k, v("x")), v("t")), tgt(sm.clone()))), h);
    let step_ = lm("m", nat(k + 1), lm("ih", pmf(v("m")),
        mk2(gty(sm.clone()), eq_ty(sm.clone()), gsucc(k, em, ge_m), eq_new)));
    let z = zero(k + 1);
    let base = mk2(gty(z.clone()), eq_ty(z), gzero(k), rfl(pair_s(zero(k), if fill { tt() } else { ff() })));
    let pn = ap3(v("g"), lm("M", nat(k + 1), pmf(v("M"))), base, step_);
    let target = look(n, &cp, low(k + 1, v("M")));
    let fin = rew(state(k), sh_m(v("M")), tgt(v("M")), pr2(gty(v("M")), eq_ty(v("M")), pn),
        lm("t", state(k), idt(bool0(), snd(k, v("t")), target.clone())), rfl(target));
    let proof = lm("x", bits(k), lm("hx", hx_ty, lm("M", nat(k + 1), lm("g", ap(good1(k), v("M")), fin))));
    (stmt, proof)
}

// ---------- the stages ----------
/// The one-hot multiplicand stream `e_0 = look(1, 0, .., 0)` in `Bits(K0)`.
fn x_stream(n: usize) -> T {
    lm("i", nat(K0), look(n, &oh(n, 0), v("i")))
}
struct Cx {
    n: usize,
    x: Expr,
    acc: Vec<Expr>,
    /// `ssh[s] = x << s` as a closed stream in `Bits(K0 + s)`
    ssh: Vec<Expr>,
    /// `hx[s] : Pi i:Nat_(K0+s). Good i -> (x << s) i = look(oh_s)(low i)`
    hx: Vec<Expr>,
    /// `h[j]`: the stage theorem, closed over the bits and witnesses
    h: Vec<Expr>,
    dx: Expr,
    dc: Expr,
}
fn all_args(n: usize) -> Vec<T> {
    (0..n).map(yv).chain((0..n).map(|m| v(GN(m)))).collect()
}
fn build(n: usize, fill: bool, stages: usize) -> Cx {
    let x = ex(&x_stream(n));
    let acc: Vec<Expr> = (0..=n).map(|j| acc_sym(j, fill)).collect();
    let ssh: Vec<Expr> = (0..n).map(|s| ex(&shl_n(K0, s, K(x), fill))).collect();
    let mut hx: Vec<Expr> = vec![ex(&lm("i", nat(K0), lm("g", gk(K0, v("i")), rfl(look(n, &oh(n, 0), v("i"))))))];
    for s in 0..n.saturating_sub(1) {
        let k = K0 + s as u32;
        let pe = K(ex(&psh(n, k, &oh(n, s), fill).1));
        let hxs = K(hx[s]);
        let sx = K(ssh[s]);
        hx.push(ex(&lm("M", nat(k + 1), lm("g", ap(good1(k), v("M")), apn(pe, &[sx, hxs, v("M"), v("g")])))));
    }
    let dx = ex(&d_lemma(n, &f_x, true).1);
    let dc = ex(&d_lemma(n, &f_c, false).1);
    let z0 = K(ex(&z0_proof(n)));
    // H_0: acc_0 i = ff = look(zeros) i
    let h0 = ex(&lam_bits(XN, n, lm("i", nat(K0), lm("g", gk(K0, v("i")),
        rew(bool0(), look(n, &zeros(n), v("i")), ff(), ap2(z0, v("i"), v("g")),
            lm("b", bool0(), idt(bool0(), ff(), v("b"))), rfl(ff()))))));
    let mut cx = Cx { n, x, acc, ssh, hx, h: vec![h0], dx, dc };
    for s in 0..stages.min(n) {
        let hs = stage(&cx, s);
        cx.h.push(hs);
    }
    cx
}
/// the hypotheses of `Dc` / `Dx` at stage s (multiplier bit s), as proofs
pub(crate) fn hyps_c(n: usize, s: usize) -> Vec<T> {
    (0..n)
        .map(|m| {
            if m < s {
                cases2(v(GN(m)), v(GN(s)), yv(s), bool0(), &|a, c| maj(a, and2(c, ff()), ff()), &|_, _| ff())
            } else {
                rfl(ff())
            }
        })
        .collect()
}
pub(crate) fn hyps_x(n: usize, s: usize) -> Vec<T> {
    (0..n)
        .map(|m| {
            if m < s {
                cases2(v(GN(m)), v(GN(s)), yv(s), bool0(), &|a, c| xor(xor(a, and2(c, ff())), ff()), &|a, _| a)
            } else if m == s {
                cases1(v(GN(s)), &|bb| xor(xor(ff(), and2(bb, tt())), ff()), &|bb| bb)
            } else {
                cases1(v(GN(s)), &|bb| xor(xor(ff(), and2(bb, ff())), ff()), &|_| ff())
            }
        })
        .collect()
}
/// stage s: from `H_s` to `H_(s+1)`.
fn stage(cx: &Cx, s: usize) -> Expr {
    let n = cx.n;
    let kj = K0 + s as u32;
    let ys: Vec<T> = (0..n).map(yv).collect();
    let su = big_a(&cx.acc, s, &ys, &K(cx.x));
    let sv = tm(kj, yv(s), K(cx.ssh[s]));
    let (as_, os, an) = (a_tuple(n, s), oh(n, s), a_tuple(n, s + 1));
    let ih = |e: T, ge: T| ap2(apn(K(cx.h[s]), &all_args(n)), e, ge);
    let hxs = |e: T, ge: T| ap2(K(cx.hx[s]), e, ge);
    let la = |e: T| look(n, &as_, low(kj, e));
    let cc = |e: T| and2(yv(s), look(n, &os, low(kj, e)));
    // sv e = y_s & (x << s) e  =  y_s & look(oh_s)(low e)
    let ht = |e: T, ge: T| {
        rew(bool0(), ap(K(cx.ssh[s]), e.clone()), look(n, &os, low(kj, e.clone())), hxs(e.clone(), ge),
            lm("b", bool0(), idt(bool0(), and2(yv(s), v("b")), cc(e.clone()))), rfl(cc(e)))
    };
    let hp_c = rfl(ff());
    let hp_x = cases1(v(GN(s)), &|bb| xor(xor(ff(), and2(bb, ff())), ff()), &|_| ff());
    let to_false = |e: T, ge: T| {
        let dcp = d_app(cx.dc, yv(s), hp_c.clone(), low(kj, e.clone()), low_good(kj, e.clone(), ge.clone()), &as_, &os, None, hyps_c(n, s));
        rew(bool0(), ap(su.clone(), e.clone()), la(e.clone()), ih(e.clone(), ge.clone()),
            lm("b", bool0(), idt(bool0(), maj(v("b"), ap(sv.clone(), e.clone()), ff()), ff())),
            rew(bool0(), ap(sv.clone(), e.clone()), cc(e.clone()), ht(e.clone(), ge),
                lm("b", bool0(), idt(bool0(), maj(la(e.clone()), v("b"), ff()), ff())), dcp))
    };
    let pn = carry_false(kj, &su, &sv, &to_false);
    let stn = st(kj, maj, su.clone(), sv.clone(), v("N"));
    let target = pair_s(embed(kj, v("N")), ff());
    let eq_ty = idt(state(kj), stn.clone(), target.clone());
    let gty = gk(kj, embed(kj, v("N")));
    let (eq_n, ge_n) = (pr2(gty.clone(), eq_ty.clone(), pn.clone()), pr1(gty, eq_ty, pn));
    let en = embed(kj, v("N"));
    let r = look(n, &an, low(kj, en.clone()));
    let dxp = d_app(cx.dx, yv(s), hp_x, low(kj, en.clone()), low_good(kj, en.clone(), ge_n.clone()), &as_, &os, Some(&an), hyps_x(n, s));
    let leaf = rew(bool0(), ap(su.clone(), en.clone()), la(en.clone()), ih(en.clone(), ge_n.clone()),
        lm("b", bool0(), idt(bool0(), xor(xor(v("b"), ap(sv.clone(), en.clone())), ff()), r.clone())),
        rew(bool0(), ap(sv.clone(), en.clone()), cc(en.clone()), ht(en.clone(), ge_n),
            lm("b", bool0(), idt(bool0(), xor(xor(la(en.clone()), v("b")), ff()), r.clone())), dxp));
    let fin = rew(state(kj), stn, target, eq_n,
        lm("t", state(kj), idt(bool0(), sumfn(kj, su.clone(), sv.clone(), v("t")), r)), leaf);
    ex(&lam_bits(XN, n, lm("N", nat(kj + 1), lm("g", ap(good1(kj), v("N")), fin))))
}
/// `Pi a.. ga.. . Pi i:Nat_(K0+j). Good i -> Id(Bool0, acc_j i, look(A_j)(low i))`
fn h_stmt(n: usize, j: usize, fill: bool) -> Expr {
    let kj = K0 + j as u32;
    let ys: Vec<T> = (0..n).map(yv).collect();
    let acc: Vec<Expr> = (0..=n).map(|j| acc_sym(j, fill)).collect();
    let x = ex(&x_stream(n));
    let mut t = pi_("i", nat(kj), arr(gk(kj, v("i")),
        idt(bool0(), ap(big_a(&acc, j, &ys, &K(x)), v("i")), look(n, &a_tuple(n, j), low(kj, v("i"))))));
    for m in (0..n).rev() {
        t = pi_(GN(m), ap(goodbool(), yv(m)), t);
    }
    for m in (0..n).rev() {
        t = pi_(AN(m), bool0(), t);
    }
    ex(&t)
}

// ---------- tests ----------
fn chk(name: &str, pf: &Expr, stmt: &Expr) {
    let (r, ms) = timed_check(pf, stmt);
    println!("[{name}] {} in {ms:.2} ms", if r.is_ok() { "ACCEPTED" } else { "REJECTED" });
    r.unwrap_or_else(|m| panic!("{name}: {}", m.chars().take(1200).collect::<String>()));
}

#[test]
fn the_symbolic_accumulator_is_well_typed_and_multiplies() {
    for j in 0..=4usize {
        let f = acc_sym(j, false);
        let ty = kernel::typecheck(&f).unwrap_or_else(|m| panic!("acc_sym({j}): {m}"));
        let want = (0..j).rev().fold(arr(bits(K0), bits(K0 + j as u32)), |t, _| arr(bool0(), t));
        assert!(kernel::def_eq(&ty, &ex(&want)), "acc_sym({j}) has the wrong type");
    }
    // with literal multiplier bits it is the product of the one-hot stream 1 (`i -> i Bool0 tt (\_. ff)`) and y: bit p of y
    // (p < m), zero above
    let x_one = lm("i", nat(K0), ap3(v("i"), bool0(), tt(), lm("_", bool0(), ff())));
    let m = 4usize;
    for yval in 0..(1u128 << m) {
        let prod = ap(apn(K(acc_sym(m, false)), &ybits(m, yval)), K(ex(&x_one)));
        for p in 0..m + 2 {
            let got = ex(&ap(prod.clone(), numeral(K0 + m as u32, p)));
            assert!(kernel::def_eq(&got, &ex(&bit_of(yval, p))), "1 * {yval}: bit {p}");
        }
    }
}

#[test]
fn z0_and_the_pointwise_lookup_lemmas_check() {
    for n in 1..=5usize {
        chk(&format!("Z0 n={n}"), &ex(&z0_proof(n)), &ex(&z0_stmt(n)));
        let (s, p) = d_lemma(n, &f_x, true);
        chk(&format!("Dx n={n}"), &ex(&p), &ex(&s));
        let (s, p) = d_lemma(n, &f_c, false);
        chk(&format!("Dc n={n}"), &ex(&p), &ex(&s));
    }
}

#[test]
fn the_shift_transports_a_lookup_at_every_level() {
    let n = 3usize;
    for k in 1..=4u32 {
        for s in 0..n - 1 {
            let (stmt, pf) = psh(n, k, &oh(n, s), false);
            chk(&format!("Psh n={n} k={k} c=oh_{s}"), &ex(&pf), &ex(&stmt));
        }
    }
}

#[test]
fn the_stream_theorem_holds_at_every_good_position() {
    for n in 1..=4usize {
        let cx = build(n, false, n);
        for j in 0..=n {
            chk(&format!("H_{j} n={n}"), &cx.h[j], &h_stmt(n, j, false));
        }
    }
}

/// Per-stage check times of the stream theorem alone. Run by exact name; `SYMMUL_NS=4,6,8` picks the widths.
#[test]
#[ignore]
fn symmul_uniform_stage_scaling() {
    let ns: Vec<usize> = crate::job::Setup::process().var("SYMMUL_NS")
        .map(|s| s.split(',').filter_map(|t| t.parse().ok()).collect())
        .unwrap_or_else(|| vec![4]);
    for n in ns {
        let cx = build(n, false, n);
        let line: Vec<String> = (0..=n).map(|j| format!("H_{j} {:.2}", timed_check(&cx.h[j], &h_stmt(n, j, false)).1)).collect();
        println!("SYMMUL_UNIFORM_STAGES n={n}: {}", line.join(", "));
    }
}

/// The shift's fill bit flipped, at the lemma level: the shift transports a lookup (`Psh`) only for the real fill bit `false`,
/// because its base case is the state `(zero, fill)`; with `fill = true` the lemma no longer checks.
#[test]
fn psh_rejects_the_shifts_fill_bit_mutation() {
    let (stmt, pf) = psh(3, 1, &oh(3, 0), true);
    let (r, _) = timed_check(&ex(&pf), &ex(&stmt));
    let m = r.expect_err("Psh with fill=true was accepted");
    println!("[stream mutant] Psh with the stream shift's fill=true: REJECTED: {}", m.chars().take(140).collect::<String>());
    // control: the same lemma with the real fill bit is accepted
    let (stmt, pf) = psh(3, 1, &oh(3, 0), false);
    chk("Psh n=3 k=1 fill=false", &ex(&pf), &ex(&stmt));
}

/// The header's cost claim is the measured one: the stream theorem's distinct nodes (shared handles) grow about quadratically
/// over the stages and its fully unfolded tree is larger.
#[test]
fn header_states_what_the_size_claims_depend_on() {
    let sizes: Vec<(usize, u128)> = (2..=6usize).map(|n| kernel::term_sizes(&build(n, false, n).h[n])).collect();
    println!("[stream sizes] (distinct, unfolded) of H_n for n=2..6: {sizes:?}");
    for w in sizes.windows(2) {
        assert!(w[1].0 < w[0].0 * 2, "distinct nodes grew by 2x or more in one bit: {sizes:?}");
        assert!(w[1].1 > w[0].1 * 4, "unfolded size grew by less than 4x in one bit: {sizes:?}");
    }
    let src = include_str!("symmul_stream.rs");
    let header: String = src.lines().take_while(|l| l.starts_with("//")).collect::<Vec<_>>().join("\n");
    for phrase in ["distinct nodes", "NOT bridged", "docs/tier-cycle/", "7.4, 9.2, 18.7 ms"] {
        assert!(header.contains(phrase), "the header must say: {phrase}");
    }
}
