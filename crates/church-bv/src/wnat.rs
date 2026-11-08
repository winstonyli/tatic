// Spike (2026-11-07, o1): is the level wall of `mul.rs#a_single_nested_fold_is_ill_typed` a property of the kernel, or only of
// Church numerals? The stream adder raises its level because a Church `Nat_k` folds only into `Sort k`, so a fold whose state is
// a stream has no fixed point. `wrec`'s motive is unrestricted, so an index built as a W-type can fold into its own stream type.
//
// The index. A bare Church tag gives a `wrec` step no way to use `f : B(a) -> N`, since a Church bool has no dependent case; the
// tag therefore carries its own witness:
//   Maybe X := Pi C:Sort1. (X -> C) -> C -> C                                  : Sort2
//   Tag     := Sigma X:Sort1. Sigma m:Maybe X. GoodMaybe X m                   : Sort2
//   N       := wty(Tag, \t. fst t)                                             : Sort2
//   Bits    := N -> Bool0                                                      : Sort2
// so `add : Bits -> Bits -> Bits` raises no level, and a multiplier fold is one `wrec`. `Empty` and `Unit` are derived (`empty` is
// `wty(unit, \_. unit)`), so no postulate enters. The position is the tree itself: no position in the state, no `embed`.
//
// The tree is not canonical: `nothing` under an inhabited `X` is a second zero, and `X` may branch, so `succ` is not injective
// and there is no general induction `Pi Q. Q zero -> .. -> Pi n. Q n`. A proof splits a tag only through `GoodMaybe`, whose motive
// sits in `Sort1` and sees `m` but not its witness, so `ind` below takes the statement in reduced form, with the tag's `m`
// abstracted. That covers exactly the statements that read a tree through its tag, which is all a stream function can do.
//
// Terms are kernel terms built through `Cx`: a binder hands its variable to the body as an `At`, and no index is written by hand.
use crate::encoding::*;
use tatic_kernel::*;

// ---------- the index ----------
fn unit() -> Expr {
    constant(|| id(bool0(), t(), t()))
}
fn star() -> Expr {
    constant(|| refl(t()))
}
fn empty() -> Expr {
    constant(|| wty(unit(), Cx::default().under(|_, _| unit())))
}
fn maybe(cx: &mut Cx, x: Expr) -> Expr {
    let x = cx.mark(x);
    cx.pi(sort(1), |cx, c| {
        let c = cx.at(c);
        arrow(arrow(cx.at(x), c), arrow(c, c))
    })
}
fn just(cx: &mut Cx, x: Expr, a: Expr) -> Expr {
    let (x, a) = (cx.mark(x), cx.mark(a));
    cx.lam(sort(1), |cx, c| cx.lam(arrow(cx.at(x), cx.at(c)), |cx, j| cx.lam(cx.at(c), |cx, _| app(cx.at(j), cx.at(a)))))
}
fn nothing(cx: &mut Cx, x: Expr) -> Expr {
    let x = cx.mark(x);
    cx.lam(sort(1), |cx, c| cx.lam(arrow(cx.at(x), cx.at(c)), |cx, _| cx.lam(cx.at(c), |cx, e| cx.at(e))))
}
fn goodmaybe(cx: &mut Cx, x: Expr, m: Expr) -> Expr {
    let (x, m) = (cx.mark(x), cx.mark(m));
    let mx = maybe(cx, cx.at(x));
    cx.pi(arrow(mx, sort(1)), |cx, p| {
        let hj = cx.pi(cx.at(x), |cx, a| app(cx.at(p), just(cx, cx.at(x), cx.at(a))));
        cx.pi(hj, |cx, _| {
            let hn = app(cx.at(p), nothing(cx, cx.at(x)));
            cx.pi(hn, |cx, _| app(cx.at(p), cx.at(m)))
        })
    })
}
fn tag_inner(cx: &mut Cx, x: Expr) -> Expr {
    let x = cx.mark(x);
    sigma(maybe(cx, cx.at(x)), cx.under(|cx, m| goodmaybe(cx, cx.at(x), cx.at(m))))
}
fn tag_ty() -> Expr {
    constant(|| sigma(sort(1), Cx::default().under(|cx, x| tag_inner(cx, cx.at(x)))))
}
fn tag_mk(cx: &mut Cx, x: Expr, m: Expr, g: Expr) -> Expr {
    let xa = cx.mark(x);
    let fam = cx.under(|cx, x| tag_inner(cx, cx.at(x)));
    let inner = cx.under(|cx, m| goodmaybe(cx, cx.at(xa), cx.at(m)));
    pair(fam, x, pair(inner, m, g))
}
fn tag_x(t: Expr) -> Expr {
    let motive = constant(|| lam(tag_ty(), sort(1)));
    let step = constant(|| Cx::default().lam(sort(1), |cx, x| {
        let ti = tag_inner(cx, cx.at(x));
        cx.lam(ti, |cx, _| cx.at(x))
    }));
    sigrec(motive, step, t)
}
fn tag_m(t: Expr) -> Expr {
    let motive = constant(|| Cx::default().lam(tag_ty(), |cx, t| maybe(cx, tag_x(cx.at(t)))));
    let step = constant(|| Cx::default().lam(sort(1), |cx, x| {
        let ti = tag_inner(cx, cx.at(x));
        cx.lam(ti, |cx, r| {
            let ti = tag_inner(cx, cx.at(x));
            let motive = cx.lam(ti, |cx, _| maybe(cx, cx.at(x)));
            let mx = maybe(cx, cx.at(x));
            let step = cx.lam(mx, |cx, m| {
                let gm = goodmaybe(cx, cx.at(x), cx.at(m));
                cx.lam(gm, |cx, _| cx.at(m))
            });
            sigrec(motive, step, cx.at(r))
        })
    }));
    sigrec(motive, step, t)
}
pub(super) fn nw() -> Expr {
    constant(|| wty(tag_ty(), Cx::default().under(|cx, t| tag_x(cx.at(t)))))
}
pub(super) fn bw() -> Expr {
    constant(|| arrow(nw(), bool0()))
}
/// `nothing`'s tag over `empty`; its `GoodMaybe` witness is the `nothing` hypothesis.
fn zero_tag() -> Expr {
    constant(|| {
        let (cx, e) = (&mut Cx::default(), empty());
        let (m, mx) = (nothing(cx, e), maybe(cx, e));
        let g = cx.lam(arrow(mx, sort(1)), |cx, p| {
            let hj = cx.pi(e, |cx, a| app(cx.at(p), just(cx, e, cx.at(a))));
            cx.lam(hj, |cx, _| {
                let hn = app(cx.at(p), nothing(cx, e));
                cx.lam(hn, |cx, hn| cx.at(hn))
            })
        });
        tag_mk(cx, e, m, g)
    })
}
/// `just star`'s tag over `unit`; its `GoodMaybe` witness is the `just` hypothesis at `star`.
fn succ_tag() -> Expr {
    constant(|| {
        let (cx, u) = (&mut Cx::default(), unit());
        let (m, mx) = (just(cx, u, star()), maybe(cx, u));
        let g = cx.lam(arrow(mx, sort(1)), |cx, p| {
            let hj = cx.pi(u, |cx, a| app(cx.at(p), just(cx, u, cx.at(a))));
            cx.lam(hj, |cx, hj| {
                let hn = app(cx.at(p), nothing(cx, u));
                cx.lam(hn, |cx, _| app(cx.at(hj), star()))
            })
        });
        tag_mk(cx, u, m, g)
    })
}
/// The zero tree: `nothing` over `empty`, whose child function is `empty -> N` by `wrec` (the one child of a tree of `empty`
/// is the recursive answer).
fn zero_w() -> Expr {
    constant(|| {
        let absurd = Cx::default().lam(empty(), |cx, e| {
            let step = cx.lam(unit(), |cx, a| cx.lam(arrow(unit(), empty()), |cx, _| cx.lam(arrow(unit(), nw()), |cx, ih| app(cx.at(ih), cx.at(a)))));
            wrec(lam(empty(), nw()), unit(), step, cx.at(e))
        });
        sup(zero_tag(), absurd)
    })
}
fn succ_w(cx: &mut Cx, n: Expr) -> Expr {
    let n = cx.mark(n);
    sup(succ_tag(), cx.lam(unit(), |cx, _| cx.at(n)))
}
pub(super) fn num(j: usize) -> Expr {
    (0..j).fold(zero_w(), |e, _| succ_w(&mut Cx::default(), e))
}

// ---------- the tag split ----------
/// What a tag split needs, at an abstracted tag: the children type `X`, the tag's `m : Maybe X`, the child function `f` and the
/// recursive results `ih`.
pub(super) struct Tag {
    pub(super) x_ty: At,
    pub(super) m: At,
    pub(super) f: At,
    pub(super) ih: At,
}
/// The tag's case split into `Bool0`: `k (f w) (ih w)` at `just w`, else `z`.
pub(super) fn tag_case(cx: &mut Cx, tag: &Tag, k: &dyn Fn(&mut Cx, Expr, Expr) -> Expr, z: Expr) -> Expr {
    let on_just = cx.lam(cx.at(tag.x_ty), |cx, w| {
        let (fw, ihw) = (app(cx.at(tag.f), cx.at(w)), app(cx.at(tag.ih), cx.at(w)));
        k(cx, fw, ihw)
    });
    app3(cx.at(tag.m), bool0(), on_just, z)
}

// ---------- streams ----------
/// Non-dependent recursion on `n` into `res`; `body` gets the node's `Tag`.
fn rec_w(cx: &mut Cx, res: Expr, n: Expr, body: &dyn Fn(&mut Cx, &Tag) -> Expr) -> Expr {
    let (res, n) = (cx.mark(res), cx.mark(n));
    let motive = cx.lam(nw(), |cx, _| cx.at(res));
    let children = cx.under(|cx, t| tag_x(cx.at(t)));
    let step = cx.lam(tag_ty(), |cx, t| {
        let x_ty = cx.mark(tag_x(cx.at(t)));
        cx.lam(arrow(cx.at(x_ty), nw()), |cx, f| cx.lam(arrow(cx.at(x_ty), cx.at(res)), |cx, ih| {
            let m = cx.mark(tag_m(cx.at(t)));
            body(cx, &Tag { x_ty, m, f, ih })
        }))
    });
    wrec(motive, children, step, cx.at(n))
}
fn carry_fn() -> Expr {
    constant(|| Cx::default().lam(bw(), |cx, x| cx.lam(bw(), |cx, y| cx.lam(nw(), |cx, i| {
        rec_w(cx, bool0(), cx.at(i), &|cx, tag| tag_case(cx, tag, &|cx, p, ih| maj(app(cx.at(x), p), app(cx.at(y), p), ih), f()))
    }))))
}
pub(super) fn carry(a: Expr, c: Expr, i: Expr) -> Expr {
    app3(carry_fn(), a, c, i)
}
fn add_fn() -> Expr {
    constant(|| Cx::default().lam(bw(), |cx, x| cx.lam(bw(), |cx, y| cx.lam(nw(), |cx, i| {
        let (x, y, i) = (cx.at(x), cx.at(y), cx.at(i));
        xor3(app(x, i), app(y, i), carry(x, y, i))
    }))))
}
pub(super) fn add(a: Expr, c: Expr) -> Expr {
    app2(add_fn(), a, c)
}
/// Bit `i` of the shift: `x (i - 1)`, and `fill` at 0 (false for the real shift; true is the mutant).
fn shl_fn(fill: bool) -> Expr {
    fn build(fill: bool) -> Expr {
        Cx::default().lam(bw(), |cx, x| cx.lam(nw(), |cx, i| {
            rec_w(cx, bool0(), cx.at(i), &|cx, tag| tag_case(cx, tag, &|cx, p, _| app(cx.at(x), p), bit(fill)))
        }))
    }
    if fill { build(true) } else { constant(|| build(false)) }
}
pub(super) fn shl(a: Expr) -> Expr {
    app(shl_fn(false), a)
}
fn shr(cx: &mut Cx, y: Expr) -> Expr {
    let y = cx.mark(y);
    cx.lam(nw(), |cx, i| app(cx.at(y), succ_w(cx, cx.at(i))))
}
pub(super) fn zw() -> Expr {
    constant(|| Cx::default().lam(nw(), |_, _| f()))
}
/// The partial product, `j -> and(x j, z)`: the operand first, so `x j = false` makes it false by computation.
fn tmask(cx: &mut Cx, x: Expr, z: Expr) -> Expr {
    let (x, z) = (cx.mark(x), cx.mark(z));
    cx.lam(nw(), |cx, j| and(app(cx.at(x), cx.at(j)), cx.at(z)))
}
/// Horner on the multiplier: `mul (succ p) x y = (x & y_0) + shl (mul p x (shr y))`, one fold whose motive is a stream function.
fn mul_fn(fill: bool) -> Expr {
    fn build(fill: bool) -> Expr {
        let res = arrow(bw(), arrow(bw(), bw()));
        Cx::default().lam(nw(), |cx, m| rec_w(cx, res, cx.at(m), &|cx, tag| cx.lam(bw(), |cx, x| cx.lam(bw(), |cx, y| cx.lam(nw(), |cx, i| {
            tag_case(cx, tag, &|cx, _, ih| {
                let tail = app2(ih, cx.at(x), shr(cx, cx.at(y)));
                let low = tmask(cx, cx.at(x), app(cx.at(y), zero_w()));
                app(add(low, app(shl_fn(fill), tail)), cx.at(i))
            }, f())
        })))))
    }
    if fill { build(true) } else { constant(|| build(false)) }
}
fn mul(m: Expr, x: Expr, y: Expr) -> Expr {
    app3(mul_fn(false), m, x, y)
}
/// The stream of the low `nb` bits of `val`, as a chain of closed tag cases.
pub(super) fn stream_of(val: u128, nb: usize) -> Expr {
    (0..nb).rev().fold(zw(), |tail, j| Cx::default().lam(nw(), |cx, i| {
        rec_w(cx, bool0(), cx.at(i), &|cx, tag| tag_case(cx, tag, &|_, p, _| app(tail, p), bit((val >> j) & 1 == 1)))
    }))
}

// ---------- proofs ----------
pub(super) fn eqb(a: Expr, c: Expr) -> Expr {
    id(bool0(), a, c)
}
/// Pointwise equality of two streams.
pub(super) fn ptw(cx: &mut Cx, a: Expr, c: Expr) -> Expr {
    let (a, c) = (cx.mark(a), cx.mark(c));
    cx.pi(nw(), |cx, i| eqb(app(cx.at(a), cx.at(i)), app(cx.at(c), cx.at(i))))
}
pub(super) fn xor3(a: Expr, c: Expr, d: Expr) -> Expr {
    xor(xor(a, c), d)
}
/// `\a b c. op a b c`, the function `cong_n` rewrites the three arguments of.
fn ternary(op: fn(Expr, Expr, Expr) -> Expr) -> Expr {
    Cx::default().lam(bool0(), |cx, a| cx.lam(bool0(), |cx, b| cx.lam(bool0(), |cx, c| op(cx.at(a), cx.at(b), cx.at(c)))))
}
/// `\t. body t`, the `Bool0 -> Bool0` function a `cong1` rewrites along.
fn along(cx: &mut Cx, body: impl FnOnce(&mut Cx, Expr) -> Expr) -> Expr {
    cx.lam(bool0(), |cx, t| {
        let t = cx.at(t);
        body(cx, t)
    })
}
fn cong_b(fam: &Expr, l: Expr, r: Expr, p: Expr) -> Expr {
    cong1(&bool0(), &bool0(), fam, l, r, p)
}
/// Induction on `target` for the motive `\n. Pi tele. body(n, tele)`, where the telescope `tys` brings the statement down to
/// `Sort1`. `pred` is the statement reduced at the tag's abstracted `m`; `hj (f w) (ih w)` proves it at `just w`, `hn` at
/// `nothing`. All four get the telescope's variables.
pub(super) fn ind(cx: &mut Cx, tys: &[Ty], body: &dyn Fn(&mut Cx, Expr, &[At]) -> Expr, target: Expr,
                  pred: &dyn Fn(&mut Cx, &Tag, &[At]) -> Expr,
                  hj: &dyn Fn(&mut Cx, Expr, Expr, &[At]) -> Expr,
                  hn: &dyn Fn(&mut Cx, &[At]) -> Expr) -> Expr {
    let motive = |cx: &mut Cx, n: Expr| -> Expr {
        let n = cx.mark(n);
        tele(cx, false, tys, &mut vec![], &mut |cx, xs| body(cx, cx.at(n), xs))
    };
    // Pi f:(X -> N). Pi ih:(Pi w:X. motive (f w)). motive (sup tag f)
    let goal = |cx: &mut Cx, tag: Expr| -> Expr {
        let (tag, x_ty) = (cx.mark(tag), cx.mark(tag_x(tag)));
        cx.pi(arrow(cx.at(x_ty), nw()), |cx, f| {
            let ih = cx.pi(cx.at(x_ty), |cx, w| motive(cx, app(cx.at(f), cx.at(w))));
            cx.pi(ih, |cx, _| motive(cx, sup(cx.at(tag), cx.at(f))))
        })
    };
    let step = cx.lam(tag_ty(), |cx, t| {
        let by_t = cx.lam(tag_ty(), |cx, t| goal(cx, cx.at(t)));
        let split = cx.lam(sort(1), |cx, x| {
            let ti = tag_inner(cx, cx.at(x));
            cx.lam(ti, |cx, r| {
                let ti = tag_inner(cx, cx.at(x));
                let by_r = cx.lam(ti, |cx, r| {
                    let fam = cx.under(|cx, x| tag_inner(cx, cx.at(x)));
                    goal(cx, pair(fam, cx.at(x), cx.at(r)))
                });
                let mx = maybe(cx, cx.at(x));
                let leaf = cx.lam(mx, |cx, m| {
                    let gm = goodmaybe(cx, cx.at(x), cx.at(m));
                    cx.lam(gm, |cx, g| cx.lam(arrow(cx.at(x), nw()), |cx, f| {
                        let ih_ty = cx.pi(cx.at(x), |cx, w| motive(cx, app(cx.at(f), cx.at(w))));
                        cx.lam(ih_ty, |cx, ih| tele(cx, true, tys, &mut vec![], &mut |cx, xs| {
                            let mx = maybe(cx, cx.at(x));
                            let p = cx.lam(mx, |cx, m| pred(cx, &Tag { x_ty: x, m, f, ih }, xs));
                            let hjs = cx.lam(cx.at(x), |cx, w| {
                                let (fw, ihw) = (app(cx.at(f), cx.at(w)), app(cx.at(ih), cx.at(w)));
                                hj(cx, fw, ihw, xs)
                            });
                            let hns = hn(cx, xs);
                            app3(cx.at(g), p, hjs, hns)
                        }))
                    }))
                });
                sigrec(by_r, leaf, cx.at(r))
            })
        });
        sigrec(by_t, split, cx.at(t))
    });
    let motive_n = cx.lam(nw(), |cx, n| motive(cx, cx.at(n)));
    let children = cx.under(|cx, t| tag_x(cx.at(t)));
    wrec(motive_n, children, step, target)
}
fn carry_at(a: Expr, c: Expr, p: Expr) -> Expr {
    maj(app(a, p), app(c, p), carry(a, c, p))
}

/// `Pi a a2 c c2. a ~ a2 -> c ~ c2 -> Pi n. carry a c n = carry a2 c2 n`
fn carry_cong() -> Expr {
    constant(|| Cx::default().lam(bw(), |cx, a| cx.lam(bw(), |cx, a2| cx.lam(bw(), |cx, c| cx.lam(bw(), |cx, c2| {
        let ha_ty = ptw(cx, cx.at(a), cx.at(a2));
        cx.lam(ha_ty, |cx, ha| {
            let hc_ty = ptw(cx, cx.at(c), cx.at(c2));
            cx.lam(hc_ty, |cx, hc| cx.lam(nw(), |cx, n| {
                ind(cx, &[], &|cx, n, _| eqb(carry(cx.at(a), cx.at(c), n), carry(cx.at(a2), cx.at(c2), n)), cx.at(n),
                    &|cx, tag, _| {
                        let l = tag_case(cx, tag, &|cx, p, _| carry_at(cx.at(a), cx.at(c), p), f());
                        eqb(l, tag_case(cx, tag, &|cx, p, _| carry_at(cx.at(a2), cx.at(c2), p), f()))
                    },
                    &|cx, p, ih, _| {
                        let (a, a2, c, c2) = (cx.at(a), cx.at(a2), cx.at(c), cx.at(c2));
                        cong_n(&bool0(), &bool0(), &ternary(maj), &[app(a, p), app(c, p), carry(a, c, p)],
                            &[app(a2, p), app(c2, p), carry(a2, c2, p)], vec![app(cx.at(ha), p), app(cx.at(hc), p), ih])
                    },
                    &|_, _| refl(f()))
            }))
        })
    })))))
}
/// `Pi a a2 c c2. a ~ a2 -> c ~ c2 -> Pi i. add a c i = add a2 c2 i`
fn add_cong() -> Expr {
    constant(|| Cx::default().lam(bw(), |cx, a| cx.lam(bw(), |cx, a2| cx.lam(bw(), |cx, c| cx.lam(bw(), |cx, c2| {
        let ha_ty = ptw(cx, cx.at(a), cx.at(a2));
        cx.lam(ha_ty, |cx, ha| {
            let hc_ty = ptw(cx, cx.at(c), cx.at(c2));
            cx.lam(hc_ty, |cx, hc| cx.lam(nw(), |cx, i| {
                let (a, a2, c, c2, ha, hc, i) = (cx.at(a), cx.at(a2), cx.at(c), cx.at(c2), cx.at(ha), cx.at(hc), cx.at(i));
                let ce = apps(carry_cong(), vec![a, a2, c, c2, ha, hc, i]);
                cong_n(&bool0(), &bool0(), &ternary(xor3), &[app(a, i), app(c, i), carry(a, c, i)],
                    &[app(a2, i), app(c2, i), carry(a2, c2, i)], vec![app(ha, i), app(hc, i), ce])
            }))
        })
    })))))
}
fn add_cong_at(a: Expr, a2: Expr, c: Expr, c2: Expr, ha: Expr, hc: Expr, i: Expr) -> Expr {
    apps(add_cong(), vec![a, a2, c, c2, ha, hc, i])
}
/// `Pi a a2. a ~ a2 -> Pi n. shl a n = shl a2 n`
fn shl_cong() -> Expr {
    constant(|| Cx::default().lam(bw(), |cx, a| cx.lam(bw(), |cx, a2| {
        let ha_ty = ptw(cx, cx.at(a), cx.at(a2));
        cx.lam(ha_ty, |cx, ha| cx.lam(nw(), |cx, n| {
            ind(cx, &[], &|cx, n, _| eqb(app(shl(cx.at(a)), n), app(shl(cx.at(a2)), n)), cx.at(n),
                &|cx, tag, _| {
                    let l = tag_case(cx, tag, &|cx, p, _| app(cx.at(a), p), f());
                    eqb(l, tag_case(cx, tag, &|cx, p, _| app(cx.at(a2), p), f()))
                },
                &|cx, p, _, _| app(cx.at(ha), p), &|_, _| refl(f()))
        }))
    })))
}
/// `Pi a. (Pi i. a i = false) -> Pi n. shl a n = false`
fn shl_false() -> Expr {
    constant(|| Cx::default().lam(bw(), |cx, a| {
        let ha_ty = ptw(cx, cx.at(a), zw());
        cx.lam(ha_ty, |cx, ha| cx.lam(nw(), |cx, n| {
            ind(cx, &[], &|cx, n, _| eqb(app(shl(cx.at(a)), n), f()), cx.at(n),
                &|cx, tag, _| eqb(tag_case(cx, tag, &|cx, p, _| app(cx.at(a), p), f()), f()),
                &|cx, p, _, _| app(cx.at(ha), p), &|_, _| refl(f()))
        }))
    }))
}
/// `Pi n. carry zs zs n = false`
fn carry_zero() -> Expr {
    constant(|| Cx::default().lam(nw(), |cx, n| {
        let z = zw();
        ind(cx, &[], &|_, n, _| eqb(carry(z, z, n), f()), cx.at(n),
            &|cx, tag, _| eqb(tag_case(cx, tag, &|_, p, _| carry_at(z, z, p), f()), f()),
            // maj(z p, z p, false) computes to false
            &|cx, p, ih, _| {
                let pa = cx.mark(p);
                let fam = along(cx, |cx, t| maj(app(z, cx.at(pa)), app(z, cx.at(pa)), t));
                cong_b(&fam, carry(z, z, p), f(), ih)
            },
            &|_, _| refl(f()))
    }))
}
/// `Pi i. add zs zs i = false`
fn add_zero() -> Expr {
    constant(|| Cx::default().lam(nw(), |cx, i| {
        let (z, ia) = (zw(), i);
        // xor3(z i, z i, false) computes to false
        let fam = along(cx, |cx, t| xor3(app(z, cx.at(ia)), app(z, cx.at(ia)), t));
        let i = cx.at(i);
        cong_b(&fam, carry(z, z, i), f(), app(carry_zero(), i))
    }))
}

// stage 3
fn stmt_zero_mul(rhs: Expr) -> Expr {
    Cx::default().pi(nw(), |cx, m| cx.pi(bw(), |cx, y| cx.pi(nw(), |cx, i| eqb(app(mul(cx.at(m), zw(), cx.at(y)), cx.at(i)), rhs))))
}
fn proof_zero_mul() -> Expr {
    let z = zw();
    let tys = [ty!(|_c, _x| bw()), ty!(|_c, _x| nw())];
    // add(tmask z (y 0), shl (mul p z (shr y))) i, at the tail's count `p`
    let at = |cx: &mut Cx, p: Expr, xs: &[At]| -> (Expr, Expr) {
        let (y, i) = (cx.at(xs[0]), cx.at(xs[1]));
        let low = tmask(cx, z, app(y, zero_w()));
        let tail = mul(p, z, shr(cx, y));
        (app(add(low, shl(tail)), i), tail)
    };
    Cx::default().lam(nw(), |cx, m| ind(cx, &tys,
        &|cx, n, xs| eqb(app(mul(n, z, cx.at(xs[0])), cx.at(xs[1])), f()),
        cx.at(m),
        &|cx, tag, xs| eqb(tag_case(cx, tag, &|cx, p, _| at(cx, p, xs).0, f()), f()),
        &|cx, p, ih, xs| {
            let (y, i) = (cx.at(xs[0]), cx.at(xs[1]));
            let (lhs, tail) = at(cx, p, xs);
            let low = tmask(cx, z, app(y, zero_w()));
            // shl tail ~ zs, because the tail is false everywhere by the induction hypothesis
            let sy = shr(cx, y);
            let (tl, ih_at) = (cx.mark(tail), cx.mark(app(ih, sy)));
            let hc = cx.lam(nw(), |cx, q| apps(shl_false(), vec![cx.at(tl), cx.at(ih_at), cx.at(q)]));
            let ha = cx.lam(nw(), |_, _| refl(f()));
            let e = add_cong_at(low, z, shl(tail), z, ha, hc, i);
            trans_proof(&bool0(), &lhs, &app(add(z, z), i), &f(), e, app(add_zero(), i))
        },
        &|_, _| refl(f())))
}

// stage 4a: commutativity of the stream adder, real carries, goodness needed
pub(super) fn good_stream(cx: &mut Cx, a: Expr) -> Expr {
    let a = cx.mark(a);
    cx.pi(nw(), |cx, i| app(good_bool(), app(cx.at(a), cx.at(i))))
}
fn stmt_add_comm(rhs: &dyn Fn(Expr, Expr) -> Expr) -> Expr {
    Cx::default().pi(bw(), |cx, x| cx.pi(bw(), |cx, y| {
        let gx = good_stream(cx, cx.at(x));
        cx.pi(gx, |cx, _| {
            let gy = good_stream(cx, cx.at(y));
            cx.pi(gy, |cx, _| cx.pi(nw(), |cx, i| {
                let (x, y, i) = (cx.at(x), cx.at(y), cx.at(i));
                eqb(app(add(x, y), i), app(rhs(x, y), i))
            }))
        })
    }))
}
/// Case split on two bits: `l(a, b) = r(a, b)` in `ty`, from the witnesses `ga`, `gb`; `yb` is the actual second bit.
fn cases2(cx: &mut Cx, ga: Expr, gb: Expr, yb: Expr, ty: Expr, l: &dyn Fn(&Cx, Expr, Expr) -> Expr, r: &dyn Fn(&Cx, Expr, Expr) -> Expr) -> Expr {
    let (yb, ty) = (cx.mark(yb), cx.mark(ty));
    let tm = |cx: &Cx, a: Expr, c: Expr| id(cx.at(ty), l(cx, a, c), r(cx, a, c));
    let m1 = cx.lam(bool0(), |cx, a| tm(cx, cx.at(a), cx.at(yb)));
    let inner = |cx: &mut Cx, av: Expr| {
        let m2 = cx.lam(bool0(), |cx, c| tm(cx, av, cx.at(c)));
        app3(gb, m2, refl(l(cx, av, t())), refl(l(cx, av, f())))
    };
    let (it, iff) = (inner(cx, t()), inner(cx, f()));
    app3(ga, m1, it, iff)
}
/// `op(x p, y p, carry x y p) = op(y p, x p, carry y x p)`, from `e : carry x y p = carry y x p` and a case split on the bits at `p`.
fn comm_at(cx: &mut Cx, op: fn(Expr, Expr, Expr) -> Expr, [x, y, gx, gy]: [At; 4], p: Expr, e: Expr) -> Expr {
    let (x, y) = (cx.at(x), cx.at(y));
    let (xp, yp, l, r) = (app(x, p), app(y, p), carry(x, y, p), carry(y, x, p));
    let (xa, ya, ra) = (cx.mark(xp), cx.mark(yp), cx.mark(r));
    let leaf = cases2(cx, app(cx.at(gx), p), app(cx.at(gy), p), yp, bool0(),
        &|cx, a, c| op(a, c, cx.at(ra)), &|cx, a, c| op(c, a, cx.at(ra)));
    let fam = along(cx, |cx, t| op(cx.at(xa), cx.at(ya), t));
    trans_proof(&bool0(), &op(xp, yp, l), &op(xp, yp, r), &op(yp, xp, r), cong_b(&fam, l, r, e), leaf)
}
fn proof_add_comm() -> Expr {
    Cx::default().lam(bw(), |cx, x| cx.lam(bw(), |cx, y| {
        let gx_ty = good_stream(cx, cx.at(x));
        cx.lam(gx_ty, |cx, gx| {
            let gy_ty = good_stream(cx, cx.at(y));
            cx.lam(gy_ty, |cx, gy| cx.lam(nw(), |cx, i| {
                let ce = ind(cx, &[], &|cx, n, _| eqb(carry(cx.at(x), cx.at(y), n), carry(cx.at(y), cx.at(x), n)), cx.at(i),
                    &|cx, tag, _| {
                        let l = tag_case(cx, tag, &|cx, p, _| carry_at(cx.at(x), cx.at(y), p), f());
                        eqb(l, tag_case(cx, tag, &|cx, p, _| carry_at(cx.at(y), cx.at(x), p), f()))
                    },
                    &|cx, p, ih, _| comm_at(cx, maj, [x, y, gx, gy], p, ih),
                    &|_, _| refl(f()));
                comm_at(cx, xor3, [x, y, gx, gy], cx.at(i), ce)
            }))
        })
    }))
}

// stage 4b: the shift law, with the multiplier's width, multiplicand and multiplier bits all symbolic
/// `Pi a c n. carry (shl a) (shl c) (succ n) = carry a c n`: the carry of the delayed operands is the carry, delayed.
fn carry_shl() -> Expr {
    constant(|| Cx::default().lam(bw(), |cx, a| cx.lam(bw(), |cx, c| cx.lam(nw(), |cx, n| {
        ind(cx, &[], &|cx, n, _| {
            let (a, c) = (cx.at(a), cx.at(c));
            eqb(carry(shl(a), shl(c), succ_w(cx, n)), carry(a, c, n))
        }, cx.at(n),
            &|cx, tag, _| {
                let (sa, sc) = (cx.mark(shl(cx.at(a))), cx.mark(shl(cx.at(c))));
                let ta = tag_case(cx, tag, &|cx, p, _| app(cx.at(a), p), f());
                let tc = tag_case(cx, tag, &|cx, p, _| app(cx.at(c), p), f());
                let ts = tag_case(cx, tag, &|cx, p, _| carry_at(cx.at(sa), cx.at(sc), p), f());
                eqb(maj(ta, tc, ts), tag_case(cx, tag, &|cx, p, _| carry_at(cx.at(a), cx.at(c), p), f()))
            },
            // maj(a p, c p, r) on both sides once the delayed carry is rewritten to r
            &|cx, p, ih, _| {
                let (a, c) = (cx.at(a), cx.at(c));
                let (ap_, cp) = (cx.mark(app(a, p)), cx.mark(app(c, p)));
                let fam = along(cx, |cx, t| maj(cx.at(ap_), cx.at(cp), t));
                let sp = succ_w(cx, p);
                cong_b(&fam, carry(shl(a), shl(c), sp), carry(a, c, p), ih)
            },
            &|_, _| refl(f()))
    }))))
}
/// `Pi a c n. shl (add a c) n = add (shl a) (shl c) n`
fn shl_add() -> Expr {
    constant(|| Cx::default().lam(bw(), |cx, a| cx.lam(bw(), |cx, c| cx.lam(nw(), |cx, n| {
        ind(cx, &[], &|cx, n, _| {
            let (a, c) = (cx.at(a), cx.at(c));
            eqb(app(shl(add(a, c)), n), app(add(shl(a), shl(c)), n))
        }, cx.at(n),
            &|cx, tag, _| {
                let (sa, sc) = (cx.mark(shl(cx.at(a))), cx.mark(shl(cx.at(c))));
                let l = tag_case(cx, tag, &|cx, p, _| app(add(cx.at(a), cx.at(c)), p), f());
                let ta = tag_case(cx, tag, &|cx, p, _| app(cx.at(a), p), f());
                let tc = tag_case(cx, tag, &|cx, p, _| app(cx.at(c), p), f());
                eqb(l, xor3(ta, tc, tag_case(cx, tag, &|cx, p, _| carry_at(cx.at(sa), cx.at(sc), p), f())))
            },
            // xor3(a p, c p, r) = xor3(a p, c p, delayed carry), by carry_shl turned around
            &|cx, p, _, _| {
                let (a, c) = (cx.at(a), cx.at(c));
                let (ap_, cp) = (cx.mark(app(a, p)), cx.mark(app(c, p)));
                let fam = along(cx, |cx, t| xor3(cx.at(ap_), cx.at(cp), t));
                let (l, r) = (carry(shl(a), shl(c), succ_w(cx, p)), carry(a, c, p));
                cong_b(&fam, r, l, sym(&bool0(), &l, &r, app3(carry_shl(), a, c, p)))
            },
            &|_, _| refl(f()))
    }))))
}
/// `Pi x z n. tmask (shl x) z n = shl (tmask x z) n`
fn tmask_shl() -> Expr {
    constant(|| Cx::default().lam(bw(), |cx, x| cx.lam(bool0(), |cx, z| cx.lam(nw(), |cx, n| {
        ind(cx, &[], &|cx, n, _| {
            let (l, r) = (tmask(cx, shl(cx.at(x)), cx.at(z)), tmask(cx, cx.at(x), cx.at(z)));
            eqb(app(l, n), app(shl(r), n))
        }, cx.at(n),
            &|cx, tag, _| {
                let l = and(tag_case(cx, tag, &|cx, p, _| app(cx.at(x), p), f()), cx.at(z));
                eqb(l, tag_case(cx, tag, &|cx, p, _| and(app(cx.at(x), p), cx.at(z)), f()))
            },
            &|cx, p, _, _| refl(and(app(cx.at(x), p), cx.at(z))),
            &|_, _| refl(f()))
    }))))
}
fn stmt_mul_shl(fill: bool, rhs: &dyn Fn(&mut Cx, Expr) -> Expr) -> Expr {
    Cx::default().pi(nw(), |cx, m| cx.pi(bw(), |cx, x| cx.pi(bw(), |cx, y| cx.pi(nw(), |cx, i| {
        let mf = |x: Expr| app3(mul_fn(fill), cx.at(m), x, cx.at(y));
        let (l, r) = (mf(app(shl_fn(fill), cx.at(x))), mf(cx.at(x)));
        let r = rhs(cx, r);
        eqb(app(l, cx.at(i)), app(r, cx.at(i)))
    }))))
}
fn proof_mul_shl() -> Expr {
    let tys = [ty!(|_c, _x| bw()), ty!(|_c, _x| bw()), ty!(|_c, _x| nw())];
    // the operands at the current depth: (x, y, i, the low partial products a2 = tmask (shl x) y0 and a = tmask x y0, shr y)
    let ops = |cx: &mut Cx, xs: &[At]| -> [Expr; 6] {
        let (x, y, i) = (cx.at(xs[0]), cx.at(xs[1]), cx.at(xs[2]));
        let y0 = app(y, zero_w());
        let (a2, a, sy) = (tmask(cx, shl(x), y0), tmask(cx, x, y0), shr(cx, y));
        [x, y, i, a2, a, sy]
    };
    Cx::default().lam(nw(), |cx, m| ind(cx, &tys,
        &|cx, n, xs| {
            let (x, y, i) = (cx.at(xs[0]), cx.at(xs[1]), cx.at(xs[2]));
            eqb(app(mul(n, shl(x), y), i), app(shl(mul(n, x, y)), i))
        },
        cx.at(m),
        &|cx, tag, xs| {
            let lhs = tag_case(cx, tag, &|cx, p, _| {
                let [x, _, i, a2, _, sy] = ops(cx, xs);
                app(add(a2, shl(mul(p, shl(x), sy))), i)
            }, f());
            let stream = cx.lam(nw(), |cx, s| tag_case(cx, tag, &|cx, p, _| {
                let [x, _, _, _, a, sy] = ops(cx, xs);
                app(add(a, shl(mul(p, x, sy))), cx.at(s))
            }, f()));
            eqb(lhs, app(shl(stream), cx.at(xs[2])))
        },
        &|cx, p, ih, xs| {
            let [x, y, i, a2, a, sy] = ops(cx, xs);
            let (t2, t) = (mul(p, shl(x), sy), mul(p, x, sy));
            // the induction hypothesis at `shr y`: tail2 ~ shl tail
            let (ih_x, t2a, ta, xa, y0) = (cx.mark(app2(ih, x, sy)), cx.mark(t2), cx.mark(t), cx.mark(x), cx.mark(app(y, zero_w())));
            let ih_at = cx.lam(nw(), |cx, q| app(cx.at(ih_x), cx.at(q)));
            let iha = cx.mark(ih_at);
            let hb = cx.lam(nw(), |cx, r| apps(shl_cong(), vec![cx.at(t2a), shl(cx.at(ta)), cx.at(iha), cx.at(r)]));
            let ha = cx.lam(nw(), |cx, r| app3(tmask_shl(), cx.at(xa), cx.at(y0), cx.at(r)));
            let (sa, sb) = (shl(a), shl(shl(t)));
            let e1 = add_cong_at(a2, sa, shl(t2), sb, ha, hb, i);
            let mid = app(add(sa, sb), i);
            let top = app(shl(add(a, shl(t))), i);
            let e2 = app3(shl_add(), a, shl(t), i);
            trans_proof(&bool0(), &app(add(a2, shl(t2)), i), &mid, &top, e1, sym(&bool0(), &top, &mid, e2))
        },
        &|cx, xs| {
            let i = cx.at(xs[2]);
            let ok = cx.lam(nw(), |_, _| refl(f()));
            sym(&bool0(), &app(shl(zw()), i), &f(), app3(shl_false(), zw(), ok, i))
        }))
}

// ---------- stage 1: the types ----------
#[test]
fn w_index_stage1_the_fold_types_with_no_level_raise() {
    for (name, t, sort) in [("unit", unit(), 1), ("empty", empty(), 1), ("tag", tag_ty(), 2), ("N", nw(), 2), ("Bits", bw(), 2)] {
        let ty = typecheck(&t).unwrap_or_else(|e| panic!("{name}: {e}"));
        assert!(def_eq(&ty, &tatic_kernel::sort(sort)), "{name} is not in Sort{sort}");
    }
    let bb = arrow(bw(), arrow(bw(), bw()));
    for (name, t, want) in [("zero", zero_w(), nw()), ("one", num(1), nw()), ("add", add_fn(), bb),
        ("shl", shl_fn(false), arrow(bw(), bw())), ("mul", mul_fn(false), arrow(nw(), bb))] {
        let ty = typecheck(&t).unwrap_or_else(|e| panic!("{name}: {}", e.chars().take(600).collect::<String>()));
        assert!(def_eq(&ty, &want), "{name} has the wrong type");
    }
}

// ---------- stage 2: closed products compute ----------
fn product_bit_is(fill: bool, nb: usize, x: u128, y: u128, p: usize, want: Expr) -> bool {
    let prod = app3(mul_fn(fill), num(nb), stream_of(x, nb), stream_of(y, nb));
    def_eq(&app(prod, num(p)), &want)
}
#[test]
fn w_index_stage2_closed_products_compute() {
    let nb = 3;
    for (x, y) in [(5u128, 3u128), (7, 7), (6, 5), (3, 0), (0, 7), (7, 1), (4, 6), (1, 1)] {
        for p in 0..2 * nb + 2 {
            assert!(product_bit_is(false, nb, x, y, p, bit((x * y >> p) & 1 == 1)), "{x} * {y}: bit {p}");
        }
    }
}
#[test]
fn w_index_stage2_the_fill_bit_mutant_computes_wrong_products() {
    let nb = 3;
    let wrong = [(5u128, 3u128), (7, 7), (3, 0), (1, 1)].iter().filter(|&&(x, y)| {
        (0..2 * nb + 2).any(|p| !product_bit_is(true, nb, x, y, p, bit((x * y >> p) & 1 == 1)))
    }).count();
    assert_eq!(wrong, 4, "the mutant must miss every product");
}

// ---------- stages 3 and 4: laws at a symbolic position, count and operands ----------
#[test]
fn w_index_stage3_zero_times_y() {
    tatic_kernel::scoped(|| {
        checked("zero mul y = 0, m symbolic", check(&Ctx::new(), &proof_zero_mul(), &stmt_zero_mul(f())));
        assert!(check(&Ctx::new(), &proof_zero_mul(), &stmt_zero_mul(t())).is_err(), "control: mul m zs y i = true");
    })
}
#[test]
fn w_index_stage4a_add_commutes() {
    tatic_kernel::scoped(|| {
        checked("add x y = add y x", check(&Ctx::new(), &proof_add_comm(), &stmt_add_comm(&|x, y| add(y, x))));
        assert!(check(&Ctx::new(), &proof_add_comm(), &stmt_add_comm(&|_, y| add(y, y))).is_err(), "control: add x y = add y y");
    })
}
#[test]
fn w_index_stage4b_the_shift_law() {
    tatic_kernel::scoped(|| {
        let pf = proof_mul_shl();
        checked("mul m (shl x) y = shl (mul m x y)", check(&Ctx::new(), &pf, &stmt_mul_shl(false, &|_cx, t| shl(t))));
        assert!(check(&Ctx::new(), &pf, &stmt_mul_shl(false, &|_cx, t| t)).is_err(), "control: mul m (shl x) y = mul m x y");
        let filled = |_cx: &mut Cx, t: Expr| app(shl_fn(true), t);
        assert!(check(&Ctx::new(), &pf, &stmt_mul_shl(true, &filled)).is_err(), "control: the fill-bit mutant");
    })
}
/// The symbolic theorem, read at closed numbers, says what the product says: its two sides reduce to bit `p` of `2xy`.
#[test]
fn w_index_stage4b_instantiates_to_true_products() {
    let nb = 3;
    tatic_kernel::scoped(|| {
        let pf = proof_mul_shl();
        for (x, y) in [(5u128, 3u128), (7, 7), (6, 5), (3, 0)] {
            for p in 0..2 * nb + 3 {
                let at = app(app3(pf, num(nb), stream_of(x, nb), stream_of(y, nb)), num(p));
                let want = bit((2 * x * y >> p) & 1 == 1);
                checked(&format!("{x} {y} bit {p}"), check(&Ctx::new(), &at, &eqb(want, want)));
                let flip = bit((2 * x * y >> p) & 1 == 0);
                assert!(check(&Ctx::new(), &at, &eqb(flip, flip)).is_err(), "{x} {y} bit {p}: the wrong bit passed");
            }
        }
    })
}
