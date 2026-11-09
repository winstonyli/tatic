//! The machine's laws (append, if, loop, the countdown invariant) and concrete runs, each with controls that must be
//! rejected (docs/tier-cycle/, "Wasm programs as kernel data, kept").
use super::*;

/// The proof's choices that each control below breaks.
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Ctl {
    Ok,
    /// the false leaf given `Q x`
    SameLeaf,
    /// the witnesses eliminated at Sort0 without lowering
    NoLower,
    /// the conclusion stated as `Q x`
    ClaimsX,
}

/// `Pi R:Sort0. Pi Q:R->Sort0. Pi w:Bv_1. GoodBv w -> Pi x y:R. Q x -> Q y -> Q (choose w x y)`: lower `w`'s witness to
/// Sort0, eliminate it at `\w. Q (choose w x y)`, and split the bit at `\b. Q (choose (mk b) x y)`.
pub fn if_inv(ctl: Ctl) -> (Expr, Expr) {
    let tys: Vec<Ty> = vec![
        ty!(|_c, _x| sort(0)),
        ty!(|c, x| arrow(c.at(x[0]), sort(0))),
        ty!(|_c, _x| bv_ty(1)),
        ty!(|c, x| app(good_bv(1), c.at(x[2]))),
        ty!(|c, x| c.at(x[0])),
        ty!(|c, x| c.at(x[0])),
        ty!(|c, x| app(c.at(x[1]), c.at(x[4]))),
        ty!(|c, x| app(c.at(x[1]), c.at(x[5]))),
    ];
    let q_choose = |c: &Cx, x: &[At], w: Expr| app(c.at(x[1]), choose(c.at(x[0]), w, c.at(x[4]), c.at(x[5])));
    law(&tys, |c, x| {
        let stmt = if ctl == Ctl::ClaimsX { app(c.at(x[1]), c.at(x[4])) } else { q_choose(c, x, c.at(x[2])) };
        let motive = c.lam(bv_ty(1), |c, w| q_choose(c, x, c.at(w)));
        let leaf_f = if ctl == Ctl::SameLeaf { x[6] } else { x[7] };
        let good = if ctl == Ctl::NoLower { good_bool() } else { good_bool0() };
        let step = c.lam(bool0(), |c, a| {
            c.lam(app(good, c.at(a)), |c, ga| {
                let mb = c.lam(bool0(), |c, b| q_choose(c, x, church_tuple(&[c.at(b)])));
                app3(c.at(ga), mb, c.at(x[6]), c.at(leaf_f))
            })
        });
        let w = if ctl == Ctl::NoLower { c.at(x[3]) } else { app2(lower_bv(1).0, c.at(x[2]), c.at(x[3])) };
        (app2(w, motive, step), stmt)
    })
}

/// `Pi Sa Sb Sc (p1 : Prog Sa Sb) (p2 : Prog Sb Sc) N R k z. Id(G Sa, M (p1 ++ p2) .. k z, M p1 .. (M p2 .. k z) z)`, by `refl`.
pub fn append_law(w: Wasm) -> (Expr, Expr) {
    let tys: Vec<Ty> = vec![
        ty!(|_c, _x| sort(2)),
        ty!(|_c, _x| sort(2)),
        ty!(|_c, _x| sort(2)),
        ty!(|c, x| w.prog_ty(c, &|c| c.at(x[0]), &|c| c.at(x[1]))),
        ty!(|c, x| w.prog_ty(c, &|c| c.at(x[1]), &|c| c.at(x[2]))),
        ty!(|_c, _x| nat2()),
        ty!(|_c, _x| sort(0)),
        ty!(|c, x| w.g(c, x[6], c.at(x[2]))),
        ty!(|c, x| c.at(x[6])),
    ];
    law(&tys, |c, x| {
        let p = w.append(c, &|c| c.at(x[2]), x[3], x[4]);
        let p = c.mark(p);
        let l = w.meaning(c, p, x[5], x[6], x[7], x[8]);
        let k2 = w.meaning(c, x[4], x[5], x[6], x[7], x[8]);
        let k2 = c.mark(k2);
        let r = w.meaning(c, x[3], x[5], x[6], k2, x[8]);
        let ga = w.g(c, x[6], c.at(x[0]));
        (refl(l), id(ga, l, r))
    })
}

/// The If law and its invariant, over one telescope:
/// `cc m (sp : Spec(cc, m)) [gm : GoodBv m] S T (t e : Prog S T) N R [Q] k z s mu [qt qe]`.
fn if_tele(w: Wasm, inv: bool) -> Vec<Ty<'static>> {
    let mut tys: Vec<Ty> = vec![
        ty!(|c, _x| w.code_ty(c, K::B)),
        ty!(|_c, _x| bv_ty(1)),
        ty!(|c, x| w.spec(c, x[0], x[1], K::B)),
    ];
    if inv {
        tys.push(ty!(|c, x| app(good_bv(1), c.at(x[1]))));
    }
    let o = tys.len(); // S T t e N R at o..o+6
    tys.extend([
        ty!(|_c, _x| sort(2)),
        ty!(|_c, _x| sort(2)),
        ty!(|c, x| w.prog_ty(c, &|c| c.at(x[o]), &|c| c.at(x[o + 1]))),
        ty!(|c, x| w.prog_ty(c, &|c| c.at(x[o]), &|c| c.at(x[o + 1]))),
        ty!(|_c, _x| nat2()),
        ty!(|_c, _x| sort(0)),
    ]);
    if inv {
        tys.push(ty!(|c, x| arrow(c.at(x[o + 5]), sort(0))));
    }
    let o2 = tys.len(); // k z s mu
    tys.extend([
        ty!(|c, x| w.g(c, x[o + 5], c.at(x[o + 1]))),
        ty!(|c, x| c.at(x[o + 5])),
        ty!(|c, x| c.at(x[o])),
        ty!(|c, x| w.mem(c, x[o + 5])),
    ]);
    if inv {
        for arm in [o + 2, o + 3] {
            tys.push(ty!(|c, x| {
                let m = w.meaning(c, x[arm], x[o + 4], x[o + 5], x[o2], x[o2 + 1]);
                app(c.at(x[o + 6]), app2(m, c.at(x[o2 + 2]), c.at(x[o2 + 3])))
            }));
        }
    }
    tys
}

/// Names into `if_tele`'s telescope.
struct IfX {
    cc: At,
    m: At,
    sp: At,
    gm: Option<At>,
    s_ty: At,
    t_ty: At,
    th: At,
    el: At,
    fuel: At,
    r: At,
    q: Option<At>,
    k: At,
    z: At,
    s: At,
    mu: At,
    qs: Option<(At, At)>,
}
fn if_names(x: &[At], inv: bool) -> IfX {
    let o = if inv { 4 } else { 3 };
    let o2 = o + if inv { 7 } else { 6 };
    IfX {
        cc: x[0],
        m: x[1],
        sp: x[2],
        gm: inv.then(|| x[3]),
        s_ty: x[o],
        t_ty: x[o + 1],
        th: x[o + 2],
        el: x[o + 3],
        fuel: x[o + 4],
        r: x[o + 5],
        q: inv.then(|| x[o + 6]),
        k: x[o2],
        z: x[o2 + 1],
        s: x[o2 + 2],
        mu: x[o2 + 3],
        qs: inv.then(|| (x[o2 + 4], x[o2 + 5])),
    }
}
impl IfX {
    /// `M (cc S ++ if t e) N R k z s mu`; `swap` gives `if e t`.
    fn lhs(&self, w: Wasm, c: &mut Cx, swap: bool) -> Expr {
        let (th, el) = if swap { (self.el, self.th) } else { (self.th, self.el) };
        let p1 = c.mark(app(c.at(self.cc), c.at(self.s_ty)));
        let p2 = w.ifp(c, self.s_ty, self.t_ty, th, el);
        let p2 = c.mark(p2);
        let p = w.append(c, &|c| c.at(self.t_ty), p1, p2);
        let p = c.mark(p);
        app2(w.meaning(c, p, self.fuel, self.r, self.k, self.z), c.at(self.s), c.at(self.mu))
    }
    fn arm(&self, w: Wasm, c: &mut Cx, p: At) -> Expr {
        app2(w.meaning(c, p, self.fuel, self.r, self.k, self.z), c.at(self.s), c.at(self.mu))
    }
    /// `choose m (M t .. s mu) (M e .. s mu)`; `swap` exchanges the arms.
    fn rhs(&self, w: Wasm, c: &mut Cx, swap: bool) -> Expr {
        let (a, b) = (self.arm(w, c, self.th), self.arm(w, c, self.el));
        let (a, b) = if swap { (b, a) } else { (a, b) };
        choose(c.at(self.r), c.at(self.m), a, b)
    }
    /// The If law's proof: `sp` at the continuation `M (if t e) N R k z`.
    fn law_proof(&self, w: Wasm, c: &mut Cx) -> Expr {
        let p2 = w.ifp(c, self.s_ty, self.t_ty, self.th, self.el);
        let p2 = c.mark(p2);
        let k2 = w.meaning(c, p2, self.fuel, self.r, self.k, self.z);
        let args = vec![c.at(self.s_ty), c.at(self.fuel), c.at(self.r), k2, c.at(self.z), c.at(self.s), c.at(self.mu)];
        apps(c.at(self.sp), args)
    }
}

/// `Spec(cc, m) -> M (cc S ++ if t e) N R k z s mu = choose m (M t .. s mu) (M e .. s mu)`; `swap` states the arms swapped.
pub fn if_law(w: Wasm, swap: bool) -> (Expr, Expr) {
    let tys = if_tele(w, false);
    law(&tys, |c, x| {
        let n = if_names(x, false);
        let (l, r) = (n.lhs(w, c, false), n.rhs(w, c, swap));
        (n.law_proof(w, c), id(c.at(n.r), l, r))
    })
}

/// `Spec(cc, m) -> GoodBv m -> Q (M t .. s mu) -> Q (M e .. s mu) -> Q (M (cc S ++ if t e) .. s mu)`: the If law,
/// transported, of `if_inv`. `swap` states it for `if e t`.
pub fn if_good(w: Wasm, swap: bool) -> (Expr, Expr) {
    let tys = if_tele(w, true);
    law(&tys, |c, x| {
        let n = if_names(x, true);
        let (q, r) = (n.q.unwrap(), n.r);
        let (l, rh, p) = (n.lhs(w, c, false), n.rhs(w, c, false), n.law_proof(w, c));
        let stmt = app(c.at(q), if swap { n.lhs(w, c, true) } else { l });
        let proof = {
            // J at `\x y _. Q y -> Q x` takes `Q rhs` to `Q lhs`
            let motive = c.lam(c.at(r), |c, a| {
                c.lam(c.at(r), |c, b| {
                    let e = id(c.at(r), c.at(a), c.at(b));
                    c.lam(e, |c, _| arrow(app(c.at(q), c.at(b)), app(c.at(q), c.at(a))))
                })
            });
            let base = c.lam(c.at(r), |c, a| c.lam(app(c.at(q), c.at(a)), |c, h| c.at(h)));
            let (qt, qe) = n.qs.unwrap();
            let (t_ans, e_ans) = (n.arm(w, c, n.th), n.arm(w, c, n.el));
            let split = apps(if_inv(Ctl::Ok).0, vec![c.at(r), c.at(q), c.at(n.m), c.at(n.gm.unwrap()), t_ans, e_ans, c.at(qt), c.at(qe)]);
            app(jelim(motive, base, l, rh, p), split)
        };
        (proof, stmt)
    })
}

/// `GoodNat N -> (Pi s mu. I s -> Q z) -> (Pi f. Good f -> Good (B f)) -> Good (N (G A) (\s mu. z) B)`: fixpoint
/// induction over fuel, for an invariant `I : A -> Sort3` and a postcondition `Q : R -> Sort0`.
pub fn loop_law(w: Wasm) -> (Expr, Expr) {
    // A R I Q z B N gn hz hs
    let tys: Vec<Ty> = vec![
        ty!(|_c, _x| sort(2)),
        ty!(|_c, _x| sort(0)),
        ty!(|c, x| arrow(c.at(x[0]), sort(3))),
        ty!(|c, x| arrow(c.at(x[1]), sort(0))),
        ty!(|c, x| c.at(x[1])),
        ty!(|c, x| { let g = w.g(c, x[1], c.at(x[0])); arrow(g, g) }),
        ty!(|_c, _x| nat2()),
        ty!(|c, x| w.good_nat(c, x[6])),
        ty!(|c, x| { let t = timeout(w, c, x[0], x[1], x[4]); let z = c.mark(t); w.good(c, x[0], x[1], x[2], x[3], z) }),
        ty!(|c, x| {
            let g = w.g(c, x[1], c.at(x[0]));
            c.pi(g, |c, f| {
                let gf = w.good(c, x[0], x[1], x[2], x[3], f);
                let bf = c.mark(app(c.at(x[5]), c.at(f)));
                let gbf = w.good(c, x[0], x[1], x[2], x[3], bf);
                arrow(gf, gbf)
            })
        }),
    ];
    let unrolled = |c: &mut Cx, x: &[At], m: At| {
        let g = w.g(c, x[1], c.at(x[0]));
        let to = timeout(w, c, x[0], x[1], x[4]);
        c.mark(apps(c.at(m), vec![g, to, c.at(x[5])]))
    };
    law(&tys, |c, x| {
        let f = unrolled(c, x, x[6]);
        let stmt = w.good(c, x[0], x[1], x[2], x[3], f);
        let motive = c.lam(nat2(), |c, m| {
            let f = unrolled(c, x, m);
            w.good(c, x[0], x[1], x[2], x[3], f)
        });
        let step = c.lam(nat2(), |c, j| {
            let f = unrolled(c, x, j);
            let gf = w.good(c, x[0], x[1], x[2], x[3], f);
            c.lam(gf, |c, ih| apps(c.at(x[9]), vec![c.at(f), c.at(ih)]))
        });
        (apps(c.at(x[7]), vec![motive, c.at(x[8]), step]), stmt)
    })
}
fn timeout(w: Wasm, c: &mut Cx, a: At, r: At, z: At) -> Expr {
    c.lam(c.at(a), |c, _| {
        let m = w.mem(c, r);
        c.lam(m, |c, _| c.at(z))
    })
}

/// `loop L { dup; push 1; lt; if {} {push 1; <dec>; br L} }`: count the top word down to 0 (`dec` = `sub`).
pub fn countdown(dec: Op) -> Vec<Ins> {
    vec![Ins::Loop(vec![Ins::Dup, Ins::Push(1), Ins::Op(Op::LtU), Ins::If(vec![], vec![Ins::Push(1), Ins::Op(dec), Ins::Br(0)])])]
}

/// An `if` inside a loop: for every fuel with `GoodNat` and every start word with `GoodBv`, the countdown answers
/// `Q` if the timeout does and the exit continuation does on every good word:
/// `Pi S N. GoodNat N -> Pi R Q k z. Q z -> (Pi x s mu. GoodBv x -> Q (k (x,s) mu)) -> Pi x s mu. GoodBv x -> Q (M cd ..)`.
/// The invariant carries `GoodBv` of the counter, which the `if` needs and `good_sub` keeps. `dec` replaces the
/// decrement in the program only (a control).
pub fn countdown_law(w: Wasm, dec: Op) -> (Expr, Expr) {
    let n = w.n;
    let code = countdown(dec);
    // S N gn R Q k z hz hk x s mu gx
    let tys: Vec<Ty> = vec![
        ty!(|_c, _x| sort(2)),
        ty!(|_c, _x| nat2()),
        ty!(|c, x| w.good_nat(c, x[1])),
        ty!(|_c, _x| sort(0)),
        ty!(|c, x| arrow(c.at(x[3]), sort(0))),
        ty!(|c, x| { let t = w.sty(c, &[K::W], x[0]); w.g(c, x[3], t) }),
        ty!(|c, x| c.at(x[3])),
        ty!(|c, x| app(c.at(x[4]), c.at(x[6]))),
        ty!(|c, x| {
            c.pi(w.v(), |c, xv| {
                c.pi(c.at(x[0]), |c, s| {
                    let m = w.mem(c, x[3]);
                    c.pi(m, |c, mu| {
                        let ans = app2(c.at(x[5]), mkpair(c.at(x[0]), c.at(xv), c.at(s)), c.at(mu));
                        arrow(app(good_bv(n), c.at(xv)), app(c.at(x[4]), ans))
                    })
                })
            })
        }),
        ty!(|_c, _x| bv_ty(n)),
        ty!(|c, x| c.at(x[0])),
        ty!(|c, x| w.mem(c, x[3])),
        ty!(|c, x| app(good_bv(n), c.at(x[9]))),
    ];
    law(&tys, |c, x| {
        let p = w.prog(c, &code, &[K::W], x[0]);
        let p = c.mark(p);
        let m = w.meaning(c, p, x[1], x[3], x[5], x[6]);
        let stmt = app(c.at(x[4]), app2(m, mkpair(c.at(x[0]), c.at(x[9]), c.at(x[10])), c.at(x[11])));
        let proof = {
            let (s_ty, r, q, k) = (x[0], x[3], x[4], x[5]);
            // `M cd` is `N (G A) timeout B`: take `B`
            let body = match whnf(&m).node() {
                tatic_kernel::Node::App(_, b) => c.mark(b),
                other => panic!("countdown's meaning is not a fuel application: {other:?}"),
            };
            let a = c.mark(w.sty(c, &[K::W], s_ty));
            let inv = c.lam(c.at(a), |c, st| {
                let motive = c.lam(c.at(a), |_c, _| sort(3));
                let step = c.lam(w.v(), |c, xv| c.lam(c.at(s_ty), |c, _| app(good_bv(n), c.at(xv))));
                sigrec(motive, step, c.at(st))
            });
            let inv = c.mark(inv);
            let hz = c.lam(c.at(a), |c, s| {
                let m = w.mem(c, r);
                c.lam(m, |c, _| c.lam(app(c.at(inv), c.at(s)), |c, _| c.at(x[7])))
            });
            let g = w.g(c, r, c.at(a));
            let hs = c.lam(g, |c, f| {
                let gf = w.good(c, a, r, inv, q, f);
                c.lam(gf, |c, ih| {
                    c.lam(c.at(a), |c, st| {
                        let motive = c.lam(c.at(a), |c, st| {
                            let m = w.mem(c, r);
                            c.pi(m, |c, mu| {
                                let ans = apps(c.at(body), vec![c.at(f), c.at(st), c.at(mu)]);
                                arrow(app(c.at(inv), c.at(st)), app(c.at(q), ans))
                            })
                        });
                        let step = c.lam(w.v(), |c, xv| {
                            c.lam(c.at(s_ty), |c, s| {
                                let m = w.mem(c, r);
                                c.lam(m, |c, mu| {
                                    let i = app(c.at(inv), mkpair(c.at(s_ty), c.at(xv), c.at(s)));
                                    c.lam(i, |c, gx| {
                                        let (xe, se, mue) = (c.at(xv), c.at(s), c.at(mu));
                                        let one = lit(n, 1);
                                        let cond = app2(lt_u(n), xe, one);
                                        let g_cond = apps(good_lt(n).0, vec![xe, one, c.at(gx), good_lit(n, 1)]);
                                        let dec = app2(sub(n), xe, one);
                                        let g_dec = apps(good_sub(n).0, vec![xe, one, c.at(gx), good_lit(n, 1)]);
                                        let exit = app2(c.at(k), mkpair(c.at(s_ty), xe, se), mue);
                                        let again = app2(c.at(f), mkpair(c.at(s_ty), dec, se), mue);
                                        let h_exit = apps(c.at(x[8]), vec![xe, se, mue, c.at(gx)]);
                                        let h_again = apps(c.at(ih), vec![mkpair(c.at(s_ty), dec, se), mue, g_dec]);
                                        apps(if_inv(Ctl::Ok).0, vec![c.at(r), c.at(q), cond, g_cond, exit, again, h_exit, h_again])
                                    })
                                })
                            })
                        });
                        sigrec(motive, step, c.at(st))
                    })
                })
            });
            let args = vec![c.at(a), c.at(r), c.at(inv), c.at(q), c.at(x[6]), c.at(body), c.at(x[1]), c.at(x[2]), hz, hs,
                mkpair(c.at(s_ty), c.at(x[9]), c.at(x[10])), c.at(x[11]), c.at(x[12])];
            apps(loop_law(w).0, args)
        };
        (proof, stmt)
    })
}

/// `Pi S R k z s mu. Id(R, M p fuel R k z (start..s) mu, want)`, by `refl`: a concrete run.
fn run_by_refl(w: Wasm, code: &[Ins], start: &[u128], fuel: usize, want: &dyn Fn(&mut Cx, &[At]) -> Expr) -> (Expr, Expr) {
    let ks: Vec<K> = start.iter().map(|_| K::W).collect();
    let out = out_stack(code, ks.clone()).unwrap();
    let tys: Vec<Ty> = vec![
        ty!(|_c, _x| sort(2)),
        ty!(|_c, _x| sort(0)),
        ty!(|c, x| { let t = w.sty(c, &out, x[0]); w.g(c, x[1], t) }),
        ty!(|c, x| c.at(x[1])),
        ty!(|c, x| c.at(x[0])),
        ty!(|c, x| w.mem(c, x[1])),
    ];
    law(&tys, |c, x| {
        let p = w.prog(c, code, &ks, x[0]);
        let p = c.mark(p);
        let fuel = c.mark(nat2_lit(fuel));
        let st = start.iter().rev().fold(c.at(x[4]), |acc, v| mkpair(c.at(x[0]), lit(w.n, *v), acc));
        let l = app2(w.meaning(c, p, fuel, x[1], x[2], x[3]), st, c.at(x[5]));
        (refl(l), id(c.at(x[1]), l, want(c, x)))
    })
}

#[test]
pub fn wasm_programs_as_kernel_data() {
    tatic_kernel::scoped(|| run_wasm_checks(Wasm { n: 4 }, true))
}

/// The countdown invariant at n=24 stays fast. Without `conv`'s pair memo it walked a shared case tree once per path
/// (docs/tier-cycle/, "The countdown invariant was exponential"; n=32 took over 600 s).
#[test]
pub fn countdown_invariant_is_not_exponential() {
    let n = 24;
    tatic_kernel::scoped(|| {
        let (p, s) = countdown_law(Wasm { n }, Op::Sub);
        let t0 = Instant::now();
        ck("countdown invariant n=24", &p, &s);
        assert!(t0.elapsed().as_secs_f64() < 2.0, "countdown invariant took {:?}", t0.elapsed());
    })
}

/// Every law and run, with controls; prints check times (`WASM` lines).
pub fn run_wasm_checks(w: Wasm, controls: bool) {
    let n = w.n;
    let timed = |name: &str, (p, s): (Expr, Expr)| {
        let t0 = Instant::now();
        ck(&format!("{name} n={n}"), &p, &s);
        println!("WASM n={n} {name}: {:?}", t0.elapsed());
    };
    // a control's statement must be a type, so its rejection is the proof's
    let rejected = |name: &str, (p, s): (Expr, Expr)| {
        let sort_of = infer(&Ctx::new(), &s).map(|t| whnf(&t));
        assert!(matches!(sort_of.as_ref().map(|t| t.node()), Ok(tatic_kernel::Node::Sort(_))), "{name}: statement is not a type: {sort_of:?}");
        assert!(holds(&p, &s).is_err(), "{name} must be rejected at n={n}");
    };
    timed("if_inv", if_inv(Ctl::Ok));
    timed("append", append_law(w));
    timed("if law", if_law(w, false));
    timed("if invariant", if_good(w, false));
    timed("loop law", loop_law(w));
    timed("countdown invariant", countdown_law(w, Op::Sub));
    // concrete runs: the countdown from 3 exits at 0 with fuel 4 and times out with fuel 3; store then load
    let at = |v: u128| move |c: &mut Cx, x: &[At]| app2(c.at(x[2]), mkpair(c.at(x[0]), lit(n, v), c.at(x[4])), c.at(x[5]));
    timed("countdown 3, fuel 4", run_by_refl(w, &countdown(Op::Sub), &[3], 4, &at(0)));
    timed("countdown 3, fuel 3", run_by_refl(w, &countdown(Op::Sub), &[3], 3, &|c, x| c.at(x[3])));
    let mem_prog = [Ins::Push(3), Ins::Push(5), Ins::Store, Ins::Push(3), Ins::Load];
    let stored = |c: &mut Cx, x: &[At]| {
        let mu = w.upd(c, x[1], lit(n, 3), lit(n, 5), c.at(x[5]));
        app2(c.at(x[2]), mkpair(c.at(x[0]), lit(n, 5), c.at(x[4])), mu)
    };
    timed("store 5@3, load 3", run_by_refl(w, &mem_prog, &[], 0, &stored));
    if controls {
        rejected("if_inv, false leaf given Q x", if_inv(Ctl::SameLeaf));
        rejected("if_inv, no lowering", if_inv(Ctl::NoLower));
        rejected("if_inv, claims Q x", if_inv(Ctl::ClaimsX));
        rejected("if law, arms swapped", if_law(w, true));
        rejected("if invariant, arms swapped", if_good(w, true));
        rejected("countdown with add for sub", countdown_law(w, Op::Add));
        rejected("countdown 3, fuel 4, answers 1", run_by_refl(w, &countdown(Op::Sub), &[3], 4, &at(1)));
        rejected("countdown 3, fuel 3, exits", run_by_refl(w, &countdown(Op::Sub), &[3], 3, &at(0)));
    }
}

/// `WASM` check times at n = 4, 16, 32, 64, with the controls at 64.
#[test]
#[ignore]
pub fn wasm_scaling() {
    for n in [4usize, 16, 32, 64] {
        tatic_kernel::scoped(|| run_wasm_checks(Wasm { n }, n == 64))
    }
}
