//! The generator of simulation proofs (untrusted; `statement.rs` states what it proves, and the kernel is the judge).
//!
//! The proof of an entry's law (`statement.rs`) is `GoodNat`'s induction on the fuel. In the step both sides are put in
//! weak head normal form and walked in lockstep as kernel terms (`Sim::sim`), with no match on the instruction list or
//! the function:
//!   - `km a mu` against `ks a'`: the relation hypothesis;
//!   - `CH R w t e` against `CH R w' t' e'` (`CH` is the probe standing for `choose`): J through the shared choice;
//!   - a read of a local is the frame's projection, which reduces (the frame is a concrete nested pair);
//!   - a fuel variable applied to a function's `H`, `timeout`, `Bm`, a frame, a memory and a continuation (a `Call`, tail
//!     or not, of the entry itself or of a callee; ONE rule, through the induction's `j` for the entry and the outer fuel
//!     `N` for a callee): that function's LAW (the induction hypothesis, or the callee's law, a hypothesis of this proof)
//!     at the arguments read off the source side, the frame's slots having been checked against them and its padding
//!     against 0. A callee's law enters its caller's proof only as a hypothesis; `closed` discharges it with the
//!     callee's own proof.
//!
//! `CH` is a bound variable of the proof only: the statement uses the real `choose`, and `prove` applies the proof to it.
use super::statement::{callees, head_tys, widen, Ctxt, ModEntry, G};
use super::*;
use std::cell::RefCell;

/// `CH : Pi R:Sort0. Bv1 -> R -> R -> R`.
fn ch_ty() -> Expr {
    pi(sort(0), arrow(bv_ty(1), arrow(var(0), arrow(var(0), var(0)))))
}

/// The closed lemma `\R CH w t t' (pt : Id(R, t, t')) e e' (pe : Id(R, e, e')). Id(R, CH R w t e, CH R w t' e')`: J on each
/// branch. It has no free variable, so applying it (`cong`) shifts none of its arguments under its binders: the proofs
/// `pt` and `pe` (and the branches) stay one shared term at the walk's depth instead of a shifted copy per level of a
/// chain of branches (each copy a new node, the proof of a chain of `d` branches `d^2` nodes).
fn cong_lemma() -> Expr {
    Cx::default().lam(sort(0), |c, r| {
        c.lam(ch_ty(), |c, ch| {
            c.lam(bv_ty(1), |c, cd| {
                c.lam(c.at(r), |c, t| {
                    c.lam(c.at(r), |c, t2| {
                        let pt_ty = id(c.at(r), c.at(t), c.at(t2));
                        c.lam(pt_ty, |c, pt| {
                            c.lam(c.at(r), |c, e| {
                                c.lam(c.at(r), |c, e2| {
                                    let pe_ty = id(c.at(r), c.at(e), c.at(e2));
                                    c.lam(pe_ty, |c, pe| cong_body(c, (r, ch, cd), (t, t2, pt), (e, e2, pe)))
                                })
                            })
                        })
                    })
                })
            })
        })
    })
}

/// `cong_lemma`'s body, J on the then side and then on the else side.
fn cong_body(c: &mut Cx, (r, ch, cd): (At, At, At), (t, t2, pt): (At, At, At), (e, e2, pe): (At, At, At)) -> Expr {
    let pick = |c: &Cx, x: Expr, y: Expr| apps(c.at(ch), vec![c.at(r), c.at(cd), x, y]);
    let outer_m = c.lam(c.at(r), |c, a| {
        c.lam(c.at(r), |c, b| {
            let ty = id(c.at(r), c.at(a), c.at(b));
            c.lam(ty, |c, _| id(c.at(r), pick(c, c.at(a), c.at(e)), pick(c, c.at(b), c.at(e2))))
        })
    });
    let outer_b = c.lam(c.at(r), |c, a| {
        let inner_m = c.lam(c.at(r), |c, y| {
            c.lam(c.at(r), |c, y2| {
                let ty = id(c.at(r), c.at(y), c.at(y2));
                c.lam(ty, |c, _| id(c.at(r), pick(c, c.at(a), c.at(y)), pick(c, c.at(a), c.at(y2))))
            })
        });
        let inner_b = c.lam(c.at(r), |c, y| refl(pick(c, c.at(a), c.at(y))));
        jelim(inner_m, inner_b, c.at(e), c.at(e2), c.at(pe))
    });
    jelim(outer_m, outer_b, c.at(t), c.at(t2), c.at(pt))
}

/// `Id(R, CH R w t e, CH R w t' e')` from `Id(R, t, t')` and `Id(R, e, e')`: the lemma applied at the walk's depth.
fn cong(c: &Cx, r: At, ch: At, cd: At, (t, t2, pt): (Expr, Expr, Expr), (e, e2, pe): (Expr, Expr, Expr)) -> Expr {
    apps(cong_lemma(), vec![c.at(r), c.at(ch), c.at(cd), t, t2, pt, e, e2, pe])
}

/// `e` as a head and its arguments.
fn spine(e: &Expr) -> (Expr, Vec<Expr>) {
    let (mut args, mut cur) = (vec![], *e);
    while let tatic_kernel::Node::App(f, a) = cur.node() {
        args.push(a);
        cur = f;
    }
    args.reverse();
    (cur, args)
}

/// What `prove` checks of a body before generating anything: a list the machine runs from `[]` to `[word]`, its calls
/// naming positions of the module.
fn check_code(table: &Table, code: &[Ins], arities: &[Option<usize>]) -> Result<(), String> {
    if !well_formed(table, code, &[], arities) || out_stack(table, code, vec![], arities) != vec![K::W] {
        return Err("the body does not run from [] to [word]".into());
    }
    Ok(())
}

/// What the walk needs of a function it may meet called: the fuel variable it is applied through (the induction's `j`
/// for the entry itself, the outer fuel `N` for a callee), its sizes, its `Bm` and `Bs`, and its law (the induction
/// hypothesis, or the callee's law hypothesis).
#[derive(Clone, Copy)]
struct CallRule<'t> {
    head: At,
    g: G<'t>,
    bm: At,
    bs: At,
    law: At,
}

/// The proof of entry `k`'s law with the probe `CH` as its first parameter and the callees' laws as hypotheses:
/// `\CH N gn R z HC.. d x.. mu km ks rel. ..`, or why the two sides do not simulate each other.
fn proof_open(w: Machine, module: &[Option<ModEntry>], k: usize) -> Result<Expr, String> {
    let e = module.get(k).and_then(|e| e.as_ref()).ok_or_else(|| format!("no module entry at position {k}"))?;
    let arities: Vec<Option<usize>> = module.iter().map(|e| e.as_ref().map(|e| e.entry.arity)).collect();
    check_code(w.table, &e.entry.code, &arities)?;
    let g = G::fixed(w, e.entry.arity);
    let m = g.m;
    let cs = callees(k, &e.entry.code);
    let err: RefCell<Option<String>> = RefCell::new(None);
    let tys = head_tys(w, module, &cs, true);
    let proof = Cx::default().lam(ch_ty(), |c, ch| {
        tele(c, &tys, &mut vec![], &lam, &mut |c, x| {
            let (fuel, gn, r, z) = (x[0], x[1], x[2], x[3]);
            let cx = Ctxt::new(c, w, module, fuel, r, z);
            let rules: Vec<CallRule> = cs
                .iter()
                .zip(&x[4..])
                .map(|(p, hc)| {
                    let re = cx.real(c, *p);
                    CallRule { head: fuel, g: cx.g(*p), bm: re.bm, bs: re.bs, law: *hc }
                })
                .collect();
            let (hm, tm) = (cx.hm, cx.tm);
            let (bm0, bs0) = cx.bm_bs(c, k, Some(ch));
            let (bm, bs) = (c.mark(bm0), c.mark(bs0));
            let (hs0, ts0) = (g.hs(c, r), g.ts(c, r, z));
            let (hs, ts) = (c.mark(hs0), c.mark(ts0));
            g.binders(c, r, &lam, &mut |c, y| {
                // the motive at a fuel: the binders, then the two sides
                let mot = |c: &mut Cx, mm: Expr| {
                    let mm = c.mark(mm);
                    g.binders(c, r, &pi, &mut |c, y| {
                        let ya: Vec<Expr> = y[1..1 + m].iter().map(|a| c.at(*a)).collect();
                        let (mu, kmm, kss) = (y[1 + m], y[2 + m], y[3 + m]);
                        let l = app3(apps(c.at(mm), vec![c.at(hm), c.at(tm), c.at(bm)]), g.frame(&ya), c.at(mu), c.at(kmm));
                        let rhs = apps(c.at(mm), [vec![c.at(hs), c.at(ts), c.at(bs)], ya, vec![c.at(kss)]].concat());
                        id(c.at(r), l, rhs)
                    })
                };
                let motive = c.lam(nat2(), |c, mm| mot(c, c.at(mm)));
                let hz = g.binders(c, r, &lam, &mut |c, _| refl(c.at(z)));
                let step = c.lam(nat2(), |c, j| {
                    let ih_ty = mot(c, c.at(j));
                    c.lam(ih_ty, |c, ih| {
                        g.binders(c, r, &lam, &mut |c, y| {
                            // the entry itself is a call like any callee's: through `j`, with the hypothesis for its law
                            let own = CallRule { head: j, g, bm, bs, law: ih };
                            let all_rules: Vec<CallRule> = std::iter::once(own).chain(rules.iter().copied()).collect();
                            let sim = Sim { g: &g, r, ch, d: y[0], km: y[2 + m], ks: y[3 + m], rel: y[4 + m], rules: &all_rules };
                            let ya: Vec<Expr> = y[1..1 + m].iter().map(|a| c.at(*a)).collect();
                            let fr = g.frame(&ya);
                            let mj = apps(c.at(j), vec![c.at(hm), c.at(tm), c.at(bm)]);
                            let sj = apps(c.at(j), vec![c.at(hs), c.at(ts), c.at(bs)]);
                            let m0 = apps(c.at(bm), vec![mj, fr, c.at(y[1 + m]), c.at(y[2 + m])]);
                            let s0 = apps(c.at(bs), [vec![sj], ya, vec![c.at(y[3 + m])]].concat());
                            match sim.sim(c, m0, s0, "body") {
                                Ok(p) => p,
                                Err(e) => {
                                    err.borrow_mut().get_or_insert(e);
                                    refl(m0)
                                }
                            }
                        })
                    })
                });
                let mut all = vec![motive, hz, step];
                all.extend(y.iter().map(|a| c.at(*a)));
                apps(c.at(gn), all)
            })
        })
    });
    match err.into_inner() {
        Some(e) => Err(e),
        None => Ok(proof),
    }
}

/// The closed proof of entry `k`'s law, `Pi N gn R z, law_k`: the probe applied to the real `choose`, every callee's
/// law discharged by that callee's own closed proof (at the module's frame width). `path` holds the entries being
/// proved, so a cycle of calls is refused.
fn closed(w: Machine, module: &[Option<ModEntry>], k: usize, path: &mut Vec<usize>) -> Result<Expr, String> {
    if path.contains(&k) {
        return Err(format!("the module's calls form a cycle through position {k}"));
    }
    let open = app(proof_open(w, module, k)?, choose_fn());
    let e = module[k].as_ref().expect("proof_open found the entry");
    let cs = callees(k, &e.entry.code);
    path.push(k);
    let closed_callees: Vec<Expr> = cs.iter().map(|p| closed(w, module, *p, path)).collect::<Result<_, _>>()?;
    path.pop();
    let tys = head_tys(w, module, &cs, false);
    Ok(tele(&mut Cx::default(), &tys, &mut vec![], &lam, &mut |c, x| {
        let nzs: Vec<At> = x.to_vec();
        let mut all: Vec<Expr> = nzs.iter().map(|a| c.at(*a)).collect();
        for (p, cl) in cs.iter().zip(&closed_callees) {
            let gc = G::fixed(w, module[*p].as_ref().expect("proof_open found the callee").entry.arity);
            let law = gc.binders(c, nzs[2], &lam, &mut |c, y| {
                apps(*cl, [nzs.iter().map(|a| c.at(*a)).collect::<Vec<_>>(), y.iter().map(|a| c.at(*a)).collect()].concat())
            });
            all.push(law);
        }
        apps(open, all)
    }))
}

/// The proof of the statement `statement::statement(m, module, entry)`: `Pi N gn R z, law_entry`, the probe applied to
/// the real `choose`. `Err` names where the machine and the source part ways, or why the body is out of the walk's
/// reach; the kernel decides whether an `Ok` proof holds.
pub fn prove(m: &Machine, module: &[Option<ModEntry>], entry: usize) -> Result<Expr, String> {
    let w = widen(m, module);
    closed(w, module, entry, &mut vec![])
}

/// One walk's fixed names.
struct Sim<'g, 't> {
    g: &'g G<'t>,
    r: At,
    ch: At,
    /// The walk's own copy of the lifting numeral every law and the induction hypothesis take first.
    d: At,
    km: At,
    ks: At,
    rel: At,
    /// The functions the walk may meet called: the entry itself first, then its callees.
    rules: &'g [CallRule<'t>],
}

impl Sim<'_, '_> {
    /// What a term in weak head normal form is doing, for the reasons.
    fn kind(&self, c: &Cx, head: &Expr) -> &'static str {
        if *head == c.at(self.km) || *head == c.at(self.ks) {
            "returns"
        } else if *head == c.at(self.ch) {
            "branches"
        } else if self.rules.iter().any(|rl| *head == c.at(rl.head)) {
            "calls a function"
        } else {
            "is stuck"
        }
    }

    /// A proof of `Id(R, m, s)`.
    fn sim(&self, c: &mut Cx, m: Expr, s: Expr, path: &str) -> Result<Expr, String> {
        tatic_kernel::grow(|| self.sim_step(c, m, s, path))
    }

    /// The `fw` words of a frame, read off its pair spine.
    fn slots(&self, fr: Expr, path: &str) -> Result<Vec<Expr>, String> {
        let (mut cur, mut xs) = (fr, vec![]);
        for _ in 0..self.g.w.fw {
            let tatic_kernel::Node::Pair(_, x, rest) = whnf(&cur).node() else {
                return Err(format!("{path}: the frame is not a pair spine of the module's width"));
            };
            xs.push(x);
            cur = rest;
        }
        Ok(xs)
    }

    /// `Pi a mu. Id(R, k2 a mu, ks2 a)`, from walking the two continuations under their binders.
    fn cont_rel(&self, c: &mut Cx, k2: Expr, ks2: Expr, path: &str) -> Result<Expr, String> {
        let (k2m, ks2m) = (c.mark(k2), c.mark(ks2));
        let failed: RefCell<Option<String>> = RefCell::new(None);
        let w = self.g.w;
        let rel2 = c.lam(self.g.v(), |c, a| {
            let mem = w.mem(c, self.r);
            c.lam(mem, |c, mu| {
                let (l, r) = (app2(c.at(k2m), c.at(a), c.at(mu)), app(c.at(ks2m), c.at(a)));
                match self.sim(c, l, r, &format!("{path}/after")) {
                    Ok(p) => p,
                    Err(e) => {
                        failed.borrow_mut().get_or_insert(e);
                        refl(l)
                    }
                }
            })
        });
        match failed.into_inner() {
            Some(e) => Err(e),
            None => Ok(rel2),
        }
    }

    fn sim_step(&self, c: &mut Cx, m: Expr, s: Expr, path: &str) -> Result<Expr, String> {
        let n = self.g.w.n;
        let (mw, sw) = (whnf(&m), whnf(&s));
        let ((mh, ma), (sh, sa)) = (spine(&mw), spine(&sw));
        let (mk, sk) = (self.kind(c, &mh), self.kind(c, &sh));

        if mh == c.at(self.km) {
            if sh != c.at(self.ks) {
                return Err(format!("{path}: the machine {mk} but the source {sk}"));
            }
            if ma.len() != 2 || sa.len() != 1 || !def_eq(&ma[0], &sa[0]) {
                return Err(format!("{path}: both return, with different values"));
            }
            return Ok(apps(c.at(self.rel), vec![ma[0], ma[1]]));
        }
        if mh == c.at(self.ch) {
            if sh != c.at(self.ch) || ma.len() != 4 || sa.len() != 4 {
                return Err(format!("{path}: the machine {mk} but the source {sk}"));
            }
            if !def_eq(&ma[1], &sa[1]) {
                return Err(format!("{path}: the branch conditions differ"));
            }
            let pt = self.sim(c, ma[2], sa[2], &format!("{path}/then"))?;
            let pe = self.sim(c, ma[3], sa[3], &format!("{path}/else"))?;
            let cd = c.mark(ma[1]);
            return Ok(cong(c, self.r, self.ch, cd, (ma[2], sa[2], pt), (ma[3], sa[3], pe)));
        }
        // a call (of the entry itself or of a callee): `F H timeout Bm_c frame mu kont` against `F Hs ts Bs_c args ks'`,
        // answered by the law of `c` at the arguments read off the source
        if self.rules.iter().any(|rl| mh == c.at(rl.head)) {
            if ma.len() != 6 {
                return Err(format!("{path}: the machine {mk} with {} arguments", ma.len()));
            }
            let Some(rule) = self.rules.iter().find(|rl| mh == c.at(rl.head) && def_eq(&ma[2], &c.at(rl.bm))) else {
                return Err(format!("{path}: the machine calls a function that is neither this one nor one of its callees"));
            };
            let mc = rule.g.m;
            if sh != c.at(rule.head) || sa.len() != 3 + mc + 1 || !def_eq(&sa[2], &c.at(rule.bs)) {
                return Err(format!("{path}: the machine calls a function but the source {sk} (or another function, or another arity)"));
            }
            let (fr2, mu2, k2, ks2) = (ma[3], ma[4], ma[5], sa[sa.len() - 1]);
            let src_args = &sa[3..3 + mc];
            // the frame: each parameter slot holds the source's argument, the padding 0
            let slots = self.slots(fr2, path)?;
            for (i, a) in src_args.iter().enumerate() {
                if !def_eq(&slots[i], a) {
                    return Err(format!("{path}: at the call, local {i} does not hold the source's argument {i} (order or values)"));
                }
            }
            let zero = lit(n, 0);
            if let Some(i) = (mc..slots.len()).find(|i| !def_eq(&slots[*i], &zero)) {
                return Err(format!("{path}: at the call, padding slot {i} is not 0"));
            }
            let rel2 = self.cont_rel(c, k2, ks2, path)?;
            let mut all = vec![c.at(self.d)];
            all.extend_from_slice(src_args);
            all.extend([mu2, k2, ks2, rel2]);
            return Ok(apps(c.at(rule.law), all));
        }
        Err(format!("{path}: the machine {mk} but the source {sk}"))
    }
}

#[cfg(test)]
mod tests;
