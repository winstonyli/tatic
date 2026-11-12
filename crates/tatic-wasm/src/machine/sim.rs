//! The generator of simulation proofs (untrusted; `statement.rs` states what it proves, and the kernel is the judge).
//!
//! The proof of an entry's law (`statement.rs`) is `GoodNat`'s induction on the fuel. In the step both sides are put in
//! weak head normal form and walked in lockstep as kernel terms (`Sim::sim`), with no match on the instruction list or
//! the function:
//!   - `km a mu` against `ks a'`: the relation hypothesis;
//!   - `CH R w t e` against `CH R w' t' e'` (`CH` is the probe standing for `choose`): J through the shared choice;
//!   - a read of a local is the frame's projection, which reduces (the frame is a concrete nested pair).
//!
//! There is no call rule yet: a body holding a `Call` is refused. `CH` is a bound variable of the proof only: the
//! statement uses the real `choose`, and `prove` applies the proof to it.
use super::statement::{head_tys, widen, Ctxt, ModEntry, G};
use super::*;
use std::cell::RefCell;

/// `CH : Pi R:Sort0. Bv1 -> R -> R -> R`.
fn ch_ty() -> Expr {
    pi(sort(0), arrow(bv_ty(1), arrow(var(0), arrow(var(0), var(0)))))
}
/// The real choice, `\R w x y. choose R w x y`.
fn choose_fn() -> Expr {
    Cx::default().lam(sort(0), |c, r| {
        c.lam(bv_ty(1), |c, w| {
            c.lam(c.at(r), |c, x| c.lam(c.at(r), |c, y| choose(c.at(r), c.at(w), c.at(x), c.at(y))))
        })
    })
}

/// `Id(R, CH R w t e, CH R w t' e')` from `Id(R, t, t')` and `Id(R, e, e')`: J on each branch.
fn cong(c: &mut Cx, r: At, ch: At, cd: At, (t, t2, pt): (Expr, Expr, Expr), (e, e2, pe): (Expr, Expr, Expr)) -> Expr {
    let pick = |c: &Cx, x: Expr, y: Expr| apps(c.at(ch), vec![c.at(r), c.at(cd), x, y]);
    let (e, e2, pe) = (c.mark(e), c.mark(e2), c.mark(pe));
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
    jelim(outer_m, outer_b, t, t2, pt)
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

/// What `prove` checks of a body before generating anything: no call (no rule yet), and a list the machine runs from
/// `[]` to `[word]`.
fn check_code(table: &Table, code: &[Ins]) -> Result<(), String> {
    fn calls(code: &[Ins]) -> bool {
        code.iter().any(|i| match i {
            Ins::Call(_) => true,
            Ins::If(t, e) => calls(t) || calls(e),
            _ => false,
        })
    }
    if calls(code) {
        return Err("the body holds a call, which the walk has no rule for".into());
    }
    if !well_formed(table, code, &[], &[]) || out_stack(table, code, vec![], &[]) != vec![K::W] {
        return Err("the body does not run from [] to [word]".into());
    }
    Ok(())
}

/// The proof of entry `k`'s law with the probe `CH` as its first parameter: `\CH N gn R z d x.. mu km ks rel. ..`, or
/// why the two sides do not simulate each other.
fn proof_open(w: Machine, module: &[Option<ModEntry>], k: usize) -> Result<Expr, String> {
    let e = module.get(k).and_then(|e| e.as_ref()).ok_or_else(|| format!("no module entry at position {k}"))?;
    check_code(w.table, &e.entry.code)?;
    let g = G { w, m: e.entry.arity };
    let m = g.m;
    let err: RefCell<Option<String>> = RefCell::new(None);
    let tys = head_tys(w);
    let proof = Cx::default().lam(ch_ty(), |c, ch| {
        tele(c, &tys, &mut vec![], &lam, &mut |c, x| {
            let (fuel, gn, r, z) = (x[0], x[1], x[2], x[3]);
            let cx = Ctxt::new(c, w, module, fuel, r, z);
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
                    c.lam(ih_ty, |c, _ih| {
                        g.binders(c, r, &lam, &mut |c, y| {
                            let sim = Sim { r, ch, km: y[2 + m], ks: y[3 + m], rel: y[4 + m] };
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

/// The proof of the statement `statement::statement(m, module, entry)`: `Pi N gn R z, law_entry`, the probe applied to
/// the real `choose`. `Err` names where the machine and the source part ways, or why the body is out of the walk's
/// reach; the kernel decides whether an `Ok` proof holds.
pub fn prove(m: &Machine, module: &[Option<ModEntry>], entry: usize) -> Result<Expr, String> {
    let w = widen(m, module);
    let open = app(proof_open(w, module, entry)?, choose_fn());
    let tys = head_tys(w);
    Ok(tele(&mut Cx::default(), &tys, &mut vec![], &lam, &mut |c, x| apps(open, x.iter().map(|a| c.at(*a)).collect())))
}

/// One walk's fixed names.
struct Sim {
    r: At,
    ch: At,
    km: At,
    ks: At,
    rel: At,
}

impl Sim {
    /// What a term in weak head normal form is doing, for the reasons.
    fn kind(&self, c: &Cx, head: &Expr) -> &'static str {
        if *head == c.at(self.km) || *head == c.at(self.ks) {
            "returns"
        } else if *head == c.at(self.ch) {
            "branches"
        } else {
            "is stuck"
        }
    }

    /// A proof of `Id(R, m, s)`.
    fn sim(&self, c: &mut Cx, m: Expr, s: Expr, path: &str) -> Result<Expr, String> {
        tatic_kernel::grow(|| self.sim_step(c, m, s, path))
    }

    fn sim_step(&self, c: &mut Cx, m: Expr, s: Expr, path: &str) -> Result<Expr, String> {
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
        Err(format!("{path}: the machine {mk} but the source {sk}"))
    }
}

#[cfg(test)]
mod tests;
