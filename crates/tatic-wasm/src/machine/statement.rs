//! The one statement (D4; `docs/superpowers/specs/2026-11-10-v08-recursion-once-design.md`), trusted: what it means for
//! the machine's code of a module entry to simulate the entry's source, for every fuel.
//!
//! For fuel `N` with `GoodNat N`, every answer sort `R`, out-of-fuel answer `z`, arguments `a_i`, memory `mu`, machine
//! continuation `km` and source continuation `ks`, the LAW of an entry is
//!
//! ```text
//! (Pi a mu. km a mu = ks a) -> N H timeout Bm (frame a..) mu km = N Hs ts Bs a.. ks
//! ```
//!
//! `Bm = \env fr mu k. M (prog code) fr 0 mu`, the body's answer passed to `k`, is the machine's step; `N H timeout Bm`
//! unrolls it `N` times from `timeout` (`H = Fr -> Mem -> Ret -> R`, `Ret = V -> Mem -> R`). A `Call(j)` continues into
//! the module's table `\i fr mu k. (i == own) (env fr mu k) ((i == c) (N H timeout Bm_c fr mu k) .. z)`: the entry's own
//! position runs the `env` the fixpoint hands it, a callee its own fixpoint over the same fuel, anything else answers
//! `z`. `Bs = \g x.. ks. src`,
//! built by the entry's source closure (`SrcFn`) over the telescope's variables, is the source's step, unrolled the same
//! way (`Hs = V^m -> (V -> R) -> R`). Every law, the motive, the step and the hypothesis of the generator's induction
//! (`sim.rs`, untrusted) share ONE telescope `d, a.., mu, km, ks, rel`. `d` is a numeral binder that lifts the
//! induction motive to Sort3 (the kernel is not cumulative); it is vestigial in the statement. The frame is `Fr`, padded
//! with zeros to the module's width (the widest entry's arity).
//!
//! `statement` builds the proposition and `sim.rs` proves it; both take the same pieces from here, so the generator
//! cannot prove another statement than the one the kernel checks it against.
use super::*;
use std::cell::RefCell;

/// What a source builder is given: the answer sort `r`, the entry's own fixpoint variable `g`, its parameters, the probe
/// `ch` that stands for `choose` (the statement uses the real one: `None`), the outer fuel, the entry's own module
/// position and the callees' source functions (`S_N^c`, by module position).
pub struct SEnv {
    pub n: usize,
    pub r: At,
    pub g: At,
    pub params: Vec<At>,
    pub ch: Option<At>,
    pub fuel: At,
    pub own: usize,
    pub callees: Vec<(usize, At)>,
}

impl SEnv {
    /// `choose R cond t e`, through the probe in the proof.
    pub fn choose(&self, c: &Cx, cond: Expr, t: Expr, e: Expr) -> Expr {
        match self.ch {
            Some(h) => apps(c.at(h), vec![c.at(self.r), cond, t, e]),
            None => choose(c.at(self.r), cond, t, e),
        }
    }
    /// The function at module position `pos` applied to `args`, its answer passed to `k`: `g args (\res. k res)` for
    /// the entry itself (`pos == own`), `S_N^pos args (\res. k res)` for a callee.
    pub fn call(&self, c: &mut Cx, pos: usize, args: &[At], k: &dyn Fn(&mut Cx, Expr) -> Expr) -> Expr {
        let f = if pos == self.own {
            self.g
        } else {
            self.callees.iter().find(|(p, _)| *p == pos).unwrap_or_else(|| panic!("no callee at position {pos}")).1
        };
        let kont = c.lam(bv_ty(self.n), |c, res| k(c, c.at(res)));
        let mut xs: Vec<Expr> = args.iter().map(|a| c.at(*a)).collect();
        xs.push(kont);
        apps(c.at(f), xs)
    }
}

/// The source in continuation-passing form: given the environment and the final continuation, its meaning.
pub type SrcFn<'a> = dyn Fn(&mut Cx, &SEnv, &dyn Fn(&mut Cx, Expr) -> Expr) -> Expr + 'a;

/// One function of a module: its record and its source closure. Its table index is its position in the module's list.
pub struct ModEntry<'a> {
    pub entry: &'a Entry,
    pub src: &'a SrcFn<'a>,
}

/// The module's machine at its frame width: the widest entry's arity.
pub(super) fn widen<'t>(m: &Machine<'t>, module: &[Option<ModEntry>]) -> Machine<'t> {
    Machine { fw: module.iter().flatten().map(|e| e.entry.arity).max().unwrap_or(0), ..*m }
}

/// The sizes one entry is generated at: `m` parameters over the machine `w`.
#[derive(Clone, Copy)]
pub(super) struct G<'t> {
    pub w: Machine<'t>,
    pub m: usize,
}

impl G<'_> {
    pub fn v(&self) -> Expr {
        self.w.v()
    }
    /// `Ret = V -> Mem -> R`.
    pub fn ret_m(&self, c: &mut Cx, r: At) -> Expr {
        let mem = self.w.mem(c, r);
        arrow(self.v(), arrow(mem, c.at(r)))
    }
    /// `H = Fr -> Mem -> Ret -> R`.
    pub fn hm(&self, c: &mut Cx, r: At) -> Expr {
        let (mem, ret) = (self.w.mem(c, r), self.ret_m(c, r));
        arrow(self.w.fr(), arrow(mem, arrow(ret, c.at(r))))
    }
    pub fn ret_s(&self, c: &Cx, r: At) -> Expr {
        arrow(self.v(), c.at(r))
    }
    /// `Hs = V^m -> (V -> R) -> R`.
    pub fn hs(&self, c: &Cx, r: At) -> Expr {
        (0..self.m).fold(arrow(self.ret_s(c, r), c.at(r)), |acc, _| arrow(self.v(), acc))
    }
    /// `Pi a mu. Id(R, km a mu, ks a)`.
    pub fn rel_ty(&self, c: &mut Cx, r: At, km: At, ks: At) -> Expr {
        let w = self.w;
        c.pi(self.v(), |c, a| {
            let mem = w.mem(c, r);
            c.pi(mem, |c, mu| id(c.at(r), app2(c.at(km), c.at(a), c.at(mu)), app(c.at(ks), c.at(a))))
        })
    }
    /// The frame holding the parameters `args`, zeros after.
    pub fn frame(&self, args: &[Expr]) -> Expr {
        self.w.frame(args)
    }
    /// `timeout = \fr mu k. z`.
    pub fn tm(&self, c: &mut Cx, r: At, z: At) -> Expr {
        let w = self.w;
        c.lam(w.fr(), |c, _| {
            let mem = w.mem(c, r);
            c.lam(mem, |c, _| {
                let ret = self.ret_m(c, r);
                c.lam(ret, |c, _| c.at(z))
            })
        })
    }
    /// `ts = \x.. k. z`.
    pub fn ts(&self, c: &mut Cx, r: At, z: At) -> Expr {
        let n = self.w.n;
        let args: Vec<Ty> = (0..self.m).map(|_| ty!(|_c, _x| bv_ty(n))).collect();
        tele(c, &args, &mut vec![], &lam, &mut |c, _| {
            let rs = self.ret_s(c, r);
            c.lam(rs, |c, _| c.at(z))
        })
    }
    /// `Bm = \env fr mu k. M (prog code) fr 0 mu`, the body's answer passed to `k`; `ch` is the generator's probe, and
    /// `table` builds the module's callee environment from `env` (the entry's own fuel-unrolled step).
    pub fn bm(&self, c: &mut Cx, r: At, ch: Option<At>, code: &[Ins], arities: &[Option<usize>], table: &dyn Fn(&mut Cx, At) -> Expr) -> Expr {
        let (w, n) = (self.w, self.w.n);
        let hm = self.hm(c, r);
        c.lam(hm, |c, env| {
            c.lam(w.fr(), |c, fr| {
                let mem = w.mem(c, r);
                c.lam(mem, |c, mu| {
                    let rm = self.ret_m(c, r);
                    c.lam(rm, |c, k| {
                        let base = c.mark(w.v());
                        let p = w.prog(c, code, &[], base, arities);
                        let p = c.mark(p);
                        let st_ty = prod(w.v(), c.at(base));
                        let kk = c.lam(w.fr(), |c, _| {
                            c.lam(st_ty, |c, st| {
                                let mem = w.mem(c, r);
                                c.lam(mem, |c, mu2| w.split(c, r, w.v(), base, st, |c, y, _| app2(c.at(k), c.at(y), c.at(mu2))))
                            })
                        });
                        let kk = c.mark(kk);
                        let tbl = table(c, env);
                        let tbl = c.mark(tbl);
                        let m = w.meaning(c, p, kk, &MeaningEnv { r, ch, calls: Some(tbl) });
                        app3(m, c.at(fr), lit(n, 0), c.at(mu))
                    })
                })
            })
        })
    }
    /// `Bs = \g x.. ks. src`, `src` built by the entry's source closure; `fuel` and `callees` are the module's.
    pub fn bs(&self, c: &mut Cx, r: At, ch: Option<At>, src: &SrcFn, fuel: At, own: usize, callees: &[(usize, At)]) -> Expr {
        let n = self.w.n;
        let hs = self.hs(c, r);
        c.lam(hs, |c, g| {
            let vs: Vec<Ty> = (0..self.m).map(|_| ty!(|_c, _x| bv_ty(n))).collect();
            tele(c, &vs, &mut vec![], &lam, &mut |c, xs| {
                let rs = self.ret_s(c, r);
                c.lam(rs, |c, ks| {
                    let env = SEnv { n, r, g, params: xs.to_vec(), ch, fuel, own, callees: callees.to_vec() };
                    src(c, &env, &|c, v| app(c.at(ks), v))
                })
            })
        })
    }
    /// The binders of an entry's law (after `N gn R z`) and of the induction's motive, step and hypothesis: ONE
    /// telescope, the dummy numeral that lifts the motive to Sort3, then `d, a_0..a_{m-1}, mu, km, ks, rel`.
    pub fn binders(&self, c: &mut Cx, r: At, wrap: &dyn Fn(Expr, Expr) -> Expr, body: &mut dyn FnMut(&mut Cx, &[At]) -> Expr) -> Expr {
        let (g, n, m) = (self, self.w.n, self.m);
        let mut tys: Vec<Ty> = vec![ty!(|_c, _x| nat2())];
        tys.extend((0..m).map(|_| ty!(|_c, _x| bv_ty(n))));
        tys.push(ty!(|c, _x| g.w.mem(c, r)));
        tys.push(ty!(|c, _x| g.ret_m(c, r)));
        tys.push(ty!(|c, _x| g.ret_s(c, r)));
        tys.push(ty!(|c, x| g.rel_ty(c, r, x[m + 2], x[m + 3])));
        tele(c, &tys, &mut vec![], wrap, body)
    }
}

/// The telescope `N gn R z`, then (for the proof and the closed composition) the laws of `callees`.
pub(super) fn head_tys<'a>(w: Machine<'a>, module: &'a [Option<ModEntry<'a>>], callees: &[usize], with_laws: bool) -> Vec<Ty<'a>> {
    let mut tys: Vec<Ty> = vec![ty!(|_c, _x| nat2()), ty!(|c, x| w.good_nat(c, x[0])), ty!(|_c, _x| sort(0)), ty!(|c, x| c.at(x[2]))];
    if with_laws {
        for &p in callees {
            tys.push(ty!(|c, x| {
                let cx = Ctxt::new(c, w, module, x[0], x[2], x[3]);
                cx.law(c, p)
            }));
        }
    }
    tys
}

/// An entry's pieces as marks at the base depth of a statement or proof: its `Bm` and `Bs`, and the real (probe-free)
/// fixpoints `N H timeout Bm` and `N Hs ts Bs`.
#[derive(Clone, Copy)]
pub(super) struct Real {
    pub bm: At,
    pub bs: At,
    pub hc: At,
    pub sc: At,
}

/// The module at one context: the fuel `N`, the answer sort `r` and `z`, with the real pieces of each entry built on
/// demand at the depth this was made, so every mark is valid under all deeper binders.
pub(super) struct Ctxt<'a> {
    pub w: Machine<'a>,
    pub module: &'a [Option<ModEntry<'a>>],
    pub fuel: At,
    pub r: At,
    pub z: At,
    pub hm: At,
    pub tm: At,
    /// `arities[j]`: the words position `j` pops (`None`: no entry there).
    pub arities: Vec<Option<usize>>,
    memo: RefCell<Vec<Option<Real>>>,
    building: RefCell<Vec<usize>>,
}

impl<'a> Ctxt<'a> {
    pub fn new(c: &mut Cx, w: Machine<'a>, module: &'a [Option<ModEntry<'a>>], fuel: At, r: At, z: At) -> Self {
        let g0 = G { w, m: 0 };
        let hm = {
            let e = g0.hm(c, r);
            c.mark(e)
        };
        let tm = {
            let e = g0.tm(c, r, z);
            c.mark(e)
        };
        let arities = module.iter().map(|e| e.as_ref().map(|e| e.entry.arity)).collect();
        Ctxt { w, module, fuel, r, z, hm, tm, arities, memo: RefCell::new(vec![None; module.len()]), building: RefCell::new(vec![]) }
    }
    pub fn entry(&self, k: usize) -> &'a ModEntry<'a> {
        self.module.get(k).and_then(|e| e.as_ref()).unwrap_or_else(|| panic!("no module entry at position {k}"))
    }
    pub fn g(&self, k: usize) -> G<'a> {
        G { w: self.w, m: self.entry(k).entry.arity }
    }
    /// The table of entry `k`: `\i fr mu kont. (i == k) (env fr mu kont) ((i == c) (H_c fr mu kont) .. z)` over its
    /// callees `cs`, with `env` its own fuel-unrolled step.
    fn table(&self, c: &mut Cx, k: usize, env: At, cs: &[(usize, Real)]) -> Expr {
        let (w, r, z, n) = (self.w, self.r, self.z, self.w.n);
        c.lam(w.v(), |c, i| {
            c.lam(w.fr(), |c, fr| {
                let mem = w.mem(c, r);
                c.lam(mem, |c, mu| {
                    let rm = G { w, m: 0 }.ret_m(c, r);
                    c.lam(rm, |c, kont| {
                        let pick = |c: &Cx, pos: usize, yes: Expr, no: Expr| app3(app2(eq_bv(n), c.at(i), lit(n, pos as u128)), c.at(r), yes, no);
                        let mut acc = c.at(z);
                        for (pos, re) in cs.iter().rev() {
                            acc = pick(c, *pos, app3(c.at(re.hc), c.at(fr), c.at(mu), c.at(kont)), acc);
                        }
                        let own = app3(c.at(env), c.at(fr), c.at(mu), c.at(kont));
                        pick(c, k, own, acc)
                    })
                })
            })
        })
    }
    /// `Bm_k` and `Bs_k`, through the probe `probe` if any; the callees' real pieces are those of `real`.
    pub fn bm_bs(&self, c: &mut Cx, k: usize, probe: Option<At>) -> (Expr, Expr) {
        let (e, g) = (self.entry(k), self.g(k));
        let cs: Vec<(usize, Real)> = callees(k, &e.entry.code).into_iter().map(|p| (p, self.real(c, p))).collect();
        let bm = g.bm(c, self.r, probe, &e.entry.code, &self.arities, &|c, env| self.table(c, k, env, &cs));
        let scs: Vec<(usize, At)> = cs.iter().map(|(p, re)| (*p, re.sc)).collect();
        let bs = g.bs(c, self.r, probe, e.src, self.fuel, k, &scs);
        (bm, bs)
    }
    /// Entry `k`'s real (probe-free) pieces, built once.
    pub fn real(&self, c: &mut Cx, k: usize) -> Real {
        let cached = self.memo.borrow()[k];
        if let Some(re) = cached {
            return re;
        }
        assert!(!self.building.borrow().contains(&k), "the module's calls form a cycle through position {k}");
        self.building.borrow_mut().push(k);
        let g = self.g(k);
        let (bm, bs) = self.bm_bs(c, k, None);
        let (bm, bs) = (c.mark(bm), c.mark(bs));
        let (hs, ts) = (g.hs(c, self.r), g.ts(c, self.r, self.z));
        let (hs, ts) = (c.mark(hs), c.mark(ts));
        let hc = c.mark(apps(c.at(self.fuel), vec![c.at(self.hm), c.at(self.tm), c.at(bm)]));
        let sc = c.mark(apps(c.at(self.fuel), vec![c.at(hs), c.at(ts), c.at(bs)]));
        self.building.borrow_mut().pop();
        let re = Real { bm, bs, hc, sc };
        self.memo.borrow_mut()[k] = Some(re);
        re
    }
    /// The law of entry `k`: `Pi d x.. mu km ks rel. Id(R, N H timeout Bm_k (frame x..) mu km, N Hs ts Bs_k x.. ks)`.
    pub fn law(&self, c: &mut Cx, k: usize) -> Expr {
        let g = self.g(k);
        let re = self.real(c, k);
        let r = self.r;
        g.binders(c, r, &pi, &mut |c, x| {
            let m = g.m;
            let args: Vec<Expr> = x[1..1 + m].iter().map(|a| c.at(*a)).collect();
            let (mu, km, ks) = (x[1 + m], x[2 + m], x[3 + m]);
            let l = app3(c.at(re.hc), g.frame(&args), c.at(mu), c.at(km));
            let rhs = apps(c.at(re.sc), [args, vec![c.at(ks)]].concat());
            id(c.at(r), l, rhs)
        })
    }
}

/// The positions entry `k`'s code calls other than `k` itself, sorted and distinct.
pub(super) fn callees(k: usize, code: &[Ins]) -> Vec<usize> {
    fn walk(code: &[Ins], out: &mut Vec<usize>) {
        for i in code {
            match i {
                Ins::Call(j) => out.push(*j),
                Ins::If(t, e) => {
                    walk(t, out);
                    walk(e, out)
                }
                _ => {}
            }
        }
    }
    let mut out = vec![];
    walk(code, &mut out);
    out.retain(|j| *j != k);
    out.sort_unstable();
    out.dedup();
    out
}

/// `Pi N (GoodNat N) R z, law_entry`: entry `entry` of the module simulates its source, for every fuel. A single
/// function is a one-entry module, whose frame width is its own arity.
pub fn statement(m: &Machine, module: &[Option<ModEntry>], entry: usize) -> Expr {
    let w = widen(m, module);
    let tys = head_tys(w, module, &[], false);
    tele(&mut Cx::default(), &tys, &mut vec![], &pi, &mut |c, x| {
        let cx = Ctxt::new(c, w, module, x[0], x[2], x[3]);
        cx.law(c, entry)
    })
}
