//! Wasm programs as kernel data (docs/tier-cycle.md, option B; "Wasm programs over Church words" there).
//!
//! A program is a Church-encoded instruction tree typed by its start and end stacks,
//! `Prog S T = Pi F:(Sort2 -> Sort2). F T -> push -> bin -> cmp -> dup -> if -> loop -> store -> load -> F S`, where each
//! constructor takes the rest of the program (`push : Pi A. V -> F (V,A) -> F A`), so appending puts one program at the
//! other's nil and holds by beta. Its meaning `M p N R k z` interprets `F A` as `A -> Mem -> R` for an answer type
//! `R : Sort0`: words are width-n Church vectors (`encoding.rs`), stacks are nested `Sigma` pairs, memory is
//! `Mem = V -> (V -> R) -> R`, an `if` chooses between its two continuations by its one-bit condition (`choose`, as only
//! the taken branch runs), and a `loop` unrolls its body `N` times, `N` a Church numeral at Sort2, then answers the
//! timeout `z`. Nothing is postulated.
use super::*;

/// A term together with the binder depth it was built at, so it can be used under more binders (`Cx::at` shifts it).
#[derive(Clone, Copy)]
pub struct At(Expr, u32);

/// The binder depth while a term is built. Binders give their variable as an `At`, so terms are written with names,
/// not indices.
#[derive(Default)]
pub struct Cx(u32);

impl Cx {
    pub fn at(&self, a: At) -> Expr {
        shift(&a.0, 0, (self.0 - a.1) as i32)
    }
    /// `e`, built at the current depth.
    pub fn mark(&self, e: Expr) -> At {
        At(e, self.0)
    }
    fn bind(&mut self, body: impl FnOnce(&mut Cx, At) -> Expr) -> Expr {
        self.0 += 1;
        let x = At(var(0), self.0);
        let b = body(self, x);
        self.0 -= 1;
        b
    }
    pub fn lam(&mut self, ty: Expr, body: impl FnOnce(&mut Cx, At) -> Expr) -> Expr {
        lam(ty, self.bind(body))
    }
    pub fn pi(&mut self, ty: Expr, body: impl FnOnce(&mut Cx, At) -> Expr) -> Expr {
        pi(ty, self.bind(body))
    }
}

/// A telescope entry: a binder's type from the variables bound before it.
pub type Ty<'a> = Box<dyn Fn(&mut Cx, &[At]) -> Expr + 'a>;

fn tele(c: &mut Cx, lambda: bool, tys: &[Ty], xs: &mut Vec<At>, body: &mut dyn FnMut(&mut Cx, &[At]) -> Expr) -> Expr {
    if xs.len() == tys.len() {
        return body(c, xs);
    }
    let ty = tys[xs.len()](c, xs);
    let rest = |c: &mut Cx, x| {
        xs.push(x);
        let b = tele(c, lambda, tys, xs, body);
        xs.pop();
        b
    };
    if lambda { c.lam(ty, rest) } else { c.pi(ty, rest) }
}

/// `(proof, statement)`: the proof's lambdas and the statement's Pis over the same telescope.
pub fn law(tys: &[Ty], mut stmt: impl FnMut(&mut Cx, &[At]) -> Expr, mut proof: impl FnMut(&mut Cx, &[At]) -> Expr) -> (Expr, Expr) {
    let p = tele(&mut Cx::default(), true, tys, &mut vec![], &mut proof);
    let s = tele(&mut Cx::default(), false, tys, &mut vec![], &mut stmt);
    (p, s)
}

macro_rules! ty {
    (|$c:ident, $x:ident| $e:expr) => {
        Box::new(move |$c: &mut Cx, $x: &[At]| $e) as Ty
    };
}

/// `choose w x y = w (Lift R) (\c Y g. g (c R x y)) R id`, with `Lift R = Pi Y:Sort0. (R -> Y) -> Y`: a one-bit word
/// opens only at Sort1, and `Lift R` carries the Sort0 answer through it.
pub fn choose(r: Expr, w: Expr, x: Expr, y: Expr) -> Expr {
    let lift = pi(sort(0), arrow(arrow(shift(&r, 0, 1), var(0)), var(0)));
    let k = lam(bool0(), lam(sort(0), lam(arrow(shift(&r, 0, 2), var(0)),
        app(var(0), app3(var(2), shift(&r, 0, 3), shift(&x, 0, 3), shift(&y, 0, 3))))));
    apps(w, vec![lift, k, r, lam(r, var(0))])
}

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
    law(
        &tys,
        |c, x| if ctl == Ctl::ClaimsX { app(c.at(x[1]), c.at(x[4])) } else { q_choose(c, x, c.at(x[2])) },
        |c, x| {
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
            app2(w, motive, step)
        },
    )
}

/// An interpreter case's body from `A`, its operator if any, `rest`, the stack and the memory.
type Body<'a> = dyn Fn(&mut Cx, At, Option<At>, At, At, At) -> Expr + 'a;

/// What a stack slot holds: an n-bit word or a one-bit word (a compare's result).
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum K {
    W,
    B,
}

/// An instruction. Words and operators are closed terms; `Br(j)` jumps to the `j`-th enclosing loop's start.
#[derive(Clone)]
pub enum Ins {
    Push(Expr),
    Bin(Expr),
    Cmp(Expr),
    Dup,
    If(Vec<Ins>, Vec<Ins>),
    Loop(Vec<Ins>),
    Br(usize),
    Store,
    Load,
}

/// The stack after `code` from `st` (top first), or `None` if every path jumps.
pub fn out_stack(code: &[Ins], mut st: Vec<K>) -> Option<Vec<K>> {
    for ins in code {
        let pop = |st: &mut Vec<K>, want: &[K]| {
            assert!(st.starts_with(want), "stack {st:?} lacks {want:?}");
            st.drain(..want.len());
        };
        match ins {
            Ins::Push(_) => st.insert(0, K::W),
            Ins::Bin(_) => {
                pop(&mut st, &[K::W, K::W]);
                st.insert(0, K::W)
            }
            Ins::Cmp(_) => {
                pop(&mut st, &[K::W, K::W]);
                st.insert(0, K::B)
            }
            Ins::Dup => {
                pop(&mut st, &[K::W]);
                st.splice(0..0, [K::W, K::W]);
            }
            Ins::If(t, e) => {
                pop(&mut st, &[K::B]);
                st = match (out_stack(t, st.clone()), out_stack(e, st)) {
                    (Some(a), Some(b)) => {
                        assert_eq!(a, b, "if arms end on different stacks");
                        a
                    }
                    (Some(a), None) | (None, Some(a)) => a,
                    (None, None) => return None,
                }
            }
            Ins::Loop(body) => st = out_stack(body, st)?,
            Ins::Br(_) => return None,
            Ins::Store => pop(&mut st, &[K::W, K::W]),
            Ins::Load => {
                pop(&mut st, &[K::W]);
                st.insert(0, K::W)
            }
        }
    }
    Some(st)
}

/// `A x B` as a `Sigma`, both at the same depth.
pub fn prod(a: Expr, b: Expr) -> Expr {
    sigma(a, shift(&b, 0, 1))
}
/// `(a, b) : A x B`, given `B`.
pub fn mkpair(b_ty: Expr, a: Expr, b: Expr) -> Expr {
    pair(shift(&b_ty, 0, 1), a, b)
}
/// Church numerals at Sort2, the loops' fuel: `Pi C:Sort2. C -> (C -> C) -> C`.
pub fn nat2() -> Expr {
    pi(sort(2), pi(var(0), pi(arrow(var(1), var(1)), var(2))))
}
pub fn nat2_lit(k: usize) -> Expr {
    let body = (0..k).fold(var(1), |b, _| app(var(0), b));
    lam(sort(2), lam(var(0), lam(arrow(var(1), var(1)), body)))
}

/// The encoding at word width `n`.
#[derive(Clone, Copy)]
pub struct Wasm {
    pub n: usize,
}

const F_TY: fn() -> Expr = || arrow(sort(2), sort(2));

impl Wasm {
    pub fn v(&self) -> Expr {
        bv_ty(self.n)
    }
    fn word(&self, k: K) -> Expr {
        bv_ty(if k == K::W { self.n } else { 1 })
    }
    /// The stack type `ks` (top first) over the base `base`.
    pub fn sty(&self, c: &Cx, ks: &[K], base: At) -> Expr {
        ks.iter().rev().fold(c.at(base), |acc, k| prod(self.word(*k), acc))
    }
    /// `Mem = V -> (V -> R) -> R`.
    pub fn mem(&self, c: &mut Cx, r: At) -> Expr {
        let v = self.v();
        c.pi(v, |c, _| {
            let k = c.pi(v, |c, _| c.at(r));
            c.pi(k, |c, _| c.at(r))
        })
    }
    /// `G A = A -> Mem -> R`, the meaning of `F A`.
    pub fn g(&self, c: &mut Cx, r: At, a: Expr) -> Expr {
        let m = self.mem(c, r);
        arrow(a, arrow(m, c.at(r)))
    }
    fn ctor_ty(&self, c: &mut Cx, f: At, i: usize) -> Expr {
        let (v, v1) = (self.v(), bv_ty(1));
        c.pi(sort(2), |c, a| {
            let fa = |e: Expr| app(c.at(f), e);
            let a = c.at(a);
            let (va, vva, v1a) = (prod(v, a), prod(v, prod(v, a)), prod(v1, a));
            match i {
                0 => arrow(v, arrow(fa(va), fa(a))),
                1 => arrow(arrow(v, arrow(v, v)), arrow(fa(va), fa(vva))),
                2 => arrow(arrow(v, arrow(v, v1)), arrow(fa(v1a), fa(vva))),
                3 => arrow(fa(vva), fa(va)),
                4 => arrow(fa(a), arrow(fa(a), fa(v1a))),
                5 => arrow(arrow(fa(a), fa(a)), fa(a)),
                6 => arrow(fa(a), fa(vva)),
                _ => arrow(fa(va), fa(va)),
            }
        })
    }
    /// The eight constructor binders, lambdas or Pis, then `body` with their variables.
    fn ctors(&self, c: &mut Cx, f: At, lambda: bool, body: &mut dyn FnMut(&mut Cx, &[At]) -> Expr) -> Expr {
        let w = *self;
        let tys: Vec<Ty> = (0..8).map(|i| ty!(|c, _x| w.ctor_ty(c, f, i))).collect();
        tele(c, lambda, &tys, &mut vec![], body)
    }
    /// `Prog S T`, with `S` and `T` built at each use.
    pub fn prog_ty(&self, c: &mut Cx, s: &dyn Fn(&Cx) -> Expr, t: &dyn Fn(&Cx) -> Expr) -> Expr {
        c.pi(F_TY(), |c, f| {
            let nil = app(c.at(f), t(c));
            c.pi(nil, |c, _| self.ctors(c, f, false, &mut |c, _| app(c.at(f), s(c))))
        })
    }
    /// `Pi S. Prog S (K, S)`: code that pushes one value of kind `k`.
    pub fn code_ty(&self, c: &mut Cx, k: K) -> Expr {
        c.pi(sort(2), |c, s| self.prog_ty(c, &|c| c.at(s), &|c| self.sty(c, &[k], s)))
    }
    /// `code` as a program from `ks` over `base`.
    pub fn prog(&self, c: &mut Cx, code: &[Ins], ks: &[K], base: At) -> Expr {
        let out = out_stack(code, ks.to_vec()).expect("a program that falls through");
        c.lam(F_TY(), |c, f| {
            let nil = app(c.at(f), self.sty(c, &out, base));
            c.lam(nil, |c, nil| {
                self.ctors(c, f, true, &mut |c, ct| {
                    let ct = ct.to_vec();
                    self.seq(c, f, &ct, base, code, ks.to_vec(), &|c, _| c.at(nil), &[])
                })
            })
        })
    }
    #[allow(clippy::too_many_arguments)]
    fn seq(&self, c: &mut Cx, f: At, ct: &[At], base: At, code: &[Ins], st: Vec<K>, k: &dyn Fn(&mut Cx, Vec<K>) -> Expr,
        labels: &[(At, Vec<K>)]) -> Expr {
        let Some((ins, rest)) = code.split_first() else { return k(c, st) };
        let cont = |c: &mut Cx, st: Vec<K>| self.seq(c, f, ct, base, rest, st, k, labels);
        let ty = |c: &Cx, ks: &[K]| self.sty(c, ks, base);
        let cons = |c: &Cx, i: usize, args: Vec<Expr>| apps(c.at(ct[i]), args);
        let below = |n: usize| st[n..].to_vec();
        let with = |top: &[K], n: usize| [top, &st[n..]].concat();
        match ins {
            Ins::Push(w) => {
                let r = cont(c, with(&[K::W], 0));
                cons(c, 0, vec![ty(c, &st), *w, r])
            }
            Ins::Bin(op) => {
                let r = cont(c, with(&[K::W], 2));
                cons(c, 1, vec![ty(c, &below(2)), *op, r])
            }
            Ins::Cmp(op) => {
                let r = cont(c, with(&[K::B], 2));
                cons(c, 2, vec![ty(c, &below(2)), *op, r])
            }
            Ins::Dup => {
                let r = cont(c, with(&[K::W, K::W], 1));
                cons(c, 3, vec![ty(c, &below(1)), r])
            }
            Ins::If(t, e) => {
                let th = self.seq(c, f, ct, base, t, below(1), &cont, labels);
                let el = self.seq(c, f, ct, base, e, below(1), &cont, labels);
                cons(c, 4, vec![ty(c, &below(1)), th, el])
            }
            Ins::Loop(body) => {
                let a = ty(c, &st);
                let label = app(c.at(f), a);
                let b = c.lam(label, |c, l| {
                    let ls = [&[(l, st.clone())], labels].concat();
                    self.seq(c, f, ct, base, body, st.clone(), &cont, &ls)
                });
                cons(c, 5, vec![a, b])
            }
            Ins::Br(j) => {
                let (l, ls) = &labels[*j];
                assert_eq!(ls, &st, "br with a stack other than the loop's");
                c.at(*l)
            }
            Ins::Store => {
                let r = cont(c, below(2));
                cons(c, 6, vec![ty(c, &below(2)), r])
            }
            Ins::Load => {
                let r = cont(c, st.clone());
                cons(c, 7, vec![ty(c, &below(1)), r])
            }
        }
    }
    /// `upd a v mu = \b kk. (eq a b) R (kk v) (mu b kk)`.
    pub fn upd(&self, c: &mut Cx, r: At, a: Expr, v: Expr, mu: Expr) -> Expr {
        let (a, v, mu) = (c.mark(a), c.mark(v), c.mark(mu));
        let n = self.n;
        c.lam(self.v(), |c, b| {
            let kt = c.pi(self.v(), |c, _| c.at(r));
            c.lam(kt, |c, kk| app3(app2(eq_bv(n), c.at(a), c.at(b)), c.at(r), app(c.at(kk), c.at(v)), app2(c.at(mu), c.at(b), c.at(kk))))
        })
    }
    /// `sigrec` on a stack `st : A x B` into `R`: `body(c, top, below)`.
    fn split(&self, c: &mut Cx, r: At, a: Expr, b: At, st: At, body: impl FnOnce(&mut Cx, At, At) -> Expr) -> Expr {
        let a = c.mark(a);
        let motive = {
            let pt = prod(c.at(a), c.at(b));
            c.lam(pt, |c, _| c.at(r))
        };
        let step = c.lam(c.at(a), |c, x| {
            let bt = c.at(b);
            c.lam(bt, |c, s| body(c, x, s))
        });
        sigrec(motive, step, c.at(st))
    }
    /// The constructors' meanings.
    fn interp(&self, c: &mut Cx, r: At, fuel: At, z: At) -> Vec<Expr> {
        let (v, v1) = (self.v(), bv_ty(1));
        let w = *self;
        // `\A rest st mu. body`, with `rest : G (rest_ty A)` and `st : st_ty A`
        let shape = |c: &mut Cx, extra: Option<Expr>, rest_ty: &dyn Fn(Expr) -> Expr, st_ty: &dyn Fn(Expr) -> Expr,
                     body: &Body| {
            c.lam(sort(2), |c, a| {
                let inner = |c: &mut Cx, op: Option<At>| {
                    let rt = w.g(c, r, rest_ty(c.at(a)));
                    c.lam(rt, |c, rest| {
                        c.lam(st_ty(c.at(a)), |c, st| {
                            let m = w.mem(c, r);
                            c.lam(m, |c, mu| body(c, a, op, rest, st, mu))
                        })
                    })
                };
                match extra {
                    Some(t) => c.lam(t, |c, op| inner(c, Some(op))),
                    None => inner(c, None),
                }
            })
        };
        let push = c.lam(sort(2), |c, a| {
            c.lam(v, |c, x| {
                let rt = w.g(c, r, prod(v, c.at(a)));
                c.lam(rt, |c, rest| {
                    c.lam(c.at(a), |c, s| {
                        let m = w.mem(c, r);
                        c.lam(m, |c, mu| app2(c.at(rest), mkpair(c.at(a), c.at(x), c.at(s)), c.at(mu)))
                    })
                })
            })
        });
        let binop = |c: &mut Cx, out: Expr| {
            shape(c, Some(arrow(v, arrow(v, out))), &|a| prod(out, a), &|a| prod(v, prod(v, a)), &|c, a, op, rest, st, mu| {
                let below = c.mark(prod(v, c.at(a)));
                w.split(c, r, v, below, st, |c, y, rs| {
                    w.split(c, r, v, a, rs, |c, x, s| {
                        let val = app2(c.at(op.unwrap()), c.at(x), c.at(y));
                        app2(c.at(rest), mkpair(c.at(a), val, c.at(s)), c.at(mu))
                    })
                })
            })
        };
        let bin = binop(c, v);
        let cmp = binop(c, v1);
        let dup = shape(c, None, &|a| prod(v, prod(v, a)), &|a| prod(v, a), &|c, a, _, rest, st, mu| {
            w.split(c, r, v, a, st, |c, x, s| {
                let inner = mkpair(c.at(a), c.at(x), c.at(s));
                app2(c.at(rest), mkpair(prod(v, c.at(a)), c.at(x), inner), c.at(mu))
            })
        });
        let if_ = c.lam(sort(2), |c, a| {
            let ga = w.g(c, r, c.at(a));
            c.lam(ga, |c, th| {
                let ga = w.g(c, r, c.at(a));
                c.lam(ga, |c, el| {
                    c.lam(prod(v1, c.at(a)), |c, st| {
                        let m = w.mem(c, r);
                        c.lam(m, |c, mu| {
                            w.split(c, r, v1, a, st, |c, b, s| {
                                let (s, mu) = (c.at(s), c.at(mu));
                                choose(c.at(r), c.at(b), app2(c.at(th), s, mu), app2(c.at(el), s, mu))
                            })
                        })
                    })
                })
            })
        });
        let loop_ = c.lam(sort(2), |c, a| {
            let ga = w.g(c, r, c.at(a));
            c.lam(arrow(ga, ga), |c, body| {
                let timeout = c.lam(c.at(a), |c, _| {
                    let m = w.mem(c, r);
                    c.lam(m, |c, _| c.at(z))
                });
                let ga = w.g(c, r, c.at(a));
                apps(c.at(fuel), vec![ga, timeout, c.at(body)])
            })
        });
        let store = shape(c, None, &|a| a, &|a| prod(v, prod(v, a)), &|c, a, _, rest, st, mu| {
            let below = c.mark(prod(v, c.at(a)));
            w.split(c, r, v, below, st, |c, x, rs| {
                w.split(c, r, v, a, rs, |c, ad, s| {
                    let mu2 = w.upd(c, r, c.at(ad), c.at(x), c.at(mu));
                    app2(c.at(rest), c.at(s), mu2)
                })
            })
        });
        let load = shape(c, None, &|a| prod(v, a), &|a| prod(v, a), &|c, a, _, rest, st, mu| {
            w.split(c, r, v, a, st, |c, ad, s| {
                let k = c.lam(v, |c, x| app2(c.at(rest), mkpair(c.at(a), c.at(x), c.at(s)), c.at(mu)));
                app2(c.at(mu), c.at(ad), k)
            })
        });
        vec![push, bin, cmp, dup, if_, loop_, store, load]
    }
    /// `M p N R k z`, of type `G S` for `p : Prog S T` and `k : G T`.
    pub fn meaning(&self, c: &mut Cx, p: At, fuel: At, r: At, k: At, z: At) -> Expr {
        let gfam = c.lam(sort(2), |c, a| self.g(c, r, c.at(a)));
        let mut args = vec![gfam, c.at(k)];
        args.extend(self.interp(c, r, fuel, z));
        apps(c.at(p), args)
    }
    /// `p1 ++ p2 : Prog S U` for `p1 : Prog S T`, `p2 : Prog T U`.
    pub fn append(&self, c: &mut Cx, u: &dyn Fn(&Cx) -> Expr, p1: At, p2: At) -> Expr {
        c.lam(F_TY(), |c, f| {
            let nil = app(c.at(f), u(c));
            c.lam(nil, |c, nil| {
                self.ctors(c, f, true, &mut |c, ct| {
                    let ctors: Vec<Expr> = ct.iter().map(|x| c.at(*x)).collect();
                    let inner = apps(c.at(p2), [vec![c.at(f), c.at(nil)], ctors.clone()].concat());
                    apps(c.at(p1), [vec![c.at(f), inner], ctors].concat())
                })
            })
        })
    }
    /// `if t e : Prog (V1, S) T` for `t e : Prog S T`.
    pub fn ifp(&self, c: &mut Cx, s: At, t_ty: At, th: At, el: At) -> Expr {
        c.lam(F_TY(), |c, f| {
            let nil = app(c.at(f), c.at(t_ty));
            c.lam(nil, |c, nil| {
                self.ctors(c, f, true, &mut |c, ct| {
                    let ctors: Vec<Expr> = ct.iter().map(|x| c.at(*x)).collect();
                    let arm = |c: &Cx, p: At| apps(c.at(p), [vec![c.at(f), c.at(nil)], ctors.clone()].concat());
                    apps(c.at(ct[4]), vec![c.at(s), arm(c, th), arm(c, el)])
                })
            })
        })
    }
    /// `Spec(cc, m) = Pi S N R k z s mu. Id(R, M (cc S) N R k z s mu, k (m, s) mu)` for code `cc` pushing `m : kind`.
    pub fn spec(&self, c: &mut Cx, cc: At, m: At, kind: K) -> Expr {
        let w = *self;
        let tys: Vec<Ty> = vec![
            ty!(|_c, _x| sort(2)),
            ty!(|_c, _x| nat2()),
            ty!(|_c, _x| sort(0)),
            ty!(|c, x| { let t = w.sty(c, &[kind], x[0]); w.g(c, x[2], t) }),
            ty!(|c, x| c.at(x[2])),
            ty!(|c, x| c.at(x[0])),
            ty!(|c, x| w.mem(c, x[2])),
        ];
        tele(c, false, &tys, &mut vec![], &mut |c, x| {
            let p = c.mark(app(c.at(cc), c.at(x[0])));
            let lhs = app2(w.meaning(c, p, x[1], x[2], x[3], x[4]), c.at(x[5]), c.at(x[6]));
            let rhs = app2(c.at(x[3]), mkpair(c.at(x[0]), c.at(m), c.at(x[5])), c.at(x[6]));
            id(c.at(x[2]), lhs, rhs)
        })
    }
    /// `GoodNat N = Pi P:(Nat2 -> Sort3). P 0 -> (Pi j. P j -> P (S j)) -> P N`: induction over fuel, as a hypothesis.
    pub fn good_nat(&self, c: &mut Cx, fuel: At) -> Expr {
        c.pi(arrow(nat2(), sort(3)), |c, p| {
            let p0 = app(c.at(p), nat2_lit(0));
            c.pi(p0, |c, _| {
                let step = c.pi(nat2(), |c, j| {
                    let succ = c.lam(sort(2), |c, cc| {
                        c.lam(c.at(cc), |c, b| {
                            let ct = arrow(c.at(cc), c.at(cc));
                            c.lam(ct, |c, s| app(c.at(s), apps(c.at(j), vec![c.at(cc), c.at(b), c.at(s)])))
                        })
                    });
                    arrow(app(c.at(p), c.at(j)), app(c.at(p), succ))
                });
                c.pi(step, |c, _| app(c.at(p), c.at(fuel)))
            })
        })
    }
    /// `Good f = Pi s mu. I s -> Q (f s mu)`.
    pub fn good(&self, c: &mut Cx, a: At, r: At, i: At, q: At, f: At) -> Expr {
        c.pi(c.at(a), |c, s| {
            let m = self.mem(c, r);
            c.pi(m, |c, mu| arrow(app(c.at(i), c.at(s)), app(c.at(q), app2(c.at(f), c.at(s), c.at(mu)))))
        })
    }
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
    let lhs = |c: &mut Cx, x: &[At]| {
        let p = w.append(c, &|c| c.at(x[2]), x[3], x[4]);
        let p = c.mark(p);
        w.meaning(c, p, x[5], x[6], x[7], x[8])
    };
    law(
        &tys,
        |c, x| {
            let l = lhs(c, x);
            let k2 = w.meaning(c, x[4], x[5], x[6], x[7], x[8]);
            let k2 = c.mark(k2);
            let r = w.meaning(c, x[3], x[5], x[6], k2, x[8]);
            let ga = w.g(c, x[6], c.at(x[0]));
            id(ga, l, r)
        },
        |c, x| refl(lhs(c, x)),
    )
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
    law(
        &tys,
        |c, x| {
            let n = if_names(x, false);
            let (l, r) = (n.lhs(w, c, false), n.rhs(w, c, swap));
            id(c.at(n.r), l, r)
        },
        |c, x| if_names(x, false).law_proof(w, c),
    )
}

/// `Spec(cc, m) -> GoodBv m -> Q (M t .. s mu) -> Q (M e .. s mu) -> Q (M (cc S ++ if t e) .. s mu)`: the If law,
/// transported, of `if_inv`. `swap` states it for `if e t`.
pub fn if_good(w: Wasm, swap: bool) -> (Expr, Expr) {
    let tys = if_tele(w, true);
    law(
        &tys,
        |c, x| {
            let n = if_names(x, true);
            let l = n.lhs(w, c, swap);
            app(c.at(n.q.unwrap()), l)
        },
        |c, x| {
            let n = if_names(x, true);
            let (q, r) = (n.q.unwrap(), n.r);
            let (l, rh, p) = (n.lhs(w, c, false), n.rhs(w, c, false), n.law_proof(w, c));
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
        },
    )
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
    law(
        &tys,
        |c, x| {
            let f = unrolled(c, x, x[6]);
            w.good(c, x[0], x[1], x[2], x[3], f)
        },
        |c, x| {
            let motive = c.lam(nat2(), |c, m| {
                let f = unrolled(c, x, m);
                w.good(c, x[0], x[1], x[2], x[3], f)
            });
            let step = c.lam(nat2(), |c, j| {
                let f = unrolled(c, x, j);
                let gf = w.good(c, x[0], x[1], x[2], x[3], f);
                c.lam(gf, |c, ih| apps(c.at(x[9]), vec![c.at(f), c.at(ih)]))
            });
            apps(c.at(x[7]), vec![motive, c.at(x[8]), step])
        },
    )
}
fn timeout(w: Wasm, c: &mut Cx, a: At, r: At, z: At) -> Expr {
    c.lam(c.at(a), |c, _| {
        let m = w.mem(c, r);
        c.lam(m, |c, _| c.at(z))
    })
}

/// `loop L { dup; push 1; lt; if {} {push 1; <dec>; br L} }`: count the top word down to 0 (`dec` = `sub`).
pub fn countdown(w: Wasm, dec: Expr) -> Vec<Ins> {
    let one = lit(w.n, 1);
    vec![Ins::Loop(vec![Ins::Dup, Ins::Push(one), Ins::Cmp(lt_u(w.n)), Ins::If(vec![], vec![Ins::Push(one), Ins::Bin(dec), Ins::Br(0)])])]
}

/// An `if` inside a loop: for every fuel with `GoodNat` and every start word with `GoodBv`, the countdown answers
/// `Q` if the timeout does and the exit continuation does on every good word:
/// `Pi S N. GoodNat N -> Pi R Q k z. Q z -> (Pi x s mu. GoodBv x -> Q (k (x,s) mu)) -> Pi x s mu. GoodBv x -> Q (M cd ..)`.
/// The invariant carries `GoodBv` of the counter, which the `if` needs and `good_sub` keeps. `dec` replaces the
/// decrement in the program only (a control).
pub fn countdown_law(w: Wasm, dec: Expr) -> (Expr, Expr) {
    let n = w.n;
    let code = countdown(w, dec);
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
    let m_cd = |c: &mut Cx, x: &[At]| {
        let p = w.prog(c, &code, &[K::W], x[0]);
        let p = c.mark(p);
        w.meaning(c, p, x[1], x[3], x[5], x[6])
    };
    law(
        &tys,
        |c, x| {
            let m = m_cd(c, x);
            app(c.at(x[4]), app2(m, mkpair(c.at(x[0]), c.at(x[9]), c.at(x[10])), c.at(x[11])))
        },
        |c, x| {
            let (s_ty, r, q, k) = (x[0], x[3], x[4], x[5]);
            // `M cd` is `N (G A) timeout B`: take `B`
            let m = m_cd(c, x);
            let body = match whnf(&m).node() {
                tatic::kernel::Node::App(_, b) => c.mark(b),
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
        },
    )
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
    let lhs = |c: &mut Cx, x: &[At]| {
        let p = w.prog(c, code, &ks, x[0]);
        let p = c.mark(p);
        let fuel = c.mark(nat2_lit(fuel));
        let st = start.iter().rev().fold(c.at(x[4]), |acc, v| mkpair(c.at(x[0]), lit(w.n, *v), acc));
        app2(w.meaning(c, p, fuel, x[1], x[2], x[3]), st, c.at(x[5]))
    };
    law(&tys, |c, x| { let (l, r) = (lhs(c, x), want(c, x)); id(c.at(x[1]), l, r) }, |c, x| refl(lhs(c, x)))
}

#[test]
pub fn wasm_programs_as_kernel_data() {
    {
        let n = 4;
        tatic::kernel::scoped(|| run_wasm_checks(Wasm { n }, true))
    }
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
        assert!(matches!(sort_of.as_ref().map(|t| t.node()), Ok(tatic::kernel::Node::Sort(_))), "{name}: statement is not a type: {sort_of:?}");
        assert!(holds(&p, &s).is_err(), "{name} must be rejected at n={n}");
    };
    timed("if_inv", if_inv(Ctl::Ok));
    timed("append", append_law(w));
    timed("if law", if_law(w, false));
    timed("if invariant", if_good(w, false));
    timed("loop law", loop_law(w));
    timed("countdown invariant", countdown_law(w, sub(n)));
    // concrete runs: the countdown from 3 exits at 0 with fuel 4 and times out with fuel 3; store then load
    let at = |v: u128| move |c: &mut Cx, x: &[At]| app2(c.at(x[2]), mkpair(c.at(x[0]), lit(n, v), c.at(x[4])), c.at(x[5]));
    timed("countdown 3, fuel 4", run_by_refl(w, &countdown(w, sub(n)), &[3], 4, &at(0)));
    timed("countdown 3, fuel 3", run_by_refl(w, &countdown(w, sub(n)), &[3], 3, &|c, x| c.at(x[3])));
    let mem_prog = [Ins::Push(lit(n, 3)), Ins::Push(lit(n, 5)), Ins::Store, Ins::Push(lit(n, 3)), Ins::Load];
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
        rejected("countdown with add for sub", countdown_law(w, add(n)));
        rejected("countdown 3, fuel 4, answers 1", run_by_refl(w, &countdown(w, sub(n)), &[3], 4, &at(1)));
        rejected("countdown 3, fuel 3, exits", run_by_refl(w, &countdown(w, sub(n)), &[3], 3, &at(0)));
    }
}

/// `WASM` check times at n = 4, 16. The countdown invariant is exponential in n under `conv` without a pair memo
/// (docs/tier-cycle.md, "The countdown invariant is exponential"): n=32 did not finish in 600 s.
#[test]
#[ignore]
pub fn wasm_scaling() {
    for n in [4usize, 16] {
        tatic::kernel::scoped(|| run_wasm_checks(Wasm { n }, n == 16))
    }
}
