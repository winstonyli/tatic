//! The `Prog` constructors and their meanings: `prod`, `Ctor`, `Machine`, and the interpreter `impl Machine` (`machine.rs` holds the instruction set).
use super::*;

/// `A x B` as a `Sigma`, both at the same depth.
pub fn prod(a: Expr, b: Expr) -> Expr {
    sigma(a, shift(&b, 0, 1))
}
/// `(a, b) : A x B`, given `B`.
pub fn mkpair(b_ty: Expr, a: Expr, b: Expr) -> Expr {
    pair(shift(&b_ty, 0, 1), a, b)
}
/// Church numerals at Sort2, the fuel of the module fixpoint (`statement.rs`): `Pi C:Sort2. C -> (C -> C) -> C`.
pub fn nat2() -> Expr {
    pi(sort(2), pi(var(0), pi(arrow(var(1), var(1)), var(2))))
}
pub fn nat2_lit(k: usize) -> Expr {
    let body = (0..k).fold(var(1), |b, _| app(var(0), b));
    lam(sort(2), lam(var(0), lam(arrow(var(1), var(1)), body)))
}

/// The machine's constructors, in `Prog`'s binder order: one leaf constructor per row class, then the structural ones.
#[derive(Clone, Copy, PartialEq, Debug)]
enum Ctor {
    Leaf(Class),
    If,
    Call,
    Br,
}

/// The one list the constructor order is read from (`ctor_ty`, `interp`, `seq_step`, the count). Only `Word` takes the
/// row's domain circuit after its operator (`ctor_ty`).
fn ctor_list() -> [Ctor; 7] {
    [Ctor::Leaf(Class::Const), Ctor::Leaf(Class::Word), Ctor::Leaf(Class::Bit), Ctor::If, Ctor::Call, Ctor::Leaf(Class::Set), Ctor::Br]
}

fn ctor_idx(k: Ctor) -> usize {
    ctor_list().iter().position(|x| *x == k).expect("ctor_list holds every constructor")
}

/// The encoding at word width `n` and frame width `fw`, over `table`'s rows. Every frame is `V^fw x V` (`fw` slots and
/// a terminal word); a callee's is padded with zeros to the module-wide width (`statement::statement` widens it).
#[derive(Clone, Copy)]
pub struct Machine<'t> {
    pub n: usize,
    pub fw: usize,
    pub table: &'t Table,
}

/// What `meaning` is given beside the program and its continuation: the answer type `r`; for the generator's proofs,
/// `ch`, an opaque `choose` (`Pi R:Sort0. Bv_1 -> R -> R -> R`) an `If` uses in place of the real one; and `calls`, the
/// callee environment `V -> Fr -> Mem -> Ret -> R` (`Ret = V -> Mem -> R`) a `Call(j)` continues into at `j`, which the
/// statement builder fills from the module fixpoint over fuel; and `restart`, `Fr -> Mem -> R`, what a `Br` continues
/// into: the activation's own entry run again at a frame and memory with the activation's own return continuation
/// (`\fr mu. env fr mu k`, filled in `G::bm`).
#[derive(Clone, Copy)]
pub struct MeaningEnv {
    pub r: At,
    pub ch: Option<At>,
    pub calls: At,
    pub restart: At,
    /// The `R`-typed answer a Word guard's else branch takes (the statement's out-of-fuel answer `z`).
    pub z: At,
}

const F_TY: fn() -> Expr = || arrow(sort(2), sort(2));

impl Machine<'_> {
    pub fn v(&self) -> Expr {
        bv_ty(self.n)
    }
    pub(super) fn word(&self, k: K) -> Expr {
        bv_ty(if k == K::W { self.n } else { 1 })
    }
    /// The stack type `ks` (top first) over the base `base`.
    pub fn sty(&self, c: &Cx, ks: &[K], base: At) -> Expr {
        // the words are closed, so only the base moves: shift it under all `ks.len()` binders once
        let base = shift(&c.at(base), 0, ks.len() as i32);
        ks.iter().rev().fold(base, |acc, k| sigma(self.word(*k), acc))
    }
    /// The opaque memory `Mem = V -> (V -> R) -> R`; no instruction reads it.
    pub fn mem(&self, c: &mut Cx, r: At) -> Expr {
        let v = self.v();
        c.pi(v, |c, _| {
            let k = c.pi(v, |c, _| c.at(r));
            c.pi(k, |c, _| c.at(r))
        })
    }
    /// `G A = Fr -> A -> Mem -> R`, the meaning of `F A`.
    pub fn g(&self, c: &mut Cx, r: At, a: Expr) -> Expr {
        let m = self.mem(c, r);
        arrow(self.fr(), arrow(a, arrow(m, c.at(r))))
    }
    /// `V^m x a`.
    pub fn words(&self, m: usize, a: Expr) -> Expr {
        (0..m).fold(a, |acc, _| prod(self.v(), acc))
    }
    /// `Fr = V^fw x V`.
    pub fn fr(&self) -> Expr {
        self.words(self.fw, self.v())
    }
    /// The frame holding `vals` at slots `0..`, zeros up to the width `fw`, and a terminal zero word.
    pub fn frame(&self, vals: &[Expr]) -> Expr {
        assert!(vals.len() <= self.fw, "{} slots over a frame of width {}", vals.len(), self.fw);
        let n = self.n;
        (0..self.fw).rev().fold(lit(n, 0), |acc, i| mkpair(self.words(self.fw - 1 - i, self.v()), vals.get(i).copied().unwrap_or(lit(n, 0)), acc))
    }
    /// A Const-class operand's type, `Fr -> Pi R:Sort0. (V -> R) -> R`: the word is handed to a continuation, so the
    /// interpreter pushes the reduced component, never the redex `op fr` (a stack value that shares no node with the
    /// source's makes every conversion of the two walk both term trees).
    pub fn operand_ty(&self) -> Expr {
        arrow(self.fr(), pi(sort(0), arrow(arrow(self.v(), var(0)), var(0))))
    }
    /// The operand that hands `word fr` to its continuation.
    pub fn handing(&self, c: &mut Cx, word: &dyn Fn(&mut Cx, At) -> Expr) -> Expr {
        c.lam(self.fr(), |c, fr| c.lam(sort(0), |c, r| c.lam(arrow(self.v(), c.at(r)), |c, k| app(c.at(k), word(c, fr)))))
    }
    /// Slot `i` of the frame `fr` (of `k` slots left), by `sigrec`, handed to `cont : V -> res`.
    fn nth(&self, c: &mut Cx, i: usize, k: usize, fr: At, res: At, cont: At) -> Expr {
        assert!(i < k, "local {i} is out of the frame's width");
        let tail = c.mark(self.words(k - 1, self.v()));
        self.split(c, res, self.v(), tail, fr, |c, x, rest| {
            if i == 0 { app(c.at(cont), c.at(x)) } else { self.nth(c, i - 1, k - 1, rest, res, cont) }
        })
    }
    /// A Set-class operand's type, `Fr -> V -> Fr`.
    pub fn setter_ty(&self) -> Expr {
        arrow(self.fr(), arrow(self.v(), self.fr()))
    }
    /// `fr` (of `k` slots left) with slot `i` replaced by `x`, rebuilt as a concrete nested pair.
    fn put(&self, c: &mut Cx, i: usize, k: usize, fr: At, x: At) -> Expr {
        assert!(i < k, "local {i} is out of the frame's width");
        let tail_ty = self.words(k - 1, self.v());
        let res = c.mark(self.words(k, self.v()));
        let tail = c.mark(tail_ty.clone());
        self.split(c, res, self.v(), tail, fr, |c, y, rest| {
            if i == 0 {
                mkpair(tail_ty.clone(), c.at(x), c.at(rest))
            } else {
                let inner = self.put(c, i - 1, k - 1, rest, x);
                mkpair(tail_ty.clone(), c.at(y), inner)
            }
        })
    }
    /// The operand of the `local.set` row: the frame with slot `i` replaced.
    pub fn setter(&self, c: &mut Cx, i: usize) -> Expr {
        c.lam(self.fr(), |c, fr| c.lam(self.v(), |c, x| self.put(c, i, self.fw, fr, x)))
    }
    /// The operand of the `local.get` row: hands slot `i` of the frame to its continuation.
    pub fn getter(&self, c: &mut Cx, i: usize) -> Expr {
        c.lam(self.fr(), |c, fr| {
            c.lam(sort(0), |c, r| c.lam(arrow(self.v(), c.at(r)), |c, k| self.nth(c, i, self.fw, fr, r, k)))
        })
    }
    /// The row `name` of the table; panics on a name the table lacks (`well_formed` rejects those first).
    fn row(&self, name: &str) -> &Row {
        self.table.row(name).unwrap_or_else(|| panic!("no row {name:?}"))
    }
    /// Constructor `k`'s type over the family `f`; a `Word` leaf takes the operator, then the domain `V -> V -> Bv_1`.
    fn ctor_ty(&self, c: &mut Cx, f: At, k: Ctor) -> Expr {
        let (v, v1) = (self.v(), bv_ty(1));
        c.pi(sort(2), |c, a_at| {
            let fa = |e: Expr| app(c.at(f), e);
            let a = c.at(a_at);
            let (va, vva, v1a) = (prod(v, a), prod(v, prod(v, a)), prod(v1, a));
            match k {
                Ctor::Leaf(Class::Const) => arrow(self.operand_ty(), arrow(fa(va), fa(a))),
                Ctor::Leaf(Class::Word) => arrow(arrow(v, arrow(v, v)), arrow(arrow(v, arrow(v, v1)), arrow(fa(va), fa(vva)))),
                Ctor::Leaf(Class::Bit) => arrow(arrow(v, arrow(v, v1)), arrow(fa(v1a), fa(vva))),
                Ctor::If => arrow(fa(a), arrow(fa(a), fa(v1a))),
                Ctor::Leaf(Class::Set) => arrow(self.setter_ty(), arrow(fa(a), fa(va))),
                Ctor::Br => arrow(fa(va), fa(a)),
                // `Pi S. (S -> Fr x A) -> V -> F (V, A) -> F S`: the arguments over `A` are `S`, the callee's index
                // a word, the rest of the program continues with the callee's answer pushed
                Ctor::Call => c.pi(sort(2), |c, s| {
                    let (a, sa) = (c.at(a_at), c.at(s));
                    arrow(arrow(sa, prod(self.fr(), a)), arrow(v, arrow(app(c.at(f), prod(v, a)), app(c.at(f), sa))))
                }),
            }
        })
    }
    /// The constructor binders, each wrapped by `wrap` (`lam` or `pi`), then `body` with their variables.
    fn ctors(&self, c: &mut Cx, f: At, wrap: fn(Expr, Expr) -> Expr, body: &mut dyn FnMut(&mut Cx, &[At]) -> Expr) -> Expr {
        let w = *self;
        let tys: Vec<Ty> = ctor_list().into_iter().map(|k| ty!(|c, _x| w.ctor_ty(c, f, k))).collect();
        tele(c, &tys, &mut vec![], &wrap, body)
    }
    /// `Prog S T`, with `S` and `T` built at each use.
    pub fn prog_ty(&self, c: &mut Cx, s: &dyn Fn(&Cx) -> Expr, t: &dyn Fn(&Cx) -> Expr) -> Expr {
        c.pi(F_TY(), |c, f| {
            let nil = app(c.at(f), t(c));
            c.pi(nil, |c, _| self.ctors(c, f, pi, &mut |c, _| app(c.at(f), s(c))))
        })
    }
    /// `Pi S. Prog S (K, S)`: code that pushes one value of kind `k`.
    pub fn code_ty(&self, c: &mut Cx, k: K) -> Expr {
        c.pi(sort(2), |c, s| self.prog_ty(c, &|c| c.at(s), &|c| self.sty(c, &[k], s)))
    }
    /// `code` as a program from `ks` over `base`; `arities[j]` is the number of words module position `j` pops.
    pub fn prog(&self, c: &mut Cx, code: &[Ins], ks: &[K], base: At, arities: &[Option<usize>]) -> Expr {
        let out = out_stack(self.table, code, ks.to_vec(), arities);
        c.lam(F_TY(), |c, f| {
            let nil = app(c.at(f), self.sty(c, &out, base));
            c.lam(nil, |c, nil| {
                self.ctors(c, f, lam, &mut |c, ct| {
                    let ct = ct.to_vec();
                    self.seq(c, f, &ct, base, code, ks.to_vec(), arities, &|c, _| c.at(nil))
                })
            })
        })
    }
    #[allow(clippy::too_many_arguments)]
    fn seq(&self, c: &mut Cx, f: At, ct: &[At], base: At, code: &[Ins], st: Vec<K>, ar: &[Option<usize>], k: &dyn Fn(&mut Cx, Vec<K>) -> Expr) -> Expr {
        // one frame per instruction through `cont`: run on the kernel's growable stack (a 2 MB thread overflowed at
        // the JIT's tree cap)
        tatic_kernel::grow(|| self.seq_step(c, f, ct, base, code, st, ar, k))
    }
    #[allow(clippy::too_many_arguments)]
    fn seq_step(&self, c: &mut Cx, f: At, ct: &[At], base: At, code: &[Ins], st: Vec<K>, ar: &[Option<usize>], k: &dyn Fn(&mut Cx, Vec<K>) -> Expr) -> Expr {
        let Some((ins, rest)) = code.split_first() else { return k(c, st) };
        let cont = |c: &mut Cx, st: Vec<K>| self.seq(c, f, ct, base, rest, st, ar, k);
        let ty = |c: &Cx, ks: &[K]| self.sty(c, ks, base);
        let cons = |c: &Cx, i: usize, args: Vec<Expr>| apps(c.at(ct[i]), args);
        let below = |n: usize| st[n..].to_vec();
        let with = |top: &[K], n: usize| [top, &st[n..]].concat();
        match ins {
            Ins::Row { name, operand } => {
                let row = self.row(name);
                let (pops, i) = (row.class.pops(), ctor_idx(Ctor::Leaf(row.class)));
                let r = cont(c, match row.class.push() {
                    Some(k) => with(&[k], pops),
                    None => below(pops),
                });
                let meaning = (row.meaning)(c, self, *operand);
                let mut args = vec![ty(c, &below(pops)), meaning];
                // a Word row also carries its domain `V -> V -> Bv_1`, built at this site through `constant_n`
                if row.class == Class::Word {
                    args.push(constant_n(row.dom.circuit, self.n));
                }
                args.push(r);
                cons(c, i, args)
            }
            Ins::Raw(s) => unreachable!("prog's out_stack rejects Raw({s:?})"),
            Ins::Br => {
                let r = cont(c, with(&[K::W], 0));
                cons(c, ctor_idx(Ctor::Br), vec![ty(c, &st), r])
            }
            Ins::Call(j) => {
                let m = ar.get(*j).copied().flatten().unwrap_or_else(|| panic!("prog's out_stack rejects Call({j})"));
                let (s_ty, a_ty) = (ty(c, &st), ty(c, &below(m)));
                let unpack = self.unpack(c, m, s_ty.clone(), a_ty.clone());
                let r = cont(c, with(&[K::W], m));
                cons(c, ctor_idx(Ctor::Call), vec![a_ty, s_ty, unpack, lit(self.n, *j as u128), r])
            }
            Ins::If(t, e) => {
                let th = self.seq(c, f, ct, base, t, below(1), ar, &cont);
                let el = self.seq(c, f, ct, base, e, below(1), ar, &cont);
                cons(c, ctor_idx(Ctor::If), vec![ty(c, &below(1)), th, el])
            }
        }
    }
    /// The `Call` operand `unpack : S -> Fr x A` for a callee of `m` parameters: the arguments (the deepest is the first
    /// parameter) go to the callee's slots `0..m`, every other slot is 0, and the stack `A` below them comes back.
    fn unpack(&self, c: &mut Cx, m: usize, s_ty: Expr, a_ty: Expr) -> Expr {
        let (s_at, a_at) = (c.mark(s_ty), c.mark(a_ty));
        c.lam(c.at(s_at), |c, s| {
            let res = c.mark(prod(self.fr(), c.at(a_at)));
            self.split_args(c, res, a_at, m, s, &mut |c, xs, rest| {
                let vals: Vec<Expr> = xs.iter().map(|x| c.at(*x)).collect();
                mkpair(c.at(a_at), self.frame(&vals), c.at(rest))
            })
        })
    }
    /// `sigrec` on a stack `st : V^m x A` into `R`: `body(c, words, below)` with the words in parameter order (the
    /// deepest first).
    fn split_args(&self, c: &mut Cx, r: At, a: At, m: usize, st: At, body: &mut dyn FnMut(&mut Cx, Vec<At>, At) -> Expr) -> Expr {
        if m == 0 {
            return body(c, vec![], st);
        }
        let tail = c.mark(self.words(m - 1, c.at(a)));
        self.split(c, r, self.v(), tail, st, |c, x, s| {
            self.split_args(c, r, a, m - 1, s, &mut |c, mut xs, rest| {
                xs.push(x);
                body(c, xs, rest)
            })
        })
    }
    /// `sigrec` on a stack `st : A x B` into `R`: `body(c, top, below)`.
    pub(super) fn split(&self, c: &mut Cx, r: At, a: Expr, b: At, st: At, body: impl FnOnce(&mut Cx, At, At) -> Expr) -> Expr {
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
    fn interp(&self, c: &mut Cx, r: At, ch: Option<At>, z: At, calls: At, restart: At) -> Vec<Expr> {
        let (v, v1) = (self.v(), bv_ty(1));
        let w = *self;
        let fr_ty = self.fr();
        // `\A [ops..] rest fr st mu. body`, with `rest : G (rest_ty A)` and `st : st_ty A`; `extras` are the operand types
        let shape = |c: &mut Cx, extras: &[Expr], rest_ty: &dyn Fn(Expr) -> Expr, st_ty: &dyn Fn(Expr) -> Expr,
                     body: &Body| {
            fn bind(c: &mut Cx, tys: &[Expr], ops: &mut Vec<At>, k: &mut dyn FnMut(&mut Cx, &[At]) -> Expr) -> Expr {
                match tys.split_first() {
                    None => k(c, ops),
                    Some((t, rest)) => c.lam(*t, |c, op| {
                        ops.push(op);
                        bind(c, rest, ops, k)
                    }),
                }
            }
            c.lam(sort(2), |c, a| {
                bind(c, extras, &mut vec![], &mut |c, ops| {
                    let rt = w.g(c, r, rest_ty(c.at(a)));
                    c.lam(rt, |c, rest| {
                        c.lam(fr_ty, |c, fr| {
                            c.lam(st_ty(c.at(a)), |c, st| {
                                let m = w.mem(c, r);
                                c.lam(m, |c, mu| body(c, a, ops, rest, fr, st, mu))
                            })
                        })
                    })
                })
            })
        };
        // `choose R cond t e`, through the proof's opaque probe when there is one
        let pick = |c: &Cx, cond: Expr, t: Expr, e: Expr| match ch {
            Some(f) => apps(c.at(f), vec![c.at(r), cond, t, e]),
            None => choose(c.at(r), cond, t, e),
        };
        // a 0-to-1 row pushes its operand's value at the frame
        let konst = shape(c, &[self.operand_ty()], &|a| prod(v, a), &|a| a, &|c, a, ops, rest, fr, st, mu| {
            let kont = c.lam(v, |c, x| app3(c.at(rest), c.at(fr), mkpair(c.at(a), c.at(x), c.at(st)), c.at(mu)));
            app3(c.at(ops[0]), c.at(fr), c.at(r), kont)
        });
        // a 2-to-1 row pops `y` then `x` and pushes `op x y`; a Word row first guards on its domain `dom x y`
        // (else branch `z`, the statement's no-value answer), through `pick`
        let binop = |c: &mut Cx, out: Expr, guarded: bool| {
            let mut extras = vec![arrow(v, arrow(v, out))];
            if guarded {
                extras.push(arrow(v, arrow(v, v1)));
            }
            shape(c, &extras, &|a| prod(out, a), &|a| prod(v, prod(v, a)), &|c, a, ops, rest, fr, st, mu| {
                let below = c.mark(prod(v, c.at(a)));
                w.split(c, r, v, below, st, |c, y, rs| {
                    w.split(c, r, v, a, rs, |c, x, s| {
                        let val = app2(c.at(ops[0]), c.at(x), c.at(y));
                        let kk = app3(c.at(rest), c.at(fr), mkpair(c.at(a), val, c.at(s)), c.at(mu));
                        if !guarded {
                            return kk;
                        }
                        pick(c, app2(c.at(ops[1]), c.at(x), c.at(y)), kk, c.at(z))
                    })
                })
            })
        };
        let bin = binop(c, v, true);
        let cmp = binop(c, v1, false);
        let if_ = c.lam(sort(2), |c, a| {
            let ga = w.g(c, r, c.at(a));
            c.lam(ga, |c, th| {
                let ga = w.g(c, r, c.at(a));
                c.lam(ga, |c, el| {
                    c.lam(fr_ty, |c, fr| {
                        c.lam(prod(v1, c.at(a)), |c, st| {
                            let m = w.mem(c, r);
                            c.lam(m, |c, mu| {
                                w.split(c, r, v1, a, st, |c, b, s| {
                                    let (fr, s, mu) = (c.at(fr), c.at(s), c.at(mu));
                                    let (x, y) = (app3(c.at(th), fr.clone(), s.clone(), mu.clone()), app3(c.at(el), fr, s, mu));
                                    pick(c, c.at(b), x, y)
                                })
                            })
                        })
                    })
                })
            })
        });
        // `\A S unp idx rest fr st mu`: unpack the arguments into the callee's frame, run entry `idx` of the environment
        // there at the memory as it is, and continue with the callee's final memory, the caller's own frame and the
        // callee's answer pushed. With an empty `rest` that continuation is the activation's own, up to the relation.
        let call = c.lam(sort(2), |c, a| {
            c.lam(sort(2), |c, s| {
                let up_ty = arrow(c.at(s), prod(fr_ty, c.at(a)));
                c.lam(up_ty, |c, unp| {
                    c.lam(v, |c, idx| {
                        let rt = w.g(c, r, prod(v, c.at(a)));
                        c.lam(rt, |c, rest| {
                            c.lam(fr_ty, |c, fr| {
                                c.lam(c.at(s), |c, st| {
                                    let m = w.mem(c, r);
                                    c.lam(m, |c, mu| {
                                        let ua = c.mark(app(c.at(unp), c.at(st)));
                                        w.split(c, r, fr_ty, a, ua, |c, fr2, below| {
                                            let kont = c.lam(v, |c, y| {
                                                let mm = w.mem(c, r);
                                                c.lam(mm, |c, mu2| app3(c.at(rest), c.at(fr), mkpair(c.at(a), c.at(y), c.at(below)), c.at(mu2)))
                                            });
                                            app(app3(c.at(calls), c.at(idx), c.at(fr2), c.at(mu)), kont)
                                        })
                                    })
                                })
                            })
                        })
                    })
                })
            })
        });
        // `\A op rest fr st mu`: pop the word, write it to the frame through `op`, run `rest` at the new frame
        let set = shape(c, &[self.setter_ty()], &|a| a, &|a| prod(v, a), &|c, a, ops, rest, fr, st, mu| {
            w.split(c, r, v, a, st, |c, x, s| {
                let fr2 = app2(c.at(ops[0]), c.at(fr), c.at(x));
                app3(c.at(rest), fr2, c.at(s), c.at(mu))
            })
        });
        // `\A rest fr st mu`: the activation's own entry again at the current frame (the stack and the rest are dropped)
        let br = shape(c, &[], &|a| prod(v, a), &|a| a, &|c, _a, _ops, _rest, fr, _st, mu| app2(c.at(restart), c.at(fr), c.at(mu)));
        let built = [
            (Ctor::Leaf(Class::Const), konst),
            (Ctor::Leaf(Class::Word), bin),
            (Ctor::Leaf(Class::Bit), cmp),
            (Ctor::If, if_),
            (Ctor::Call, call),
            (Ctor::Leaf(Class::Set), set),
            (Ctor::Br, br),
        ];
        ctor_list().into_iter().map(|k| built.iter().find(|(b, _)| *b == k).expect("interp builds every constructor").1).collect()
    }
    /// `M p R k`, of type `G S` for `p : Prog S T` and `k : G T`.
    pub fn meaning(&self, c: &mut Cx, p: At, k: At, me: &MeaningEnv) -> Expr {
        let r = me.r;
        let gfam = c.lam(sort(2), |c, a| self.g(c, r, c.at(a)));
        let mut args = vec![gfam, c.at(k)];
        args.extend(self.interp(c, r, me.ch, me.z, me.calls, me.restart));
        apps(c.at(p), args)
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
}
