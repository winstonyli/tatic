//! The machine: programs as kernel data (docs/tier-cycle/, "Wasm programs as kernel data, kept"; option B of "Formalizing the target machine" there),
//! over a `Table` of rows (`wasm::table` is the wasm one).
//!
//! A program is a Church-encoded instruction tree typed by its start and end stacks,
//! `Prog S T = Pi F:(Sort2 -> Sort2). F T -> const -> word -> bit -> if -> loop -> store -> load -> F S` (one leaf
//! constructor per row class, in `ctor_list` order), where each
//! constructor takes the rest of the program (`push : Pi A. V -> F (V,A) -> F A`), so appending puts one program at the
//! other's nil and holds by beta. Its meaning `M p N R k z` interprets `F A` as `A -> Mem -> R` for an answer type
//! `R : Sort0`: words are width-n Church vectors (`encoding.rs`), stacks are nested `Sigma` pairs, memory is
//! `Mem = V -> (V -> R) -> R`, an `if` chooses between its two continuations by its one-bit condition (`choose`, as only
//! the taken branch runs), and a `loop` unrolls its body `N` times, `N` a Church numeral at Sort2, then answers the
//! timeout `z`. Nothing is postulated.
use super::*;

/// `choose w x y = w (Lift R) (\c Y g. g (c R x y)) R id`, with `Lift R = Pi Y:Sort0. (R -> Y) -> Y`: a one-bit word
/// opens only at Sort1, and `Lift R` carries the Sort0 answer through it.
pub fn choose(r: Expr, w: Expr, x: Expr, y: Expr) -> Expr {
    let lift = pi(sort(0), arrow(arrow(shift(&r, 0, 1), var(0)), var(0)));
    let k = lam(bool0(), lam(sort(0), lam(arrow(shift(&r, 0, 2), var(0)),
        app(var(0), app3(var(2), shift(&r, 0, 3), shift(&x, 0, 3), shift(&y, 0, 3))))));
    apps(w, vec![lift, k, r, lam(r, var(0))])
}

/// An interpreter case's body from `A`, its operator if any, `rest`, the stack and the memory.
type Body<'a> = dyn Fn(&mut Cx, At, Option<At>, At, At, At) -> Expr + 'a;

/// What a stack slot holds: an n-bit word or a one-bit word (a compare's result).
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum K {
    W,
    B,
}

/// The shape of a row: its stack effect and the constructor class it is built through. `Const` is 0 to 1 with a word
/// result, `Word` 2 to 1 word-valued, `Bit` 2 to 1 bit-valued.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Class {
    Const,
    Word,
    Bit,
}

impl Class {
    /// How many words the row pops.
    pub fn pops(self) -> usize {
        match self {
            Class::Const => 0,
            Class::Word | Class::Bit => 2,
        }
    }
    /// What the row leaves on the stack.
    pub fn kind(self) -> K {
        match self {
            Class::Const | Class::Word => K::W,
            Class::Bit => K::B,
        }
    }
}

/// One leaf instruction: its name, class, kernel meaning and printed line. `meaning(c, m, operand)` is the
/// constructor's operand: for `Const` the word (a numeral), for `Word`/`Bit` the closed circuit (`operand` is 0).
pub struct Row {
    pub name: &'static str,
    pub class: Class,
    pub meaning: fn(&mut Cx, &Machine, i64) -> Expr,
    pub line: fn(i64) -> String,
}

/// A backend's leaf instructions, by name.
pub struct Table {
    rows: Vec<Row>,
}

impl Table {
    /// Panics on a duplicate name.
    pub fn new(rows: Vec<Row>) -> Table {
        for (i, r) in rows.iter().enumerate() {
            assert!(rows[..i].iter().all(|q| q.name != r.name), "duplicate row {:?}", r.name);
        }
        Table { rows }
    }
    pub fn row(&self, name: &str) -> Option<&Row> {
        self.rows.iter().find(|r| r.name == name)
    }
}

/// An instruction of a function body (spec 2026-11-08-v07-straight-line-gate-design.md, section 2). `Br(j)` jumps to
/// the `j`-th enclosing loop's start. `Store` and `Load` serve the machine's own laws and are never emitted;
/// `Raw` is a line the lowering emits that the machine does not model, so a body holding one is not well formed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ins {
    /// A table row; a 2-to-1 row carries operand 0.
    Row { name: &'static str, operand: i64 },
    /// `local.get $p{i}`: slot `i` of the frame, at address `i`.
    LocalGet(u32),
    If(Vec<Ins>, Vec<Ins>),
    Loop(Vec<Ins>),
    Br(usize),
    Store,
    Load,
    Raw(String),
}

/// The one stack analysis: the stack after `code` from `st` (top first), `None` if every path jumps, or why the
/// code is ill formed. `loops` holds the entry stacks of the enclosing loops, innermost first.
fn shape(table: &Table, code: &[Ins], mut st: Vec<K>, loops: &[Vec<K>]) -> Result<Option<Vec<K>>, String> {
    let pop = |st: &mut Vec<K>, want: &[K]| {
        if !st.starts_with(want) {
            return Err(format!("stack {st:?} lacks {want:?}"));
        }
        st.drain(..want.len());
        Ok(())
    };
    for ins in code {
        match ins {
            Ins::LocalGet(_) => st.insert(0, K::W),
            Ins::Row { name, operand } => {
                let Some(row) = table.row(name) else { return Err(format!("unknown row {name:?}")) };
                if row.class != Class::Const && *operand != 0 {
                    return Err(format!("row {name:?} takes no operand, got {operand}"));
                }
                pop(&mut st, &[K::W, K::W][..row.class.pops()])?;
                st.insert(0, row.class.kind())
            }
            Ins::If(t, e) => {
                pop(&mut st, &[K::B])?;
                st = match (shape(table, t, st.clone(), loops)?, shape(table, e, st, loops)?) {
                    (Some(a), Some(b)) if a != b => return Err(format!("if arms end on different stacks: {a:?}, {b:?}")),
                    (Some(a), _) | (None, Some(a)) => a,
                    (None, None) => return Ok(None),
                }
            }
            Ins::Loop(body) => {
                let ls = [std::slice::from_ref(&st), loops].concat();
                match shape(table, body, st.clone(), &ls)? {
                    Some(s) => st = s,
                    None => return Ok(None),
                }
            }
            Ins::Br(j) => {
                let Some(want) = loops.get(*j) else { return Err(format!("br {j} with {} enclosing loops", loops.len())) };
                if want != &st {
                    return Err(format!("br {j} with stack {st:?}, the loop's is {want:?}"));
                }
                return Ok(None);
            }
            Ins::Store => pop(&mut st, &[K::W, K::W])?,
            Ins::Load => {
                pop(&mut st, &[K::W])?;
                st.insert(0, K::W)
            }
            Ins::Raw(s) => return Err(format!("raw line {s:?}")),
        }
    }
    Ok(Some(st))
}

/// The stack after `code` from `st` (top first), or `None` if every path jumps; panics on ill-formed code.
pub fn out_stack(table: &Table, code: &[Ins], st: Vec<K>) -> Option<Vec<K>> {
    shape(table, code, st, &[]).unwrap_or_else(|e| panic!("{e}"))
}

/// Whether `code` from `st` is something the machine runs and falls through: no `Raw`, no unknown row or operand on a
/// 2-to-1 row, no underflow, matching `if` arms and `br`s to an enclosing loop with its entry stack.
pub fn well_formed(table: &Table, code: &[Ins], st: &[K]) -> bool {
    matches!(shape(table, code, st.to_vec(), &[]), Ok(Some(_)))
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

/// The machine's constructors, in `Prog`'s binder order: one leaf constructor per row class, then the structural ones.
#[derive(Clone, Copy, PartialEq, Debug)]
enum Ctor {
    Leaf(Class),
    If,
    Loop,
    Store,
    Load,
}

/// The one list the constructor order is read from (`ctor_ty`, `interp`, `seq_step`, `ifp`, the count).
fn ctor_list() -> [Ctor; 7] {
    [Ctor::Leaf(Class::Const), Ctor::Leaf(Class::Word), Ctor::Leaf(Class::Bit), Ctor::If, Ctor::Loop, Ctor::Store, Ctor::Load]
}

fn ctor_idx(k: Ctor) -> usize {
    ctor_list().iter().position(|x| *x == k).expect("ctor_list holds every constructor")
}

/// The encoding at word width `n`, over `table`'s rows.
#[derive(Clone, Copy)]
pub struct Machine<'t> {
    pub n: usize,
    pub table: &'t Table,
}

const F_TY: fn() -> Expr = || arrow(sort(2), sort(2));

impl Machine<'_> {
    pub fn v(&self) -> Expr {
        bv_ty(self.n)
    }
    fn word(&self, k: K) -> Expr {
        bv_ty(if k == K::W { self.n } else { 1 })
    }
    /// The stack type `ks` (top first) over the base `base`.
    pub fn sty(&self, c: &Cx, ks: &[K], base: At) -> Expr {
        // the words are closed, so only the base moves: shift it under all `ks.len()` binders once
        let base = shift(&c.at(base), 0, ks.len() as i32);
        ks.iter().rev().fold(base, |acc, k| sigma(self.word(*k), acc))
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
    /// The row `name` of the table; panics on a name the table lacks (`well_formed` rejects those first).
    fn row(&self, name: &str) -> &Row {
        self.table.row(name).unwrap_or_else(|| panic!("no row {name:?}"))
    }
    fn ctor_ty(&self, c: &mut Cx, f: At, k: Ctor) -> Expr {
        let (v, v1) = (self.v(), bv_ty(1));
        c.pi(sort(2), |c, a| {
            let fa = |e: Expr| app(c.at(f), e);
            let a = c.at(a);
            let (va, vva, v1a) = (prod(v, a), prod(v, prod(v, a)), prod(v1, a));
            match k {
                Ctor::Leaf(Class::Const) => arrow(v, arrow(fa(va), fa(a))),
                Ctor::Leaf(Class::Word) => arrow(arrow(v, arrow(v, v)), arrow(fa(va), fa(vva))),
                Ctor::Leaf(Class::Bit) => arrow(arrow(v, arrow(v, v1)), arrow(fa(v1a), fa(vva))),
                Ctor::If => arrow(fa(a), arrow(fa(a), fa(v1a))),
                Ctor::Loop => arrow(arrow(fa(a), fa(a)), fa(a)),
                Ctor::Store => arrow(fa(a), fa(vva)),
                Ctor::Load => arrow(fa(va), fa(va)),
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
    /// `code` as a program from `ks` over `base`.
    pub fn prog(&self, c: &mut Cx, code: &[Ins], ks: &[K], base: At) -> Expr {
        let out = out_stack(self.table, code, ks.to_vec()).expect("a program that falls through");
        c.lam(F_TY(), |c, f| {
            let nil = app(c.at(f), self.sty(c, &out, base));
            c.lam(nil, |c, nil| {
                self.ctors(c, f, lam, &mut |c, ct| {
                    let ct = ct.to_vec();
                    self.seq(c, f, &ct, base, code, ks.to_vec(), &|c, _| c.at(nil), &[])
                })
            })
        })
    }
    #[allow(clippy::too_many_arguments)]
    fn seq(&self, c: &mut Cx, f: At, ct: &[At], base: At, code: &[Ins], st: Vec<K>, k: &dyn Fn(&mut Cx, Vec<K>) -> Expr,
        labels: &[(At, Vec<K>)]) -> Expr {
        // one frame per instruction through `cont`: run on the kernel's growable stack (a 2 MB thread overflowed at
        // the JIT's tree cap)
        tatic_kernel::grow(|| self.seq_step(c, f, ct, base, code, st, k, labels))
    }
    #[allow(clippy::too_many_arguments)]
    fn seq_step(&self, c: &mut Cx, f: At, ct: &[At], base: At, code: &[Ins], st: Vec<K>, k: &dyn Fn(&mut Cx, Vec<K>) -> Expr,
        labels: &[(At, Vec<K>)]) -> Expr {
        let Some((ins, rest)) = code.split_first() else { return k(c, st) };
        let cont = |c: &mut Cx, st: Vec<K>| self.seq(c, f, ct, base, rest, st, k, labels);
        let ty = |c: &Cx, ks: &[K]| self.sty(c, ks, base);
        let cons = |c: &Cx, i: usize, args: Vec<Expr>| apps(c.at(ct[i]), args);
        let below = |n: usize| st[n..].to_vec();
        let with = |top: &[K], n: usize| [top, &st[n..]].concat();
        match ins {
            Ins::Row { name, operand } => {
                let row = self.row(name);
                let (pops, i) = (row.class.pops(), ctor_idx(Ctor::Leaf(row.class)));
                let r = cont(c, with(&[row.class.kind()], pops));
                let meaning = (row.meaning)(c, self, *operand);
                cons(c, i, vec![ty(c, &below(pops)), meaning, r])
            }
            // push the slot's address, then load it
            Ins::LocalGet(i) => {
                let r = cont(c, with(&[K::W], 0));
                let load = cons(c, ctor_idx(Ctor::Load), vec![ty(c, &st), r]);
                cons(c, ctor_idx(Ctor::Leaf(Class::Const)), vec![ty(c, &st), lit(self.n, *i as u128), load])
            }
            Ins::Raw(s) => unreachable!("prog's out_stack rejects Raw({s:?})"),
            Ins::If(t, e) => {
                let th = self.seq(c, f, ct, base, t, below(1), &cont, labels);
                let el = self.seq(c, f, ct, base, e, below(1), &cont, labels);
                cons(c, ctor_idx(Ctor::If), vec![ty(c, &below(1)), th, el])
            }
            Ins::Loop(body) => {
                let a = ty(c, &st);
                let label = app(c.at(f), a);
                let b = c.lam(label, |c, l| {
                    let ls = [&[(l, st.clone())], labels].concat();
                    self.seq(c, f, ct, base, body, st.clone(), &cont, &ls)
                });
                cons(c, ctor_idx(Ctor::Loop), vec![a, b])
            }
            Ins::Br(j) => {
                let (l, ls) = &labels[*j];
                assert_eq!(ls, &st, "br with a stack other than the loop's");
                c.at(*l)
            }
            Ins::Store => {
                let r = cont(c, below(2));
                cons(c, ctor_idx(Ctor::Store), vec![ty(c, &below(2)), r])
            }
            Ins::Load => {
                let r = cont(c, st.clone());
                cons(c, ctor_idx(Ctor::Load), vec![ty(c, &below(1)), r])
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
        let built = [
            (Ctor::Leaf(Class::Const), push),
            (Ctor::Leaf(Class::Word), bin),
            (Ctor::Leaf(Class::Bit), cmp),
            (Ctor::If, if_),
            (Ctor::Loop, loop_),
            (Ctor::Store, store),
            (Ctor::Load, load),
        ];
        ctor_list().into_iter().map(|k| built.iter().find(|(b, _)| *b == k).expect("interp builds every constructor").1).collect()
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
                self.ctors(c, f, lam, &mut |c, ct| {
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
                self.ctors(c, f, lam, &mut |c, ct| {
                    let ctors: Vec<Expr> = ct.iter().map(|x| c.at(*x)).collect();
                    let arm = |c: &Cx, p: At| apps(c.at(p), [vec![c.at(f), c.at(nil)], ctors.clone()].concat());
                    apps(c.at(ct[ctor_idx(Ctor::If)]), vec![c.at(s), arm(c, th), arm(c, el)])
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
        tele(c, &tys, &mut vec![], &pi, &mut |c, x| {
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

pub mod laws;

#[cfg(test)]
mod tests {
    use super::*;

    /// `sty`'s one shift of the base gives the nested `prod`s' term, under binders and at both word widths.
    #[test]
    fn sty_is_the_nested_prods() {
        let t = crate::wasm::table();
        let w = Machine { n: 64, table: &t };
        Cx::default().under(|c, base| {
            c.under(|c, _| {
                for ks in [vec![], vec![K::W], vec![K::B, K::W], vec![K::W, K::W, K::B, K::W, K::W]] {
                    let prods = ks.iter().rev().fold(c.at(base), |acc, k| prod(w.word(*k), acc));
                    assert!(prods == w.sty(c, &ks, base), "sty differs at {ks:?}");
                }
                sort(0)
            })
        });
    }

    #[test]
    fn well_formed_rejects_raw_underflow_bad_br_and_mismatched_arms() {
        let t = crate::wasm::table();
        let cmp_if = |e: Vec<Ins>| vec![konst(1), konst(2), row("lt"), Ins::If(vec![konst(1)], e)];
        assert!(!well_formed(&t, &[Ins::Raw("x".into())], &[]));
        assert!(!well_formed(&t, &[row("add")], &[]));
        assert!(!well_formed(&t, &[Ins::Loop(vec![Ins::Br(1)])], &[]));
        assert!(!well_formed(&t, &cmp_if(vec![]), &[]));
        assert!(well_formed(&t, &cmp_if(vec![konst(2)]), &[]));
        assert!(well_formed(&t, &[Ins::Loop(vec![Ins::LocalGet(0)])], &[]));
    }

    fn konst(v: i64) -> Ins {
        Ins::Row { name: "const", operand: v }
    }
    fn row(name: &'static str) -> Ins {
        Ins::Row { name, operand: 0 }
    }

    #[test]
    fn well_formed_rejects_unknown_rows_and_operands_on_binary_rows() {
        let t = crate::wasm::table();
        assert!(!well_formed(&t, &[Ins::Row { name: "nope", operand: 0 }], &[]));
        assert!(!well_formed(&t, &[konst(1), konst(2), Ins::Row { name: "add", operand: 7 }], &[]));
        assert!(well_formed(&t, &[konst(1), konst(2), Ins::Row { name: "add", operand: 0 }], &[]));
    }

    /// `[local.get 1, local.get 0, sub]` over the frame `upd 0 a (upd 1 b mu)` answers `sub b a` by `refl`, and not
    /// `sub a b`: the slots and the operand order are observable.
    #[test]
    fn local_get_reads_the_frame() {
        let t = crate::wasm::table();
        let w = Machine { n: 8, table: &t };
        let n = w.n;
        let code = [Ins::LocalGet(1), Ins::LocalGet(0), row("sub")];
        // S R k z a b s mu
        let law_for = |b_minus_a: bool| {
            let tys: Vec<Ty> = vec![
                ty!(|_c, _x| sort(2)),
                ty!(|_c, _x| sort(0)),
                ty!(|c, x| { let t = w.sty(c, &[K::W], x[0]); w.g(c, x[1], t) }),
                ty!(|c, x| c.at(x[1])),
                ty!(|_c, _x| bv_ty(n)),
                ty!(|_c, _x| bv_ty(n)),
                ty!(|c, x| c.at(x[0])),
                ty!(|c, x| w.mem(c, x[1])),
            ];
            let frame = |c: &mut Cx, x: &[At]| {
                let inner = w.upd(c, x[1], lit(n, 1), c.at(x[5]), c.at(x[7]));
                w.upd(c, x[1], lit(n, 0), c.at(x[4]), inner)
            };
            law(&tys, |c, x| {
                let p = w.prog(c, &code, &[], x[0]);
                let p = c.mark(p);
                let fuel = c.mark(nat2_lit(0));
                let m = frame(c, x);
                let l = app2(w.meaning(c, p, fuel, x[1], x[2], x[3]), c.at(x[6]), m);
                let (p, q) = if b_minus_a { (x[5], x[4]) } else { (x[4], x[5]) };
                let val = app2(sub(n), c.at(p), c.at(q));
                (refl(l), id(c.at(x[1]), l, app2(c.at(x[2]), mkpair(c.at(x[0]), val, c.at(x[6])), m)))
            })
        };
        tatic_kernel::scoped(|| {
            let (p, s) = law_for(true);
            ck("local.get 1, local.get 0, sub = sub b a", &p, &s);
            let (p, s) = law_for(false);
            assert!(holds(&p, &s).is_err(), "sub a b must be rejected");
        })
    }
}
