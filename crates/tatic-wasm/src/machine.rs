//! The machine: programs as kernel data (docs/tier-cycle/, "Wasm programs as kernel data, kept"; option B of "Formalizing the target machine" there),
//! over a `Table` of rows (`wasm::table` is the wasm one).
//!
//! A program is a Church-encoded instruction tree typed by its start and end stacks,
//! `Prog S T = Pi F:(Sort2 -> Sort2). F T -> const -> word -> bit -> if -> F S` (one leaf constructor per row class,
//! in `ctor_list` order), where each
//! constructor takes the rest of the program (`const : Pi A. Op -> F (V,A) -> F A`, with the operand
//! `Op = Fr -> Pi R:Sort0. (V -> R) -> R` handing its word to a continuation). Its meaning `M p R k` interprets `F A` as `Fr -> A -> Mem -> R` for an answer type `R : Sort0`: words are width-n Church vectors
//! (`encoding.rs`), stacks are nested `Sigma` pairs, the locals are a frame `Fr = V^fw x V` of nested word pairs
//! passed into every interpreter and never returned (a `const`-class operand projects it), memory is the opaque
//! `Mem = V -> (V -> R) -> R` that nothing reads, and an `if` chooses between its two continuations by its one-bit
//! condition (`choose`, as only the taken branch runs). Nothing is postulated.
use super::*;

/// `choose w x y = w (Lift R) (\c Y g. g (c R x y)) R id`, with `Lift R = Pi Y:Sort0. (R -> Y) -> Y`: a one-bit word
/// opens only at Sort1, and `Lift R` carries the Sort0 answer through it.
pub fn choose(r: Expr, w: Expr, x: Expr, y: Expr) -> Expr {
    let lift = pi(sort(0), arrow(arrow(shift(&r, 0, 1), var(0)), var(0)));
    let k = lam(bool0(), lam(sort(0), lam(arrow(shift(&r, 0, 2), var(0)),
        app(var(0), app3(var(2), shift(&r, 0, 3), shift(&x, 0, 3), shift(&y, 0, 3))))));
    apps(w, vec![lift, k, r, lam(r, var(0))])
}

/// An interpreter case's body from `A`, its operator if any, `rest`, the frame, the stack and the memory.
type Body<'a> = dyn Fn(&mut Cx, At, Option<At>, At, At, At, At) -> Expr + 'a;

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
/// constructor's operand: for `Const` a function of the frame that hands its word (a constant, or a projection of the
/// frame) to a continuation (`Machine::operand_ty`; a plain `Fr -> V` left the redex `op fr` in every stack value, and
/// conversion blew up), for `Word`/`Bit` the closed circuit (`operand` is 0).
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
    /// The row names, in table order.
    pub fn names(&self) -> Vec<&'static str> {
        self.rows.iter().map(|r| r.name).collect()
    }
}

/// An instruction of a function body (spec 2026-11-08-v07-straight-line-gate-design.md, section 2).
/// `Raw` is a line the lowering emits that the machine does not model, so a body holding one is not well formed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ins {
    /// A table row; a 2-to-1 row carries operand 0.
    Row { name: &'static str, operand: i64 },
    If(Vec<Ins>, Vec<Ins>),
    /// `call`/`return_call` to the module position `j` (the printer picks by its tail rule): pops the callee's
    /// arity in words, pushes one. It has no meaning before S2c.
    Call(usize),
    Raw(String),
}

/// How a function reaches its captures: `Params(k)` as its leading parameters `$e0 .. $e{k-1}`; `Pointer` through
/// `$env`, a pointer to its environment slots in linear memory.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EnvAccess {
    Params(usize),
    Pointer,
}

/// A function of a module: its parameter count, how it reaches its captures, and its body.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Entry {
    pub arity: usize,
    pub env: EnvAccess,
    pub code: Vec<Ins>,
}

/// The one stack analysis: the stack after `code` from `st` (top first), or why the
/// code is ill formed. `arities[j]` is the number of words module position `j` pops (`None`: no such callee).
fn shape(table: &Table, code: &[Ins], mut st: Vec<K>, arities: &[Option<usize>]) -> Result<Vec<K>, String> {
    let pop = |st: &mut Vec<K>, want: &[K]| {
        if !st.starts_with(want) {
            return Err(format!("stack {st:?} lacks {want:?}"));
        }
        st.drain(..want.len());
        Ok(())
    };
    for ins in code {
        match ins {
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
                let (a, b) = (shape(table, t, st.clone(), arities)?, shape(table, e, st, arities)?);
                if a != b {
                    return Err(format!("if arms end on different stacks: {a:?}, {b:?}"));
                }
                st = a
            }
            Ins::Call(j) => {
                let Some(Some(n)) = arities.get(*j) else { return Err(format!("call to position {j}, which has no arity")) };
                pop(&mut st, &vec![K::W; *n])?;
                st.insert(0, K::W)
            }
            Ins::Raw(s) => return Err(format!("raw line {s:?}")),
        }
    }
    Ok(st)
}

/// The stack after `code` from `st` (top first); panics on ill-formed code.
pub fn out_stack(table: &Table, code: &[Ins], st: Vec<K>, arities: &[Option<usize>]) -> Vec<K> {
    shape(table, code, st, arities).unwrap_or_else(|e| panic!("{e}"))
}

/// Whether `code` from `st` is something the machine runs and falls through: no `Raw`, no unknown row or operand on a
/// 2-to-1 row, no underflow, matching `if` arms, and each `Call(j)` to a position with an arity.
pub fn well_formed(table: &Table, code: &[Ins], st: &[K], arities: &[Option<usize>]) -> bool {
    shape(table, code, st.to_vec(), arities).is_ok()
}

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
}

/// The one list the constructor order is read from (`ctor_ty`, `interp`, `seq_step`, the count).
fn ctor_list() -> [Ctor; 4] {
    [Ctor::Leaf(Class::Const), Ctor::Leaf(Class::Word), Ctor::Leaf(Class::Bit), Ctor::If]
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

/// What `meaning` is given beside the program and its continuation: the answer type `r` and, for the generator's
/// proofs, `ch`, an opaque `choose` (`Pi R:Sort0. Bv_1 -> R -> R -> R`) an `If` uses in place of the real one.
#[derive(Clone, Copy)]
pub struct MeaningEnv {
    pub r: At,
    pub ch: Option<At>,
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
    fn ctor_ty(&self, c: &mut Cx, f: At, k: Ctor) -> Expr {
        let (v, v1) = (self.v(), bv_ty(1));
        c.pi(sort(2), |c, a| {
            let fa = |e: Expr| app(c.at(f), e);
            let a = c.at(a);
            let (va, vva, v1a) = (prod(v, a), prod(v, prod(v, a)), prod(v1, a));
            match k {
                Ctor::Leaf(Class::Const) => arrow(self.operand_ty(), arrow(fa(va), fa(a))),
                Ctor::Leaf(Class::Word) => arrow(arrow(v, arrow(v, v)), arrow(fa(va), fa(vva))),
                Ctor::Leaf(Class::Bit) => arrow(arrow(v, arrow(v, v1)), arrow(fa(v1a), fa(vva))),
                Ctor::If => arrow(fa(a), arrow(fa(a), fa(v1a))),
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
        let out = out_stack(self.table, code, ks.to_vec(), &[]);
        c.lam(F_TY(), |c, f| {
            let nil = app(c.at(f), self.sty(c, &out, base));
            c.lam(nil, |c, nil| {
                self.ctors(c, f, lam, &mut |c, ct| {
                    let ct = ct.to_vec();
                    self.seq(c, f, &ct, base, code, ks.to_vec(), &|c, _| c.at(nil))
                })
            })
        })
    }
    #[allow(clippy::too_many_arguments)]
    fn seq(&self, c: &mut Cx, f: At, ct: &[At], base: At, code: &[Ins], st: Vec<K>, k: &dyn Fn(&mut Cx, Vec<K>) -> Expr) -> Expr {
        // one frame per instruction through `cont`: run on the kernel's growable stack (a 2 MB thread overflowed at
        // the JIT's tree cap)
        tatic_kernel::grow(|| self.seq_step(c, f, ct, base, code, st, k))
    }
    #[allow(clippy::too_many_arguments)]
    fn seq_step(&self, c: &mut Cx, f: At, ct: &[At], base: At, code: &[Ins], st: Vec<K>, k: &dyn Fn(&mut Cx, Vec<K>) -> Expr) -> Expr {
        let Some((ins, rest)) = code.split_first() else { return k(c, st) };
        let cont = |c: &mut Cx, st: Vec<K>| self.seq(c, f, ct, base, rest, st, k);
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
            Ins::Raw(s) => unreachable!("prog's out_stack rejects Raw({s:?})"),
            Ins::Call(_) => unreachable!("Call has no meaning before S2c"),
            Ins::If(t, e) => {
                let th = self.seq(c, f, ct, base, t, below(1), &cont);
                let el = self.seq(c, f, ct, base, e, below(1), &cont);
                cons(c, ctor_idx(Ctor::If), vec![ty(c, &below(1)), th, el])
            }
        }
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
    fn interp(&self, c: &mut Cx, r: At, ch: Option<At>) -> Vec<Expr> {
        let (v, v1) = (self.v(), bv_ty(1));
        let w = *self;
        let fr_ty = self.fr();
        // `\A [op] rest fr st mu. body`, with `rest : G (rest_ty A)` and `st : st_ty A`
        let shape = |c: &mut Cx, extra: Option<Expr>, rest_ty: &dyn Fn(Expr) -> Expr, st_ty: &dyn Fn(Expr) -> Expr,
                     body: &Body| {
            c.lam(sort(2), |c, a| {
                let inner = |c: &mut Cx, op: Option<At>| {
                    let rt = w.g(c, r, rest_ty(c.at(a)));
                    c.lam(rt, |c, rest| {
                        c.lam(fr_ty, |c, fr| {
                            c.lam(st_ty(c.at(a)), |c, st| {
                                let m = w.mem(c, r);
                                c.lam(m, |c, mu| body(c, a, op, rest, fr, st, mu))
                            })
                        })
                    })
                };
                match extra {
                    Some(t) => c.lam(t, |c, op| inner(c, Some(op))),
                    None => inner(c, None),
                }
            })
        };
        // a 0-to-1 row pushes its operand's value at the frame
        let konst = shape(c, Some(self.operand_ty()), &|a| prod(v, a), &|a| a, &|c, a, op, rest, fr, st, mu| {
            let kont = c.lam(v, |c, x| app3(c.at(rest), c.at(fr), mkpair(c.at(a), c.at(x), c.at(st)), c.at(mu)));
            app3(c.at(op.unwrap()), c.at(fr), c.at(r), kont)
        });
        let binop = |c: &mut Cx, out: Expr| {
            shape(c, Some(arrow(v, arrow(v, out))), &|a| prod(out, a), &|a| prod(v, prod(v, a)), &|c, a, op, rest, fr, st, mu| {
                let below = c.mark(prod(v, c.at(a)));
                w.split(c, r, v, below, st, |c, y, rs| {
                    w.split(c, r, v, a, rs, |c, x, s| {
                        let val = app2(c.at(op.unwrap()), c.at(x), c.at(y));
                        app3(c.at(rest), c.at(fr), mkpair(c.at(a), val, c.at(s)), c.at(mu))
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
                    c.lam(fr_ty, |c, fr| {
                        c.lam(prod(v1, c.at(a)), |c, st| {
                            let m = w.mem(c, r);
                            c.lam(m, |c, mu| {
                                w.split(c, r, v1, a, st, |c, b, s| {
                                    let (fr, s, mu) = (c.at(fr), c.at(s), c.at(mu));
                                    let (x, y) = (app3(c.at(th), fr.clone(), s.clone(), mu.clone()), app3(c.at(el), fr, s, mu));
                                    match ch {
                                        Some(f) => apps(c.at(f), vec![c.at(r), c.at(b), x, y]),
                                        None => choose(c.at(r), c.at(b), x, y),
                                    }
                                })
                            })
                        })
                    })
                })
            })
        });
        let built = [
            (Ctor::Leaf(Class::Const), konst),
            (Ctor::Leaf(Class::Word), bin),
            (Ctor::Leaf(Class::Bit), cmp),
            (Ctor::If, if_),
        ];
        ctor_list().into_iter().map(|k| built.iter().find(|(b, _)| *b == k).expect("interp builds every constructor").1).collect()
    }
    /// `M p R k`, of type `G S` for `p : Prog S T` and `k : G T`.
    pub fn meaning(&self, c: &mut Cx, p: At, k: At, me: &MeaningEnv) -> Expr {
        let r = me.r;
        let gfam = c.lam(sort(2), |c, a| self.g(c, r, c.at(a)));
        let mut args = vec![gfam, c.at(k)];
        args.extend(self.interp(c, r, me.ch));
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

pub mod sim;
pub mod statement;

#[cfg(test)]
mod tests {
    use super::*;

    /// `sty`'s one shift of the base gives the nested `prod`s' term, under binders and at both word widths.
    #[test]
    fn sty_is_the_nested_prods() {
        let t = crate::wasm::table();
        let w = Machine { n: 64, fw: 0, table: &t };
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
    fn well_formed_rejects_raw_underflow_and_mismatched_arms() {
        let t = crate::wasm::table();
        let cmp_if = |e: Vec<Ins>| vec![konst(1), konst(2), row("lt"), Ins::If(vec![konst(1)], e)];
        assert!(!well_formed(&t, &[Ins::Raw("x".into())], &[], &[]));
        assert!(!well_formed(&t, &[row("add")], &[], &[]));
        assert!(!well_formed(&t, &cmp_if(vec![]), &[], &[]));
        assert!(well_formed(&t, &cmp_if(vec![konst(2)]), &[], &[]));
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
        assert!(!well_formed(&t, &[Ins::Row { name: "nope", operand: 0 }], &[], &[]));
        assert!(!well_formed(&t, &[konst(1), konst(2), Ins::Row { name: "add", operand: 7 }], &[], &[]));
        assert!(well_formed(&t, &[konst(1), konst(2), Ins::Row { name: "add", operand: 0 }], &[], &[]));
    }

    /// A `Call(j)` pops its callee's arity and pushes one word; a position without an arity is ill formed.
    #[test]
    fn call_pops_the_callees_arity_and_pushes_one_word() {
        let t = crate::wasm::table();
        let ar = [Some(2), None, Some(0)];
        assert!(well_formed(&t, &[konst(1), konst(2), Ins::Call(0)], &[], &ar));
        assert_eq!(out_stack(&t, &[konst(1), konst(2), Ins::Call(0)], vec![], &ar), vec![K::W]);
        assert!(well_formed(&t, &[Ins::Call(2)], &[], &ar));
        assert!(!well_formed(&t, &[konst(1), Ins::Call(0)], &[], &ar), "underflow");
        assert!(!well_formed(&t, &[Ins::Call(1)], &[], &ar), "no arity");
        assert!(!well_formed(&t, &[Ins::Call(3)], &[], &ar), "no such position");
        assert!(!well_formed(&t, &[Ins::Call(2)], &[], &[]), "no table of arities");
    }

    /// `[local.get 1, local.get 0, sub]` over the frame `(a, (b))` answers `sub b a` by `refl`, and not `sub a b`: the
    /// slots and the operand order are observable. Slot 2 of a width-2 frame is out of range.
    #[test]
    fn local_get_reads_the_frame() {
        let t = crate::wasm::table();
        let w = Machine { n: 8, fw: 2, table: &t };
        let n = w.n;
        let get = |i| Ins::Row { name: "local.get", operand: i };
        let code = [get(1), get(0), row("sub")];
        // S R k a b fr s mu
        let law_for = |b_minus_a: bool| {
            let tys: Vec<Ty> = vec![
                ty!(|_c, _x| sort(2)),
                ty!(|_c, _x| sort(0)),
                ty!(|c, x| { let t = w.sty(c, &[K::W], x[0]); w.g(c, x[1], t) }),
                ty!(|_c, _x| bv_ty(n)),
                ty!(|_c, _x| bv_ty(n)),
                ty!(|c, x| c.at(x[0])),
                ty!(|c, x| w.mem(c, x[1])),
            ];
            law(&tys, |c, x| {
                let p = w.prog(c, &code, &[], x[0]);
                let p = c.mark(p);
                let fr = w.frame(&[c.at(x[3]), c.at(x[4])]);
                let me = MeaningEnv { r: x[1], ch: None };
                let l = app3(w.meaning(c, p, x[2], &me), fr, c.at(x[5]), c.at(x[6]));
                let (p, q) = if b_minus_a { (x[4], x[3]) } else { (x[3], x[4]) };
                let val = app2(sub(n), c.at(p), c.at(q));
                (refl(l), id(c.at(x[1]), l, app3(c.at(x[2]), fr, mkpair(c.at(x[0]), val, c.at(x[5])), c.at(x[6]))))
            })
        };
        tatic_kernel::scoped(|| {
            let (p, s) = law_for(true);
            ck("local.get 1, local.get 0, sub = sub b a", &p, &s);
            let (p, s) = law_for(false);
            assert!(holds(&p, &s).is_err(), "sub a b must be rejected");
        });
        let out_of_range = std::panic::catch_unwind(|| {
            let t = crate::wasm::table();
            let w = Machine { n: 8, fw: 2, table: &t };
            Cx::default().under(|c, base| {
                w.prog(c, &[Ins::Row { name: "local.get", operand: 2 }], &[], base);
                sort(0)
            })
        });
        let msg = out_of_range.expect_err("local.get 2 at fw 2 must panic");
        let msg = msg.downcast_ref::<String>().cloned().unwrap_or_default();
        assert!(msg.contains("out of the frame's width"), "{msg}");
    }

    /// `frame([x])` at `fw` 3 is `(x, (0, (0, 0)))`: padded with zeros and a terminal zero word.
    #[test]
    fn frame_pads_with_zeros() {
        let t = crate::wasm::table();
        let w = Machine { n: 8, fw: 3, table: &t };
        let z = lit(8, 0);
        let xv = lit(8, 5);
        let want = mkpair(w.words(2, w.v()), xv, mkpair(w.words(1, w.v()), z, mkpair(w.words(0, w.v()), z, z)));
        assert!(def_eq(&w.frame(&[xv]), &want), "frame([x]) is not (x, (0, (0, 0)))");
        assert!(def_eq(&infer(&Ctx::new(), &w.frame(&[xv])).unwrap(), &w.fr()), "frame has the type Fr");
    }
}
