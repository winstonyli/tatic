//! The gate (v0.8; `docs/superpowers/specs/2026-11-10-v08-recursion-once-design.md`, D4): the kernel checks that the
//! instruction list the JIT prints, run on `tatic_wasm`'s machine at n = 64, simulates the source term for every
//! fuel. The statement is `tatic_wasm::machine::statement`'s (trusted); `tatic_wasm::machine::sim::prove` (untrusted)
//! makes the proof. The source side is built from the term, never from `code` (`source_fn`), so a lowering bug cannot
//! cancel itself. Both sides read operators from the one table (`shape::wasm_table`, the row's `meaning`), so a wrong
//! row is the table check's to catch (`jit/op_table_tests.rs`), not the gate's.

use hashbrown::HashSet;
use tatic_kernel::{app2, scoped, Expr};
use tatic_wasm::encoding::{holds, lit, low_bits, Cx};
use tatic_wasm::machine::sim::prove;
use tatic_wasm::machine::statement::{statement, ModEntry, SEnv, SrcFn};
use tatic_wasm::machine::{well_formed, Class, Entry, EnvAccess, Ins, Machine, Table};

use crate::jit::compile::tree_size;
use crate::jit::shape::{classify, is_comparison, peel, Shape};
use crate::lang::term::{Hash, Term, TermStore};

const N: usize = 64;

/// The largest tree (`compile::tree_size`) the gate takes: the largest power of two under the JIT path's 0.4 s.
/// `doubling(12)` (8192 nodes) took 0.35-0.38 s, `doubling(13)` (16384) 0.74-0.88 s, nearly all of it the check (doc
/// 15, "Why the build grew 2.2x per doubling").
pub(crate) const MAX_GATE_TREE: u64 = 8192;

/// Whether `h` is in the gate's fragment (D3a): `arity` ≥ 1 leading `Abs`, then a body of parameters, literals and
/// table rows, where every `If` is in tail position and tests a comparison of operands, and comparisons appear
/// nowhere else; and at most `MAX_GATE_TREE` nodes as a tree.
pub fn in_fragment(table: &Table, store: &TermStore, h: Hash, arity: usize) -> bool {
    if arity == 0 || tree_size(store, h) > MAX_GATE_TREE {
        return false;
    }
    let mut body = h;
    for _ in 0..arity {
        match store.resolve(body) {
            Term::Abs(b) => body = *b,
            _ => return false,
        }
    }
    tail(table, store, body, arity, &mut HashSet::new())
}

/// A tail position: an `If` on a comparison of operands with tail arms, or an operand.
fn tail(table: &Table, store: &TermStore, h: Hash, m: usize, seen: &mut HashSet<Hash>) -> bool {
    match store.resolve(h) {
        Term::If(c, t, e) => match store.resolve(*c) {
            Term::Prim(p, a, b) => {
                is_comparison(*p)
                    && operand(table, store, *a, m, seen)
                    && operand(table, store, *b, m, seen)
                    && tail(table, store, *t, m, seen)
                    && tail(table, store, *e, m, seen)
            }
            _ => false,
        },
        _ => operand(table, store, h, m, seen),
    }
}

/// An operand: a parameter, a literal, or a word-result row of operands. `seen` holds operands already accepted, so
/// a shared subterm is checked once.
fn operand(table: &Table, store: &TermStore, h: Hash, m: usize, seen: &mut HashSet<Hash>) -> bool {
    if seen.contains(&h) {
        return true;
    }
    let ok = match store.resolve(h) {
        Term::Var(i) => (*i as usize) < m,
        Term::Lit(_) => true,
        Term::Prim(p, a, b) => {
            table.row(p.name()).is_some_and(|r| r.class == Class::Word)
                && operand(table, store, *a, m, seen)
                && operand(table, store, *b, m, seen)
        }
        _ => false,
    };
    if ok {
        seen.insert(h);
    }
    ok
}

/// The source in a form `parse` has already checked: parameters by position, literals, word rows, and `If`s on a
/// comparison in tail position.
enum Src {
    Param(usize),
    Lit(u128),
    Prim(&'static str, Box<Src>, Box<Src>),
    If(&'static str, Box<Src>, Box<Src>, Box<Src>, Box<Src>),
}

/// `h` as a `Src`: only a tail position admits an `If`. `None` outside the fragment.
fn parse(table: &Table, store: &TermStore, h: Hash, arity: usize, self_idx: Option<u32>, tail: bool) -> Option<Src> {
    let sub = |h, tail| parse(table, store, h, arity, self_idx, tail).map(Box::new);
    match classify(store, h, arity, self_idx) {
        Shape::If(c, t, e) if tail => {
            let Shape::Prim(p, a, b) = classify(store, c, arity, self_idx) else { return None };
            is_comparison(p).then_some(())?;
            Some(Src::If(p.name(), sub(a, false)?, sub(b, false)?, sub(t, true)?, sub(e, true)?))
        }
        // de Bruijn 0 is the last parameter; written here, not taken from `shape::local_index`
        Shape::Var(i) => ((i as usize) < arity).then(|| Src::Param(arity - 1 - i as usize)),
        Shape::Lit(v) => Some(Src::Lit((v as u64 as u128) & low_bits(N))),
        Shape::Prim(p, a, b) => {
            table.row(p.name()).is_some_and(|r| r.class == Class::Word).then_some(())?;
            Some(Src::Prim(p.name(), sub(a, false)?, sub(b, false)?))
        }
        _ => None,
    }
}

/// The meaning of the row `name`. A 2-to-1 row's meaning is a closed circuit, so it needs no binder context.
fn row_term(w: &Machine, name: &str) -> Expr {
    (w.table.row(name).expect("parse admits only table rows").meaning)(&mut Cx::default(), w, 0)
}

/// `s` in continuation-passing form with the continuation `k`, evaluating operands left to right, as the lowering
/// emits them. Total: `parse` has already kept out everything else.
fn cps(w: &Machine, e: &SEnv, c: &mut Cx, s: &Src, k: &dyn Fn(&mut Cx, Expr) -> Expr) -> Expr {
    // one frame per node and continuation: run on the kernel's growable stack, as `Machine::seq` does
    tatic_kernel::grow(|| match s {
        Src::Param(i) => k(c, c.at(e.params[*i])),
        Src::Lit(v) => k(c, lit(e.n, *v)),
        Src::Prim(o, a, b) => cps(w, e, c, a, &|c, x| {
            let x = c.mark(x);
            cps(w, e, c, b, &|c, y| k(c, app2(row_term(w, o), c.at(x), y)))
        }),
        Src::If(o, a, b, t, f) => cps(w, e, c, a, &|c, x| {
            let x = c.mark(x);
            cps(w, e, c, b, &|c, y| {
                let cond = app2(row_term(w, o), c.at(x), y);
                let (t2, f2) = (cps(w, e, c, t, k), cps(w, e, c, f, k));
                e.choose(c, cond, t2, f2)
            })
        }),
    })
}

/// `h`'s arity and its source function for the statement (D4's seam), or `None` outside the fragment. The closure is
/// built from the term and the table alone, never from the `Ins` list, so a lowering bug cannot cancel itself.
pub(crate) fn source_fn<'s>(table: &'s Table, store: &'s TermStore, h: Hash) -> Option<(usize, Box<SrcFn<'s>>)> {
    let (arity, body, is_rec) = peel(store, h)?;
    let src = parse(table, store, body, arity, is_rec.then_some(arity as u32), true)?;
    let w = Machine { n: N, fw: 0, table };
    Some((arity, Box::new(move |c: &mut Cx, e: &SEnv, k: &dyn Fn(&mut Cx, Expr) -> Expr| cps(&w, e, c, &src, k))))
}

/// `(statement, the generator's proof)` for `h` and its emitted `code`, apart (the measurements time them apart from
/// the check). `None` when `h` is outside the fragment or `code` is not a list the machine runs.
pub(crate) fn build(table: &Table, store: &TermStore, h: Hash, arity: usize, code: &[Ins]) -> Option<(Expr, Result<Expr, String>)> {
    if !in_fragment(table, store, h, arity) || !well_formed(table, code, &[], &[]) {
        return None;
    }
    let (a, src) = source_fn(table, store, h)?;
    if a != arity {
        return None;
    }
    let entry = Entry { arity, env: EnvAccess::Params(0), code: code.to_vec() };
    let module = [Some(ModEntry { entry: &entry, src: &*src })];
    let w = Machine { n: N, fw: 0, table };
    Some((statement(&w, &module, 0), prove(&w, &module, 0)))
}

/// Whether the kernel accepts `code` as `h` at n = 64. False for a term outside the fragment, for a list the machine
/// does not run (`well_formed`), and for a proof the generator cannot make or the kernel refuses.
pub fn gate(table: &Table, store: &TermStore, h: Hash, arity: usize, code: &[Ins]) -> bool {
    scoped(|| match build(table, store, h, arity, code) {
        Some((stmt, Ok(proof))) => holds(&proof, &stmt).is_ok(),
        _ => false,
    })
}
