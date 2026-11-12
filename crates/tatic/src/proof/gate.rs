//! The gate (v0.8; `docs/superpowers/specs/2026-11-10-v08-recursion-once-design.md`, D3, D4): the kernel checks that the
//! instruction list the JIT prints, run on `tatic_wasm`'s machine at n = 64, simulates the source term for every
//! fuel. The statement is `tatic_wasm::machine::statement`'s (trusted); `tatic_wasm::machine::sim::prove` (untrusted)
//! makes the proof. The source side is built from the term, never from `code` (`source_fn`), so a lowering bug cannot
//! cancel itself. Both sides read operators from the one table (`shape::wasm_table`, the row's `meaning`), so a wrong
//! row is the table check's to catch (`jit/op_table_tests.rs`), not the gate's. The answer is a `Verdict`: what the
//! source reading takes is `Accepted` or `Rejected` for good, the rest is `NotCovered` and goes to `kernel_verify`.

use hashbrown::HashMap;
use tatic_kernel::{app2, scoped, Expr};
use tatic_wasm::encoding::{holds, lit, low_bits, At, Cx};
use tatic_wasm::machine::sim::prove;
use tatic_wasm::machine::statement::{statement, ModEntry, SEnv, SrcFn};
use tatic_wasm::machine::{shape_check, Class, Machine, Table};

use crate::jit::compile::{tree_size, CompiledFragment};
use crate::jit::shape::{classify, is_comparison, peel, Shape};
use crate::lang::term::{Hash, TermStore};

const N: usize = 64;

/// The largest cost (`cost`) the gate takes: the largest power of two under the JIT path's 0.4 s. `doubling(12)` (8192
/// nodes) took 0.35-0.38 s, `doubling(13)` (16384) 0.74-0.88 s, nearly all of it the check (doc 15, "Why the build grew
/// 2.2x per doubling").
pub(crate) const MAX_GATE_TREE: u64 = 8192;

/// What one `Call` site adds to a term's cost beyond its tree nodes (fitted in T12; 0 until then).
pub const CALL_WEIGHT: u64 = 0;

/// The layer that refused a covered term.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Layer {
    /// The shape check over the module's records (`machine::shape_check`), or a record that is not the source's.
    Shape,
    /// The generator's walk found the machine and the source parting ways.
    Walk,
    /// The generator made a proof and the kernel refused it.
    Kernel,
}

/// The gate's answer. `NotCovered` is decided from the source and the registry-derived module alone, never from the
/// instruction list, and goes to `kernel_verify`; for a covered term the verdict is final.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Verdict {
    Accepted,
    Rejected(Layer, String),
    NotCovered(String),
}

// holds no `Expr`, so it leaves a `scoped` region as it is
impl tatic_kernel::Escape for Verdict {
    fn escape(self) -> Self {
        self
    }
}

/// The source in a form `parse` has already checked: parameters by position, literals, word rows, `If`s on a
/// comparison in tail position, and self-calls (an operand anywhere; their arguments are evaluated left to right).
enum Src {
    Param(usize),
    Lit(u128),
    Prim(&'static str, Box<Src>, Box<Src>),
    If(&'static str, Box<Src>, Box<Src>, Box<Src>, Box<Src>),
    SelfCall(Vec<Src>),
}

/// `h` as a `Src`: only a tail position admits an `If`. `None` outside what `cps` reads.
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
        Shape::SelfCall(args) => {
            let args: Vec<Src> = args.into_iter().map(|a| parse(table, store, a, arity, self_idx, false)).collect::<Option<_>>()?;
            (args.len() == arity).then_some(Src::SelfCall(args))
        }
        _ => None,
    }
}

/// The meaning of the row `name`. A 2-to-1 row's meaning is a closed circuit, so it needs no binder context.
fn row_term(w: &Machine, name: &str) -> Expr {
    (w.table.row(name).expect("parse admits only table rows").meaning)(&mut Cx::default(), w, 0)
}

/// The arguments of a self-call evaluated left to right (each mark taken in turn), then `k` on all of them.
fn cps_args(w: &Machine, e: &SEnv, c: &mut Cx, args: &[Src], done: Vec<At>, k: &dyn Fn(&mut Cx, &[At]) -> Expr) -> Expr {
    match args.split_first() {
        None => k(c, &done),
        Some((a, rest)) => cps(w, e, c, a, &|c, x| {
            let mut d = done.clone();
            d.push(c.mark(x));
            cps_args(w, e, c, rest, d, k)
        }),
    }
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
        Src::SelfCall(args) => cps_args(w, e, c, args, vec![], &|c, xs| e.call(c, e.own, xs, k)),
    })
}

/// `h`'s arity and its source function for the statement (D4's seam), or `None` when `cps` cannot take the term. The
/// closure is built from the term and the table alone, never from the `Ins` list, so a lowering bug cannot cancel itself.
pub(crate) fn source_fn<'s>(table: &'s Table, store: &'s TermStore, h: Hash) -> Option<(usize, Box<SrcFn<'s>>)> {
    let (arity, body, is_rec) = peel(store, h)?;
    let src = parse(table, store, body, arity, is_rec.then_some(arity as u32), true)?;
    let w = Machine { n: N, fw: 0, table };
    Some((arity, Box::new(move |c: &mut Cx, e: &SEnv, k: &dyn Fn(&mut Cx, Expr) -> Expr| cps(&w, e, c, &src, k))))
}

/// The self-call and combinator-call sites `classify` reads in `h`'s body (after the optional `Rec` and the `Abs`
/// binders, the reading `source_fn` does), counted with multiplicity like the tree.
pub(crate) fn call_sites(store: &TermStore, h: Hash) -> u64 {
    fn walk(store: &TermStore, h: Hash, arity: usize, self_idx: Option<u32>, memo: &mut HashMap<Hash, u64>) -> u64 {
        if let Some(n) = memo.get(&h) {
            return *n;
        }
        let n = tatic_kernel::grow(|| {
            let mut all = |hs: &[Hash]| hs.iter().fold(0u64, |n, a| n.saturating_add(walk(store, *a, arity, self_idx, memo)));
            match classify(store, h, arity, self_idx) {
                Shape::SelfCall(args) => all(&args).saturating_add(1),
                Shape::CombinatorCall { args, .. } => all(&args).saturating_add(1),
                Shape::If(c, t, e) => all(&[c, t, e]),
                Shape::Prim(_, a, b) => all(&[a, b]),
                _ => 0,
            }
        });
        memo.insert(h, n);
        n
    }
    let Some((arity, body, is_rec)) = peel(store, h) else { return 0 };
    walk(store, body, arity, is_rec.then_some(arity as u32), &mut HashMap::new())
}

/// A term's cost against `MAX_GATE_TREE`: its tree nodes plus `CALL_WEIGHT` per call site of `h` and of the registry's
/// `callees`. Read from the source and the registry-derived module only, never from the emitted `Ins` list: padding the
/// code with `Call`s must not move a term from `Rejected` to `NotCovered`.
fn cost(store: &TermStore, h: Hash, callees: &[Hash]) -> u64 {
    let tree = tree_size(store, h);
    if tree > MAX_GATE_TREE {
        return tree;
    }
    let sites: u64 = std::iter::once(&h).chain(callees).map(|t| call_sites(store, *t)).fold(0, u64::saturating_add);
    tree.saturating_add(CALL_WEIGHT.saturating_mul(sites))
}

/// `(statement, the generator's proof)` for `h` and the fragment `frag` it compiled to, apart (the measurements time
/// them apart from the check). `Err` is the verdict when there is no statement to build: `NotCovered` when `cps` cannot
/// take the term, it is over the budget, or the module holds a record other than the entry (until S3); `Rejected(Shape)`
/// when the records fail the shape check or are not the source's.
pub(crate) fn build(table: &Table, store: &TermStore, h: Hash, frag: &CompiledFragment) -> Result<(Expr, Result<Expr, String>), Verdict> {
    let Some((arity, src)) = source_fn(table, store, h) else {
        return Err(Verdict::NotCovered("the term is outside what the source reading takes".into()));
    };
    if cost(store, h, &[]) > MAX_GATE_TREE {
        return Err(Verdict::NotCovered(format!("over the budget of {MAX_GATE_TREE}")));
    }
    let records = frag.records();
    if records.iter().enumerate().any(|(p, r)| r.is_some() && p != frag.entry_pos) {
        return Err(Verdict::NotCovered("the module holds a function other than the entry".into()));
    }
    shape_check(table, &records).map_err(|m| Verdict::Rejected(Layer::Shape, m))?;
    let entry = frag.entry();
    if entry.arity != arity {
        return Err(Verdict::Rejected(Layer::Shape, format!("the record takes {} parameters, the source {arity}", entry.arity)));
    }
    let mut module: Vec<Option<ModEntry>> = (0..frag.entry_pos).map(|_| None).collect();
    module.push(Some(ModEntry { entry, src: &*src }));
    let w = Machine { n: N, fw: 0, table };
    Ok((statement(&w, &module, frag.entry_pos), prove(&w, &module, frag.entry_pos)))
}

/// The verdict on `frag`, the compiled form of `h`, at n = 64: `build`'s `Err` as it is; else the generator's refusal is
/// `Rejected(Walk)`, the kernel's `Rejected(Kernel)`, and a proof the kernel accepts `Accepted`.
pub fn gate(table: &Table, store: &TermStore, h: Hash, frag: &CompiledFragment) -> Verdict {
    scoped(|| match build(table, store, h, frag) {
        Err(v) => v,
        Ok((_, Err(why))) => Verdict::Rejected(Layer::Walk, why),
        Ok((stmt, Ok(proof))) => match holds(&proof, &stmt) {
            Ok(()) => Verdict::Accepted,
            Err(why) => Verdict::Rejected(Layer::Kernel, why),
        },
    })
}
