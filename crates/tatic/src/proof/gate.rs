//! The gate (v0.8; `docs/superpowers/specs/2026-11-10-v08-recursion-once-design.md`, D3, D4): the kernel checks that the
//! instruction list the JIT prints, run on `tatic_wasm`'s machine at n = 64, simulates the source term for every
//! fuel. The statement is `tatic_wasm::machine::statement`'s (trusted); `tatic_wasm::machine::sim::prove` (untrusted)
//! makes the proof. The source side is built from the term, never from `code` (`source_fn`), so a lowering bug cannot
//! cancel itself. Both sides read operators from the one table (`tatic_wasm::wasm::table`, the row's `meaning`), and both guard
//! every Word site by the row's `dom` through the walk's probe (`choose(dom x y, K, z)`), so a wrong
//! row is the table check's to catch (`jit/op_table_tests.rs`), not the gate's. The answer is a `Verdict`: what the
//! source reading takes is `Accepted` or `Rejected` for good, the rest is `NotCovered` and goes to `kernel_verify`.

use std::collections::BTreeSet;

use hashbrown::{HashMap, HashSet};
use tatic_kernel::{app2, scoped, Expr};
use tatic_wasm::encoding::{holds, lit, low_bits, At, Cx};
use tatic_wasm::machine::sim::prove;
use tatic_wasm::machine::statement::{callees, statement, ModEntry, SEnv, SrcFn};
use tatic_wasm::machine::{shape_check, Class, Machine, Table};

use crate::jit::compile::{tree_size, CompiledFragment};
use crate::jit::shape::{classify, free_vars, peel, Shape};
use crate::lang::term::{Hash, TermStore};

const N: usize = 64;

/// The largest cost (`cost`) the gate takes: the largest power of two under the JIT path's 0.4 s, set in v0.7 when
/// `doubling(12)` (8192 nodes) took 0.35-0.38 s and `doubling(13)` (16384) 0.74-0.88 s (doc 15, "Why the build grew
/// 2.2x per doubling"). Under v0.8's relational statement `doubling(12)` stays near it, untimed (doc 15, "v0.8's build:
/// measurements and checks (2026-11-11)").
pub(crate) const MAX_GATE_TREE: u64 = 8192;

/// What one `Call` site adds to a term's cost beyond its tree nodes, in nodes (fitted in T12, see its run record).
pub const CALL_WEIGHT: u64 = 228;

/// The layer that refused a covered term.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Layer {
    /// The shape check over the module's records (`machine::shape_check`).
    Shape,
    /// The registry's terms do not pair with the records (`pairing`): a source that is not its record's, or a callee
    /// the code calls and the source does not (or the reverse).
    Pairing,
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
/// comparison in tail position, and calls (an operand anywhere; their arguments are evaluated left to right): to the
/// function itself (`None`) or to a closed callee at its module position.
enum Src {
    Param(usize),
    Lit(u128),
    Prim(&'static str, Box<Src>, Box<Src>),
    If(&'static str, Box<Src>, Box<Src>, Box<Src>, Box<Src>),
    Call(Option<usize>, Vec<Src>),
}

/// What `parse` reads a function body against: the table, the store, the function's parameter count and self-reference,
/// and the registry (a closed callee's term to its module position).
struct Reading<'a> {
    table: &'a Table,
    store: &'a TermStore,
    arity: usize,
    self_idx: Option<u32>,
    pos_of: &'a dyn Fn(Hash) -> Option<usize>,
}

/// `h` as a `Src`: only a tail position admits an `If`. `None` outside what `cps` reads.
fn parse(rd: &Reading, h: Hash, tail: bool) -> Option<Src> {
    let (arity, store) = (rd.arity, rd.store);
    let sub = |h, tail| parse(rd, h, tail).map(Box::new);
    let args = |hs: Vec<Hash>, want: usize| -> Option<Vec<Src>> {
        let args: Vec<Src> = hs.into_iter().map(|a| parse(rd, a, false)).collect::<Option<_>>()?;
        (args.len() == want).then_some(args)
    };
    match classify(store, h, arity, rd.self_idx) {
        Shape::If(c, t, e) if tail => {
            let Shape::Prim(p, a, b) = classify(store, c, arity, rd.self_idx) else { return None };
            rd.table.row(p.name()).is_some_and(|r| r.class == Class::Bit).then_some(())?;
            Some(Src::If(p.name(), sub(a, false)?, sub(b, false)?, sub(t, true)?, sub(e, true)?))
        }
        // de Bruijn 0 is the last parameter; written here, not taken from `shape::local_index`
        Shape::Var(i) => ((i as usize) < arity).then(|| Src::Param(arity - 1 - i as usize)),
        Shape::Lit(v) => Some(Src::Lit((v as u64 as u128) & low_bits(N))),
        Shape::Prim(p, a, b) => {
            rd.table.row(p.name()).is_some_and(|r| r.class == Class::Word).then_some(())?;
            Some(Src::Prim(p.name(), sub(a, false)?, sub(b, false)?))
        }
        Shape::SelfCall(hs) => Some(Src::Call(None, args(hs, arity)?)),
        // a saturated call of a closed literal combinator the registry holds
        Shape::CombinatorCall { root, arity: callee, args: hs } => {
            let (a, body, is_rec) = peel(store, root)?;
            free_vars(store, body, a, is_rec).is_empty().then_some(())?;
            Some(Src::Call(Some((rd.pos_of)(root)?), args(hs, callee)?))
        }
        _ => None,
    }
}

/// The meaning of the row `name`. A 2-to-1 row's meaning is a closed circuit, so it needs no binder context.
fn row_term(w: &Machine, name: &str) -> Expr {
    (w.table.row(name).expect("parse admits only table rows").meaning)(&mut Cx::default(), w, 0)
}

/// The arguments of a call evaluated left to right (each mark taken in turn), then `k` on all of them.
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
            cps(w, e, c, b, &|c, y| {
                // the Word row's domain guard `choose(dom x y, K, z)`, as the machine's binop carries it
                let y = c.mark(y);
                let kk = k(c, app2(row_term(w, o), c.at(x), c.at(y)));
                let dom = tatic_wasm::encoding::constant_n(w.table.row(o).expect("parse admits only table rows").dom.circuit, w.n);
                e.choose(c, app2(dom, c.at(x), c.at(y)), kk, c.at(e.z))
            })
        }),
        Src::If(o, a, b, t, f) => cps(w, e, c, a, &|c, x| {
            let x = c.mark(x);
            cps(w, e, c, b, &|c, y| {
                let cond = app2(row_term(w, o), c.at(x), y);
                let (t2, f2) = (cps(w, e, c, t, k), cps(w, e, c, f, k));
                e.choose(c, cond, t2, f2)
            })
        }),
        Src::Call(to, args) => cps_args(w, e, c, args, vec![], &|c, xs| e.call(c, to.unwrap_or(e.own), xs, k)),
    })
}

/// `h`'s arity and its source function for the statement (D4's seam), or `None` when `cps` cannot take the term. The
/// closure is built from the term, the table and the registry (`pos_of`) alone, never from the `Ins` list, so a
/// lowering bug cannot cancel itself.
pub(crate) fn source_fn<'s>(table: &'s Table, store: &'s TermStore, h: Hash, pos_of: &dyn Fn(Hash) -> Option<usize>) -> Option<(usize, Box<SrcFn<'s>>)> {
    let (arity, body, is_rec) = peel(store, h)?;
    let src = parse(&Reading { table, store, arity, self_idx: is_rec.then_some(arity as u32), pos_of }, body, true)?;
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

/// The closed callees' terms `h`'s body calls (`Shape::CombinatorCall` roots), each once.
fn callee_heads(store: &TermStore, h: Hash) -> HashSet<Hash> {
    fn walk(store: &TermStore, h: Hash, arity: usize, self_idx: Option<u32>, seen: &mut HashSet<Hash>, out: &mut HashSet<Hash>) {
        if !seen.insert(h) {
            return;
        }
        tatic_kernel::grow(|| {
            let kids = match classify(store, h, arity, self_idx) {
                Shape::SelfCall(args) => args,
                Shape::CombinatorCall { root, args, .. } => {
                    out.insert(root);
                    args
                }
                Shape::If(c, t, e) => vec![c, t, e],
                Shape::Prim(_, a, b) => vec![a, b],
                _ => vec![],
            };
            kids.into_iter().for_each(|a| walk(store, a, arity, self_idx, seen, out));
        })
    }
    let mut out = HashSet::new();
    if let Some((arity, body, is_rec)) = peel(store, h) {
        walk(store, body, arity, is_rec.then_some(arity as u32), &mut HashSet::new(), &mut out);
    }
    out
}

/// `cost` of `h` with the call sites of the registry's callee terms in `frag` (the entry's own are `h`'s).
pub(crate) fn module_cost(store: &TermStore, h: Hash, frag: &CompiledFragment) -> u64 {
    let callees: Vec<Hash> = frag.sources().into_iter().enumerate().filter(|(p, _)| *p != frag.entry_pos).filter_map(|(_, t)| t).collect();
    cost(store, h, &callees)
}

/// The registry pairing (trusted): each record's source term peels to the record's arity, and the callees the source
/// calls (its closed heads, by the registry's positions) are the positions the record's code calls other than its own.
/// So a statement built from the sources is about the functions the code calls, and `SEnv::call` finds each callee.
fn pairing(store: &TermStore, frag: &CompiledFragment) -> Result<(), String> {
    let (sources, records) = (frag.sources(), frag.records());
    let pos_of = |x: Hash| sources.iter().position(|s| *s == Some(x));
    for (p, (src, rec)) in sources.iter().zip(&records).enumerate() {
        let (Some(h), Some(rec)) = (src, rec) else {
            if src.is_some() != rec.is_some() {
                return Err(format!("position {p} holds a source or a record without the other"));
            }
            continue;
        };
        let arity = peel(store, *h).map(|t| t.0);
        if arity != Some(rec.arity) {
            return Err(format!("position {p}: the record takes {} parameters, its source {arity:?}", rec.arity));
        }
        let from_source: BTreeSet<usize> = callee_heads(store, *h).into_iter().map(|c| pos_of(c).unwrap_or(usize::MAX)).filter(|c| *c != p).collect();
        let from_code: BTreeSet<usize> = callees(p, &rec.code).into_iter().collect();
        if from_source != from_code {
            return Err(format!("position {p}: the source calls {from_source:?}, the code {from_code:?}"));
        }
    }
    Ok(())
}

/// `(statement, the generator's proof)` for `h` and the module `frag` it compiled to, apart (the measurements time
/// them apart from the check). `Err` is the verdict when there is no statement to build: `NotCovered` when `cps` cannot
/// take the term or one of the registry's callees, a record has no source term, or the cost is over the budget;
/// `Rejected(Shape)` when the records fail the shape check; `Rejected(Pairing)` when the sources are not the records'.
pub(crate) fn build(table: &Table, store: &TermStore, h: Hash, frag: &CompiledFragment) -> Result<(Expr, Result<Expr, String>), Verdict> {
    let (sources, records) = (frag.sources(), frag.records());
    let pos_of = |x: Hash| sources.iter().position(|s| *s == Some(x));
    if sources[frag.entry_pos] != Some(h) {
        return Err(Verdict::Rejected(Layer::Pairing, "the entry's source is not the term".into()));
    }
    let mut fns = Vec::with_capacity(records.len());
    for (p, rec) in records.iter().enumerate() {
        fns.push(match (rec, sources[p]) {
            (None, _) => None,
            (Some(_), None) => return Err(Verdict::NotCovered(format!("the record at position {p} has no source term"))),
            (Some(_), Some(t)) => match source_fn(table, store, t, &pos_of) {
                Some((_, f)) => Some(f),
                None => return Err(Verdict::NotCovered(format!("position {p} is outside what the source reading takes"))),
            },
        });
    }
    if module_cost(store, h, frag) > MAX_GATE_TREE {
        return Err(Verdict::NotCovered(format!("over the budget of {MAX_GATE_TREE}")));
    }
    shape_check(table, &records).map_err(|m| Verdict::Rejected(Layer::Shape, m))?;
    pairing(store, frag).map_err(|m| Verdict::Rejected(Layer::Pairing, m))?;
    let module: Vec<Option<ModEntry>> = records.iter().zip(&fns).map(|(r, f)| Some(ModEntry { entry: (*r)?, src: &**(f.as_ref()?) })).collect();
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
