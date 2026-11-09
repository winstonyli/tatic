//! The straight-line gate (v0.7; `docs/superpowers/specs/2026-11-08-v07-straight-line-gate-design.md`, sections 6
//! and D3a): the kernel checks that the instruction list the JIT prints, run on `tatic_wasm`'s machine at n = 64,
//! equals the source term, for every input. The statement is
//!
//! ```text
//! Pi S R k z q_0 .. q_{m-1} s mu.  Id(R, M (prog code) 1 R k z s (frame q mu), rhs)
//! ```
//!
//! proved by `refl`. `frame` puts parameter `q_j` at address `j` (`LocalGet j` reads it); fuel 1 lets the `loop $L`
//! wrapper with no `br` run its body once. `rhs` is built from the source term, never from `code` (`cps`), so a
//! lowering bug cannot cancel itself. Both sides read operators from the one table (`shape::op_of`, `Op::term`), so a
//! wrong row is the table check's to catch (`jit/op_table_tests.rs`), not the gate's.

use hashbrown::HashSet;
use tatic_kernel::{app2, id, refl, scoped, sort, Expr};
use tatic_wasm::encoding::{holds, law, lit, low_bits, ty, At, Cx, Ty};
use tatic_wasm::wasm::{choose, mkpair, nat2_lit, well_formed, Ins, Wasm, K};

use crate::jit::compile::tree_size;
use crate::jit::shape::{is_comparison, op_of};
use crate::lang::term::{Hash, Term, TermStore};

const N: usize = 64;

/// The largest tree (`compile::tree_size`) the gate takes: the largest power of two under the JIT path's 0.4 s.
/// `doubling(12)` (8192 nodes) took 0.35-0.38 s, `doubling(13)` (16384) 0.74-0.88 s, nearly all of it the check (doc
/// 15, "Why the build grew 2.2x per doubling").
const MAX_GATE_TREE: u64 = 8192;

/// Whether `h` is in the gate's fragment (D3a): `arity` ≥ 1 leading `Abs`, then a body of parameters, literals and
/// table rows, where every `If` is in tail position and tests a comparison of operands, and comparisons appear
/// nowhere else; and at most `MAX_GATE_TREE` nodes as a tree.
pub fn in_fragment(store: &TermStore, h: Hash, arity: usize) -> bool {
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
    tail(store, body, arity, &mut HashSet::new())
}

/// A tail position: an `If` on a comparison of operands with tail arms, or an operand.
fn tail(store: &TermStore, h: Hash, m: usize, seen: &mut HashSet<Hash>) -> bool {
    match store.resolve(h) {
        Term::If(c, t, e) => match store.resolve(*c) {
            Term::Prim(p, a, b) => {
                is_comparison(*p)
                    && operand(store, *a, m, seen)
                    && operand(store, *b, m, seen)
                    && tail(store, *t, m, seen)
                    && tail(store, *e, m, seen)
            }
            _ => false,
        },
        _ => operand(store, h, m, seen),
    }
}

/// An operand: a parameter, a literal, or a word-result row of operands. `seen` holds operands already accepted, so
/// a shared subterm is checked once.
fn operand(store: &TermStore, h: Hash, m: usize, seen: &mut HashSet<Hash>) -> bool {
    if seen.contains(&h) {
        return true;
    }
    let ok = match store.resolve(h) {
        Term::Var(i) => (*i as usize) < m,
        Term::Lit(_) => true,
        Term::Prim(p, a, b) => {
            op_of(*p).is_some_and(|o| o.kind() == K::W) && operand(store, *a, m, seen) && operand(store, *b, m, seen)
        }
        _ => false,
    };
    if ok {
        seen.insert(h);
    }
    ok
}

/// Whether the kernel accepts `code` as `h` at n = 64. False for a term outside the fragment and for a list the
/// machine does not run (`well_formed`).
pub fn gate(store: &TermStore, h: Hash, arity: usize, code: &[Ins]) -> bool {
    gate_with(store, h, arity, code, 1, false)
}

/// `gate` with the loop fuel given, and with `strip_loop` proving the body of the `[Loop(body)]` wrapper instead.
pub(crate) fn gate_with(store: &TermStore, h: Hash, arity: usize, code: &[Ins], fuel: usize, strip_loop: bool) -> bool {
    let code = match (strip_loop, code) {
        (false, _) => code,
        (true, [Ins::Loop(body)]) => body.as_slice(),
        (true, _) => panic!("strip_loop on a list that is not one Loop"),
    };
    if !in_fragment(store, h, arity) || !well_formed(code, &[]) {
        return false;
    }
    scoped(|| {
        let (proof, stmt) = statement(store, h, arity, code, fuel);
        holds(&proof, &stmt).is_ok()
    })
}

/// `(refl lhs, Pi S R k z q.. s mu. Id(R, lhs, rhs))` for `h`, a fragment term of `m` parameters, and a well-formed
/// `code` (the measurements time it apart from the check).
pub(crate) fn statement(store: &TermStore, h: Hash, m: usize, code: &[Ins], fuel: usize) -> (Expr, Expr) {
    let mut body = h;
    for _ in 0..m {
        let Term::Abs(b) = store.resolve(body) else { unreachable!("in_fragment checks the leading Abs") };
        body = *b;
    }
    let w = Wasm { n: N };
    let mut tys: Vec<Ty> = vec![
        ty!(|_c, _x| sort(2)),
        ty!(|_c, _x| sort(0)),
        ty!(|c, x| {
            let a = w.sty(c, &[K::W], x[0]);
            w.g(c, x[1], a)
        }),
        ty!(|c, x| c.at(x[1])),
    ];
    tys.extend((0..m).map(|_| ty!(|_c, _x| w.v())));
    tys.push(ty!(|c, x| c.at(x[0])));
    tys.push(ty!(|c, x| w.mem(c, x[1])));
    let (s_at, mu_at) = (4 + m, 5 + m);
    let frame = |c: &mut Cx, x: &[At]| {
        (0..m).rev().fold(c.at(x[mu_at]), |acc, j| w.upd(c, x[1], lit(N, j as u128), c.at(x[4 + j]), acc))
    };
    let lhs = |c: &mut Cx, x: &[At]| {
        let p = w.prog(c, code, &[], x[0]);
        let p = c.mark(p);
        let fuel = c.mark(nat2_lit(fuel));
        let fr = frame(c, x);
        app2(w.meaning(c, p, fuel, x[1], x[2], x[3]), c.at(x[s_at]), fr)
    };
    law(
        &tys,
        |c, x| {
            let l = lhs(c, x);
            let fr = frame(c, x);
            let (r, k, st, s) = (c.at(x[1]), c.at(x[2]), c.at(x[0]), c.at(x[s_at]));
            let qs: Vec<Expr> = (0..m).map(|j| c.at(x[4 + j])).collect();
            let src = Source { store, qs, r: r.clone() };
            let rhs = src.cps(body, &|v| app2(k.clone(), mkpair(st.clone(), v, s.clone()), fr.clone()));
            id(r, l, rhs)
        },
        |c, x| refl(lhs(c, x)),
    )
}

/// The right side's builder over the source term: parameters `qs` (q_j is `$p{j}`) and the answer type `r`.
struct Source<'a> {
    store: &'a TermStore,
    qs: Vec<Expr>,
    r: Expr,
}

impl Source<'_> {
    /// `h` in continuation-passing form with the meta-continuation `k`, evaluating operands left to right, as the
    /// lowering emits them. An `If` copies `k` into both arms; in the fragment every `If` is in tail position, so
    /// nothing grows.
    fn cps(&self, h: Hash, k: &dyn Fn(Expr) -> Expr) -> Expr {
        // one frame per node and continuation: run on the kernel's growable stack, as `Wasm::seq` does
        tatic_kernel::grow(|| self.cps_step(h, k))
    }

    fn cps_step(&self, h: Hash, k: &dyn Fn(Expr) -> Expr) -> Expr {
        match self.store.resolve(h) {
            Term::Lit(v) => k(lit(N, (*v as u64 as u128) & low_bits(N))),
            // de Bruijn 0 is the last parameter; written here, not taken from `shape::local_index`
            Term::Var(i) => k(self.qs[self.qs.len() - 1 - *i as usize].clone()),
            Term::Prim(p, a, b) => {
                let o = op_of(*p).expect("in_fragment admits only table rows").term(N);
                self.cps(*a, &|x| self.cps(*b, &|y| k(app2(o.clone(), x.clone(), y))))
            }
            Term::If(c, t, e) => {
                let Term::Prim(p, a, b) = self.store.resolve(*c) else { unreachable!("in_fragment: an If tests a Prim") };
                let o = op_of(*p).expect("in_fragment admits only table rows").term(N);
                self.cps(*a, &|x| {
                    self.cps(*b, &|y| choose(self.r.clone(), app2(o.clone(), x.clone(), y), self.cps(*t, k), self.cps(*e, k)))
                })
            }
            other => unreachable!("in_fragment admits no {other:?}"),
        }
    }
}
