//! UNTRUSTED prototype: a closure-based (NbE-style) `def_eq` over the
//! kernel's own `Expr`, to measure whether lazy substitution would cut the
//! conversion cost the bit-vector lemma pays (`docs/superpowers/specs/
//! 2026-09-30-kernel-node-churn-options.md`, option L1). Nothing in the
//! kernel, `proof.rs` or the pipeline calls it; `kernel::def_eq` stays the
//! only conversion check anyone trusts. It exists to be differential-tested
//! against that function and timed beside it.
//!
//! Design. Evaluation turns an `Expr` under an environment of lazy,
//! shared cells (call by need) into a weak head normal value; beta pushes
//! the argument cell onto the environment instead of substituting, so no
//! body is rebuilt. Binders are kept as closures; conversion compares two
//! values by applying their closures to a fresh variable named by a de
//! Bruijn *level*. It decides the same relation as `kernel::def_eq`: equal
//! normal forms, comparing every child the kernel's `nf` visits, binder
//! domain annotations included (`Lam`/`Pi` domains, `WRec`'s `children_ty`,
//! `Pair`'s `fam`).
//!
//! Reduction rules mirror `kernel::whnf_step`: beta; `J` on `Refl` gives
//! `base a`; `WRec` on `Sup(a, f)` gives `step a f (\y:B(a). wrec .. (f y))`;
//! `SigRec` on `Pair(_, a, b)` gives `step a b`. `Const` and `Free` are
//! inert atoms.

use crate::kernel::{Expr, Rc as KRc, grow};
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

/// (node address, addresses of the cells its loose variables are bound to).
type CellKey = (usize, Vec<usize>);

/// Pointer-keyed sharing for `def_eq_lazy_shared`: a node referenced from more than one place is
/// evaluated once per (node, the cells its loose variables are bound to), and a cell for such a
/// node is built once per the same key. Each entry keeps its key's node and environment alive so
/// the addresses in the key stay unique.
#[derive(Default)]
struct Memo {
    cells: HashMap<CellKey, (KRc<Expr>, Env, Thunk)>,
    vals: HashMap<CellKey, (KRc<Expr>, Env, V)>,
    /// Pairs of values already found convertible (at any level: a value's meaning does not
    /// depend on the level it is compared at, only on the levels inside it).
    equal: HashMap<(usize, usize), (V, V)>,
}
/// Counters for `def_eq_lazy_shared`, to see where its time goes (read with `take_stats`).
#[derive(Default, Debug, Clone)]
pub struct Stats {
    pub eval_calls: u64,
    pub betas: u64,
    pub eval_keyed: u64,
    pub eval_hits: u64,
    pub cell_calls: u64,
    pub cell_keyed: u64,
    pub cell_hits: u64,
    pub key_slots: u64,
    pub conv_calls: u64,
    pub conv_ptr_hits: u64,
    pub conv_equal_hits: u64,
    pub force_evals: u64,
    pub cells_len: usize,
    pub vals_len: usize,
    pub equal_len: usize,
    /// Memo lookups and hits, split by `[eval, cell]` and bucketed by key length, by the node's
    /// strong count, and by its `Expr` variant (see `record`).
    pub by_klen: [[Hist; 2]; 1],
    pub by_count: [[Hist; 2]; 1],
    pub by_kind: [[Hist; 2]; 1],
}
#[derive(Default, Debug, Clone, Copy)]
pub struct Hist {
    pub lookups: [u64; 10],
    pub hits: [u64; 10],
}
fn record(cell: usize, e: &KRc<Expr>, klen: usize, hit: bool) {
    let kl = match klen {
        0..=4 => klen,
        5..=6 => 5,
        7..=8 => 6,
        9..=12 => 7,
        13..=20 => 8,
        _ => 9,
    };
    let cnt = match KRc::strong_count(e) {
        0..=2 => 0,
        3 => 1,
        4 => 2,
        5..=8 => 3,
        9..=16 => 4,
        17..=64 => 5,
        _ => 6,
    };
    let kind = match &**e {
        Expr::Var(_) => 0,
        Expr::App(..) => 1,
        Expr::Lam(..) => 2,
        Expr::Pi(..) => 3,
        Expr::Sort(_) | Expr::Const(_) | Expr::Free(_) => 4,
        Expr::Id(..) | Expr::Refl(_) | Expr::J { .. } => 5,
        _ => 6,
    };
    bump(|s| {
        for (h, i) in [(&mut s.by_klen[0][cell], kl), (&mut s.by_count[0][cell], cnt), (&mut s.by_kind[0][cell], kind)] {
            h.lookups[i] += 1;
            if hit {
                h.hits[i] += 1;
            }
        }
    });
}
thread_local! {
    static STATS: RefCell<Stats> = RefCell::new(Stats::default());
}
fn bump(f: impl FnOnce(&mut Stats)) {
    STATS.with(|s| f(&mut s.borrow_mut()));
}
/// The counters since the last call (map sizes are those at the end of the last shared call).
pub fn take_stats() -> Stats {
    STATS.with(|s| std::mem::take(&mut *s.borrow_mut()))
}

thread_local! {
    static MEMO: RefCell<Option<Memo>> = const { RefCell::new(None) };
}

fn memo_key(e: &KRc<Expr>, env: &Env) -> (usize, Vec<usize>) {
    let mut cells = Vec::new();
    let mut node = env.as_ref();
    for _ in 0..e.loose() {
        match node {
            Some(n) => {
                cells.push(Rc::as_ptr(&n.head.0) as *const u8 as usize);
                node = n.tail.as_ref();
            }
            None => break,
        }
    }
    bump(|s| s.key_slots += cells.len() as u64);
    (KRc::as_ptr(e) as *const u8 as usize, cells)
}

thread_local! {
    static MAX_LOOSE: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
}
/// Only nodes with at most this many loose variables are memoised by `def_eq_lazy_shared`
/// (default `0`: closed nodes only, whose key is just their address; `u32::MAX` memoises all).
pub fn set_memo_max_loose(n: u32) {
    MAX_LOOSE.with(|c| c.set(n));
}

fn memo_on(e: &KRc<Expr>) -> bool {
    KRc::strong_count(e) > 1 && e.loose() <= MAX_LOOSE.with(|c| c.get()) && MEMO.with(|m| m.borrow().is_some())
}

type V = Rc<Val>;

/// A lazily evaluated, shared cell: forced at most once.
#[derive(Clone)]
struct Thunk(Rc<RefCell<Cell>>);

enum Cell {
    Delayed(KRc<Expr>, Env),
    Lazy(Box<dyn FnOnce() -> V>),
    Running,
    Done(V),
}

impl Thunk {
    fn delay(e: &KRc<Expr>, env: &Env) -> Thunk {
        let fresh = || Thunk(Rc::new(RefCell::new(Cell::Delayed(e.clone(), env.clone()))));
        bump(|s| s.cell_calls += 1);
        if !memo_on(e) {
            return fresh();
        }
        bump(|s| s.cell_keyed += 1);
        let key = memo_key(e, env);
        if let Some(t) = MEMO.with(|m| m.borrow().as_ref().and_then(|m| m.cells.get(&key).map(|x| x.2.clone()))) {
            bump(|s| s.cell_hits += 1);
            record(1, e, key.1.len(), true);
            return t;
        }
        let t = fresh();
        record(1, e, key.1.len(), false);
        MEMO.with(|m| m.borrow_mut().as_mut().map(|m| m.cells.insert(key, (e.clone(), env.clone(), t.clone()))));
        t
    }
    fn lazy(f: impl FnOnce() -> V + 'static) -> Thunk {
        Thunk(Rc::new(RefCell::new(Cell::Lazy(Box::new(f)))))
    }
    fn done(v: V) -> Thunk {
        Thunk(Rc::new(RefCell::new(Cell::Done(v))))
    }
    fn force(&self) -> V {
        let cell = std::mem::replace(&mut *self.0.borrow_mut(), Cell::Running);
        let v = match cell {
            Cell::Done(v) => v,
            Cell::Delayed(e, env) => {
                bump(|s| s.force_evals += 1);
                eval(&env, &e)
            }
            Cell::Lazy(f) => f(),
            Cell::Running => panic!("kernel_lazy: a cell depends on itself"),
        };
        *self.0.borrow_mut() = Cell::Done(v.clone());
        v
    }
}

/// The environment: index 0 is the head.
type Env = Option<Rc<EnvNode>>;
struct EnvNode {
    head: Thunk,
    tail: Env,
}

fn push(env: &Env, t: Thunk) -> Env {
    Some(Rc::new(EnvNode { head: t, tail: env.clone() }))
}

fn lookup(env: &Env, i: u32) -> Thunk {
    let mut node = env.as_ref().expect("kernel_lazy: unbound variable");
    for _ in 0..i {
        node = node.tail.as_ref().expect("kernel_lazy: unbound variable");
    }
    node.head.clone()
}

/// A binder body: a term under an environment, or the induction-hypothesis
/// function `WRec` hands its step (`\y. wrec motive cty step (f y)`).
#[derive(Clone)]
enum Clo {
    Term(Env, KRc<Expr>),
    Ih { motive: Thunk, cty: Box<Clo>, step: Thunk, f: Thunk },
}

impl Clo {
    fn apply(&self, arg: Thunk) -> V {
        match self {
            Clo::Term(env, body) => {
                bump(|s| s.betas += 1);
                eval(&push(env, arg), body)
            }
            Clo::Ih { motive, cty, step, f } => {
                let target = apply(&f.force(), arg);
                wrec(motive, cty, step, target)
            }
        }
    }
}

/// Weak head normal values. Stuck eliminations keep their (already
/// reduced) head or target as a `V` and everything else as cells.
enum Val {
    Sort(u32),
    Const(u32),
    Free(u32),
    /// A variable bound by conversion itself, by de Bruijn level.
    Level(u32),
    Pi(Thunk, Clo),
    Lam(Thunk, Clo),
    App(V, Thunk),
    Id(Thunk, Thunk, Thunk),
    Refl(Thunk),
    J { motive: Thunk, base: Thunk, a: Thunk, b: Thunk, p: V },
    W(Thunk, Clo),
    Sup(Thunk, Thunk),
    WRec { motive: Thunk, cty: Clo, step: Thunk, target: V },
    Sigma(Thunk, Clo),
    Pair(Clo, Thunk, Thunk),
    SigRec { motive: Thunk, step: Thunk, target: V },
}

fn apply(f: &V, arg: Thunk) -> V {
    grow(|| match &**f {
        Val::Lam(_, clo) => clo.apply(arg),
        _ => Rc::new(Val::App(f.clone(), arg)),
    })
}

fn wrec(motive: &Thunk, cty: &Clo, step: &Thunk, target: V) -> V {
    grow(|| match &*target {
        Val::Sup(a, f) => {
            let (cty2, a2) = (cty.clone(), a.clone());
            let dom = Thunk::lazy(move || cty2.apply(a2));
            let ih = Rc::new(Val::Lam(
                dom,
                Clo::Ih { motive: motive.clone(), cty: Box::new(cty.clone()), step: step.clone(), f: f.clone() },
            ));
            let stepped = apply(&apply(&step.force(), a.clone()), f.clone());
            apply(&stepped, Thunk::done(ih))
        }
        _ => Rc::new(Val::WRec { motive: motive.clone(), cty: cty.clone(), step: step.clone(), target }),
    })
}

fn eval(env: &Env, e: &KRc<Expr>) -> V {
    bump(|s| s.eval_calls += 1);
    if !memo_on(e) {
        return eval_node(env, e);
    }
    bump(|s| s.eval_keyed += 1);
    let key = memo_key(e, env);
    if let Some(v) = MEMO.with(|m| m.borrow().as_ref().and_then(|m| m.vals.get(&key).map(|x| x.2.clone()))) {
        bump(|s| s.eval_hits += 1);
        record(0, e, key.1.len(), true);
        return v;
    }
    record(0, e, key.1.len(), false);
    let v = eval_node(env, e);
    MEMO.with(|m| m.borrow_mut().as_mut().map(|m| m.vals.insert(key, (e.clone(), env.clone(), v.clone()))));
    v
}

fn eval_node(env: &Env, e: &KRc<Expr>) -> V {
    grow(|| {
        let d = |x: &KRc<Expr>| Thunk::delay(x, env);
        let c = |x: &KRc<Expr>| Clo::Term(env.clone(), x.clone());
        match &**e {
            Expr::Var(i) => lookup(env, *i).force(),
            Expr::Sort(i) => Rc::new(Val::Sort(*i)),
            Expr::Const(l) => Rc::new(Val::Const(*l)),
            Expr::Free(l) => Rc::new(Val::Free(*l)),
            Expr::Pi(a, b) => Rc::new(Val::Pi(d(a), c(b))),
            Expr::Lam(a, b) => Rc::new(Val::Lam(d(a), c(b))),
            Expr::App(f, a) => apply(&eval(env, f), d(a)),
            Expr::Id(a, x, y) => Rc::new(Val::Id(d(a), d(x), d(y))),
            Expr::Refl(a) => Rc::new(Val::Refl(d(a))),
            Expr::J { motive, base, a, b, p } => {
                let wp = eval(env, p);
                match &*wp {
                    Val::Refl(_) => apply(&eval(env, base), d(a)),
                    _ => Rc::new(Val::J { motive: d(motive), base: d(base), a: d(a), b: d(b), p: wp }),
                }
            }
            Expr::W(a, b) => Rc::new(Val::W(d(a), c(b))),
            Expr::Sup(a, f) => Rc::new(Val::Sup(d(a), d(f))),
            Expr::WRec { motive, children_ty, step, target } => wrec(&d(motive), &c(children_ty), &d(step), eval(env, target)),
            Expr::Sigma(a, b) => Rc::new(Val::Sigma(d(a), c(b))),
            Expr::Pair(fam, a, b) => Rc::new(Val::Pair(c(fam), d(a), d(b))),
            Expr::SigRec { motive, step, target } => {
                let wt = eval(env, target);
                match &*wt {
                    Val::Pair(_, a, b) => apply(&apply(&eval(env, step), a.clone()), b.clone()),
                    _ => Rc::new(Val::SigRec { motive: d(motive), step: d(step), target: wt }),
                }
            }
        }
    })
}

fn conv_cell(l: u32, x: &Thunk, y: &Thunk) -> bool {
    Rc::ptr_eq(&x.0, &y.0) || conv(l, &x.force(), &y.force())
}

/// Two closures agree when their bodies agree on a fresh variable.
fn conv_clo(l: u32, x: &Clo, y: &Clo) -> bool {
    let v = Thunk::done(Rc::new(Val::Level(l)));
    conv(l + 1, &x.apply(v.clone()), &y.apply(v))
}

fn conv(l: u32, x: &V, y: &V) -> bool {
    bump(|s| s.conv_calls += 1);
    if Rc::ptr_eq(x, y) {
        bump(|s| s.conv_ptr_hits += 1);
        return true;
    }
    let key = (Rc::as_ptr(x) as *const u8 as usize, Rc::as_ptr(y) as *const u8 as usize);
    let on = MEMO.with(|m| m.borrow().is_some());
    if on && MEMO.with(|m| m.borrow().as_ref().is_some_and(|m| m.equal.contains_key(&key))) {
        bump(|s| s.conv_equal_hits += 1);
        return true;
    }
    let r = conv_node(l, x, y);
    if on && r {
        MEMO.with(|m| m.borrow_mut().as_mut().map(|m| m.equal.insert(key, (x.clone(), y.clone()))));
    }
    r
}

fn conv_node(l: u32, x: &V, y: &V) -> bool {
    grow(|| match (&**x, &**y) {
        (Val::Sort(i), Val::Sort(j)) | (Val::Const(i), Val::Const(j)) | (Val::Free(i), Val::Free(j)) | (Val::Level(i), Val::Level(j)) => i == j,
        (Val::Pi(a1, b1), Val::Pi(a2, b2))
        | (Val::Lam(a1, b1), Val::Lam(a2, b2))
        | (Val::W(a1, b1), Val::W(a2, b2))
        | (Val::Sigma(a1, b1), Val::Sigma(a2, b2)) => conv_cell(l, a1, a2) && conv_clo(l, b1, b2),
        (Val::App(f1, a1), Val::App(f2, a2)) => conv(l, f1, f2) && conv_cell(l, a1, a2),
        (Val::Id(a1, b1, c1), Val::Id(a2, b2, c2)) => conv_cell(l, a1, a2) && conv_cell(l, b1, b2) && conv_cell(l, c1, c2),
        (Val::Refl(a), Val::Refl(b)) => conv_cell(l, a, b),
        (Val::Sup(a1, f1), Val::Sup(a2, f2)) => conv_cell(l, a1, a2) && conv_cell(l, f1, f2),
        (Val::Pair(fam1, a1, b1), Val::Pair(fam2, a2, b2)) => conv_clo(l, fam1, fam2) && conv_cell(l, a1, a2) && conv_cell(l, b1, b2),
        (
            Val::J { motive: m1, base: s1, a: a1, b: b1, p: p1 },
            Val::J { motive: m2, base: s2, a: a2, b: b2, p: p2 },
        ) => conv_cell(l, m1, m2) && conv_cell(l, s1, s2) && conv_cell(l, a1, a2) && conv_cell(l, b1, b2) && conv(l, p1, p2),
        (
            Val::WRec { motive: m1, cty: c1, step: s1, target: t1 },
            Val::WRec { motive: m2, cty: c2, step: s2, target: t2 },
        ) => conv_cell(l, m1, m2) && conv_clo(l, c1, c2) && conv_cell(l, s1, s2) && conv(l, t1, t2),
        (Val::SigRec { motive: m1, step: s1, target: t1 }, Val::SigRec { motive: m2, step: s2, target: t2 }) => {
            conv_cell(l, m1, m2) && conv_cell(l, s1, s2) && conv(l, t1, t2)
        }
        _ => false,
    })
}

/// Decides `kernel::def_eq(a, b)` for terms with at most `depth` loose
/// variables: `Var(i)` outside every binder is a distinct inert variable.
pub fn def_eq_lazy(a: &Expr, b: &Expr, depth: u32) -> bool {
    let mut env: Env = None;
    for level in 0..depth {
        env = push(&env, Thunk::done(Rc::new(Val::Level(level))));
    }
    let (a, b) = (KRc::new(a.clone()), KRc::new(b.clone()));
    conv(depth, &eval(&env, &a), &eval(&env, &b))
}

/// `def_eq_lazy` with the pointer-keyed sharing above, for the same inputs.
pub fn def_eq_lazy_shared(a: &Expr, b: &Expr, depth: u32) -> bool {
    MEMO.with(|m| *m.borrow_mut() = Some(Memo::default()));
    let r = def_eq_lazy(a, b, depth);
    let (c, v, q) = MEMO.with(|m| {
        let m = m.borrow();
        let m = m.as_ref().unwrap();
        (m.cells.len(), m.vals.len(), m.equal.len())
    });
    bump(|s| {
        s.cells_len += c;
        s.vals_len += v;
        s.equal_len += q;
    });
    MEMO.with(|m| *m.borrow_mut() = None);
    r
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{app, def_eq, id, jelim, lam, pair, pi, refl, shift, sigma, sigrec, sort, sup, var, wrec, wty};

    fn eq(a: &Expr, b: &Expr, depth: u32) -> bool {
        let plain = def_eq_lazy(a, b, depth);
        assert_eq!(plain, def_eq_lazy_shared(a, b, depth), "shared and plain disagree on {a:?} vs {b:?}");
        plain
    }

    /// A doubling DAG: `a_(k+1) = Sup(a_k, a_k)` with both children the same `Rc`. Two independently
    /// built copies compare in O(k) with sharing and O(2^k) without.
    #[test]
    fn shared_mode_keeps_a_doubling_dag_linear() {
        fn dag(k: u32) -> Expr {
            let mut n = KRc::new(sort(0));
            for _ in 0..k {
                n = KRc::new(Expr::Sup(n.clone(), n.clone()));
            }
            (*n).clone()
        }
        let k = 40;
        let (a, b) = (dag(k), dag(k));
        assert!(def_eq_lazy_shared(&a, &b, 0));
        // a differing leaf is still found
        let mut c = KRc::new(sort(1));
        for _ in 0..k {
            c = KRc::new(Expr::Sup(c.clone(), c.clone()));
        }
        assert!(!def_eq_lazy_shared(&a, &(*c).clone(), 0));
    }

    #[test]
    fn beta_and_stuck_variables() {
        let id_fn = lam(sort(0), var(0));
        assert!(eq(&app(id_fn.clone(), sort(3)), &sort(3), 0));
        assert!(!eq(&app(id_fn, sort(3)), &sort(4), 0));
        assert!(eq(&var(0), &var(0), 1));
        assert!(!eq(&var(0), &var(1), 2));
    }

    #[test]
    fn lambda_domains_are_compared_like_the_kernel() {
        let a = lam(sort(0), var(0));
        let b = lam(sort(1), var(0));
        assert!(!eq(&a, &b, 0));
        assert_eq!(eq(&a, &b, 0), def_eq(&a, &b));
    }

    #[test]
    fn j_on_refl_reduces_but_j_on_a_variable_is_stuck() {
        let motive = lam(sort(0), lam(sort(0), lam(sort(0), sort(0))));
        let base = lam(sort(0), var(0));
        let j_refl = jelim(motive.clone(), base.clone(), sort(1), sort(1), refl(sort(1)));
        assert!(eq(&j_refl, &sort(1), 0));
        let j_var = jelim(motive.clone(), base.clone(), sort(1), sort(1), var(0));
        assert!(!eq(&j_var, &sort(1), 1));
        assert!(eq(&j_var, &j_var.clone(), 1));
        assert_eq!(eq(&j_var, &sort(1), 1), def_eq(&j_var, &sort(1)));
    }

    #[test]
    fn wrec_on_sup_and_sigrec_on_pair_reduce() {
        // wrec(motive, B, step, sup(a, f)) = step a f (\y. wrec .. (f y))
        let step = lam(sort(0), lam(sort(0), lam(sort(0), var(2))));
        let w = wrec(sort(0), sort(0), step.clone(), sup(sort(5), sort(6)));
        assert!(eq(&w, &sort(5), 0));
        assert_eq!(eq(&w, &sort(5), 0), def_eq(&w, &sort(5)));
        let s = sigrec(sort(0), lam(sort(0), lam(sort(0), var(1))), pair(sort(0), sort(7), sort(8)));
        assert!(eq(&s, &sort(7), 0));
        assert!(!eq(&s, &sort(8), 0));
    }

    /// `J` reduces to `base a` with the `J`'s own `a`, not `b`, even when
    /// the two differ (ill-typed, but the kernel reduces it).
    #[test]
    fn j_on_refl_uses_its_own_a() {
        let motive = lam(sort(0), lam(sort(0), lam(sort(0), sort(0))));
        let base = lam(sort(0), var(0));
        let j = jelim(motive, base, sort(1), sort(2), refl(sort(1)));
        assert!(eq(&j, &sort(1), 0) && !eq(&j, &sort(2), 0));
        assert_eq!(eq(&j, &sort(1), 0), def_eq(&j, &sort(1)));
    }

    /// The induction-hypothesis function `WRec` hands its step carries the
    /// honest domain `B(a)` and recurses on `f y`: a step returning its
    /// third argument gives `\y:B(a). wrec .. (f y)`, and a wrong domain
    /// is a different term.
    #[test]
    fn wrec_induction_hypothesis_has_its_domain_and_body() {
        let step = lam(sort(0), lam(sort(0), lam(sort(0), var(0))));
        let lhs = wrec(sort(0), sort(7), step.clone(), sup(sort(5), sort(6)));
        let rhs = |dom: u32| lam(sort(dom), wrec(sort(0), sort(7), step.clone(), app(sort(6), var(0))));
        assert!(eq(&lhs, &rhs(7), 0), "kernel says {}", def_eq(&lhs, &rhs(7)));
        assert!(!eq(&lhs, &rhs(8), 0));
        assert_eq!(eq(&lhs, &rhs(7), 0), def_eq(&lhs, &rhs(7)));
        assert_eq!(eq(&lhs, &rhs(8), 0), def_eq(&lhs, &rhs(8)));
    }

    /// The kernel's own random `Expr` generator (ill-typed as often as
    /// not), copied from `kernel::tests`.
    fn random_expr(seed: &mut u64, fuel: u32) -> Expr {
        let mut next = || {
            *seed = seed.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = *seed;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            z ^ (z >> 31)
        };
        let pick = next();
        let k = (next() % 4) as u32;
        if fuel == 0 || pick % 4 == 0 {
            return if pick % 8 == 0 { sort(k % 2) } else { var(k) };
        }
        let mut sub = || random_expr(seed, fuel - 1);
        match (pick >> 3) % 13 {
            0 => pi(sub(), sub()),
            1 => lam(sub(), sub()),
            2 => app(sub(), sub()),
            3 => id(sub(), sub(), sub()),
            4 => refl(sub()),
            5 => jelim(sub(), sub(), sub(), sub(), sub()),
            6 => wty(sub(), sub()),
            7 => sup(sub(), sub()),
            8 => wrec(sub(), sub(), sub(), sub()),
            9 => sigma(sub(), sub()),
            10 => pair(sub(), sub(), sub()),
            11 => sigrec(sub(), sub(), sub()),
            _ => app(sub(), sub()),
        }
    }

    /// Wraps some subterms in a redex that reduces back to them, as the
    /// kernel's own `with_redexes` does.
    fn with_redexes(e: &Expr, seed: &mut u64) -> Expr {
        *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        let wrap = (*seed >> 33).is_multiple_of(4);
        let mut go = |x: &KRc<Expr>| with_redexes(x, seed);
        let rebuilt = match e {
            Expr::Pi(a, b) => pi(go(a), go(b)),
            Expr::Lam(a, b) => lam(go(a), go(b)),
            Expr::App(f, a) => app(go(f), go(a)),
            Expr::Id(a, x, y) => id(go(a), go(x), go(y)),
            Expr::Sigma(a, b) => sigma(go(a), go(b)),
            Expr::Pair(fam, a, b) => pair(go(fam), go(a), go(b)),
            other => other.clone(),
        };
        if wrap { app(lam(sort(0), shift(&rebuilt, 0, 1)), sort(0)) } else { rebuilt }
    }

    /// `def_eq_lazy` agrees with `kernel::def_eq` on random pairs, some
    /// unrelated and some the same term with different redexes inserted.
    #[test]
    fn def_eq_lazy_agrees_with_the_kernel() {
        let (mut seed, mut equal, mut unequal) = (7u64, 0, 0);
        for i in 0..20_000 {
            let a = random_expr(&mut seed, 4);
            let b = if i % 2 == 0 { a.clone() } else { random_expr(&mut seed, 4) };
            let (a, b) = (with_redexes(&a, &mut seed), with_redexes(&b, &mut seed));
            let reference = def_eq(&a, &b);
            assert_eq!(def_eq_lazy(&a, &b, 4), reference, "a {a:?}, b {b:?}");
            if reference && a != b { equal += 1 } else if !reference { unequal += 1 }
        }
        assert!(equal > 2_000 && unequal > 2_000, "equal {equal}, unequal {unequal}");
    }
}
