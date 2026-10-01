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
use std::rc::Rc;

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
        Thunk(Rc::new(RefCell::new(Cell::Delayed(e.clone(), env.clone()))))
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
            Cell::Delayed(e, env) => eval(&env, &e),
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
            Clo::Term(env, body) => eval(&push(env, arg), body),
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
    if Rc::ptr_eq(x, y) {
        return true;
    }
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{app, def_eq, id, jelim, lam, pair, pi, refl, shift, sigma, sigrec, sort, sup, var, wrec, wty};

    fn eq(a: &Expr, b: &Expr, depth: u32) -> bool {
        def_eq_lazy(a, b, depth)
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
