//! Simple (monomorphic) type inference over `Term`: the JIT's static gate
//! against ill-typed code.
//!
//! Compiled code is untyped: an `Int` and a closure are both a raw `i64`,
//! with no tag to test. So a fragment that adds a closure to an `Int`, or
//! calls an `Int`, returns garbage where `eval` returns `TypeError` or
//! `NotAFunction`. `jit.rs`'s sample battery only catches that when a
//! sample reaches the ill-typed code, and the kernel theorem is stated over
//! postulated symbols that say nothing about types (`RELATED_WORK.md` §28,
//! §38). This closes the gap statically: [`well_typed`] accepts a term only
//! if it has type `Int -> ... -> Int`. By the usual type-safety argument, a
//! term that does can then never reach `TypeError`, `NotAFunction` or
//! `UnboundVariable` on `Int` arguments; `DivByZero` and divergence remain
//! possible, as in any typed language.
//!
//! The types are `Int`, `a -> b` and unification variables, with no
//! polymorphism: a closure used at two different types is declined. Two
//! rules go beyond the textbook ones:
//! - `Rec` must wrap an `Abs`, which is also all `compile.rs` compiles.
//!   `eval` treats a `Rec` value as a function, so `Rec(Lit 5) + 1` would
//!   otherwise type as `Int` and fail at runtime.
//! - An `If` whose condition is closed arithmetic over literals only types
//!   the branch that condition picks. `eval` can never take the other one,
//!   so its types don't matter, and dead ill-typed branches (used in tests
//!   and benches to exercise curried dispatch) stay compilable. The
//!   condition is evaluated with `eval` itself; if it fails, both branches
//!   are typed.
//!
//! Trusted, so it shares no code with the compiler (checked by the
//! `independent_of_the_compiler` test).

use crate::eval;
use crate::term::{Hash, Term, TermStore};

#[derive(Clone, Copy)]
enum Ty {
    Var,
    Int,
    Fun(usize, usize),
}

/// Union-find over type nodes.
struct Types {
    parent: Vec<usize>,
    ty: Vec<Ty>,
}

impl Types {
    fn fresh(&mut self, t: Ty) -> usize {
        self.parent.push(self.parent.len());
        self.ty.push(t);
        self.parent.len() - 1
    }

    fn find(&mut self, x: usize) -> usize {
        let p = self.parent[x];
        if p == x {
            return x;
        }
        let r = self.find(p);
        self.parent[x] = r;
        r
    }

    fn occurs(&mut self, v: usize, t: usize) -> bool {
        let t = self.find(t);
        t == v
            || match self.ty[t] {
                Ty::Fun(a, b) => self.occurs(v, a) || self.occurs(v, b),
                _ => false,
            }
    }

    fn unify(&mut self, a: usize, b: usize) -> Option<()> {
        let (a, b) = (self.find(a), self.find(b));
        if a == b {
            return Some(());
        }
        match (self.ty[a], self.ty[b]) {
            (Ty::Var, _) => {
                if self.occurs(a, b) {
                    return None;
                }
                self.parent[a] = b;
            }
            (_, Ty::Var) => return self.unify(b, a),
            (Ty::Int, Ty::Int) => self.parent[a] = b,
            (Ty::Fun(a1, a2), Ty::Fun(b1, b2)) => {
                self.parent[a] = b;
                self.unify(a1, b1)?;
                self.unify(a2, b2)?;
            }
            _ => return None,
        }
        Some(())
    }
}

/// Whether `t` is built from literals and primitives only.
fn constant(s: &TermStore, t: Hash) -> bool {
    match *s.resolve(t) {
        Term::Lit(_) => true,
        Term::Prim(_, a, b) => constant(s, a) && constant(s, b),
        _ => false,
    }
}

/// The type of `t` under `env` (innermost binder last).
fn infer(s: &TermStore, t: Hash, env: &mut Vec<usize>, tys: &mut Types) -> Option<usize> {
    Some(match *s.resolve(t) {
        Term::Var(i) => *env.iter().rev().nth(i as usize)?,
        Term::Lit(_) => tys.fresh(Ty::Int),
        Term::Prim(_, a, b) => {
            let int = tys.fresh(Ty::Int);
            let ta = infer(s, a, env, tys)?;
            tys.unify(ta, int)?;
            let tb = infer(s, b, env, tys)?;
            tys.unify(tb, int)?;
            int
        }
        Term::If(c, x, y) => {
            let int = tys.fresh(Ty::Int);
            let tc = infer(s, c, env, tys)?;
            tys.unify(tc, int)?;
            if constant(s, c)
                && let Ok(k) = eval::apply_term(s, c, &[])
            {
                return infer(s, if k != 0 { x } else { y }, env, tys);
            }
            let tx = infer(s, x, env, tys)?;
            let ty = infer(s, y, env, tys)?;
            tys.unify(tx, ty)?;
            tx
        }
        Term::Abs(body) => {
            let a = tys.fresh(Ty::Var);
            env.push(a);
            let tb = infer(s, body, env, tys);
            env.pop();
            tys.fresh(Ty::Fun(a, tb?))
        }
        Term::App(f, a) => {
            let tf = infer(s, f, env, tys)?;
            let ta = infer(s, a, env, tys)?;
            let r = tys.fresh(Ty::Var);
            let want = tys.fresh(Ty::Fun(ta, r));
            tys.unify(tf, want)?;
            r
        }
        Term::Rec(inner) => {
            if !matches!(s.resolve(inner), Term::Abs(_)) {
                return None;
            }
            let me = tys.fresh(Ty::Var);
            env.push(me);
            let ti = infer(s, inner, env, tys);
            env.pop();
            let ti = ti?;
            tys.unify(me, ti)?;
            ti
        }
    })
}

/// Whether the closed term `h` has type `Int -> ... -> Int`, with `arity`
/// arguments. See the module docs for what that rules out.
pub fn well_typed(s: &TermStore, h: Hash, arity: usize) -> bool {
    let mut tys = Types { parent: vec![], ty: vec![] };
    let Some(t) = infer(s, h, &mut vec![], &mut tys) else {
        return false;
    };
    let mut want = tys.fresh(Ty::Int);
    for _ in 0..arity {
        let int = tys.fresh(Ty::Int);
        want = tys.fresh(Ty::Fun(int, want));
    }
    tys.unify(t, want).is_some()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::PrimOp;

    #[test]
    fn independent_of_the_compiler() {
        crate::independence::assert_independent(
            "typing.rs",
            include_str!("typing.rs"),
            &["compile", "lower_wat", "specialise", "spec_check", "proof", "jit"],
            &["eval", "term"],
        );
    }

    /// `\n. (\g. if n == 777 then g 1 + g else n) (\x. x + n)`: adds a
    /// closure to an `Int` on one branch.
    fn closure_plus_int(s: &mut TermStore) -> Hash {
        let (v0, v1, one, k) = (s.var(0), s.var(1), s.lit(1), s.lit(777));
        let g1 = s.app(v0, one);
        let bad = s.prim(PrimOp::Add, g1, v0);
        let cond = s.prim(PrimOp::Eq, v1, k);
        let body = s.if_(cond, bad, v1);
        let lam = s.abs(body);
        let arg_body = s.prim(PrimOp::Add, v0, v1);
        let arg = s.abs(arg_body);
        let redex = s.app(lam, arg);
        s.abs(redex)
    }

    #[test]
    fn well_typed_arithmetic_and_closures_are_accepted() {
        let mut s = TermStore::new();
        // \x y. (\f. f x) (\z. z * y)
        let (v0, v1, v2) = (s.var(0), s.var(1), s.var(2));
        let fx = s.app(v0, v2);
        let applier = s.abs(fx);
        let zy = s.prim(PrimOp::Mul, v0, v1);
        let f = s.abs(zy);
        let call = s.app(applier, f);
        let inner = s.abs(call);
        let h = s.abs(inner);
        assert!(well_typed(&s, h, 2));
        assert!(!well_typed(&s, h, 1), "at arity 1 the result is a function, not an Int");
    }

    #[test]
    fn a_closure_used_as_an_int_is_declined() {
        let mut s = TermStore::new();
        let h = closure_plus_int(&mut s);
        assert!(!well_typed(&s, h, 1));
    }

    #[test]
    fn an_ill_typed_branch_is_ignored_only_when_the_condition_is_constant() {
        // \n. if C then n else n 1: calls an Int on the else branch.
        for (cond_is_constant, expect) in [(true, true), (false, false)] {
            let mut s = TermStore::new();
            let (v0, zero, one) = (s.var(0), s.lit(0), s.lit(1));
            let cond = if cond_is_constant { s.prim(PrimOp::Lt, zero, one) } else { s.prim(PrimOp::Lt, zero, v0) };
            let bad = s.app(v0, one);
            let body = s.if_(cond, v0, bad);
            let h = s.abs(body);
            assert_eq!(well_typed(&s, h, 1), expect, "constant condition: {cond_is_constant}");
        }
        // A constant condition that fails to evaluate types both branches.
        let mut s = TermStore::new();
        let (v0, zero, one) = (s.var(0), s.lit(0), s.lit(1));
        let cond = s.prim(PrimOp::Div, one, zero);
        let bad = s.app(v0, one);
        let body = s.if_(cond, v0, bad);
        let h = s.abs(body);
        assert!(!well_typed(&s, h, 1));
    }

    #[test]
    fn rec_must_wrap_an_abs() {
        // \x. rec(5) + x: `eval` gives TypeError, since a `Rec` value is a function.
        let mut s = TermStore::new();
        let five = s.lit(5);
        let r = s.rec(five);
        let v0 = s.var(0);
        let body = s.prim(PrimOp::Add, r, v0);
        let h = s.abs(body);
        assert_eq!(eval::apply_term(&s, h, &[1]), Err(eval::EvalError::TypeError));
        assert!(!well_typed(&s, h, 1));
    }

    #[test]
    fn recursion_is_typed_through_its_self_reference() {
        // rec f n. if n <= 0 then 0 else f (n - 1)
        let mut s = TermStore::new();
        let (n, f, zero, one) = (s.var(0), s.var(1), s.lit(0), s.lit(1));
        let cond = s.prim(PrimOp::Le, n, zero);
        let n1 = s.prim(PrimOp::Sub, n, one);
        let call = s.app(f, n1);
        let body = s.if_(cond, zero, call);
        let lam = s.abs(body);
        let h = s.rec(lam);
        assert!(well_typed(&s, h, 1));
        // The same, but returning `f` itself on the base case.
        let bad = s.if_(cond, f, call);
        let lam = s.abs(bad);
        let h = s.rec(lam);
        assert!(!well_typed(&s, h, 1));
    }

    #[test]
    fn self_application_open_terms_and_closure_parameters_are_declined() {
        let mut s = TermStore::new();
        let v0 = s.var(0);
        let xx = s.app(v0, v0);
        let omega = s.abs(xx);
        assert!(!well_typed(&s, omega, 1), "occurs check");
        let v1 = s.var(1);
        let open = s.abs(v1);
        assert!(!well_typed(&s, open, 1));
        // \f x. f x takes a closure, which the JIT can't pass.
        let fx = s.app(v1, v0);
        let inner = s.abs(fx);
        let apply = s.abs(inner);
        assert!(!well_typed(&s, apply, 2));
    }
}
