//! Simple (monomorphic) type inference over `Term`: the JIT's static gate
//! against ill-typed code.
//!
//! Compiled code is untyped: an `Int` and a closure are both a raw `i64`,
//! with no tag to test. So a fragment that adds a closure to an `Int`, or
//! calls an `Int`, returns garbage where `eval` returns `TypeError` or
//! `NotAFunction`. `jit.rs`'s sample battery only catches that when a
//! sample reaches the ill-typed code, and the kernel theorem is stated over
//! postulated symbols that say nothing about types (`docs/related-work/` §28,
//! §38). This closes the gap statically: [`well_typed`] accepts a term only
//! if it has type `Int -> ... -> Int`. By the usual type-safety argument, a
//! term that does can then never reach `TypeError`, `NotAFunction` or
//! `UnboundVariable` on `Int` arguments; `DivByZero` and divergence remain
//! possible, as in any typed language. That claim is fuzzed, not proved
//! (`a_well_typed_term_never_goes_wrong`, `docs/related-work/` §45).
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

use crate::lang::eval;
use crate::lang::term::{Hash, Term, TermStore};
use hashbrown::{HashMap, HashSet};

#[derive(Clone, Copy)]
enum Ty {
    Var,
    Int,
    Fun(usize, usize),
}

/// Union-find over type nodes, and the memo that makes `infer` linear in
/// shared subterms.
#[derive(Default)]
struct Types {
    parent: Vec<usize>,
    ty: Vec<Ty>,
    /// Each environment `infer` has seen, as (enclosing environment, the
    /// binder's type node), numbered from 1; 0 is the empty environment.
    envs: HashMap<(usize, usize), usize>,
    /// The current environment's number, innermost last.
    env_ids: Vec<usize>,
    /// Ground types already inferred, by (subterm, environment).
    memo: HashMap<(Hash, usize), usize>,
    /// Calls to `infer`, for tests.
    steps: usize,
    /// Turns the memo off, for tests that check it changes no answer.
    no_memo: bool,
}

impl Types {
    fn push_env(&mut self, env: &mut Vec<usize>, a: usize) {
        let outer = self.env_ids.last().copied().unwrap_or(0);
        let next = self.envs.len() + 1;
        let id = *self.envs.entry((outer, a)).or_insert(next);
        self.env_ids.push(id);
        env.push(a);
    }

    fn pop_env(&mut self, env: &mut Vec<usize>) {
        self.env_ids.pop();
        env.pop();
    }

    /// Whether some node of `t`, a representative, satisfies `hit`. Each
    /// node is visited once, so a type shared many times inside `t` costs
    /// no more than once.
    fn any_node(&mut self, t: usize, hit: impl Fn(usize, Ty) -> bool) -> bool {
        let mut seen = HashSet::new();
        let mut todo = vec![t];
        while let Some(t) = todo.pop() {
            let t = self.find(t);
            if !seen.insert(t) {
                continue;
            }
            if hit(t, self.ty[t]) {
                return true;
            }
            if let Ty::Fun(a, b) = self.ty[t] {
                todo.extend([a, b]);
            }
        }
        false
    }

    /// Whether `t` contains no type variable.
    fn ground(&mut self, t: usize) -> bool {
        !self.any_node(t, |_, ty| matches!(ty, Ty::Var))
    }

    fn fresh(&mut self, t: Ty) -> usize {
        self.parent.push(self.parent.len());
        self.ty.push(t);
        self.parent.len() - 1
    }

    fn find(&mut self, x: usize) -> usize {
        let mut root = x;
        while self.parent[root] != root {
            root = self.parent[root];
        }
        let mut x = x;
        while self.parent[x] != root {
            (x, self.parent[x]) = (self.parent[x], root);
        }
        root
    }

    /// Whether the representative `v` occurs in `t`.
    fn occurs(&mut self, v: usize, t: usize) -> bool {
        self.any_node(t, |n, _| n == v)
    }

    fn unify(&mut self, a: usize, b: usize) -> Option<()> {
        let (a, b) = (self.find(a), self.find(b));
        if a == b {
            return Some(());
        }
        // Linking `a` into a `b` that contains it would make the type graph
        // cyclic: an infinite type, which every later walk would follow
        // forever. That is the occurs check, and it is owed when two arrows
        // are linked as much as when a variable is bound: from
        // `f : a -> a`, the call `f (\y. f)` needs `a = b -> (a -> a)`.
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
                if self.occurs(a, b) {
                    return None;
                }
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
///
/// A hash-consed term can share a subterm exponentially often, so a
/// ground result is memoised. Re-inferring the same subterm in the same
/// environment would unify a fresh copy of the same constraints, which
/// succeeds again and fixes the copy to the same ground type, so the memo
/// changes no answer. A result with variables isn't memoised: a copy's
/// variables are fresh, which is what lets a shared lambda be used at two
/// types.
fn infer(s: &TermStore, t: Hash, env: &mut Vec<usize>, tys: &mut Types) -> Option<usize> {
    tys.steps += 1;
    let key = (t, tys.env_ids.last().copied().unwrap_or(0));
    if let Some(&ty) = tys.memo.get(&key) {
        return Some(ty);
    }
    let ty = infer_uncached(s, t, env, tys)?;
    if !tys.no_memo && tys.ground(ty) {
        tys.memo.insert(key, ty);
    }
    Some(ty)
}

fn infer_uncached(s: &TermStore, t: Hash, env: &mut Vec<usize>, tys: &mut Types) -> Option<usize> {
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
            tys.push_env(env, a);
            let tb = infer(s, body, env, tys);
            tys.pop_env(env);
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
            tys.push_env(env, me);
            let ti = infer(s, inner, env, tys);
            tys.pop_env(env);
            let ti = ti?;
            tys.unify(me, ti)?;
            ti
        }
    })
}

/// Whether the closed term `h` has type `Int -> ... -> Int`, with `arity`
/// arguments. See the module docs for what that rules out.
pub fn well_typed(s: &TermStore, h: Hash, arity: usize) -> bool {
    well_typed_in(s, h, arity, Types::default())
}

fn well_typed_in(s: &TermStore, h: Hash, arity: usize, mut tys: Types) -> bool {
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
mod tests;
