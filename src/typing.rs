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
//! possible, as in any typed language. That claim is fuzzed, not proved
//! (`a_well_typed_term_never_goes_wrong`, `RELATED_WORK.md` §45).
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
use std::collections::{HashMap, HashSet};

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
    fn a_shared_subterm_is_typed_once() {
        // \n. t_12, where t_0 = n and t_{i+1} = t_i + t_i: 13 distinct
        // subterms, 8191 as a tree.
        let mut s = TermStore::new();
        let mut t = s.var(0);
        for _ in 0..12 {
            t = s.prim(PrimOp::Add, t, t);
        }
        let h = s.abs(t);
        let mut tys = Types::default();
        assert!(infer(&s, h, &mut vec![], &mut tys).is_some());
        assert!(tys.steps < 100, "{} steps", tys.steps);
    }

    #[test]
    fn a_shared_lambda_can_still_be_used_at_two_types() {
        // \n. (\k. k n) id + (\k. k id) id 0, with one `id = \x. x` node
        // used at `Int -> Int` and at `(Int -> Int) -> (Int -> Int)`.
        let mut s = TermStore::new();
        let (v0, v1, zero) = (s.var(0), s.var(1), s.lit(0));
        let id = s.abs(v0);
        let kn = s.app(v0, v1);
        let apply_n = s.abs(kn);
        let a = s.app(apply_n, id);
        let kid = s.app(v0, id);
        let apply_id = s.abs(kid);
        let b = s.app2(apply_id, id, zero);
        let body = s.prim(PrimOp::Add, a, b);
        let h = s.abs(body);
        assert_eq!(eval::apply_term(&s, h, &[4]), Ok(4));
        assert!(well_typed(&s, h, 1));
    }

    /// A random term generator for the two fuzz tests below: every
    /// constructor, well-typed or not, with subterms reused so the memo is
    /// exercised. Every term it builds terminates, so `eval` can be run on
    /// any of them: in the simply typed fragment that's strong
    /// normalisation, and a `Rec` either can't name itself or is a loop
    /// whose counter, clamped to 20, goes down by one per self-call.
    struct Gen {
        rng: u64,
        /// Earlier subterms, by the scope they were built in.
        pool: HashMap<Vec<bool>, Vec<Hash>>,
    }

    impl Gen {
        fn below(&mut self, n: u64) -> u64 {
            // splitmix64, as in the other fuzzers.
            self.rng = self.rng.wrapping_add(0x9E3779B97F4A7C15);
            let mut z = self.rng;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
            (z ^ (z >> 31)) % n
        }

        fn lit(&mut self, s: &mut TermStore) -> Hash {
            let n = self.below(14) as i64 - 3;
            s.lit(n)
        }

        fn op(&mut self) -> PrimOp {
            use PrimOp::*;
            [Add, Sub, Mul, Div, Mod, Lt, Le, Eq][self.below(8) as usize]
        }

        /// Closed arithmetic over literals, which may divide by zero.
        fn constant(&mut self, s: &mut TermStore, fuel: u32) -> Hash {
            if fuel == 0 || self.below(2) == 0 {
                return self.lit(s);
            }
            let op = self.op();
            let a = self.constant(s, fuel - 1);
            let b = self.constant(s, fuel - 1);
            s.prim(op, a, b)
        }

        /// `scope` holds the enclosing binders, innermost last; `false`
        /// marks a `Rec`'s self-reference, which only a loop's own
        /// self-call may name.
        fn term(&mut self, s: &mut TermStore, scope: &mut Vec<bool>, fuel: u32) -> Hash {
            let earlier = self.pool.get(scope).map_or(0, Vec::len);
            if earlier > 0 && self.below(3) == 0 {
                let i = self.below(earlier as u64) as usize;
                return self.pool[scope][i];
            }
            let t = self.fresh_term(s, scope, fuel);
            self.pool.entry(scope.clone()).or_default().push(t);
            t
        }

        fn fresh_term(&mut self, s: &mut TermStore, scope: &mut Vec<bool>, fuel: u32) -> Hash {
            let vars: Vec<u32> =
                scope.iter().rev().enumerate().filter(|&(_, &ok)| ok).map(|(i, _)| i as u32).collect();
            if fuel == 0 || self.below(4) == 0 {
                return if !vars.is_empty() && self.below(3) != 0 {
                    s.var(vars[self.below(vars.len() as u64) as usize])
                } else {
                    self.lit(s)
                };
            }
            let f = fuel - 1;
            match self.below(9) {
                0 | 1 => {
                    let op = self.op();
                    let a = self.term(s, scope, f);
                    // `a op a` shares `a` in one environment, as the
                    // exponential case does.
                    let b = if self.below(2) == 0 { a } else { self.term(s, scope, f) };
                    s.prim(op, a, b)
                }
                2 => {
                    let c = if self.below(3) == 0 { self.constant(s, 2) } else { self.term(s, scope, f) };
                    let x = self.term(s, scope, f);
                    let y = self.term(s, scope, f);
                    s.if_(c, x, y)
                }
                3 | 4 => {
                    scope.push(true);
                    let body = self.term(s, scope, f);
                    scope.pop();
                    s.abs(body)
                }
                5 | 6 => {
                    let g = self.term(s, scope, f);
                    let a = self.term(s, scope, f);
                    s.app(g, a)
                }
                7 => {
                    // A `Rec` that can't name itself: typed only if it
                    // wraps an `Abs`.
                    scope.push(false);
                    let body = self.term(s, scope, f);
                    scope.pop();
                    s.rec(body)
                }
                _ => self.bounded_loop(s, scope, f),
            }
        }

        /// `rec f n. if 20 < n then e1 else if n <= 0 then e2
        ///           else (\r. e3) (f (n - 1))`, where only the self-call
        /// names `f`.
        fn bounded_loop(&mut self, s: &mut TermStore, scope: &mut Vec<bool>, fuel: u32) -> Hash {
            scope.extend([false, true]);
            let e1 = self.term(s, scope, fuel);
            let e2 = self.term(s, scope, fuel);
            scope.push(true);
            let e3 = self.term(s, scope, fuel);
            scope.pop();
            scope.truncate(scope.len() - 2);
            let (n, me, one, twenty, zero) = (s.var(0), s.var(1), s.lit(1), s.lit(20), s.lit(0));
            let n1 = s.prim(PrimOp::Sub, n, one);
            let call = s.app(me, n1);
            let then = s.abs(e3);
            let step = s.app(then, call);
            let low = s.prim(PrimOp::Le, n, zero);
            let inner = s.if_(low, e2, step);
            let high = s.prim(PrimOp::Lt, twenty, n);
            let body = s.if_(high, e1, inner);
            let lam = s.abs(body);
            s.rec(lam)
        }

        /// A term of `arity` parameters.
        fn program(&mut self, s: &mut TermStore, arity: usize) -> Hash {
            let mut scope = vec![true; arity];
            let mut h = self.term(s, &mut scope, 6);
            for _ in 0..arity {
                h = s.abs(h);
            }
            h
        }
    }

    /// The type-safety claim in the module docs: a term `well_typed` at
    /// `arity` never gets stuck on `Int` arguments. Also checks each
    /// program's arity-0 and arity-1 readings, and every subterm, since
    /// the generator's pool shares them.
    #[test]
    fn a_well_typed_term_never_goes_wrong() {
        // `eval` recurses once per nested loop iteration, deeper than a
        // test thread's default stack in a debug build.
        std::thread::Builder::new().stack_size(256 << 20).spawn(well_typed_terms_never_go_wrong).unwrap().join().unwrap();
    }

    fn well_typed_terms_never_go_wrong() {
        const SEEDS: u64 = 4000;
        const ARGS: [i64; 5] = [0, 1, -2, 7, 25];
        let (mut typed, mut ran, mut div) = (0, 0, 0);
        for seed in 0..SEEDS {
            let mut g = Gen { rng: seed, pool: HashMap::new() };
            let mut s = TermStore::new();
            let arity = g.below(3) as usize;
            let h = g.program(&mut s, arity);
            if !well_typed(&s, h, arity) {
                continue;
            }
            typed += 1;
            for args in (0..ARGS.len().pow(arity as u32)).map(|mut i| {
                (0..arity)
                    .map(|_| {
                        let a = ARGS[i % ARGS.len()];
                        i /= ARGS.len();
                        a
                    })
                    .collect::<Vec<_>>()
            }) {
                ran += 1;
                match eval::apply_term(&s, h, &args) {
                    Ok(_) => {}
                    Err(eval::EvalError::DivByZero) => div += 1,
                    Err(e) => panic!("seed {seed}: well typed at arity {arity}, but {e:?} at {args:?}"),
                }
            }
        }
        println!("{typed} of {SEEDS} well typed; {ran} runs, {div} divided by zero");
        assert!(typed >= SEEDS / 10, "only {typed} well-typed terms: the generator has drifted");
    }

    /// The memo changes no answer: on every generated term, with and
    /// without it, `well_typed` agrees.
    #[test]
    fn the_memo_changes_no_answer() {
        const SEEDS: u64 = 4000;
        let mut shared = 0;
        for seed in 0..SEEDS {
            let mut g = Gen { rng: seed, pool: HashMap::new() };
            let mut s = TermStore::new();
            let arity = g.below(3) as usize;
            let h = g.program(&mut s, arity);
            let (mut with, mut without) = (Types::default(), Types { no_memo: true, ..Types::default() });
            let memo = infer(&s, h, &mut vec![], &mut with).is_some();
            let plain = infer(&s, h, &mut vec![], &mut without).is_some();
            assert_eq!(memo, plain, "seed {seed}: inference");
            if with.steps < without.steps {
                shared += 1;
            }
            let no_memo = Types { no_memo: true, ..Types::default() };
            assert_eq!(well_typed(&s, h, arity), well_typed_in(&s, h, arity, no_memo), "seed {seed}");
        }
        println!("the memo saved work on {shared} of {SEEDS} terms");
        // Most terms are ill-typed and stop early, so this floor is low.
        assert!(shared >= SEEDS / 25, "the memo saved work on only {shared} terms");
    }

    #[test]
    fn an_infinite_type_through_two_arrows_is_declined() {
        // \n. \f. (if n then f else \x. x) (\y. f): the `if` makes `f`'s
        // type `a -> a`, and the call then needs `a = b -> (a -> a)`.
        let mut s = TermStore::new();
        let (v0, v1) = (s.var(0), s.var(1));
        let id = s.abs(v0);
        let pick = s.if_(v1, v0, id);
        let const_f = s.abs(v1);
        let call = s.app(pick, const_f);
        let inner = s.abs(call);
        let h = s.abs(inner);
        assert!(!well_typed(&s, h, 2));
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
