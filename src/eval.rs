//! Reference interpreter: defines the semantics every other representation
//! of a term (in particular, JIT-compiled code) is judged equivalent to.
//!
//! `eval` is trampolined for its own tail positions (`If`'s chosen branch,
//! and applying a value that resolves the current call) rather than
//! recursing through ordinary Rust calls: it mutates a local `(env, h)`
//! pair in a `loop` and only ever `return`s once it hits something that
//! isn't itself a further tail call (a `Var`, `Lit`, `Prim`, or a fresh
//! `Closure`/`Rec` value). This matters because a *tail-recursive* term
//! (see `compile.rs`'s own `loop`/`br` conversion for the same shape) is
//! exactly a term whose self-call sits in one of these tail positions --
//! without trampolining, each iteration would consume a fresh native stack
//! frame here, capping how deep any tail-recursive term could run before
//! overflowing (empirically, somewhere between 8,000 and 10,000 levels
//! even in release mode) for a reason that has nothing to do with the
//! term's own semantics, unlike a genuinely *non*-tail-recursive call
//! (e.g. naive `fib`), which still grows the stack here exactly as it
//! grows a Wasm `call` chain in the compiled reading -- an honest, shared
//! limit, not something trampolining is meant to paper over.

use std::rc::Rc;

use crate::term::{Hash, PrimOp, Term, TermStore};

#[derive(Clone)]
pub enum Value {
    Int(i64),
    Closure(Env, Hash),
    /// A not-yet-unrolled self-recursive function value (see `Term::Rec`).
    Rec(Env, Hash),
}

#[derive(Clone, Default)]
pub enum Env {
    #[default]
    Empty,
    Cons(Rc<(Value, Env)>),
}

impl Env {
    fn push(&self, v: Value) -> Env {
        Env::Cons(Rc::new((v, self.clone())))
    }

    fn get(&self, mut i: u32) -> Result<Value, EvalError> {
        let mut cur = self;
        loop {
            match cur {
                Env::Empty => return Err(EvalError::UnboundVariable),
                Env::Cons(rc) => {
                    if i == 0 {
                        return Ok(rc.0.clone());
                    }
                    i -= 1;
                    cur = &rc.1;
                }
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EvalError {
    UnboundVariable,
    TypeError,
    DivByZero,
    NotAFunction,
    /// A compiled (JIT) code path trapped; carried through so callers can
    /// compare interpreter and compiled outcomes uniformly.
    Trap,
}

pub fn eval(store: &TermStore, env: &Env, h: Hash) -> Result<Value, EvalError> {
    let mut env = env.clone();
    let mut h = h;
    loop {
        match store.resolve(h) {
            Term::Var(i) => return env.get(*i),
            Term::Lit(n) => return Ok(Value::Int(*n)),
            Term::Prim(op, a, b) => {
                let a = eval(store, &env, *a)?;
                let b = eval(store, &env, *b)?;
                let (Value::Int(x), Value::Int(y)) = (a, b) else {
                    return Err(EvalError::TypeError);
                };
                return apply_prim(*op, x, y);
            }
            Term::If(c, t, e) => {
                let Value::Int(cv) = eval(store, &env, *c)? else {
                    return Err(EvalError::TypeError);
                };
                h = if cv != 0 { *t } else { *e };
            }
            Term::Abs(body) => return Ok(Value::Closure(env.clone(), *body)),
            Term::Rec(inner) => return Ok(Value::Rec(env.clone(), *inner)),
            Term::App(f, a) => {
                let fv = eval(store, &env, *f)?;
                let av = eval(store, &env, *a)?;
                let (next_env, next_h) = apply_step(store, fv, av)?;
                env = next_env;
                h = next_h;
            }
        }
    }
}

/// Reduces applying `f` to `arg` down to the `(env, h)` pair whose
/// evaluation *is* the result -- shared by `eval`'s own tail-position
/// `App` handling (which loops on the result instead of recursing) and
/// `apply_value` below (which isn't itself in a tail position -- it's
/// driven by `apply_term`'s own, separate, bounded-by-arity loop over
/// concrete argument values -- so it just evaluates the pair directly).
/// A `Rec` value unrolls one layer (binding the recursive value itself
/// into scope) before recursing into itself; this recursion is bounded by
/// how many `Rec`-unrollings the applied value chains through, not by
/// anything that scales with a term's own loop-iteration count, so it
/// stays a plain call.
fn apply_step(store: &TermStore, f: Value, arg: Value) -> Result<(Env, Hash), EvalError> {
    match f {
        Value::Closure(env, body) => Ok((env.push(arg), body)),
        Value::Rec(env, inner) => {
            // Unroll one layer: bind the recursive value itself into scope,
            // then evaluate `inner` (typically an `Abs`, so this just makes
            // a closure) and apply as normal.
            let self_val = Value::Rec(env.clone(), inner);
            let ext = env.push(self_val);
            let fval = eval(store, &ext, inner)?;
            apply_step(store, fval, arg)
        }
        Value::Int(_) => Err(EvalError::NotAFunction),
    }
}

fn apply_prim(op: PrimOp, x: i64, y: i64) -> Result<Value, EvalError> {
    use PrimOp::*;
    Ok(match op {
        Add => Value::Int(x.wrapping_add(y)),
        Sub => Value::Int(x.wrapping_sub(y)),
        Mul => Value::Int(x.wrapping_mul(y)),
        Div => {
            if y == 0 {
                return Err(EvalError::DivByZero);
            }
            Value::Int(x.wrapping_div(y))
        }
        Mod => {
            if y == 0 {
                return Err(EvalError::DivByZero);
            }
            Value::Int(x.wrapping_rem(y))
        }
        Lt => Value::Int((x < y) as i64),
        Le => Value::Int((x <= y) as i64),
        Eq => Value::Int((x == y) as i64),
    })
}

fn apply_value(store: &TermStore, f: Value, arg: Value) -> Result<Value, EvalError> {
    let (env, h) = apply_step(store, f, arg)?;
    eval(store, &env, h)
}

/// Evaluate `h` as a (possibly zero-arity) function and apply it to `args`
/// in order. This is the interpreter-only entry point mirrored by the JIT.
pub fn apply_term(store: &TermStore, h: Hash, args: &[i64]) -> Result<i64, EvalError> {
    let mut v = eval(store, &Env::Empty, h)?;
    for &a in args {
        v = apply_value(store, v, Value::Int(a))?;
    }
    match v {
        Value::Int(n) => Ok(n),
        _ => Err(EvalError::TypeError),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::PrimOp;

    fn factorial(s: &mut TermStore) -> Hash {
        // rec f n = if n <= 1 then 1 else n * f(n - 1)
        let n = s.var(0);
        let f = s.var(1);
        let one = s.lit(1);
        let cond = s.prim(PrimOp::Le, n, one);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one);
        let rec_call = s.app(f, n_minus_1);
        let n2 = s.var(0);
        let else_branch = s.prim(PrimOp::Mul, n2, rec_call);
        let one2 = s.lit(1);
        let body = s.if_(cond, one2, else_branch);
        let abs = s.abs(body);
        s.rec(abs)
    }

    #[test]
    fn factorial_interprets_correctly() {
        let mut s = TermStore::new();
        let fact = factorial(&mut s);
        assert_eq!(apply_term(&s, fact, &[0]).unwrap(), 1);
        assert_eq!(apply_term(&s, fact, &[1]).unwrap(), 1);
        assert_eq!(apply_term(&s, fact, &[5]).unwrap(), 120);
        assert_eq!(apply_term(&s, fact, &[10]).unwrap(), 3628800);
    }

    fn countdown(s: &mut TermStore) -> Hash {
        // rec f n = if n <= 0 then 0 else f(n - 1) -- the simplest possible
        // tail-recursive shape, isolating the trampoline itself from any
        // other per-iteration cost.
        let n = s.var(0);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Le, n, zero);
        let n2 = s.var(0);
        let one = s.lit(1);
        let n_minus_1 = s.prim(PrimOp::Sub, n2, one);
        let f = s.var(1);
        let rec_call = s.app(f, n_minus_1);
        let zero2 = s.lit(0);
        let body = s.if_(cond, zero2, rec_call);
        let abs = s.abs(body);
        s.rec(abs)
    }

    #[test]
    fn deep_tail_recursion_does_not_overflow_the_native_stack() {
        // Comfortably past the ~8,000-10,000 levels a plain (non-
        // trampolined) recursive eval() overflows at even in release mode
        // (see this module's own docs) -- if eval's App/If handling ever
        // regresses back to recursing instead of looping on a tail call,
        // this crashes the whole test process (a real stack overflow
        // aborts, it doesn't panic cleanly), not just fails an assertion.
        let mut s = TermStore::new();
        let h = countdown(&mut s);
        assert_eq!(apply_term(&s, h, &[2_000_000]).unwrap(), 0);
    }

    #[test]
    fn deep_tail_recursion_creating_and_calling_a_fresh_closure_each_iteration_does_not_overflow() {
        // rec f n acc = if n <= 0 then acc else f(n-1, (\y. acc+y)(n)) --
        // same shape as benches::common::capturing_closure_loop /
        // compile::tests::self_recursion_creating_a_fresh_capturing_closure_every_iteration_compiles,
        // exercising the trampoline's App/Closure-application path (not
        // just If's own tail branch) at depth.
        let mut s = TermStore::new();
        let y = s.var(0);
        let acc_captured = s.var(1);
        let sum = s.prim(PrimOp::Add, acc_captured, y);
        let closure = s.abs(sum);
        let n_ref = s.var(1);
        let new_acc = s.app(closure, n_ref);
        let n = s.var(1);
        let acc = s.var(0);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Le, n, zero);
        let one = s.lit(1);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one);
        let f = s.var(2);
        let rec_call = s.app2(f, n_minus_1, new_acc);
        let body = s.if_(cond, acc, rec_call);
        let inner = s.abs(body);
        let abs = s.abs(inner);
        let h = s.rec(abs);

        assert_eq!(apply_term(&s, h, &[100_000, 0]).unwrap(), 100_000 * 100_001 / 2);
    }

    #[test]
    fn higher_order_terms_still_work() {
        // twice = \f. \x. f (f x); inc = \y. y + 1; (twice inc) 5 == 7
        let mut s = TermStore::new();
        let f = s.var(1);
        let x = s.var(0);
        let fx = s.app(f, x);
        let ffx = s.app(f, fx);
        let inner = s.abs(ffx);
        let twice = s.abs(inner);

        let y = s.var(0);
        let one = s.lit(1);
        let y_plus_1 = s.prim(PrimOp::Add, y, one);
        let inc = s.abs(y_plus_1);

        let five = s.lit(5);
        let applied = s.app2(twice, inc, five);
        assert_eq!(apply_term(&s, applied, &[]).unwrap(), 7);
    }

    #[test]
    fn div_by_zero_errors_instead_of_panicking() {
        let mut s = TermStore::new();
        let one = s.lit(1);
        let zero = s.lit(0);
        let div = s.prim(PrimOp::Div, one, zero);
        assert_eq!(apply_term(&s, div, &[]), Err(EvalError::DivByZero));
    }
}
