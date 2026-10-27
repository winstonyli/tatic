//! Reference interpreter: defines the semantics every other representation
//! of a term (in particular, JIT-compiled code) is judged equivalent to.
//!
//! `eval` is trampolined for its own tail positions (`If`'s chosen branch,
//! and applying a value that resolves the current call) rather than
//! recursing through ordinary Rust calls: it mutates a local `(env, h)`
//! pair in a `loop` and only ever `return`s once it hits something that
//! isn't itself a further tail call (a `Var`, `Lit`, `Prim`, or a fresh
//! `Closure`/`Rec` value). This matters because a *tail-recursive* term
//! (see `lower_wat.rs`'s own `loop`/`br` lowering for the same shape) is
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
    use crate::samples::{capturing_closure_loop, factorial, source, twice_inc_5};

    #[test]
    fn factorial_interprets_correctly() {
        let mut s = TermStore::new();
        let fact = factorial(&mut s);
        assert_eq!(apply_term(&s, fact, &[0]).unwrap(), 1);
        assert_eq!(apply_term(&s, fact, &[1]).unwrap(), 1);
        assert_eq!(apply_term(&s, fact, &[5]).unwrap(), 120);
        assert_eq!(apply_term(&s, fact, &[10]).unwrap(), 3628800);
    }

    #[test]
    fn deep_tail_recursion_does_not_overflow_the_native_stack() {
        // Comfortably past the ~8,000-10,000 levels a plain (non-
        // trampolined) recursive eval() overflows at even in release mode
        // (see this module's own docs) -- if eval's App/If handling ever
        // regresses back to recursing instead of looping on a tail call,
        // this crashes the whole test process (a real stack overflow
        // aborts, it doesn't panic cleanly), not just fails an assertion.
        // The simplest tail-recursive shape, isolating the trampoline
        // itself from any other per-iteration cost.
        let mut s = TermStore::new();
        let h = source(&mut s, "rec f n = if n <= 0 then 0 else f (n - 1)");
        assert_eq!(apply_term(&s, h, &[2_000_000]).unwrap(), 0);
    }

    #[test]
    fn deep_tail_recursion_creating_and_calling_a_fresh_closure_each_iteration_does_not_overflow() {
        // Exercises the trampoline's App/Closure-application path (not
        // just If's own tail branch) at depth.
        let mut s = TermStore::new();
        let h = capturing_closure_loop(&mut s);
        assert_eq!(apply_term(&s, h, &[100_000, 0]).unwrap(), 100_000 * 100_001 / 2);
    }

    #[test]
    fn higher_order_terms_still_work() {
        let mut s = TermStore::new();
        let applied = twice_inc_5(&mut s);
        assert_eq!(apply_term(&s, applied, &[]).unwrap(), 7);
    }

    #[test]
    fn div_by_zero_errors_instead_of_panicking() {
        let mut s = TermStore::new();
        let div = source(&mut s, "1 / 0");
        assert_eq!(apply_term(&s, div, &[]), Err(EvalError::DivByZero));
    }
}
