//! Reference interpreter: defines the semantics every other representation
//! of a term (in particular, JIT-compiled code) is judged equivalent to.

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
    match store.resolve(h) {
        Term::Var(i) => env.get(*i),
        Term::Lit(n) => Ok(Value::Int(*n)),
        Term::Prim(op, a, b) => {
            let a = eval(store, env, *a)?;
            let b = eval(store, env, *b)?;
            let (Value::Int(x), Value::Int(y)) = (a, b) else {
                return Err(EvalError::TypeError);
            };
            apply_prim(*op, x, y)
        }
        Term::If(c, t, e) => {
            let Value::Int(cv) = eval(store, env, *c)? else {
                return Err(EvalError::TypeError);
            };
            if cv != 0 {
                eval(store, env, *t)
            } else {
                eval(store, env, *e)
            }
        }
        Term::Abs(body) => Ok(Value::Closure(env.clone(), *body)),
        Term::Rec(inner) => Ok(Value::Rec(env.clone(), *inner)),
        Term::App(f, a) => {
            let fv = eval(store, env, *f)?;
            let av = eval(store, env, *a)?;
            apply_value(store, fv, av)
        }
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
    match f {
        Value::Closure(env, body) => eval(store, &env.push(arg), body),
        Value::Rec(env, inner) => {
            // Unroll one layer: bind the recursive value itself into scope,
            // then evaluate `inner` (typically an `Abs`, so this just makes
            // a closure) and apply as normal.
            let self_val = Value::Rec(env.clone(), inner);
            let ext = env.push(self_val);
            let fval = eval(store, &ext, inner)?;
            apply_value(store, fval, arg)
        }
        Value::Int(_) => Err(EvalError::NotAFunction),
    }
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
