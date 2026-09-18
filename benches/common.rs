//! Term builders shared by the benchmarks -- the same terms `main.rs` uses
//! for its demo, kept in one place so `execution.rs` and `proofs.rs` don't
//! each carry their own copy.
//!
//! Included into both bench binaries via `#[path]`; each one only uses a
//! subset, hence the blanket `dead_code` allow rather than one per binary.
#![allow(dead_code)]

use tatic::term::{Hash, PrimOp, TermStore};

/// `rec f n = if n <= 1 then 1 else n * f(n - 1)`
pub fn factorial(s: &mut TermStore) -> Hash {
    let n = s.var(0);
    let f = s.var(1);
    let one = s.lit(1);
    let cond = s.prim(PrimOp::Le, n, one);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one);
    let rec_call = s.app(f, n_minus_1);
    let else_branch = s.prim(PrimOp::Mul, n, rec_call);
    let body = s.if_(cond, one, else_branch);
    let abs = s.abs(body);
    s.rec(abs)
}

/// `rec f n = if n < 2 then n else f(n - 1) + f(n - 2)` (naive, exponential;
/// not tail-recursive, so `compile.rs` emits a plain `call`, not a loop).
pub fn fib(s: &mut TermStore) -> Hash {
    let n = s.var(0);
    let f = s.var(1);
    let two = s.lit(2);
    let cond = s.prim(PrimOp::Lt, n, two);
    let one = s.lit(1);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one);
    let n_minus_2 = s.prim(PrimOp::Sub, n, two);
    let call1 = s.app(f, n_minus_1);
    let call2 = s.app(f, n_minus_2);
    let else_branch = s.prim(PrimOp::Add, call1, call2);
    let body = s.if_(cond, n, else_branch);
    let abs = s.abs(body);
    s.rec(abs)
}

/// `rec f a b = if b == 0 then a else f(b, a mod b)` (tail-recursive, 2-ary
/// -- `compile.rs` turns the self-call into a `loop`/`br`).
pub fn gcd(s: &mut TermStore) -> Hash {
    let b = s.var(0);
    let a = s.var(1);
    let f = s.var(2);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Eq, b, zero);
    let a_mod_b = s.prim(PrimOp::Mod, a, b);
    let rec_call = s.app2(f, b, a_mod_b);
    let body = s.if_(cond, a, rec_call);
    let inner = s.abs(body);
    let abs = s.abs(inner);
    s.rec(abs)
}

/// `rec f a b = if a == 0 then b else if b == 0 then a else f(b, a mod b)`
/// -- deeper than `gcd` above: two base leaves and one tail leaf reached
/// via a depth-2 path, exercising `prove_tail_recursive_universal`'s
/// per-leaf `Ev` construction instead of the single-base/single-tail
/// special case.
pub fn gcd_with_two_base_cases(s: &mut TermStore) -> Hash {
    let b = s.var(0);
    let a = s.var(1);
    let f = s.var(2);
    let zero = s.lit(0);
    let cond_a = s.prim(PrimOp::Eq, a, zero);
    let cond_b = s.prim(PrimOp::Eq, b, zero);
    let a_mod_b = s.prim(PrimOp::Mod, a, b);
    let rec_call = s.app2(f, b, a_mod_b);
    let inner_if = s.if_(cond_b, a, rec_call);
    let body = s.if_(cond_a, b, inner_if);
    let inner = s.abs(body);
    let abs = s.abs(inner);
    s.rec(abs)
}

/// `rec f n acc = if n <= 0 then acc else f (n - 1) ((\y. acc + y) n)` --
/// tail-recursive, but each iteration creates *and immediately calls* a
/// fresh capturing closure (`\y. acc + y`, capturing `acc`, `f`'s own
/// second parameter, which changes every iteration) as a literal callee
/// -- a direct-call site (`push_closure_env` then `call`, no
/// `call_indirect`), so this isolates the cost of `compile.rs`'s new
/// closure-conversion path -- one bump-allocator call per iteration --
/// from `call_indirect`'s own unpacking overhead.
pub fn capturing_closure_loop(s: &mut TermStore) -> Hash {
    // `\y. acc + y`, referenced at body's own top level (f=Var(2),
    // n=Var(1), acc=Var(0)) -- inside the closure's own body, one more
    // binder (y) has been passed, so acc is Var(1), y is Var(0).
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
    s.rec(abs)
}

/// `\a b. if a < b then a * 2 else b + 1` -- straight-line, no recursion.
pub fn straight_line(s: &mut TermStore) -> Hash {
    let a = s.var(1);
    let b = s.var(0);
    let cond = s.prim(PrimOp::Lt, a, b);
    let two = s.lit(2);
    let then_branch = s.prim(PrimOp::Mul, a, two);
    let one = s.lit(1);
    let else_branch = s.prim(PrimOp::Add, b, one);
    let body = s.if_(cond, then_branch, else_branch);
    let inner = s.abs(body);
    s.abs(inner)
}
