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
