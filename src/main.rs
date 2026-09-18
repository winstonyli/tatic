use std::time::Instant;

use tatic::eval;
use tatic::jit::JitEngine;
use tatic::term::{Hash, PrimOp, TermStore};

/// `rec f n = if n <= 1 then 1 else n * f(n - 1)`
fn factorial(s: &mut TermStore) -> Hash {
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

/// `rec f n = if n < 2 then n else f(n - 1) + f(n - 2)` (naive, exponential)
fn fib(s: &mut TermStore) -> Hash {
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

/// `rec f a b = if b == 0 then a else f(b, a mod b)` (tail-recursive, 2-ary)
fn gcd(s: &mut TermStore) -> Hash {
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

/// A genuinely higher-order, non-numeric closed term: `(twice inc) 5`, where
/// `twice = \f. \x. f (f x)` and `inc = \y. y + 1`. Outside the compilable
/// fragment entirely -- demonstrates that the JIT degrades gracefully to
/// the interpreter for terms it can't (and shouldn't try to) compile.
fn higher_order_demo(s: &mut TermStore) -> Hash {
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
    s.app2(twice, inc, five)
}

fn main() {
    let mut store = TermStore::new();
    let fact = factorial(&mut store);
    let fibonacci = fib(&mut store);
    let gcd_term = gcd(&mut store);
    let hof = higher_order_demo(&mut store);

    let mut jit = JitEngine::new();

    println!("-- factorial(10) --");
    println!("interpreted: {}", eval::apply_term(&store, fact, &[10]).unwrap());
    println!("jit:         {}", jit.apply(&store, fact, &[10]).unwrap());

    println!("\n-- gcd(270, 192), 2-ary tail recursion --");
    println!("jit: {}", jit.apply(&store, gcd_term, &[270, 192]).unwrap());

    println!("\n-- (twice inc) 5, genuinely higher-order, not JIT-able --");
    println!("jit (falls back to interpreter): {}", jit.apply(&store, hof, &[]).unwrap());

    println!("\n-- fib(30), naive exponential recursion: interpreter vs JIT --");
    let t0 = Instant::now();
    let interp_result = eval::apply_term(&store, fibonacci, &[30]).unwrap();
    let interp_time = t0.elapsed();

    let t1 = Instant::now();
    let jit_result = jit.apply(&store, fibonacci, &[30]).unwrap(); // compiles + verifies + runs
    let jit_time = t1.elapsed();

    println!("interpreted: fib(30) = {interp_result} in {interp_time:?}");
    println!("jit (cold, incl. compile+verify): fib(30) = {jit_result} in {jit_time:?}");

    let t2 = Instant::now();
    let jit_result_2 = jit.apply(&store, fibonacci, &[30]).unwrap(); // cache hit
    let jit_time_2 = t2.elapsed();
    println!("jit (warm, cached compiled form): fib(30) = {jit_result_2} in {jit_time_2:?}");

    println!("\n-- JIT stats -- {:?}", jit.stats);
}
