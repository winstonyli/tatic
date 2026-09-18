use std::time::Instant;

use tatic::eval;
use tatic::jit::JitEngine;
use tatic::syntax;
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

/// `\a b. if a < b then a * 2 else b + 1` -- straight-line, no recursion,
/// so `proof.rs` can build a kernel-checked equivalence proof for it (see
/// `proof.rs` docs for why the recursive examples above can't get one yet).
fn straight_line(s: &mut TermStore) -> Hash {
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

/// A higher-order, non-numeric closed term: `(twice inc) 5`, where
/// `twice = \f. \x. f (f x)` and `inc = \y. y + 1`. Both `twice` and `inc`
/// are non-capturing ("known") lambdas, so `compile.rs` compiles this: each
/// becomes its own Wasm function, `inc` referenced from `twice`'s body
/// through a shared function table (`call_indirect`).
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

/// A genuinely *capturing* closure: `(\x. if x > 0 then (\y. x + y) else
/// (\y. x - y)) 3`, then applied to `4`. The inner lambdas reference `x`,
/// bound by the *enclosing* function, not their own parameter range --
/// still outside `compile.rs`'s fragment (see its module docs), so this
/// demonstrates the JIT degrading gracefully to the interpreter for a term
/// it can't (and shouldn't try to) compile.
fn capturing_closure_demo(s: &mut TermStore) -> Hash {
    let x1 = s.var(0);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Lt, zero, x1);
    let y_pos = s.var(0);
    let x_pos = s.var(1);
    let plus = s.prim(PrimOp::Add, x_pos, y_pos);
    let then_closure = s.abs(plus);
    let y_neg = s.var(0);
    let x_neg = s.var(1);
    let minus = s.prim(PrimOp::Sub, x_neg, y_neg);
    let else_closure = s.abs(minus);
    let picked = s.if_(cond, then_closure, else_closure);
    let inner = s.abs(picked);
    let three = s.lit(3);
    let picked_closure = s.app(inner, three);
    let four = s.lit(4);
    s.app(picked_closure, four)
}

fn main() {
    let mut store = TermStore::new();
    let fact = factorial(&mut store);
    let fibonacci = fib(&mut store);
    let gcd_term = gcd(&mut store);
    let hof = higher_order_demo(&mut store);
    let sl = straight_line(&mut store);

    let mut jit = JitEngine::new();

    println!("-- syntax.rs: parsing a real source string instead of hand-building De Bruijn terms --");
    let parsed_fact = syntax::parse(&mut store, "rec f n = if n <= 1 then 1 else n * f (n - 1)")
        .expect("valid source should parse");
    println!("parsed factorial == hand-built factorial (same content hash): {}", parsed_fact == fact);
    println!("jit: factorial(10) = {}", jit.apply(&store, parsed_fact, &[10]).unwrap());
    match syntax::parse(&mut store, "n + 1") {
        Ok(_) => unreachable!(),
        Err(e) => println!("parse error on `n + 1` (n unbound): {e}"),
    }
    println!("pretty-printed gcd: {}", syntax::print(&store, gcd_term));

    println!("\n-- factorial(10) --");
    println!("interpreted: {}", eval::apply_term(&store, fact, &[10]).unwrap());
    println!("jit:         {}", jit.apply(&store, fact, &[10]).unwrap());
    println!("kernel-checked equivalence proof: {}", jit.is_kernel_verified(fact));

    println!("\n-- gcd(270, 192), 2-ary tail recursion --");
    println!("jit: {}", jit.apply(&store, gcd_term, &[270, 192]).unwrap());
    println!("kernel-checked equivalence proof: {}", jit.is_kernel_verified(gcd_term));

    println!("\n-- straight_line(3, 5), no recursion --");
    println!("jit: {}", jit.apply(&store, sl, &[3, 5]).unwrap());
    println!(
        "kernel-checked equivalence proof: {} (sample verification alone gates trust either way; see proof.rs)",
        jit.is_kernel_verified(sl)
    );

    println!("\n-- (twice inc) 5, non-capturing closures via a shared function table --");
    println!("interpreted: {}", eval::apply_term(&store, hof, &[]).unwrap());
    println!("jit:         {}", jit.apply(&store, hof, &[]).unwrap());
    println!("compiled so far: {}, interpreted so far: {}", jit.stats.compiled, jit.stats.interpreted);
    println!("kernel-checked equivalence proof: {}", jit.is_kernel_verified(hof));

    let capturing = capturing_closure_demo(&mut store);
    println!("\n-- capturing closure, still out of compile.rs's fragment --");
    println!("interpreted: {}", eval::apply_term(&store, capturing, &[]).unwrap());
    println!("jit (falls back to interpreter): {}", jit.apply(&store, capturing, &[]).unwrap());

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
