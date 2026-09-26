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
/// bound by the *enclosing* function, not their own parameter range.
/// `App(App(inner, 3), 4)` is exactly the same term shape as a plain
/// 2-ary call `inner(3, 4)` (`compile.rs`'s own `unwind_app_spine` can't
/// tell curried application from multi-arg application apart, see its
/// docs), and `inner`'s own arity is 1, not 2 -- so this reads as
/// `inner` *over-applied* by one argument. Used to be rejected outright
/// for exactly that reason; `lower_wat.rs`'s "Over-application" docs
/// now cover this shape: `inner`'s saturated call (`inner(3)`) compiles
/// normally, and whatever closure it returns (capturing `x`, allocated
/// fresh) is dispatched on the extra argument through `call_indirect`,
/// the same way calling a closure-typed variable already works.
fn over_applied_capturing_closure_demo(s: &mut TermStore) -> Hash {
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

/// `\x. (\g. g 5) (if x > 0 then (\y. x + y) else (\y. x - y))` -- the
/// same capturing closure as `over_applied_capturing_closure_demo`, but
/// applied through a call to a closure-typed *parameter* (`g`) instead of
/// by over-application, exercising real closure conversion via the
/// *other* dispatch path (`call_indirect` through a variable rather than
/// through a freshly computed saturated-call result): a fresh
/// heap-allocated environment for whichever inner lambda gets picked,
/// captured `x` included, packed with its table index into one `i64`,
/// and unpacked again at the `call_indirect` inside `g`'s own caller.
fn compiled_capturing_closure_demo(s: &mut TermStore) -> Hash {
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
    let picker = s.abs(picked);

    let g = s.var(0);
    let five = s.lit(5);
    let call_g = s.app(g, five);
    let calls_its_arg = s.abs(call_g);

    let x2 = s.var(0);
    let chosen = s.app(picker, x2);
    let called = s.app(calls_its_arg, chosen);
    s.abs(called)
}

/// `\w. caller(if 0 < w then inc else dec, 5)` where `inc = \y. y + 1`,
/// `dec = \z. z - 1`, `caller = \g x. g x` -- an `If` choosing between two
/// closures, same shape as `compiled_capturing_closure_demo`'s own
/// `picker`, but *used as a value* (an argument to `caller`) instead of
/// *directly called*. `denote_closure`'s own `If` case covers two `Clo`
/// branches too (`ite_clo`, postulated lazily), the same way `call_ref`
/// now covers a *directly-called* combinator whose own body is such an
/// `If` (`combinator_return_type`, see its docs) -- both dispatch paths
/// get a kernel-checked proof now, so this demo and
/// `compiled_capturing_closure_demo` no longer contrast on that front;
/// kept side by side to show the two are handled by genuinely different
/// machinery (`ite_clo` here, `call_ref`'s own return-type classification
/// there), not because only one of them compiles or proves.
fn ite_between_closures_used_as_a_value_demo(s: &mut TermStore) -> Hash {
    let y = s.var(0);
    let one = s.lit(1);
    let inc_body = s.prim(PrimOp::Add, y, one);
    let inc = s.abs(inc_body);

    let z = s.var(0);
    let one2 = s.lit(1);
    let dec_body = s.prim(PrimOp::Sub, z, one2);
    let dec = s.abs(dec_body);

    let w = s.var(0);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Lt, zero, w);
    let chosen = s.if_(cond, inc, dec);

    let g = s.var(1);
    let x = s.var(0);
    let gx = s.app(g, x);
    let inner_caller = s.abs(gx);
    let caller = s.abs(inner_caller);

    let five = s.lit(5);
    let applied = s.app2(caller, chosen, five);
    s.abs(applied)
}

/// `\z. (\g2. g2 4) ((\x y. x + y + z) 3)` -- partial application of a
/// *capturing* literal lambda (`\x y. x + y + z`, captures `z`, under-
/// applied by one argument), completed through a wrapper the same way any
/// other closure value would be. `lower_wat.rs`'s `Lowering::pap_env` already
/// composed the wrapper's own environment with a copy of the root's;
/// `pap_ref` now mirrors that (a leading `Env_n` parameter when the root
/// captures), so this gets a kernel-checked proof too, not just empirical
/// sample verification.
fn capturing_partial_application_demo(s: &mut TermStore) -> Hash {
    let y = s.var(0);
    let x = s.var(1);
    let z_captured = s.var(2);
    let xy = s.prim(PrimOp::Add, x, y);
    let xyz = s.prim(PrimOp::Add, xy, z_captured);
    let inner = s.abs(xyz);
    let capturing_add = s.abs(inner);

    let three = s.lit(3);
    let partial = s.app(capturing_add, three);

    let g2 = s.var(0);
    let four = s.lit(4);
    let call_g2 = s.app(g2, four);
    let caller = s.abs(call_g2);

    let called = s.app(caller, partial);
    s.abs(called)
}

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

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

    let capturing = over_applied_capturing_closure_demo(&mut store);
    println!("\n-- over-applying a literal lambda that returns a capturing closure --");
    println!("interpreted: {}", eval::apply_term(&store, capturing, &[]).unwrap());
    println!("jit:         {}", jit.apply(&store, capturing, &[]).unwrap());
    println!("compiled so far: {}, interpreted so far: {}", jit.stats.compiled, jit.stats.interpreted);
    println!("kernel-checked equivalence proof: {}", jit.is_kernel_verified(capturing));

    let compiled_capturing = compiled_capturing_closure_demo(&mut store);
    println!("\n-- a capturing closure real closure conversion *does* compile --");
    for x in [3, -3] {
        let interp = eval::apply_term(&store, compiled_capturing, &[x]).unwrap();
        let jitted = jit.apply(&store, compiled_capturing, &[x]).unwrap();
        println!("x={x}: interpreted={interp}, jit={jitted}");
    }
    println!("kernel-checked equivalence proof: {}", jit.is_kernel_verified(compiled_capturing));

    let ite_closures = ite_between_closures_used_as_a_value_demo(&mut store);
    println!("\n-- the same If-between-closures shape, but used as a value instead of called --");
    for w in [3, -3] {
        let interp = eval::apply_term(&store, ite_closures, &[w]).unwrap();
        let jitted = jit.apply(&store, ite_closures, &[w]).unwrap();
        println!("w={w}: interpreted={interp}, jit={jitted}");
    }
    println!("kernel-checked equivalence proof: {}", jit.is_kernel_verified(ite_closures));

    let capturing_pap = capturing_partial_application_demo(&mut store);
    println!("\n-- partial application of a capturing closure --");
    for z in [10, -3] {
        let interp = eval::apply_term(&store, capturing_pap, &[z]).unwrap();
        let jitted = jit.apply(&store, capturing_pap, &[z]).unwrap();
        println!("z={z}: interpreted={interp}, jit={jitted}");
    }
    println!("kernel-checked equivalence proof: {}", jit.is_kernel_verified(capturing_pap));

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
