use std::time::Instant;

use tatic::eval;
use tatic::jit::JitEngine;
use tatic::samples;
use tatic::syntax;
use tatic::term::TermStore;

/// A genuinely *capturing* closure, over-applied: the inner lambdas
/// reference `x`, bound by the *enclosing* function, not their own
/// parameter range. `App(App(inner, 3), 4)` is exactly the same term shape
/// as a plain 2-ary call `inner(3, 4)` (`compile.rs`'s own
/// `unwind_app_spine` can't tell curried application from multi-arg
/// application apart, see its docs), and `inner`'s own arity is 1, not 2
/// -- so this reads as `inner` *over-applied* by one argument. Used to be
/// rejected outright for exactly that reason; `lower_wat.rs`'s
/// "Over-application" docs now cover this shape: `inner`'s saturated call
/// (`inner(3)`) compiles normally, and whatever closure it returns
/// (capturing `x`, allocated fresh) is dispatched on the extra argument
/// through `call_indirect`, the same way calling a closure-typed variable
/// already works.
const OVER_APPLIED_CAPTURING_CLOSURE: &str = r"(\x. if x > 0 then (\y. x + y) else (\y. x - y)) 3 4";

/// The same capturing closure as `OVER_APPLIED_CAPTURING_CLOSURE`, but
/// applied through a call to a closure-typed *parameter* (`g`) instead of
/// by over-application, exercising real closure conversion via the
/// *other* dispatch path (`call_indirect` through a variable rather than
/// through a freshly computed saturated-call result): a fresh
/// heap-allocated environment for whichever inner lambda gets picked,
/// captured `x` included, packed with its table index into one `i64`, and
/// unpacked again at the `call_indirect` inside `g`'s own caller.
const COMPILED_CAPTURING_CLOSURE: &str = r"\x. (\g. g 5) ((\x. if x > 0 then (\y. x + y) else (\y. x - y)) x)";

/// An `If` choosing between two closures, same shape as
/// `COMPILED_CAPTURING_CLOSURE`'s own picker, but *used as a value* (an
/// argument to `caller = \g x. g x`) instead of *directly called*.
/// `denote_closure`'s own `If` case covers two `Clo` branches too
/// (`ite_clo`, postulated lazily), the same way `call_ref` covers a
/// *directly-called* combinator whose own body is such an `If`
/// (`combinator_return_type`, see its docs) -- both dispatch paths get a
/// kernel-checked proof, so the two demos don't contrast on that front;
/// kept side by side to show the two are handled by different machinery
/// (`ite_clo` here, `call_ref`'s own return-type classification there).
const ITE_BETWEEN_CLOSURES_USED_AS_A_VALUE: &str = r"\w. (\g x. g x) (if 0 < w then (\y. y + 1) else (\z. z - 1)) 5";

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn main() {
    let mut store = TermStore::new();
    let fact = samples::factorial(&mut store);
    let fibonacci = samples::fib(&mut store);
    let gcd_term = samples::gcd(&mut store);
    let hof = samples::twice_inc_5(&mut store);
    let sl = samples::straight_line(&mut store);

    let mut jit = JitEngine::new();

    println!("-- syntax.rs: terms are written as source and parsed to De Bruijn terms --");
    println!("jit: factorial(10) = {}", jit.apply(&store, fact, &[10]).unwrap());
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

    let capturing = syntax::parse(&mut store, OVER_APPLIED_CAPTURING_CLOSURE).unwrap();
    println!("\n-- over-applying a literal lambda that returns a capturing closure --");
    println!("interpreted: {}", eval::apply_term(&store, capturing, &[]).unwrap());
    println!("jit:         {}", jit.apply(&store, capturing, &[]).unwrap());
    println!("compiled so far: {}, interpreted so far: {}", jit.stats.compiled, jit.stats.interpreted);
    println!("kernel-checked equivalence proof: {}", jit.is_kernel_verified(capturing));

    let compiled_capturing = syntax::parse(&mut store, COMPILED_CAPTURING_CLOSURE).unwrap();
    println!("\n-- a capturing closure real closure conversion *does* compile --");
    for x in [3, -3] {
        let interp = eval::apply_term(&store, compiled_capturing, &[x]).unwrap();
        let jitted = jit.apply(&store, compiled_capturing, &[x]).unwrap();
        println!("x={x}: interpreted={interp}, jit={jitted}");
    }
    println!("kernel-checked equivalence proof: {}", jit.is_kernel_verified(compiled_capturing));

    let ite_closures = syntax::parse(&mut store, ITE_BETWEEN_CLOSURES_USED_AS_A_VALUE).unwrap();
    println!("\n-- the same If-between-closures shape, but used as a value instead of called --");
    for w in [3, -3] {
        let interp = eval::apply_term(&store, ite_closures, &[w]).unwrap();
        let jitted = jit.apply(&store, ite_closures, &[w]).unwrap();
        println!("w={w}: interpreted={interp}, jit={jitted}");
    }
    println!("kernel-checked equivalence proof: {}", jit.is_kernel_verified(ite_closures));

    let capturing_pap = samples::a_pap_capturing(&mut store);
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
