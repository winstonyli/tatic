//! Interpreter vs JIT: how much the compile-once, verify-once, cache
//! discipline in `jit.rs` actually buys over `eval.rs`'s tree-walking
//! interpreter, and what the one-time compile+verify cost looks like
//! relative to a cached call.

use criterion::{criterion_group, criterion_main, black_box, BatchSize, Criterion};

use tatic::eval;
use tatic::jit::JitEngine;
use tatic::term::TermStore;

#[path = "common.rs"]
mod common;

fn fib_30(c: &mut Criterion) {
    let mut group = c.benchmark_group("fib_30_non_tail_recursion");

    let mut store = TermStore::new();
    let h = common::fib(&mut store);

    // Naive exponential fib(30) is ~700ms interpreted -- a handful of
    // samples is enough to see the shape without an unreasonably slow run.
    group.sample_size(10);
    group.bench_function("interpreter", |b| {
        b.iter(|| eval::apply_term(&store, h, black_box(&[30])).unwrap())
    });

    group.sample_size(100);
    group.bench_function("jit_cold_compile_and_verify", |b| {
        b.iter_batched(
            || {
                let mut store = TermStore::new();
                let h = common::fib(&mut store);
                (store, h, JitEngine::new())
            },
            |(store, h, mut jit)| jit.apply(&store, h, black_box(&[30])).unwrap(),
            BatchSize::SmallInput,
        )
    });

    let mut jit = JitEngine::new();
    jit.apply(&store, h, &[30]).unwrap(); // warm the cache once, outside the timed loop
    group.bench_function("jit_warm_cache_hit", |b| {
        b.iter(|| jit.apply(&store, h, black_box(&[30])).unwrap())
    });

    group.finish();
}

fn gcd_large(c: &mut Criterion) {
    let mut group = c.benchmark_group("gcd_tail_recursion_to_loop");

    let mut store = TermStore::new();
    let h = common::gcd(&mut store);
    let args: [i64; 2] = [1_000_000_007, 998_244_353]; // large coprime pair, many Euclidean steps

    group.bench_function("interpreter", |b| {
        b.iter(|| eval::apply_term(&store, h, black_box(&args)).unwrap())
    });

    group.bench_function("jit_cold_compile_and_verify", |b| {
        b.iter_batched(
            || {
                let mut store = TermStore::new();
                let h = common::gcd(&mut store);
                (store, h, JitEngine::new())
            },
            |(store, h, mut jit)| jit.apply(&store, h, black_box(&args)).unwrap(),
            BatchSize::SmallInput,
        )
    });

    let mut jit = JitEngine::new();
    jit.apply(&store, h, &args).unwrap();
    group.bench_function("jit_warm_cache_hit", |b| {
        b.iter(|| jit.apply(&store, h, black_box(&args)).unwrap())
    });

    group.finish();
}

fn factorial_10(c: &mut Criterion) {
    let mut group = c.benchmark_group("factorial_10");

    let mut store = TermStore::new();
    let h = common::factorial(&mut store);

    group.bench_function("interpreter", |b| {
        b.iter(|| eval::apply_term(&store, h, black_box(&[10])).unwrap())
    });

    let mut jit = JitEngine::new();
    jit.apply(&store, h, &[10]).unwrap();
    group.bench_function("jit_warm_cache_hit", |b| {
        b.iter(|| jit.apply(&store, h, black_box(&[10])).unwrap())
    });

    group.finish();
}

fn capturing_closure_loop(c: &mut Criterion) {
    let mut group = c.benchmark_group("capturing_closure_loop");

    let mut store = TermStore::new();
    let h = common::capturing_closure_loop(&mut store);
    // creates+calls 20,000 fresh capturing closures -- eval.rs's own App/If
    // handling is trampolined (see its own module docs) precisely so a
    // depth like this, or much deeper, never risks the native stack; this
    // round number is just enough to make steady-state cost dominate over
    // fixed per-call overhead, not a ceiling.
    let args: [i64; 2] = [20_000, 0];

    group.sample_size(20);
    group.bench_function("interpreter", |b| {
        b.iter(|| eval::apply_term(&store, h, black_box(&args)).unwrap())
    });

    group.bench_function("jit_cold_compile_and_verify", |b| {
        b.iter_batched(
            || {
                let mut store = TermStore::new();
                let h = common::capturing_closure_loop(&mut store);
                (store, h, JitEngine::new())
            },
            |(store, h, mut jit)| jit.apply(&store, h, black_box(&args)).unwrap(),
            // Unlike fib_30/gcd_large's cold-compile groups, this one's
            // per-iteration cost is low enough (~2ms) that `SmallInput`
            // batches many full `(TermStore, JitEngine)` setups -- each
            // holding its own `wasmtime::Engine` -- alive simultaneously,
            // ballooning memory. `PerIteration` keeps exactly one alive at
            // a time regardless of how fast the operation is.
            BatchSize::PerIteration,
        )
    });

    let mut jit = JitEngine::new();
    jit.apply(&store, h, &args).unwrap();
    group.bench_function("jit_warm_cache_hit", |b| {
        b.iter(|| jit.apply(&store, h, black_box(&args)).unwrap())
    });

    group.finish();
}

fn closure_typed_loop_carried_parameter_loop(c: &mut Criterion) {
    let mut group = c.benchmark_group("closure_typed_loop_carried_parameter_loop");

    let mut store = TermStore::new();
    let h = common::closure_typed_loop_carried_parameter_loop(&mut store);
    // The term itself is closed (n, g, x all baked in), so every call
    // passes no arguments.
    let args: [i64; 0] = [];

    group.sample_size(20);
    group.bench_function("interpreter", |b| {
        b.iter(|| eval::apply_term(&store, h, black_box(&args)).unwrap())
    });

    group.bench_function("jit_cold_compile_and_verify", |b| {
        b.iter_batched(
            || {
                let mut store = TermStore::new();
                let h = common::closure_typed_loop_carried_parameter_loop(&mut store);
                (store, h, JitEngine::new())
            },
            |(store, h, mut jit)| jit.apply(&store, h, black_box(&args)).unwrap(),
            // See capturing_closure_loop's own comment: this group's
            // per-iteration cost is low enough that SmallInput would
            // otherwise keep many full (TermStore, JitEngine) setups
            // alive simultaneously.
            BatchSize::PerIteration,
        )
    });

    let mut jit = JitEngine::new();
    jit.apply(&store, h, &args).unwrap();
    group.bench_function("jit_warm_cache_hit", |b| {
        b.iter(|| jit.apply(&store, h, black_box(&args)).unwrap())
    });

    group.finish();
}

/// Isolates the cost of `compile.rs`'s curried-dispatch fallback
/// (`emit_curried_stages`/`emit_dynamic_apply`, see `RELATED_WORK.md`
/// §9's own "since implemented" note): the same loop, the same 20,000
/// iterations, the same hot `g(x)` call each one, as
/// `closure_typed_loop_carried_parameter_loop` just above, except one
/// syntactically-present-but-dead call site elsewhere in the same
/// function makes `g` `ArityUse::Inconsistent`, which switches the
/// *whole* fragment (not just the dead call) to the curried,
/// one-argument-at-a-time convention -- see
/// `common::inconsistent_arity_loop_carried_parameter_loop`'s own docs.
/// Both groups' `jit_warm_cache_hit` bar is the number that actually
/// matters here: everything else about the two terms is identical, so
/// the difference between them *is* the curried-dispatch overhead on an
/// otherwise-fast-path-eligible hot loop, isolated from compile time
/// (which the `jit_cold_compile_and_verify` bars below capture
/// separately, and which the two-pass discovery/emit restructuring
/// itself makes a fixed, per-compile cost, not a per-call one).
fn inconsistent_arity_loop_carried_parameter_loop(c: &mut Criterion) {
    let mut group = c.benchmark_group("inconsistent_arity_loop_carried_parameter_loop");

    let mut store = TermStore::new();
    let h = common::inconsistent_arity_loop_carried_parameter_loop(&mut store);
    let args: [i64; 0] = [];

    group.sample_size(20);
    group.bench_function("interpreter", |b| {
        b.iter(|| eval::apply_term(&store, h, black_box(&args)).unwrap())
    });

    group.bench_function("jit_cold_compile_and_verify", |b| {
        b.iter_batched(
            || {
                let mut store = TermStore::new();
                let h = common::inconsistent_arity_loop_carried_parameter_loop(&mut store);
                (store, h, JitEngine::new())
            },
            |(store, h, mut jit)| jit.apply(&store, h, black_box(&args)).unwrap(),
            BatchSize::PerIteration,
        )
    });

    let mut jit = JitEngine::new();
    jit.apply(&store, h, &args).unwrap();
    group.bench_function("jit_warm_cache_hit", |b| {
        b.iter(|| jit.apply(&store, h, black_box(&args)).unwrap())
    });

    group.finish();
}

fn partial_application_loop(c: &mut Criterion) {
    let mut group = c.benchmark_group("partial_application_loop");

    let mut store = TermStore::new();
    let h = common::partial_application_loop(&mut store);
    // Same depth as capturing_closure_loop, for the same reason -- see its
    // own comment above.
    let args: [i64; 2] = [20_000, 0];

    group.sample_size(20);
    group.bench_function("interpreter", |b| {
        b.iter(|| eval::apply_term(&store, h, black_box(&args)).unwrap())
    });

    group.bench_function("jit_cold_compile_and_verify", |b| {
        b.iter_batched(
            || {
                let mut store = TermStore::new();
                let h = common::partial_application_loop(&mut store);
                (store, h, JitEngine::new())
            },
            |(store, h, mut jit)| jit.apply(&store, h, black_box(&args)).unwrap(),
            // See capturing_closure_loop's own comment: this group's
            // per-iteration cost is low enough that SmallInput would
            // otherwise keep many full (TermStore, JitEngine) setups
            // alive simultaneously.
            BatchSize::PerIteration,
        )
    });

    let mut jit = JitEngine::new();
    jit.apply(&store, h, &args).unwrap();
    group.bench_function("jit_warm_cache_hit", |b| {
        b.iter(|| jit.apply(&store, h, black_box(&args)).unwrap())
    });

    group.finish();
}

criterion_group!(
    benches,
    fib_30,
    gcd_large,
    factorial_10,
    capturing_closure_loop,
    partial_application_loop,
    closure_typed_loop_carried_parameter_loop,
    inconsistent_arity_loop_carried_parameter_loop
);
criterion_main!(benches);
