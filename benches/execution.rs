//! Interpreter vs JIT: how much the compile-once, verify-once, cache
//! discipline in `jit.rs` actually buys over `eval.rs`'s tree-walking
//! interpreter, and what the one-time compile+verify cost looks like
//! relative to a cached call.

use criterion::{criterion_group, criterion_main, black_box, BatchSize, Criterion};

use tatic::eval;
use tatic::jit::JitEngine;
use tatic::term::{Hash, TermStore};

#[path = "common.rs"]
mod common;

/// Warm `jit`'s cache on `h` once, outside the timed loop, and fail the
/// run if what got cached is not the path the group's `jit_warm_cache_hit`
/// bar claims to measure. The installation gate (`RELATED_WORK.md` 29) can
/// turn a compiled term into an interpreted one with nothing here noticing
/// -- the bar keeps reporting a number, just a different one -- which is
/// how `inconsistent_arity_loop_carried_parameter_loop`'s bar changed
/// meaning unseen (`RELATED_WORK.md` 30). Each group states the path it
/// expects, so a change to the gate or a proof budget breaks the run
/// instead.
fn warm(jit: &mut JitEngine, store: &TermStore, h: Hash, args: &[i64], expect_compiled: bool) {
    jit.apply(store, h, args).unwrap();
    assert_eq!(
        jit.stats.compiled == 1,
        expect_compiled,
        "the cached path is not the one this group's jit_warm_cache_hit bar measures: {:?}",
        jit.stats
    );
}

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
    warm(&mut jit, &store, h, &[30], true);
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
    warm(&mut jit, &store, h, &args, true);
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
    warm(&mut jit, &store, h, &[10], true);
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
    warm(&mut jit, &store, h, &args, true);
    group.bench_function("jit_warm_cache_hit", |b| {
        b.iter(|| jit.apply(&store, h, black_box(&args)).unwrap())
    });

    group.finish();
}

fn closure_typed_loop_carried_parameter_loop(c: &mut Criterion) {
    let mut group = c.benchmark_group("closure_typed_loop_carried_parameter_loop");

    let mut store = TermStore::new();
    let h = common::closure_typed_loop_carried_parameter_loop(&mut store, 20_000);
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
                let h = common::closure_typed_loop_carried_parameter_loop(&mut store, 20_000);
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
    warm(&mut jit, &store, h, &args, true);
    group.bench_function("jit_warm_cache_hit", |b| {
        b.iter(|| jit.apply(&store, h, black_box(&args)).unwrap())
    });

    group.finish();
}

/// Isolates the cost of `compile.rs`'s curried-dispatch fallback
/// (`emit_curried_stages`/`emit_dynamic_apply`, see `RELATED_WORK.md`
/// §9's own "since implemented" note): the same loop, the same hot
/// `g(x)` call each iteration, as `closure_typed_loop_carried_parameter_loop`,
/// except one syntactically-present-but-dead call site elsewhere in the
/// same function makes `g` `ArityUse::Inconsistent`, which switches the
/// *whole* fragment (not just the dead call) to the curried,
/// one-argument-at-a-time convention -- see
/// `common::inconsistent_arity_loop_carried_parameter_loop`'s own docs.
/// `jit_warm_cache_hit` against `consistent_baseline_jit_warm_cache_hit`
/// is the number that matters: everything else about the two terms is
/// identical, so the difference *is* the curried-dispatch overhead on an
/// otherwise-fast-path-eligible hot loop, isolated from compile time
/// (which `jit_cold_compile_and_verify` captures separately, and which the
/// two-pass discovery/emit restructuring itself makes a fixed,
/// per-compile cost, not a per-call one).
///
/// Why `PAIR_ITERS` rather than the other loop groups' 20,000: no
/// universal strategy covers an inconsistently-called closure
/// (`param_types_for` declines it), so the only proof is
/// `prove_closure_expr_instance`'s per-execution trace -- `Universal`
/// here because the term is closed (arity 0), but one trace step per
/// iteration against a 200-step budget. At 20,000 the budget runs out,
/// the installation gate (`RELATED_WORK.md` 29) declines, and every bar
/// measured the interpreter (`RELATED_WORK.md` 30). The baseline is
/// benched at the same length, in this same group, so the pair stays
/// comparable; the companion group keeps 20,000 for its own comparison
/// with `capturing_closure_loop`.
fn inconsistent_arity_loop_carried_parameter_loop(c: &mut Criterion) {
    /// Measured ceiling on this machine: 199 installs, 200 is declined.
    /// 150 keeps margin under the budget while the loop still dominates
    /// the warm call: fixed per-call overhead is ~220 ns (a 1-iteration
    /// loop), the baseline ~730 ns. `warm` fails the run if either side
    /// stops installing.
    const PAIR_ITERS: i64 = 150;

    let mut group = c.benchmark_group("inconsistent_arity_loop_carried_parameter_loop");

    let mut store = TermStore::new();
    let h = common::inconsistent_arity_loop_carried_parameter_loop(&mut store, PAIR_ITERS);
    let args: [i64; 0] = [];

    group.sample_size(20);
    group.bench_function("interpreter", |b| {
        b.iter(|| eval::apply_term(&store, h, black_box(&args)).unwrap())
    });

    group.bench_function("jit_cold_compile_and_verify", |b| {
        b.iter_batched(
            || {
                let mut store = TermStore::new();
                let h = common::inconsistent_arity_loop_carried_parameter_loop(&mut store, PAIR_ITERS);
                (store, h, JitEngine::new())
            },
            |(store, h, mut jit)| jit.apply(&store, h, black_box(&args)).unwrap(),
            BatchSize::PerIteration,
        )
    });

    let mut jit = JitEngine::new();
    warm(&mut jit, &store, h, &args, true);
    group.bench_function("jit_warm_cache_hit", |b| {
        b.iter(|| jit.apply(&store, h, black_box(&args)).unwrap())
    });

    let mut base_store = TermStore::new();
    let base = common::closure_typed_loop_carried_parameter_loop(&mut base_store, PAIR_ITERS);
    let mut base_jit = JitEngine::new();
    warm(&mut base_jit, &base_store, base, &args, true);
    group.bench_function("consistent_baseline_jit_warm_cache_hit", |b| {
        b.iter(|| base_jit.apply(&base_store, base, black_box(&args)).unwrap())
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
    warm(&mut jit, &store, h, &args, true);
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
