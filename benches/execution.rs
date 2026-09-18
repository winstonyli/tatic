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

criterion_group!(benches, fib_30, gcd_large, factorial_10);
criterion_main!(benches);
