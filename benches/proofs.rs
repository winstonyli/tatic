//! Cost of building kernel-checked proofs in `proof.rs`: the straight-line
//! case (one `refl`), a single per-call relational (translation-validation)
//! proof, and the one-time universal proof -- plus a direct comparison
//! between N relational proofs and one universal proof, since that
//! crossover is the whole argument for building the universal proof at
//! all (see `proof.rs`'s module docs).

use criterion::{criterion_group, criterion_main, black_box, Criterion};

use tatic::proof::{
    prove_closure_expr, prove_closure_expr_instance, prove_pure_expr, prove_tail_recursive_call, prove_tail_recursive_instance,
    prove_tail_recursive_universal,
};
use tatic::term::TermStore;
use tatic::eval;

#[path = "common.rs"]
mod common;

fn straight_line_proof(c: &mut Criterion) {
    let mut store = TermStore::new();
    let h = common::straight_line(&mut store);
    c.bench_function("straight_line_refl_proof", |b| {
        b.iter(|| prove_pure_expr(&store, black_box(h)).unwrap())
    });
}

fn relational_per_call_proof(c: &mut Criterion) {
    let mut store = TermStore::new();
    let h = common::gcd(&mut store);
    c.bench_function("gcd_relational_proof_single_call", |b| {
        b.iter(|| prove_tail_recursive_call(&store, black_box(h), black_box(&[270, 192])).unwrap())
    });
}

fn universal_proof(c: &mut Criterion) {
    let mut group = c.benchmark_group("universal_proof_one_time_by_leaf_count");

    let mut store2 = TermStore::new();
    let h2 = common::gcd(&mut store2); // 1 base leaf, 1 tail leaf
    group.bench_function("gcd_2_leaves", |b| {
        b.iter(|| prove_tail_recursive_universal(&store2, black_box(h2)).unwrap())
    });

    let mut store3 = TermStore::new();
    let h3 = common::gcd_with_two_base_cases(&mut store3); // 2 base leaves, 1 tail leaf (depth 2)
    group.bench_function("gcd_3_leaves", |b| {
        b.iter(|| prove_tail_recursive_universal(&store3, black_box(h3)).unwrap())
    });

    group.finish();
}

/// The crossover this project's whole "universal vs per-call" argument
/// rests on: N relational proofs (one per sample point `jit.rs` verifies
/// against) versus the single fixed cost of the universal theorem.
fn relational_scaling_vs_universal(c: &mut Criterion) {
    let mut group = c.benchmark_group("gcd_relational_scaling_vs_universal");
    let mut store = TermStore::new();
    let h = common::gcd(&mut store);
    let sample_points: [(i64, i64); 10] = [
        (48, 18),
        (270, 192),
        (17, 5),
        (0, 7),
        (1_000_000_007, 998_244_353),
        (123_456, 789),
        (7, 7),
        (1, 1_000_000),
        (999_983, 999_979),
        (2, 3),
    ];

    for n in [1usize, 5, 10] {
        group.bench_function(format!("relational_x{n}"), |b| {
            b.iter(|| {
                for &(a, bb) in &sample_points[..n] {
                    prove_tail_recursive_call(&store, black_box(h), black_box(&[a, bb])).unwrap();
                }
            })
        });
    }
    group.bench_function("universal_x1", |b| {
        b.iter(|| prove_tail_recursive_universal(&store, black_box(h)).unwrap())
    });

    group.finish();
}

/// Cost of `prove_closure_expr` itself, across the closures fragment's own
/// shapes -- unlike the arithmetic-only groups above, none of these
/// involve `build_universal`'s induction machinery at all (the top-level
/// term must be non-recursive for this fragment), so this isolates
/// `denote_closure`'s own cost: registering/calling a combinator,
/// building an `Env_n` value, and the PAP wrapper postulate, each
/// against the non-capturing baseline (`twice_inc_5`, the same term
/// `main.rs`'s own demo uses).
fn closures_fragment_proof(c: &mut Criterion) {
    let mut group = c.benchmark_group("closures_fragment_proof");

    let mut store = TermStore::new();
    let h = common::twice_inc_5(&mut store);
    group.bench_function("non_capturing", |b| {
        b.iter(|| prove_closure_expr(&store, black_box(h)).unwrap())
    });

    let mut store2 = TermStore::new();
    let h2 = common::a_capturing_closure_call(&mut store2);
    group.bench_function("capturing", |b| {
        b.iter(|| prove_closure_expr(&store2, black_box(h2)).unwrap())
    });

    let mut store3 = TermStore::new();
    let h3 = common::a_pap_non_capturing(&mut store3);
    group.bench_function("partial_application_non_capturing", |b| {
        b.iter(|| prove_closure_expr(&store3, black_box(h3)).unwrap())
    });

    let mut store4 = TermStore::new();
    let h4 = common::a_pap_capturing(&mut store4);
    group.bench_function("partial_application_capturing", |b| {
        b.iter(|| prove_closure_expr(&store4, black_box(h4)).unwrap())
    });

    group.finish();
}

/// `prove_tail_recursive_universal`'s own cost against a closure-typed
/// loop-carried parameter (`iterate`'s shape) -- unlike the group above,
/// this *does* go through `build_universal`'s full induction pipeline
/// (`denote_closure_typed`/`prime_closure_postulates`, not just
/// `denote_closure`), so it belongs alongside `universal_proof`'s own
/// arithmetic-only leaf-count comparison, not the closures-fragment group.
fn closure_typed_recursion_universal_proof(c: &mut Criterion) {
    let mut store = TermStore::new();
    let h = common::iterate(&mut store);
    c.bench_function("closure_typed_loop_carried_parameter_universal_proof", |b| {
        b.iter(|| prove_tail_recursive_universal(&store, black_box(h)).unwrap())
    });
}

/// Cost of `prove_closure_expr_instance`'s non-tail self-recursion path
/// (`eval_dyn`/`eval_dyn_tail_recursive`'s mutual recursion via `self_ctx`,
/// landed alongside `DynBudget`) -- isolated from the tail-only shapes
/// above, and from the closures-fragment group (which never recurses at
/// all). The single-embedded-call and branching cases are kept as
/// separate functions rather than one group, since their costs come from
/// genuinely different sources: `non_tail_embedded_call`'s scales with
/// trace *depth* (bounded by `DynBudget::recursion_depth`'s per-frame
/// cost), `branching`'s with trace *size* (exponential in `n`, bounded by
/// the same budget counting every self-call, not just the live stack
/// depth -- see `common::branching_non_tail_closure_carrying_recursion`'s
/// own doc for why its `n` is kept much smaller).
fn non_tail_closure_recursion_instance_proof(c: &mut Criterion) {
    let mut group = c.benchmark_group("non_tail_closure_recursion_instance_proof");

    let mut store = TermStore::new();
    let h = common::non_tail_closure_carrying_recursion(&mut store);
    group.bench_function("non_tail_embedded_call", |b| {
        b.iter(|| prove_closure_expr_instance(&store, black_box(h), &[]).unwrap())
    });

    let mut store2 = TermStore::new();
    let h2 = common::branching_non_tail_closure_carrying_recursion(&mut store2);
    group.bench_function("branching", |b| {
        b.iter(|| prove_closure_expr_instance(&store2, black_box(h2), &[]).unwrap())
    });

    group.finish();
}

/// Cost of `eval_and_prove_call_over`'s own two over-application shapes
/// (`clo_eq_ref_if_between`/`ite_clo_eq_ref`/`apply_clo_eq_ref`, and
/// `clo_eq_ref_pap`/`apply_pap_eq_ref`), which has no standalone public
/// entry point of its own -- it's only ever reached through a recursive
/// instance proof's own self-call-argument handling
/// (`build_ev_witness`'s per-argument `eval_and_prove` call), so this
/// exercises it the same way any real usage would: a small tail-recursive
/// loop whose self-call argument is, each of 4 iterations, an
/// over-application expression rebuilding the very same `n - 1` a plain
/// `Prim::Sub` would -- deliberately trivial arithmetically (both shapes'
/// own `common::` doc comments explain why), so this measures
/// proof-construction cost, not the cost of the arithmetic it happens to
/// compute.
///
/// `prove_tail_recursive_instance` (the only public entry point) always
/// pays `build_universal`'s own one-time scaffold cost too, not just the
/// per-iteration instance work -- this is *not* a clean isolation of
/// `eval_and_prove_call_over` alone. Comparing against
/// `universal_proof_one_time_by_leaf_count` (a comparably-shaped
/// tail-recursive loop's `build_universal` cost alone, ~10-20ms) puts a
/// number on it: this benchmark's own measured cost (~90-130ms for 4
/// iterations, both shapes) is 5-10x that baseline, so most of it -- not
/// all -- is genuinely attributable to the 4 over-application instances,
/// roughly ~20-30ms each. That per-instance cost is itself a real,
/// somewhat surprising finding (three orders of magnitude past
/// `gcd_relational_proof_single_call`'s own ~24us per-call cost for
/// comparable arithmetic recursion) worth a closer look in its own right
/// -- left as a discovered fact this benchmark documents, not something
/// fixed here.
fn over_application_instance_proof(c: &mut Criterion) {
    let mut group = c.benchmark_group("over_application_instance_proof");

    let mut store = TermStore::new();
    let h = common::tail_recursive_loop_with_if_between_closures_self_call_arg(&mut store);
    assert_eq!(eval::apply_term(&store, h, &[4]).unwrap(), 0, "sanity check against the interpreter");
    group.bench_function("if_between_closures_self_call_arg", |b| {
        b.iter(|| prove_tail_recursive_instance(&store, black_box(h), &[4]).unwrap())
    });

    let mut store2 = TermStore::new();
    let h2 = common::tail_recursive_loop_with_pap_producing_root_self_call_arg(&mut store2);
    assert_eq!(eval::apply_term(&store2, h2, &[4]).unwrap(), 0, "sanity check against the interpreter");
    group.bench_function("pap_producing_root_self_call_arg", |b| {
        b.iter(|| prove_tail_recursive_instance(&store2, black_box(h2), &[4]).unwrap())
    });

    group.finish();
}

criterion_group!(
    benches,
    straight_line_proof,
    relational_per_call_proof,
    universal_proof,
    relational_scaling_vs_universal,
    closures_fragment_proof,
    closure_typed_recursion_universal_proof,
    over_application_instance_proof,
    non_tail_closure_recursion_instance_proof
);
criterion_main!(benches);
