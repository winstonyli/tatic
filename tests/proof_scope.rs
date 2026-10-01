// Does an `InternScope` held across building and re-checking a real `proof.rs` proof help? Timing only
// (design doc section 71): the proofs are small, so this is about overhead, not scale.
use std::time::Instant;
use tatic::kernel::{self, Ctx, InternScope};
use tatic::proof::prove_tail_recursive_universal;
use tatic::term::TermStore;

#[path = "../benches/common.rs"]
mod common;

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

/// Build and re-check the gcd universal proof `reps` times; (build, check) totals.
fn run(scoped: bool, two_base: bool, reps: u32) -> (std::time::Duration, std::time::Duration) {
    let mut s = TermStore::new();
    let h = if two_base { common::gcd_with_two_base_cases(&mut s) } else { common::gcd(&mut s) };
    let (mut build, mut check) = (std::time::Duration::ZERO, std::time::Duration::ZERO);
    for _ in 0..reps {
        let _scope = scoped.then(InternScope::enter);
        let t0 = Instant::now();
        let proof = prove_tail_recursive_universal(&s, h).expect("universal proof");
        build += t0.elapsed();
        let t1 = Instant::now();
        kernel::check_in(&proof.globals, &Ctx::new(), &proof.theorem_proof, &proof.theorem_ty).expect("re-check");
        check += t1.elapsed();
    }
    (build, check)
}

#[test]
#[ignore]
fn universal_proof_with_and_without_a_scope() {
    for two_base in [false, true] {
        for round in 0..3 {
            for scoped in [false, true] {
                let (b, c) = run(scoped, two_base, 200);
                println!(
                    "REAL-PROOF gcd{} round {round} scoped={scoped}: build {:.3} ms, check {:.3} ms per proof",
                    if two_base { "_3_leaves" } else { "_2_leaves" },
                    b.as_secs_f64() * 5.0,
                    c.as_secs_f64() * 5.0
                );
            }
        }
    }
}

/// How much a real proof repeats itself: distinct allocations against occurrences, unscoped and
/// built inside an `InternScope` (design doc section 80). A large ratio is what makes the scope pay.
#[test]
#[ignore]
fn real_proofs_dag_against_tree_size() {
    type Build = fn(&mut TermStore) -> tatic::term::Hash;
    let programs: [(&str, Build); 4] = [
        ("factorial", common::factorial),
        ("fib", common::fib),
        ("gcd", common::gcd),
        ("gcd_3_leaves", common::gcd_with_two_base_cases),
    ];
    for (name, build) in programs {
        let mut s = TermStore::new();
        let h = build(&mut s);
        let sizes = |scoped: bool| {
            let _scope = scoped.then(InternScope::enter);
            prove_tail_recursive_universal(&s, h).map(|p| kernel::term_sizes(&p.theorem_proof))
        };
        match (sizes(false), sizes(true)) {
            (Some((d0, t0)), Some((d1, _))) => {
                println!("REAL-SHARING {name}: tree {t0} nodes, distinct unscoped {d0} ({:.1}x), scoped {d1} ({:.1}x)", t0 as f64 / d0 as f64, t0 as f64 / d1 as f64)
            }
            _ => println!("REAL-SHARING {name}: no universal proof"),
        }
    }
}
