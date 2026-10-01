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
