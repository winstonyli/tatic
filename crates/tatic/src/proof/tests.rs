use super::*;
use crate::jit::compile;
use crate::lang::eval;
use tatic_kernel::Ctx;
use crate::support::samples::{
    a_capturing_closure_call, a_pap_capturing, a_pap_non_capturing, capturing_closure_loop, factorial, fib, gcd,
    gcd_with_two_base_cases, inc, inconsistent_arity_loop_carried_parameter_loop, iterate,
    over_application_pap_producing_root, source, straight_line, twice, twice_inc_5,
};
use crate::testing::test_corpus::{
    a_pap_of_a_capturing_self_recursive_combinator, a_pap_of_a_self_recursive_combinator,
    calls_a_capturing_closure_picked_by_if, inconsistent_arity_capturing_instance, inconsistent_arity_iterate,
    inconsistent_arity_parameter, inconsistent_arity_runtime_chosen_instance, inconsistent_arity_saturating_instance,
    inconsistent_arity_under_applying_instance, iterate_creating_a_closure_over_g, let_bound_factorial_10,
    over_application_if_between_closures_of_params,
};
use crate::lang::term::TermStore;

/// Independently re-typechecks `proof` from scratch (not just
/// trusting the `.ok()?` inside `prove_closure_expr_instance`) --
/// the same discipline `tail_recursive_call_gets_a_per_execution_proof`
/// applies.
fn check_instance_proof(proof: &EquivalenceProof) {
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.proof, &kernel::id(proof.result_ty, proof.denotation, proof.denotation))
        .expect("the recorded per-instance proof should independently re-typecheck");
}


mod basics;
mod gate;
mod per_instance;
mod universal;
mod closures;
