//! The benchmark terms (`benches/common.rs`) plus the IR fixtures, for unit
//! tests that need a realistic corpus. `tests/golden_wat.rs` keeps its own
//! copy of this list because an integration test cannot see `cfg(test)`
//! items.

#[path = "../benches/common.rs"]
mod common;

use crate::term::{Hash, TermStore};

type Builder = fn(&mut TermStore) -> Hash;

pub(crate) fn terms() -> Vec<(&'static str, TermStore, Hash)> {
    let builders: Vec<(&'static str, Builder)> = vec![
        ("factorial", common::factorial),
        ("fib", common::fib),
        ("gcd", common::gcd),
        ("gcd_with_two_base_cases", common::gcd_with_two_base_cases),
        ("capturing_closure_loop", common::capturing_closure_loop),
        ("partial_application_loop", common::partial_application_loop),
        ("closure_typed_loop_carried_parameter_loop", |s| common::closure_typed_loop_carried_parameter_loop(s, 150)),
        ("inconsistent_arity_loop_carried_parameter_loop", |s| common::inconsistent_arity_loop_carried_parameter_loop(s, 150)),
        ("straight_line", common::straight_line),
        ("twice_inc_5", common::twice_inc_5),
        ("a_capturing_closure_call", common::a_capturing_closure_call),
        ("a_pap_non_capturing", common::a_pap_non_capturing),
        ("a_pap_capturing", common::a_pap_capturing),
        ("iterate", common::iterate),
        ("non_tail_closure_carrying_recursion", common::non_tail_closure_carrying_recursion),
        ("branching_non_tail_closure_carrying_recursion", common::branching_non_tail_closure_carrying_recursion),
        ("over_application_if_between_closures", common::over_application_if_between_closures),
        ("over_application_pap_producing_root", common::over_application_pap_producing_root),
        ("tail_recursive_loop_with_if_between_closures_self_call_arg", common::tail_recursive_loop_with_if_between_closures_self_call_arg),
        ("tail_recursive_loop_with_pap_producing_root_self_call_arg", common::tail_recursive_loop_with_pap_producing_root_self_call_arg),
    ];
    let mut out: Vec<(&'static str, TermStore, Hash)> = builders
        .into_iter()
        .map(|(name, build)| {
            let mut s = TermStore::new();
            let h = build(&mut s);
            (name, s, h)
        })
        .collect();
    for (name, fixture) in [
        ("fixture_factorial", crate::ir::fixtures::factorial()),
        ("fixture_twice", crate::ir::fixtures::twice()),
        ("fixture_twice_inc", crate::ir::fixtures::twice_inc()),
    ] {
        let (s, h, _) = fixture;
        out.push((name, s, h));
    }
    out
}
