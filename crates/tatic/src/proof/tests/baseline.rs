//! The v0.8 baseline fixture: one row per census term (doc 15, "v0.7's first steps: the census and the
//! emit spike"), measured at `eba0891` behaviour. Later tasks compare the branch against it.
use super::*;
use crate::jit::{shape, JitEngine};
use crate::lang::term::Hash;
use crate::support::samples::corpus;
use crate::testing::test_corpus as tc;

/// What one census term does through the real pipeline.
#[derive(Debug, PartialEq, Eq)]
pub(super) struct BaseRow {
    pub(super) name: &'static str,
    pub(super) installs: bool,
    pub(super) compiled: u64,
    pub(super) specialised: u64,
    pub(super) tree: u64,
}

/// Rows whose `installs` may go from false to true and never back (Goal 5's one exception); for these,
/// when `installs` changed, `compiled` and `specialised` are not compared.
pub(super) const HELD_OUT: &[&str] = &[];

/// Census 1-23 (`samples::corpus`) then 24-38 (`test_corpus`), in the census list's order.
pub(super) fn census() -> Vec<(&'static str, TermStore, Hash)> {
    let mut v = corpus();
    let builders: [(&'static str, fn(&mut TermStore) -> Hash); 15] = [
        ("open_redex_probe", tc::open_redex_probe),
        ("oversized_source_with_a_shrinking_step", tc::oversized_source_with_a_shrinking_step),
        ("doubling_d4", |s| tc::doubling(s, 4)),
        ("inconsistent_arity_parameter", tc::inconsistent_arity_parameter),
        ("inconsistent_arity_saturating_instance", tc::inconsistent_arity_saturating_instance),
        ("inconsistent_arity_under_applying_instance", tc::inconsistent_arity_under_applying_instance),
        ("inconsistent_arity_capturing_instance", tc::inconsistent_arity_capturing_instance),
        ("inconsistent_arity_runtime_chosen_instance", tc::inconsistent_arity_runtime_chosen_instance),
        ("inconsistent_arity_iterate", tc::inconsistent_arity_iterate),
        ("iterate_creating_a_closure_over_g", tc::iterate_creating_a_closure_over_g),
        ("let_bound_factorial_10", tc::let_bound_factorial_10),
        ("calls_a_capturing_closure_picked_by_if", tc::calls_a_capturing_closure_picked_by_if),
        ("a_pap_of_a_self_recursive_combinator", tc::a_pap_of_a_self_recursive_combinator),
        ("a_pap_of_a_capturing_self_recursive_combinator", tc::a_pap_of_a_capturing_self_recursive_combinator),
        ("over_application_if_between_closures_of_params", tc::over_application_if_between_closures_of_params),
    ];
    for (name, build) in builders {
        let mut s = TermStore::new();
        let h = build(&mut s);
        v.push((name, s, h));
    }
    v
}

fn measure(name: &'static str, s: &TermStore, h: Hash) -> BaseRow {
    let arity = shape::peel(s, h).map(|p| p.0).unwrap_or(0);
    let mut jit = JitEngine::new();
    let _ = jit.apply(s, h, &vec![5; arity]);
    let tree = match compile::compile_specialised(s, h) {
        Some(c) => match &c.specialised {
            Some((ss, t)) => compile::tree_size(ss, *t),
            None => compile::tree_size(s, h),
        },
        None => compile::tree_size(s, h),
    };
    BaseRow { name, installs: jit.stats.compiled == 1, compiled: jit.stats.compiled, specialised: jit.stats.specialised, tree }
}

const BASELINE: &[BaseRow] = &[
    BaseRow { name: "factorial", installs: true, compiled: 1, specialised: 0, tree: 14 },
    BaseRow { name: "redundant_arithmetic_recursion", installs: true, compiled: 1, specialised: 0, tree: 18 },
    BaseRow { name: "fib", installs: true, compiled: 1, specialised: 0, tree: 18 },
    BaseRow { name: "gcd", installs: true, compiled: 1, specialised: 0, tree: 15 },
    BaseRow { name: "gcd_with_two_base_cases", installs: true, compiled: 1, specialised: 0, tree: 20 },
    BaseRow { name: "capturing_closure_loop", installs: true, compiled: 1, specialised: 1, tree: 17 },
    BaseRow { name: "partial_application_loop", installs: true, compiled: 1, specialised: 1, tree: 17 },
    BaseRow { name: "closure_typed_loop_carried_parameter_loop", installs: true, compiled: 1, specialised: 0, tree: 29 },
    BaseRow { name: "inconsistent_arity_loop_carried_parameter_loop", installs: true, compiled: 1, specialised: 0, tree: 38 },
    BaseRow { name: "straight_line", installs: true, compiled: 1, specialised: 0, tree: 12 },
    BaseRow { name: "twice", installs: false, compiled: 0, specialised: 0, tree: 7 },
    BaseRow { name: "inc", installs: true, compiled: 1, specialised: 0, tree: 4 },
    BaseRow { name: "twice_inc_5", installs: true, compiled: 1, specialised: 1, tree: 8 },
    BaseRow { name: "a_capturing_closure_call", installs: true, compiled: 1, specialised: 1, tree: 4 },
    BaseRow { name: "a_pap_non_capturing", installs: true, compiled: 1, specialised: 1, tree: 3 },
    BaseRow { name: "a_pap_capturing", installs: true, compiled: 1, specialised: 1, tree: 6 },
    BaseRow { name: "iterate", installs: false, compiled: 0, specialised: 0, tree: 20 },
    BaseRow { name: "non_tail_closure_carrying_recursion", installs: true, compiled: 1, specialised: 0, tree: 31 },
    BaseRow { name: "branching_non_tail_closure_carrying_recursion", installs: true, compiled: 1, specialised: 0, tree: 32 },
    BaseRow { name: "over_application_if_between_closures", installs: true, compiled: 1, specialised: 0, tree: 24 },
    BaseRow { name: "over_application_pap_producing_root", installs: true, compiled: 1, specialised: 1, tree: 5 },
    BaseRow { name: "tail_recursive_loop_with_if_between_closures_self_call_arg", installs: true, compiled: 1, specialised: 0, tree: 27 },
    BaseRow { name: "tail_recursive_loop_with_pap_producing_root_self_call_arg", installs: true, compiled: 1, specialised: 1, tree: 18 },
    BaseRow { name: "open_redex_probe", installs: false, compiled: 0, specialised: 0, tree: 10 },
    BaseRow { name: "oversized_source_with_a_shrinking_step", installs: false, compiled: 0, specialised: 0, tree: 8196 },
    BaseRow { name: "doubling_d4", installs: true, compiled: 1, specialised: 0, tree: 32 },
    BaseRow { name: "inconsistent_arity_parameter", installs: false, compiled: 0, specialised: 0, tree: 10 },
    BaseRow { name: "inconsistent_arity_saturating_instance", installs: true, compiled: 1, specialised: 1, tree: 11 },
    BaseRow { name: "inconsistent_arity_under_applying_instance", installs: true, compiled: 1, specialised: 0, tree: 18 },
    BaseRow { name: "inconsistent_arity_capturing_instance", installs: false, compiled: 0, specialised: 0, tree: 22 },
    BaseRow { name: "inconsistent_arity_runtime_chosen_instance", installs: false, compiled: 0, specialised: 0, tree: 29 },
    BaseRow { name: "inconsistent_arity_iterate", installs: false, compiled: 0, specialised: 0, tree: 29 },
    BaseRow { name: "iterate_creating_a_closure_over_g", installs: false, compiled: 0, specialised: 0, tree: 26 },
    BaseRow { name: "let_bound_factorial_10", installs: true, compiled: 1, specialised: 1, tree: 16 },
    BaseRow { name: "calls_a_capturing_closure_picked_by_if", installs: true, compiled: 1, specialised: 1, tree: 18 },
    BaseRow { name: "a_pap_of_a_self_recursive_combinator", installs: true, compiled: 1, specialised: 0, tree: 24 },
    BaseRow { name: "a_pap_of_a_capturing_self_recursive_combinator", installs: true, compiled: 1, specialised: 0, tree: 27 },
    BaseRow { name: "over_application_if_between_closures_of_params", installs: true, compiled: 1, specialised: 0, tree: 27 },
];

#[test]
fn baseline_fixture_matches() {
    let terms = census();
    for (name, _, _) in &terms {
        assert_eq!(BASELINE.iter().filter(|r| r.name == *name).count(), 1, "no row for {name}, or more than one");
    }
    for r in BASELINE {
        assert!(terms.iter().any(|(n, _, _)| *n == r.name), "row {} names no census term", r.name);
    }
    for (name, s, h) in &terms {
        let want = BASELINE.iter().find(|r| r.name == *name).unwrap();
        let got = measure(name, s, *h);
        if HELD_OUT.contains(name) && got.installs != want.installs {
            assert!(got.installs && !want.installs, "{name}: a held-out row's installs may go false to true, never back");
            assert_eq!((got.tree, got.name), (want.tree, want.name), "{name}");
        } else {
            assert_eq!(&got, want, "{name}");
        }
    }
}

#[test]
#[ignore]
fn print_baseline_rows() {
    for (name, s, h) in census() {
        let r = measure(name, &s, h);
        println!(
            "    BaseRow {{ name: {:?}, installs: {}, compiled: {}, specialised: {}, tree: {} }},",
            r.name, r.installs, r.compiled, r.specialised, r.tree
        );
    }
}
