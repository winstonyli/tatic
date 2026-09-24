//! Golden WAT snapshots, one per benchmark term. A change to the lowering
//! (`src/lower_wat.rs`) or the builder that changes emitted WAT fails here.
//! If the change is intended, regenerate with
//! `UPDATE_GOLDEN=1 cargo test --test golden_wat` and review the diff. A
//! term the fragment rejects is recorded as `REJECTED`, so a new
//! acceptance or rejection shows up here too. The snapshots were first
//! recorded while the transitional `try_compile` asserted the IR path
//! byte-identical to the legacy direct emitter (since retired).

#[path = "../benches/common.rs"]
mod common;

use std::fs;
use std::path::Path;

use tatic::compile::try_compile;
use tatic::term::{Hash, TermStore};

type Builder = Box<dyn Fn(&mut TermStore) -> Hash>;

fn corpus() -> Vec<(&'static str, Builder)> {
    vec![
        ("factorial", Box::new(common::factorial)),
        ("fib", Box::new(common::fib)),
        ("gcd", Box::new(common::gcd)),
        ("gcd_with_two_base_cases", Box::new(common::gcd_with_two_base_cases)),
        ("capturing_closure_loop", Box::new(common::capturing_closure_loop)),
        ("partial_application_loop", Box::new(common::partial_application_loop)),
        ("closure_typed_loop_carried_parameter_loop", Box::new(|s: &mut TermStore| common::closure_typed_loop_carried_parameter_loop(s, 150))),
        ("inconsistent_arity_loop_carried_parameter_loop", Box::new(|s: &mut TermStore| common::inconsistent_arity_loop_carried_parameter_loop(s, 150))),
        ("straight_line", Box::new(common::straight_line)),
        ("twice_inc_5", Box::new(common::twice_inc_5)),
        ("a_capturing_closure_call", Box::new(common::a_capturing_closure_call)),
        ("a_pap_non_capturing", Box::new(common::a_pap_non_capturing)),
        ("a_pap_capturing", Box::new(common::a_pap_capturing)),
        ("iterate", Box::new(common::iterate)),
        ("non_tail_closure_carrying_recursion", Box::new(common::non_tail_closure_carrying_recursion)),
        ("branching_non_tail_closure_carrying_recursion", Box::new(common::branching_non_tail_closure_carrying_recursion)),
        ("over_application_if_between_closures", Box::new(common::over_application_if_between_closures)),
        ("over_application_pap_producing_root", Box::new(common::over_application_pap_producing_root)),
        ("tail_recursive_loop_with_if_between_closures_self_call_arg", Box::new(common::tail_recursive_loop_with_if_between_closures_self_call_arg)),
        ("tail_recursive_loop_with_pap_producing_root_self_call_arg", Box::new(common::tail_recursive_loop_with_pap_producing_root_self_call_arg)),
    ]
}

#[test]
fn every_benchmark_term_lowers_to_its_golden_wat() {
    let update = std::env::var_os("UPDATE_GOLDEN").is_some();
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests").join("golden");
    let mut changed = Vec::new();
    for (name, build) in corpus() {
        let mut s = TermStore::new();
        let h = build(&mut s);
        let got = match try_compile(&s, h) {
            Some(frag) => frag.wat,
            None => "REJECTED\n".to_string(),
        };
        let path = dir.join(format!("{name}.wat"));
        if update {
            fs::create_dir_all(&dir).unwrap();
            fs::write(&path, &got).unwrap();
            continue;
        }
        let want = fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}; run with UPDATE_GOLDEN=1 to record it", path.display()));
        if want.replace("\r\n", "\n") != got {
            changed.push(name);
        }
    }
    assert!(changed.is_empty(), "emitted WAT changed for {changed:?}; if intended, rerun with UPDATE_GOLDEN=1 and review the diff");
}
