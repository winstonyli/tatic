//! Golden WAT snapshots, one per benchmark term, plus a few `rejects_*`
//! terms the fragment must reject. A change to the lowering
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
use tatic::term::{Hash, PrimOp, TermStore};

type Builder = Box<dyn Fn(&mut TermStore) -> Hash>;
/// A plain (non-capturing) builder function pointer, as `test_corpus.rs`
/// uses -- distinct from `Builder` above (`Box<dyn Fn>`), which the
/// `rejects_*` closures need but the specialised-goldens list doesn't.
type PlainBuilder = fn(&mut TermStore) -> Hash;

fn corpus() -> Vec<(&'static str, Builder)> {
    vec![
        ("factorial", Box::new(common::factorial)),
        ("fib", Box::new(common::fib)),
        ("redundant_arithmetic_recursion", Box::new(common::redundant_arithmetic_recursion)),
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
        ("rejects_a_comparison_used_as_a_value", Box::new(rejects_a_comparison_used_as_a_value)),
        ("rejects_a_non_comparison_condition", Box::new(rejects_a_non_comparison_condition)),
        ("rejects_a_literal_applied_as_a_function", Box::new(rejects_a_literal_applied_as_a_function)),
        ("rejects_a_self_reference_read_as_a_value", Box::new(rejects_a_self_reference_read_as_a_value)),
        ("rejects_a_nested_closure_capturing_self", Box::new(rejects_a_nested_closure_capturing_self)),
    ]
}

// Terms the fragment must reject. Nothing else pins "identical
// rejections" now that the legacy emitter is gone.

/// `\x. x < 1`: comparisons only appear as an `If` condition.
fn rejects_a_comparison_used_as_a_value(s: &mut TermStore) -> Hash {
    let x = s.var(0);
    let one = s.lit(1);
    let lt = s.prim(PrimOp::Lt, x, one);
    s.abs(lt)
}

/// `\x. if x + 1 then 1 else 2`
fn rejects_a_non_comparison_condition(s: &mut TermStore) -> Hash {
    let x = s.var(0);
    let one = s.lit(1);
    let two = s.lit(2);
    let cond = s.prim(PrimOp::Add, x, one);
    let body = s.if_(cond, one, two);
    s.abs(body)
}

/// `\x. 1 x`: an application headed by neither a variable nor a lambda.
fn rejects_a_literal_applied_as_a_function(s: &mut TermStore) -> Hash {
    let x = s.var(0);
    let one = s.lit(1);
    let body = s.app(one, x);
    s.abs(body)
}

/// `rec f x. f`: the self-reference is only ever called.
fn rejects_a_self_reference_read_as_a_value(s: &mut TermStore) -> Hash {
    let f = s.var(1);
    let abs = s.abs(f);
    s.rec(abs)
}

/// `rec f n. (\y. f y) n`: a lifted lambda cannot capture the enclosing
/// `Rec`'s self-reference.
fn rejects_a_nested_closure_capturing_self(s: &mut TermStore) -> Hash {
    let y = s.var(0);
    let f = s.var(2);
    let fy = s.app(f, y);
    let inner = s.abs(fy);
    let n = s.var(0);
    let body = s.app(inner, n);
    let abs = s.abs(body);
    s.rec(abs)
}

/// Compares `got` against `dir/name.wat` (CRLF-normalised), or writes it
/// there when `update`. Otherwise, on a mismatch, pushes `name` onto
/// `changed` rather than failing immediately, so a whole corpus can be
/// checked and reported in one assertion.
fn check_golden(dir: &Path, name: &str, got: &str, update: bool, changed: &mut Vec<String>) {
    let path = dir.join(format!("{name}.wat"));
    if update {
        fs::create_dir_all(dir).unwrap();
        fs::write(&path, got).unwrap();
        return;
    }
    let want = fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}; run with UPDATE_GOLDEN=1 to record it", path.display()));
    if want.replace("\r\n", "\n") != got {
        changed.push(name.to_string());
    }
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
        // So that `UPDATE_GOLDEN=1` cannot quietly record one as accepted.
        assert!(!name.starts_with("rejects_") || got == "REJECTED\n", "{name} should be rejected, but compiled to:\n{got}");
        check_golden(&dir, name, &got, update, &mut changed);
    }
    assert!(changed.is_empty(), "emitted WAT changed for {changed:?}; if intended, rerun with UPDATE_GOLDEN=1 and review the diff");
}

#[test]
fn specialised_benchmark_terms_lower_to_their_golden_wat() {
    let update = std::env::var_os("UPDATE_GOLDEN").is_some();
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests").join("golden");
    let mut changed = Vec::new();
    let terms: [(&str, PlainBuilder); 2] =
        [("partial_application_loop", common::partial_application_loop), ("capturing_closure_loop", common::capturing_closure_loop)];
    for (name, build) in terms {
        let mut s = TermStore::new();
        let h = build(&mut s);
        let c = tatic::compile::compile_specialised(&s, h).unwrap_or_else(|| panic!("{name} should compile"));
        assert!(c.specialised.is_some(), "{name} should be specialised");
        check_golden(&dir, &format!("{name}_specialised"), &c.frag.wat, update, &mut changed);
    }
    assert!(changed.is_empty(), "emitted WAT changed for {changed:?}; if intended, rerun with UPDATE_GOLDEN=1 and review the diff");
}
