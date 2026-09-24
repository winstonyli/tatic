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

/// `\n. if n == 777 then (\x. 0) v5 else 1`, with `v5` unbound: `eval`
/// fails with `UnboundVariable` at `n = 777`. Contracting the redex would
/// hide that, which is why the checker requires a closed source. Kept out
/// of `terms()`, whose terms are all closed.
pub(crate) fn open_redex_probe(s: &mut TermStore) -> Hash {
    use crate::term::PrimOp;
    let (n, zero, one, magic, v5) = (s.var(0), s.lit(0), s.lit(1), s.lit(777), s.var(5));
    let cond = s.prim(PrimOp::Eq, n, magic);
    let k0 = s.abs(zero);
    let redex = s.app(k0, v5);
    let body = s.if_(cond, redex, one);
    s.abs(body)
}

/// `\n. (\x. n) BIG`, with `BIG` a closed lambda of more than `MAX_NODES`
/// nodes (a balanced sum of `MAX_NODES` distinct literals, so about twice
/// that, and shallow enough for the recursive passes). The one βv step
/// shrinks it far below the limit, but the checker rejects the source
/// itself for its size.
pub(crate) fn oversized_source_with_a_shrinking_step(s: &mut TermStore) -> Hash {
    fn sum(s: &mut TermStore, lo: i64, hi: i64) -> Hash {
        if hi - lo == 1 {
            return s.lit(lo);
        }
        let mid = lo + (hi - lo) / 2;
        let (a, b) = (sum(s, lo, mid), sum(s, mid, hi));
        s.prim(crate::term::PrimOp::Add, a, b)
    }
    let big = sum(s, 0, crate::spec_check::MAX_NODES as i64);
    let big = s.abs(big);
    let n = s.var(1);
    let k = s.abs(n);
    let r = s.app(k, big);
    s.abs(r)
}
