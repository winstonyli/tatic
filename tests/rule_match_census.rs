// How often would the three first lemma-database rules (design doc section 10) fire on the
// benchmark corpus? Static census over hash-consed nodes: x+0, x*1, and x*2^k (k >= 1).
// Counts pattern matches only; no lemma is proven here.
#[path = "../benches/common.rs"]
mod common;

use std::collections::HashSet;
use tatic::term::{Hash, PrimOp, Term, TermStore};

type PlainBuilder = fn(&mut TermStore) -> Hash;

fn census(s: &TermStore, root: Hash) -> (usize, usize, usize, usize, usize) {
    let mut seen = HashSet::new();
    let mut stack = vec![root];
    let (mut nodes, mut add0, mut mul1, mut mulpow2, mut prims) = (0, 0, 0, 0, 0);
    let lit = |h: Hash| match s.resolve(h) {
        Term::Lit(n) => Some(*n),
        _ => None,
    };
    while let Some(h) = stack.pop() {
        if !seen.insert(h) {
            continue;
        }
        nodes += 1;
        match s.resolve(h) {
            Term::Var(_) | Term::Lit(_) => {}
            Term::Prim(op, a, b) => {
                prims += 1;
                let (la, lb) = (lit(*a), lit(*b));
                match op {
                    PrimOp::Add if la == Some(0) || lb == Some(0) => add0 += 1,
                    PrimOp::Mul => {
                        if la == Some(1) || lb == Some(1) {
                            mul1 += 1;
                        } else if [la, lb].iter().any(|l| matches!(l, Some(n) if *n > 1 && n & (n - 1) == 0)) {
                            mulpow2 += 1;
                        }
                    }
                    _ => {}
                }
                stack.extend([*a, *b]);
            }
            Term::If(c, t, e) => stack.extend([*c, *t, *e]),
            Term::Abs(b) | Term::Rec(b) => stack.push(*b),
            Term::App(f, a) => stack.extend([*f, *a]),
        }
    }
    (nodes, prims, add0, mul1, mulpow2)
}

#[test]
fn census_of_rule_patterns_over_the_corpus() {
    let corpus: Vec<(&str, PlainBuilder)> = vec![
        ("factorial", common::factorial),
        ("fib", common::fib),
        ("redundant_arithmetic_recursion", common::redundant_arithmetic_recursion),
        ("gcd", common::gcd),
        ("gcd_with_two_base_cases", common::gcd_with_two_base_cases),
        ("capturing_closure_loop", common::capturing_closure_loop),
        ("partial_application_loop", common::partial_application_loop),
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
    let mut tot = (0, 0, 0, 0, 0);
    for (name, b) in &corpus {
        let mut s = TermStore::new();
        let root = b(&mut s);
        let c = census(&s, root);
        println!("CENSUS {name}: nodes={} prims={} x+0={} x*1={} x*2^k={}", c.0, c.1, c.2, c.3, c.4);
        tot = (tot.0 + c.0, tot.1 + c.1, tot.2 + c.2, tot.3 + c.3, tot.4 + c.4);
    }
    println!("CENSUS total: nodes={} prims={} x+0={} x*1={} x*2^k={}", tot.0, tot.1, tot.2, tot.3, tot.4);
    // Pinned so a corpus change is noticed: the corpus has no redundant identity patterns, and
    // one power-of-two multiply in `straight_line`, plus `redundant_arithmetic_recursion`, which
    // was added to hold one `x+0` and one `x*8`.
    assert_eq!(tot, (286, 54, 1, 0, 2));
}

#[test]
fn the_redundant_arithmetic_benchmark_compiles() {
    let mut s = TermStore::new();
    let h = common::redundant_arithmetic_recursion(&mut s);
    assert!(tatic::compile::try_compile(&s, h).is_some());
    assert_eq!(tatic::eval::apply_term(&s, h, &[10]).unwrap(), 440);
}
