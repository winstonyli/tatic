// How often would the three first lemma-database rules (design doc section 10) fire on the
// benchmark corpus? Static census over hash-consed nodes: x+0, x*1, and x*2^k (k >= 1).
// Counts pattern matches only; no lemma is proven here.
use std::collections::HashSet;
use tatic::term::{Hash, PrimOp, Term, TermStore};

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
    let mut tot = (0, 0, 0, 0, 0);
    for (name, s, root) in tatic::samples::corpus() {
        let c = census(&s, root);
        println!("CENSUS {name}: nodes={} prims={} x+0={} x*1={} x*2^k={}", c.0, c.1, c.2, c.3, c.4);
        tot = (tot.0 + c.0, tot.1 + c.1, tot.2 + c.2, tot.3 + c.3, tot.4 + c.4);
    }
    println!("CENSUS total: nodes={} prims={} x+0={} x*1={} x*2^k={}", tot.0, tot.1, tot.2, tot.3, tot.4);
    // Pinned so a corpus change is noticed: the corpus has no redundant identity patterns, and
    // one power-of-two multiply in `straight_line`, plus `redundant_arithmetic_recursion`, which
    // was added to hold one `x+0` and one `x*8`.
    // 346 nodes and 62 prims over `samples::corpus()`'s 23 terms (286 and 54 over the 19 this
    // census listed until 2026-10-27).
    assert_eq!(tot, (346, 62, 1, 0, 2));
}

#[test]
fn the_redundant_arithmetic_benchmark_compiles() {
    let mut s = TermStore::new();
    let h = tatic::samples::redundant_arithmetic_recursion(&mut s);
    assert!(tatic::compile::try_compile(&s, h).is_some());
    assert_eq!(tatic::eval::apply_term(&s, h, &[10]).unwrap(), 440);
}
