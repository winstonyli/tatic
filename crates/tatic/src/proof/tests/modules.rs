//! S3's modules (v0.8, Goal 2): a term whose module holds callees besides the entry is `Accepted` when the registry's
//! terms pair with the records (`gate::pairing`), and `NotCovered` when a callee is outside what `cps` reads.
use super::gate::{applies_like_eval, big, compiled};
use super::*;
use crate::jit::shape::wasm_table;
use crate::jit::JitEngine;
use crate::proof::gate::{gate, Verdict};
use crate::support::samples::{source, tail_recursive_loop_with_pap_producing_root_self_call_arg, twice_inc_5};
use crate::testing::test_corpus as tc;

/// The gate's verdict on the form `try_install` proves.
fn verdict(b: fn(&mut TermStore) -> Hash) -> (Verdict, usize) {
    big(move || {
        let (s, h, frag) = compiled(&b);
        (gate(wasm_table(), &s, h, &frag), frag.records().iter().flatten().count())
    })
}

/// The verdict on the term's own fragment, unspecialised (the specialiser inlines these callees away).
fn raw_verdict(b: fn(&mut TermStore) -> Hash) -> (Verdict, usize, String) {
    big(move || {
        let mut s = TermStore::new();
        let h = b(&mut s);
        let frag = crate::jit::compile::try_compile(&s, h).expect("compiles");
        (gate(wasm_table(), &s, h, &frag), frag.records().iter().flatten().count(), frag.wat())
    })
}

#[test]
fn goal_2_targets_are_accepted() {
    type Build = fn(&mut TermStore) -> Hash;
    let targets: [(&str, Build, &[&[i64]]); 3] = [
        ("twice_inc_5", twice_inc_5, &[&[]]),
        ("let_bound_factorial_10", tc::let_bound_factorial_10, &[&[]]),
        ("tail_recursive_loop_with_pap_producing_root_self_call_arg", tail_recursive_loop_with_pap_producing_root_self_call_arg, &[&[3], &[0], &[7]]),
    ];
    for (name, b, argss) in targets {
        let (v, records) = verdict(b);
        assert!(records > 1, "{name}: a Goal 2 target compiles with a callee");
        assert_eq!(v, Verdict::Accepted, "{name}");
        let mut s = TermStore::new();
        let h = b(&mut s);
        applies_like_eval(&s, h, argss);
    }
}

#[test]
fn a_callee_wider_than_its_caller_and_the_reverse() {
    let wider: fn(&mut TermStore) -> Hash = |s| source(s, r"\x. (\a b c. a + b - c) x 1 2");
    let narrower: fn(&mut TermStore) -> Hash = |s| source(s, r"\a b c. (\x. x * 2) (a + b + c)");
    for (name, b) in [("wider callee", wider), ("narrower callee", narrower)] {
        let (v, records, _) = raw_verdict(b);
        assert!(records > 1, "{name}: compiles with a callee");
        assert_eq!(v, Verdict::Accepted, "{name}");
    }
    let mut s = TermStore::new();
    let h = wider(&mut s);
    applies_like_eval(&s, h, &[&[5], &[-3]]);
    let h = narrower(&mut s);
    applies_like_eval(&s, h, &[&[1, 2, 3], &[0, 0, 0]]);
}

/// Review Focus 5: a callee's own tail loop is a `return_call`, so a million iterations run in constant depth.
#[test]
fn a_callee_tail_loop_runs_a_million_iterations() {
    let b = |s: &mut TermStore| source(s, r"\n. (rec g n acc = if n <= 0 then acc else g (n - 1) (acc + n)) n 0");
    let (v, wat) = big(move || {
        let (s, h, frag) = compiled(&b);
        (gate(wasm_table(), &s, h, &frag), frag.wat())
    });
    assert_eq!(v, Verdict::Accepted);
    assert!(wat.contains("return_call $c0"), "{wat}");
    let mut s = TermStore::new();
    let h = b(&mut s);
    let mut jit = JitEngine::new();
    let n: i64 = 1_000_000;
    assert_eq!(jit.apply(&s, h, &[n]), Ok(n * (n + 1) / 2));
    assert_eq!(jit.stats.compiled, 1);
}

#[test]
fn a_partial_application_callee_is_not_covered() {
    let (v, _) = verdict(tc::a_pap_of_a_self_recursive_combinator);
    assert!(matches!(v, Verdict::NotCovered(_)), "{v:?}");
}

/// The pairing check: an entry that calls position 0 where its source calls positions 0 and 1 is `Rejected(Pairing)`,
/// not `NotCovered` and not a panic in the statement (`SEnv::call` finds no callee at the position the source names).
#[test]
fn code_that_calls_another_position_than_its_source_is_rejected_by_the_pairing() {
    use crate::proof::gate::Layer;
    use tatic_wasm::machine::{Entry, Ins};
    let v = big(|| {
        let mut s = TermStore::new();
        let h = source(&mut s, r"\x. (\a. a + 1) ((\b. b * 2) x)");
        let frag = crate::jit::compile::try_compile(&s, h).expect("compiles");
        let frag = crate::testing::ins_mutate::with_entry(frag, |e| Entry {
            code: e.code.iter().map(|i| if let Ins::Call(_) = i { Ins::Call(0) } else { i.clone() }).collect(),
            ..e
        });
        gate(wasm_table(), &s, h, &frag)
    });
    assert!(matches!(v, Verdict::Rejected(Layer::Pairing, _)), "{v:?}");
}
