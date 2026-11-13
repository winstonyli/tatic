//! S3's modules (v0.8, Goal 2): a term whose module holds callees besides the entry is `Accepted` when the registry's
//! terms pair with the records (`gate::pairing`), and `NotCovered` when a callee is outside what `cps` reads.
use super::gate::{applies_like_eval, big, compiled};
use super::*;
use crate::jit::JitEngine;
use crate::proof::gate::{gate, Verdict};
use crate::support::samples::{source, tail_recursive_loop_with_pap_producing_root_self_call_arg, twice_inc_5};
use crate::testing::ins_mutate::{count_call_sites, edit_call_site, mutate};
use crate::testing::test_corpus as tc;
use super::gate_mutants::{arg_instruction_added, arg_instruction_dropped, args_swapped, check_frag, get, konst, rejected_by, SiteEdit};
use crate::jit::compile::{CompiledFragment, Item};
use crate::proof::gate::{build, Layer};
use tatic_kernel::scoped;
use tatic_wasm::machine::{Entry, Ins};
use tatic_wasm::encoding::holds;

/// The gate's verdict on the form `try_install` proves.
fn verdict(b: fn(&mut TermStore) -> Hash) -> (Verdict, usize) {
    big(move || {
        let (s, h, frag) = compiled(&b);
        (gate(tatic_wasm::wasm::table(), &s, h, &frag), frag.records().iter().flatten().count())
    })
}

/// The verdict on the term's own fragment, unspecialised (the specialiser inlines these callees away).
fn raw_verdict(b: fn(&mut TermStore) -> Hash) -> (Verdict, usize, String) {
    big(move || {
        let mut s = TermStore::new();
        let h = b(&mut s);
        let frag = crate::jit::compile::try_compile(&s, h).expect("compiles");
        (gate(tatic_wasm::wasm::table(), &s, h, &frag), frag.records().iter().flatten().count(), frag.wat())
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

/// Review Focus 5: a callee's own tail loop is in the loop form (`br $top`), so a million iterations run in constant
/// depth; the entry's tail call into the callee is not a self call and stays a `return_call`.
#[test]
fn a_callee_tail_loop_runs_a_million_iterations() {
    let b = |s: &mut TermStore| source(s, r"\n. (rec g n acc = if n <= 0 then acc else g (n - 1) (acc + n)) n 0");
    let (v, wat) = big(move || {
        let (s, h, frag) = compiled(&b);
        (gate(tatic_wasm::wasm::table(), &s, h, &frag), frag.wat())
    });
    assert_eq!(v, Verdict::Accepted);
    let start = wat.find("(func $c0").expect("the callee is at position 0");
    let g = &wat[start..wat[start + 1..].find("(func").map_or(wat.len(), |i| start + 1 + i)];
    assert!(g.contains("br $top") && !g.contains("return_call $c0"), "{wat}");
    assert_eq!(wat.matches("return_call $c0").count(), 1, "{wat}");
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
        gate(tatic_wasm::wasm::table(), &s, h, &frag)
    });
    assert!(matches!(v, Verdict::Rejected(Layer::Pairing, _)), "{v:?}");
}

/// The module with the record at `pos` (and nothing else) replaced by `f` of it.
fn with_record(mut frag: CompiledFragment, pos: usize, f: impl FnOnce(Entry) -> Entry) -> CompiledFragment {
    let mut f = Some(f);
    for item in &mut frag.module {
        if let Item::Func { pos: p, entry, .. } = item {
            if *p == pos {
                *entry = (f.take().expect("one record per position"))(entry.clone());
            }
        }
    }
    assert!(f.is_none(), "no record at position {pos}");
    frag
}

fn src(text: &'static str) -> Build {
    Box::new(move |s: &mut TermStore| source(s, text))
}

/// The two Goal 2 targets whose callees the call-site set edits, and the third (the only one with a two-parameter callee).
fn call_terms() -> Vec<(&'static str, Build)> {
    vec![
        ("twice_inc_5", Box::new(twice_inc_5)),
        ("let_bound_factorial_10", Box::new(tc::let_bound_factorial_10)),
        ("tail_recursive_loop_with_pap", Box::new(tail_recursive_loop_with_pap_producing_root_self_call_arg)),
    ]
}

/// The registry spike's two-callee shapes (`w2:proof/tests/gen_real.rs#m2_terms`).
fn m2_terms() -> Vec<(&'static str, Build)> {
    vec![
        ("two callees", src(r"rec f n = if n <= 0 then 0 else (\a. a + 1) ((\b. b * 2) (f (n - 1)))")),
        ("two callees, roles exchanged", src(r"rec f n = if n <= 0 then 0 else (\b. b * 2) ((\a. a + 1) (f (n - 1)))")),
        ("two callees, twice", src(r"rec f n = if n <= 0 then 1 else (\a. a + 1) ((\b. b * 2) (f (n - 1))) + (\b. b * 2) ((\a. a + 1) (f (n - 2)))")),
        ("callee calls callee", src(r"rec f n = if n <= 0 then 0 else (rec ga a = if a <= 0 then 0 else (\d. d + 3) (ga (a - 1))) (f (n - 1)) + (\b. b * 2) (f (n - 2))")),
    ]
}

/// Every call site of the module as (caller position, callee position, site index in the caller), and the positions
/// that have a record.
fn call_sites(frag: &CompiledFragment) -> (Vec<(usize, usize, usize)>, Vec<usize>) {
    let records = frag.records();
    let positions: Vec<usize> = (0..records.len()).filter(|p| records[*p].is_some()).collect();
    let mut sites = vec![];
    for &p in &positions {
        for &q in &positions {
            sites.extend((0..count_call_sites(&records[p].unwrap().code, q)).map(|k| (p, q, k)));
        }
    }
    (sites, positions)
}

/// The module with the `site`-th `Call(callee)` of the record at `caller` edited by `edit`; `None` where it does not apply.
fn edit_site(frag: &CompiledFragment, (caller, callee, site): (usize, usize, usize), edit: SiteEdit) -> Option<CompiledFragment> {
    let arity = frag.records()[callee].unwrap().arity;
    let changed = std::cell::Cell::new(false);
    let code = edit_call_site(&frag.records()[caller].unwrap().code, site, callee, arity, tatic_wasm::wasm::table(), &|b, i, args| changed.set(edit(b, i, args)));
    changed.get().then(|| with_record(dup(frag), caller, |e| Entry { code, ..e }))
}

fn dup(frag: &CompiledFragment) -> CompiledFragment {
    CompiledFragment { module: frag.module.clone(), ..*frag }
}

type Build = Box<dyn Fn(&mut TermStore) -> Hash>;

/// Every call-site mutant of the module as (kind, label, mutant): a wrong callee index, two arguments swapped, an
/// argument instruction dropped and one added; where the edit applies.
fn site_mutants(frag: &CompiledFragment) -> Vec<(&'static str, String, CompiledFragment)> {
    let (sites, positions) = call_sites(frag);
    let mut out = vec![];
    for site @ (caller, callee, k) in sites {
        let at = format!("site {k} of Call({callee}) in position {caller}");
        for &other in positions.iter().filter(|o| **o != callee) {
            let wrong = |b: &mut Vec<Ins>, i: usize, _: &[std::ops::Range<usize>]| {
                b[i] = Ins::Call(other);
                true
            };
            out.extend(edit_site(frag, site, &wrong).map(|m| ("a wrong callee index", format!("{at} -> Call({other})"), m)));
        }
        for (kind, edit) in [("two arguments swapped", &args_swapped as SiteEdit), ("an argument instruction dropped", &arg_instruction_dropped), ("an argument instruction added", &arg_instruction_added)] {
            let applies = match kind {
                "two arguments swapped" => frag.records()[callee].unwrap().arity >= 2,
                "an argument instruction dropped" => frag.records()[callee].unwrap().arity >= 1,
                _ => true,
            };
            if applies {
                out.extend(edit_site(frag, site, edit).map(|m| (kind, format!("{kind}, {at}"), m)));
            }
        }
    }
    out
}

/// A module's subject: the term the gate sees and its fragment, built afresh at each call.
fn subject_of(b: &Build) -> impl Fn() -> (TermStore, Hash, CompiledFragment) + '_ {
    move || {
        let (s, h, f) = compiled(&**b);
        (s, h, super::loop_form::call_form_frag(f))
    }
}

/// The row `from` read as the row `to` in the first instruction of the record at `pos` that holds it.
fn flip_row(frag: CompiledFragment, pos: usize, from: &'static str, to: &'static str) -> CompiledFragment {
    let row = |n| Ins::Row { name: n, operand: 0 };
    let code = mutate(&frag.records()[pos].unwrap().code, &|i| (i == &row(from)).then_some(row(to)));
    assert_ne!(code, frag.records()[pos].unwrap().code, "position {pos} holds no {from}");
    with_record(frag, pos, |e| Entry { code, ..e })
}

/// Per call site of the three call terms: a wrong callee index, two arguments swapped (only the two-parameter callee has
/// two), an argument instruction dropped and one added, each `Rejected` at the layer the first run observed, forged
/// where `build` gives the mutant a statement; and a false callee law, the callee's body edited under its unchanged
/// source (the spikes' control: twice_inc_5's `add` read as `sub`, let_bound_factorial_10's `mul` as `add`).
#[test]
fn call_site_mutants_are_rejected() {
    let mut seen = std::collections::BTreeMap::<&str, usize>::new();
    for (name, b) in call_terms() {
        let subject = subject_of(&b);
        for (kind, label, mutant) in site_mutants(&subject().2) {
            let layer = if kind == "two arguments swapped" { Layer::Walk } else { Layer::Shape };
            check_frag(&format!("{name}: {label}"), &subject, mutant, layer);
            *seen.entry(kind).or_default() += 1;
        }
    }
    // every mutator applied: the sites are 1 (twice_inc_5), 2 (let_bound_factorial_10) and 2 (the pap loop)
    assert_eq!(seen["a wrong callee index"], 5);
    assert_eq!(seen["two arguments swapped"], 1);
    assert_eq!(seen["an argument instruction dropped"], 5);
    assert_eq!(seen["an argument instruction added"], 5);
    for (name, b, from, to) in [("twice_inc_5", Box::new(twice_inc_5) as Build, "add", "sub"), ("let_bound_factorial_10", Box::new(tc::let_bound_factorial_10), "mul", "add")] {
        let subject = subject_of(&b);
        check_frag(&format!("{name}: a false callee law ({from} -> {to} in $c0)"), &subject, flip_row(subject().2, 0, from, to), Layer::Walk);
    }
}

/// The case-13 controls: `call $c0` to `call $f`, which is `Call(0)` to `Call(n)` for the module's `n` callees, on
/// twice_inc_5 and let_bound_factorial_10.
#[test]
fn case_13_controls_are_rejected() {
    for (name, b) in call_terms().into_iter().take(2) {
        let subject = subject_of(&b);
        let n = subject().2.entry_pos;
        let mutant = with_record(subject().2, n, |e| Entry { code: mutate(&e.code, &|i| (i == &Ins::Call(0)).then_some(Ins::Call(n))), ..e });
        assert_ne!(mutant.entry().code, subject().2.entry().code, "{name}: the entry holds a Call(0)");
        check_frag(&format!("{name}: call $c0 -> call $f"), &subject, mutant, Layer::Shape);
    }
}

/// A callee narrower than the module's width (D2) reading a padding slot: `local.get 1` in a one-parameter callee.
#[test]
fn a_padding_slot_read_is_rejected() {
    let b: Build = src(r"\a b. (\x. x + 1) (a + b)");
    let subject = subject_of(&b);
    let f = subject().2;
    assert_eq!(f.records()[0].unwrap().arity, 1, "the callee is narrower than the entry");
    assert_eq!(f.entry().arity, 2);
    let code = vec![get(1), konst(1), Ins::Row { name: "add", operand: 0 }];
    check_frag("a callee reading local.get 1", &subject, with_record(f, 0, |e| Entry { code, ..e }), Layer::Shape);
}

/// The kernel negative for a call term: twice_inc_5's proof is not a proof of let_bound_factorial_10's statement, nor
/// the reverse (each is a proof of its own).
#[test]
fn a_call_terms_proof_does_not_prove_another_statement() {
    let ((s1, h1, f1), (s2, h2, f2)) = (compiled(&twice_inc_5), compiled(&tc::let_bound_factorial_10));
    big(move || {
        scoped(|| {
            let table = tatic_wasm::wasm::table();
            let (stmt1, proof1) = build(table, &s1, h1, &f1).expect("twice_inc_5 builds");
            let (stmt2, proof2) = build(table, &s2, h2, &f2).expect("let_bound_factorial_10 builds");
            let (proof1, proof2) = (proof1.expect("a proof"), proof2.expect("a proof"));
            assert!(holds(&proof1, &stmt1).is_ok() && holds(&proof2, &stmt2).is_ok());
            assert!(holds(&proof1, &stmt2).is_err());
            assert!(holds(&proof2, &stmt1).is_err());
        })
    });
}

#[test]
fn two_callee_terms_prove_in_one_module() {
    for (name, b) in m2_terms() {
        let (s, h, frag) = compiled(&*b);
        let callees = frag.records().iter().flatten().count() - 1;
        assert!(callees >= 2, "{name}: {callees} callees\n{}", frag.wat());
        assert_eq!(big(move || gate(tatic_wasm::wasm::table(), &s, h, &frag)), Verdict::Accepted, "{name}");
    }
}

/// `code` with every `Call(a)` read as `Call(b)` and the reverse.
fn swap_calls(code: &[Ins], a: usize, b: usize) -> Vec<Ins> {
    let sw = |p: usize| if p == a { b } else if p == b { a } else { p };
    code.iter()
        .map(|i| match i {
            Ins::Call(p) => Ins::Call(sw(*p)),
            Ins::If(t, e) => Ins::If(swap_calls(t, a, b), swap_calls(e, a, b)),
            other => other.clone(),
        })
        .collect()
}

#[test]
fn swapped_call_indices_are_rejected() {
    for (name, b) in m2_terms() {
        let subject = subject_of(&b);
        let mut mutant = subject().2;
        for pos in 0..=mutant.entry_pos {
            mutant = with_record(mutant, pos, |e| Entry { code: swap_calls(&e.code, 0, 1), ..e });
        }
        // the callee that calls itself and another has its self-call read as a call to position 1: a pairing mismatch
        let layer = if name == "callee calls callee" { Layer::Pairing } else { Layer::Walk };
        check_frag(&format!("{name}: Call(0) and Call(1) exchanged"), &subject, mutant, layer);
    }
}

/// Records 0 and 1 exchanged with their sources, the calls left as they are: the entry now calls the other function at
/// each position. The layer is the first run's (the plan left Pairing or Walk open).
#[test]
fn swapped_registry_entries_are_refused() {
    for (name, b) in m2_terms() {
        let (s, h, mut frag) = compiled(&*b);
        let at = |f: &CompiledFragment, p: usize| f.module.iter().position(|i| matches!(i, Item::Func { pos, .. } if *pos == p)).unwrap();
        let (i0, i1) = (at(&frag, 0), at(&frag, 1));
        let (Item::Func { entry: e0, source: s0, .. }, Item::Func { entry: e1, source: s1, .. }) = (frag.module[i0].clone(), frag.module[i1].clone()) else { unreachable!() };
        frag.module[i0] = Item::Func { pos: 0, entry: e1, source: s1 };
        frag.module[i1] = Item::Func { pos: 1, entry: e0, source: s0 };
        let v = big(move || gate(tatic_wasm::wasm::table(), &s, h, &frag));
        // the other terms' callees call nothing, so the sets agree and the walk finds the exchange; a callee that calls
        // another has its set exchanged too
        rejected_by(v, if name == "callee calls callee" { Layer::Pairing } else { Layer::Walk }, name);
    }
}

/// O4: callee 0 calling 1 and 1 calling 0 is never `Accepted` (no source term can name a cycle).
#[test]
fn a_cyclic_registry_is_never_accepted() {
    for (name, b) in m2_terms() {
        let (s, h, mut frag) = compiled(&*b);
        for (pos, to) in [(0, 1), (1, 0)] {
            frag = with_record(frag, pos, |e| Entry { code: vec![get(0), Ins::Call(to)], ..e });
        }
        let v = big(move || gate(tatic_wasm::wasm::table(), &s, h, &frag));
        assert!(matches!(v, Verdict::NotCovered(_) | Verdict::Rejected(..)), "{name}: {v:?}");
        println!("{name}: {v:?}");
    }
}

/// The loop form in a callee (Review Focus 2): `rec g`'s record at position 0 with its tail `Call(0)` as
/// `[Set 1, Set 0, Br]` is `Accepted`, and `Br` restarts the callee, not the entry. Three mutants of that record are
/// rejected: `[konst 1, add]` after its `If`, a `Set` past its arity, and the `Set`s in forward order.
#[test]
fn a_callee_loop_form_is_accepted_and_its_mutants_rejected() {
    use super::loop_form::call_form_frag;
    use crate::jit::lower_wat::loop_form;
    let b: Build = src(r"\n. (rec g n acc = if n <= 0 then acc else g (n - 1) (acc + n)) n 0");
    let subject = || {
        let (s, h, frag) = compiled(&*b);
        (s, h, call_form_frag(frag))
    };
    let (s, h, frag) = subject();
    assert_eq!(frag.records()[0].unwrap().arity, 2, "the callee g at position 0 takes n and acc");
    let with_g = |slots: &[i64], post: &[Ins]| {
        with_record(dup(&frag), 0, |e| Entry { code: [loop_form(&e.code, 0, slots), post.to_vec()].concat(), ..e })
    };
    let accepted = with_g(&[1, 0], &[]);
    let wat = accepted.wat();
    assert!(wat.contains("br $top"), "{wat}");
    let v = big(move || gate(tatic_wasm::wasm::table(), &s, h, &accepted));
    assert_eq!(v, Verdict::Accepted);
    check_frag("callee: [konst 1, add] after the If", &subject, with_g(&[1, 0], &[konst(1), Ins::Row { name: "add", operand: 0 }]), Layer::Walk);
    check_frag("callee: Sets in forward order", &subject, with_g(&[0, 1], &[]), Layer::Walk);
    let past = with_g(&[2, 0], &[]);
    check_frag("callee: Set 2 past the arity", &subject, dup(&past), Layer::Shape);
    let (s, h, _) = subject();
    match big(move || gate(tatic_wasm::wasm::table(), &s, h, &past)) {
        Verdict::Rejected(Layer::Shape, why) => assert!(why.contains("local.set 2"), "{why}"),
        other => panic!("Set 2: {other:?}"),
    }
}
