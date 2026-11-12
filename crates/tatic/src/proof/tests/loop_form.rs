//! The loop form through the gate (spec 2026-11-12-proved-loop-form-design.md): a self tail call written as `Set`s
//! and a `Br` is `Accepted` on the O3 spike's targets, and its 54 mutants are rejected at the layers that spike
//! recorded (`docs/tier-cycle/`, "v0.8's build: measurements and checks"). Every list starts from the `Call` form
//! (`call_form_frag`), so the tests read the same after the lowering emits the loop form.
use tatic_wasm::machine::{Entry, Ins};
use tatic_wasm::print::map_tail_calls;

use super::gate::{big, compiled};
use super::gate_mutants::{clip, get, konst};
use crate::jit::compile::{CompiledFragment, Item};
use crate::jit::shape::wasm_table;
use crate::lang::term::{Hash, TermStore};
use crate::proof::gate::{gate, Layer, Verdict};
use crate::support::samples::{
    capturing_closure_loop, factorial, fib, partial_application_loop, source, tail_recursive_loop_with_pap_producing_root_self_call_arg,
};
use crate::testing::ins_mutate::with_entry;

type Build = Box<dyn Fn(&mut TermStore) -> Hash + Send + Sync>;
type Transform = Box<dyn Fn(&[Ins], usize, usize) -> Vec<Ins>>;

const SUM: &str = "rec f n acc = if n <= 0 then acc else f (n - 1) (acc + n)";
/// A second sum-shaped loop with the argument order and the accumulator update swapped.
const SUM2: &str = "rec f acc n = if n <= 0 then acc else f (acc + n) (n - 1)";

pub(super) fn set(i: i64) -> Ins {
    Ins::Row { name: "local.set", operand: i }
}
fn row(name: &'static str) -> Ins {
    Ins::Row { name, operand: 0 }
}

/// The slots a self call's arguments are written to, top of the stack first: the last argument first.
pub(super) fn rev_slots(arity: usize) -> Vec<i64> {
    (0..arity as i64).rev().collect()
}

/// `code` with each tail `Call(own)` replaced by `Set`s at `slots` (in order) then `Br`.
pub(super) fn loop_form(code: &[Ins], own: usize, slots: &[i64]) -> Vec<Ins> {
    map_tail_calls(code, &mut |j| (j == own).then(|| slots.iter().map(|s| set(*s)).chain([Ins::Br]).collect()))
}

/// `code` with each tail `[Set(arity-1) .. Set(0), Br]` mapped back to `Call(own)`: the inverse of `loop_form` with the
/// reversed slots.
pub(super) fn call_form(code: &[Ins], own: usize, arity: usize) -> Vec<Ins> {
    let suffix: Vec<Ins> = rev_slots(arity).into_iter().map(set).chain([Ins::Br]).collect();
    let mut out = code.to_vec();
    if out.ends_with(&suffix) {
        out.truncate(out.len() - suffix.len());
        out.push(Ins::Call(own));
    } else if let Some(Ins::If(t, e)) = out.last_mut() {
        *t = call_form(t, own, arity);
        *e = call_form(e, own, arity);
    }
    out
}

/// `frag` with `call_form` applied to every record, at its own position and arity.
pub(super) fn call_form_frag(mut frag: CompiledFragment) -> CompiledFragment {
    for item in &mut frag.module {
        if let Item::Func { pos, entry, .. } = item {
            entry.code = call_form(&entry.code, *pos, entry.arity);
        }
    }
    frag
}

/// `code` with the `n`th (pre-order) `Call(own)` replaced by `repl`, the rest of its sequence dropped if `truncate`.
fn replace_nth_call(code: &[Ins], own: usize, n: &mut usize, repl: &[Ins], truncate: bool) -> Vec<Ins> {
    let mut out = vec![];
    for ins in code {
        match ins {
            Ins::If(t, e) => out.push(Ins::If(replace_nth_call(t, own, n, repl, truncate), replace_nth_call(e, own, n, repl, truncate))),
            Ins::Call(j) if *j == own => {
                if *n == 0 {
                    out.extend(repl.iter().cloned());
                    *n = usize::MAX;
                    if truncate {
                        return out;
                    }
                } else {
                    *n = n.wrapping_sub(1);
                    out.push(ins.clone())
                }
            }
            other => out.push(other.clone()),
        }
    }
    out
}

/// `code` with each `Call(j)` removed (the callee's call dropped).
fn strip_call(code: &[Ins], j: usize) -> Vec<Ins> {
    code.iter()
        .filter(|i| **i != Ins::Call(j))
        .map(|i| match i {
            Ins::If(t, e) => Ins::If(strip_call(t, j), strip_call(e, j)),
            o => o.clone(),
        })
        .collect()
}

fn with_code(frag: CompiledFragment, code: Vec<Ins>) -> CompiledFragment {
    with_entry(frag, |e| Entry { code, ..e })
}

/// The gate's verdict on the entry's `Call`-form code transformed by `code(list, own, arity)`, and that code.
fn run(b: &Build, code: &dyn Fn(&[Ins], usize, usize) -> Vec<Ins>) -> (Verdict, Vec<Ins>) {
    let (s, h, frag) = compiled(&**b);
    let frag = call_form_frag(frag);
    let (own, arity) = (frag.entry_pos, frag.entry().arity);
    let new = code(&frag.entry().code, own, arity);
    let mutant = with_code(frag, new.clone());
    (big(move || gate(wasm_table(), &s, h, &mutant)), new)
}

fn the_loop_form(c: &[Ins], own: usize, arity: usize) -> Vec<Ins> {
    loop_form(c, own, &rev_slots(arity))
}

fn targets() -> Vec<(&'static str, Build)> {
    vec![
        ("capturing_closure_loop", Box::new(capturing_closure_loop)),
        ("SUM", Box::new(|s| source(s, SUM))),
        ("SUM2", Box::new(|s| source(s, SUM2))),
        ("partial_application_loop", Box::new(partial_application_loop)),
        // a module with a callee: the loop's argument comes from a call to position 0
        ("tail_pap (callee at 0)", Box::new(tail_recursive_loop_with_pap_producing_root_self_call_arg)),
        ("held_out_b", Box::new(crate::testing::test_corpus::held_out_b)),
    ]
}

#[test]
fn setbr_targets_are_accepted() {
    for (name, b) in targets() {
        let (v, code) = run(&b, &the_loop_form);
        println!("{name}: {v:?}\n    {code:?}");
        assert!(format!("{code:?}").contains("Br"), "{name}: no loop form");
        assert_eq!(v, Verdict::Accepted, "{name}");
    }
}

/// Each mutant is rejected at the layer the O3 spike recorded; every verdict is printed first, so an unexpected one is
/// read, not hidden.
#[test]
fn setbr_mutants_are_rejected() {
    let mut ms: Vec<(String, Build, Transform, Layer)> = vec![];
    let two_arg: Vec<(&'static str, fn() -> Build)> = vec![
        ("capturing_closure_loop", || Box::new(capturing_closure_loop)),
        ("SUM", || Box::new(|s| source(s, SUM))),
        ("SUM2", || Box::new(|s| source(s, SUM2))),
    ];
    for (name, mk) in &two_arg {
        let mut add = |what: &str, f: Transform, layer: Layer| ms.push((format!("{name}: {what}"), mk(), f, layer));
        add("(a) Sets in forward order [0,1]", Box::new(|c, o, _| loop_form(c, o, &[0, 1])), Layer::Walk);
        add("(b1) one Set dropped (only slot 1)", Box::new(|c, o, _| loop_form(c, o, &[1])), Layer::Shape);
        add("(b2) one Set dropped (only slot 0)", Box::new(|c, o, _| loop_form(c, o, &[0])), Layer::Shape);
        add("(b3/g) Br with no Sets, args changed", Box::new(|c, o, _| loop_form(c, o, &[])), Layer::Shape);
        add("(h1) both Sets to slot 0", Box::new(|c, o, _| loop_form(c, o, &[0, 0])), Layer::Walk);
        add("(d) Set to slot 2 >= arity 2", Box::new(|c, o, _| loop_form(c, o, &[2, 0])), Layer::Shape);
        add("(d2) three Sets (underflow)", Box::new(|c, o, _| loop_form(c, o, &[2, 1, 0])), Layer::Shape);
        add(
            "(f) post-code `+1` after the if, Br in the else arm",
            Box::new(|c, o, a| [the_loop_form(c, o, a), vec![konst(1), row("add")]].concat()),
            Layer::Walk,
        );
        add(
            "(f3) arms swapped (Br in the then arm)",
            Box::new(|c, o, a| {
                let mut v = the_loop_form(c, o, a);
                if let Some(Ins::If(t, e)) = v.last_mut() {
                    std::mem::swap(t, e)
                }
                v
            }),
            Layer::Walk,
        );
        add(
            "(h4) a Set before the body changes a parameter the body then reads",
            Box::new(|c, o, a| [vec![get(1), konst(1), row("add"), set(1)], the_loop_form(c, o, a)].concat()),
            Layer::Walk,
        );
        add("(g) the list is only [Br]", Box::new(|_, _, _| vec![Ins::Br]), Layer::Walk);
        add(
            "(g2) Br first, the rest of the body after it",
            Box::new(|c, o, a| [vec![Ins::Br], the_loop_form(c, o, a)].concat()),
            Layer::Shape,
        );
        add(
            "(g3) both arms end in Br",
            Box::new(|c, o, a| {
                let mut v = the_loop_form(c, o, a);
                if let Some(Ins::If(t, _)) = v.last_mut() {
                    *t = vec![Ins::Br]
                }
                v
            }),
            Layer::Walk,
        );
        add(
            "(g4) a Br that is not last in its arm",
            Box::new(|c, o, a| {
                let mut v = the_loop_form(c, o, a);
                if let Some(Ins::If(_, e)) = v.last_mut() {
                    e.push(konst(7))
                }
                v
            }),
            Layer::Shape,
        );
    }
    // (c) a Br for a non-tail self call
    ms.push((
        "factorial: (c1) Call(0) -> [Set0, Br], `mul` after it dropped".into(),
        Box::new(factorial),
        Box::new(|c, o, _| replace_nth_call(c, o, &mut 0, &[set(0), Ins::Br], true)),
        Layer::Shape,
    ));
    ms.push((
        "factorial: (c2) Call(0) -> [Set0, Br], `mul` left after it".into(),
        Box::new(factorial),
        Box::new(|c, o, _| replace_nth_call(c, o, &mut 0, &[set(0), Ins::Br], false)),
        Layer::Walk,
    ));
    ms.push((
        "factorial: (c3) Call(0) -> Br alone, rest dropped".into(),
        Box::new(factorial),
        Box::new(|c, o, _| replace_nth_call(c, o, &mut 0, &[Ins::Br], true)),
        Layer::Shape,
    ));
    for (k, which, c4) in [(0usize, "first", Layer::Walk), (1, "second", Layer::Shape)] {
        ms.push((
            format!("fib: (c4) {which} Call(0) -> [Set0, Br], rest of the arm dropped"),
            Box::new(fib),
            Box::new(move |c, o, _| replace_nth_call(c, o, &mut { k }, &[set(0), Ins::Br], true)),
            c4,
        ));
        ms.push((
            format!("fib: (c5) {which} Call(0) -> [Set0, Br], rest of the arm left"),
            Box::new(fib),
            Box::new(move |c, o, _| replace_nth_call(c, o, &mut { k }, &[set(0), Ins::Br], false)),
            Layer::Walk,
        ));
    }
    // (e) Br with a callee call pending, on the module whose loop argument comes from a call to position 0
    let tp = || -> Build { Box::new(tail_recursive_loop_with_pap_producing_root_self_call_arg) };
    ms.push((
        "tail_pap: (e1) both Calls dropped, [Br] after the callee's arguments (callee pending)".into(),
        tp(),
        Box::new(|c, o, _| replace_nth_call(&strip_call(c, 0), o, &mut 0, &[Ins::Br], true)),
        Layer::Shape,
    ));
    ms.push((
        "tail_pap: (e4) the code still calls position 0 (in the then arm, value-equal), the else arm is [.. callee args, Br]".into(),
        tp(),
        Box::new(|_, _, _| {
            vec![
                get(0),
                konst(0),
                row("le"),
                Ins::If(vec![konst(0), get(0), Ins::Call(0)], vec![konst(0), get(0), konst(1), row("sub"), Ins::Br]),
            ]
        }),
        Layer::Shape,
    ));
    ms.push((
        "tail_pap: (e2) callee Call kept, the self Call -> [Br] (no Set)".into(),
        tp(),
        Box::new(|c, o, _| loop_form(c, o, &[])),
        Layer::Shape,
    ));
    ms.push((
        "tail_pap: (e3) callee Call dropped, its pending args' top written by Set0, then Br (value-equal, callee skipped)".into(),
        tp(),
        Box::new(|c, o, _| loop_form(&strip_call(c, 0), o, &[0])),
        Layer::Shape,
    ));
    ms.push((
        "tail_pap: (d3) Set to slot 1, a padding slot of the width-2 frame (entry arity 1), then Br".into(),
        tp(),
        Box::new(|c, o, _| loop_form(c, o, &[1])),
        Layer::Shape,
    ));
    assert_eq!(ms.len(), 54, "the O3 spike's mutants");
    let mut bad = vec![];
    for (label, b, f, want) in &ms {
        let (v, code) = run(b, &**f);
        println!("{label}\n    verdict {}\n    code {}", clip(format!("{v:?}")), clip(format!("{code:?}")));
        match &v {
            Verdict::Rejected(l, _) if l == want => {}
            Verdict::Rejected(l, _) => bad.push(format!("{label}: rejected at {l:?}, expected {want:?}")),
            other => bad.push(format!("{label}: NOT REJECTED: {}", clip(format!("{other:?}")))),
        }
    }
    assert!(bad.is_empty(), "unexpected verdicts:\n{}", bad.join("\n"));
}

/// A tail self call whose argument holds a non-tail self call: only the tail one becomes the loop form.
#[test]
fn a_mixed_self_call_body_is_accepted() {
    let b: Build = Box::new(|s| source(s, "rec f n acc = if n <= 0 then acc else f (n - 1) (acc + f (n - 1) 0)"));
    let (v, code) = run(&b, &the_loop_form);
    assert!(format!("{code:?}").contains("Br"), "{code:?}");
    assert!(format!("{code:?}").contains("Call"), "the non-tail self call stays a Call: {code:?}");
    assert_eq!(v, Verdict::Accepted);
}

/// A no-op `[get 0, Set 0]` before the loop form: the `Set`'s frame rebuild reduces.
#[test]
fn a_no_op_set_prelude_is_accepted() {
    let b: Build = Box::new(|s| source(s, SUM));
    let (v, _) = run(&b, &|c, o, a| [vec![get(0), set(0)], the_loop_form(c, o, a)].concat());
    assert_eq!(v, Verdict::Accepted);
}
