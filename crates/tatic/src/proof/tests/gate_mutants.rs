//! Goal 4's S2c mutant set: mutated bodies of the covered terms are `Rejected` at a named layer, and where the mutant
//! has a statement of its own the kernel refuses the positive case's proof against it (a forged proof).

use tatic_kernel::scoped;
use tatic_wasm::encoding::holds;
use tatic_wasm::machine::{Class, Entry, Ins, Table};

use super::baseline::census;
use super::gate::{big, compiled, the_five};
use crate::jit::compile::{compile_specialised, CompiledFragment};
use crate::lang::term::{Hash, TermStore};
use crate::proof::gate::{build, gate, Layer, Verdict};
use crate::support::samples::{capturing_closure_loop, factorial, fib, non_tail_closure_carrying_recursion, source, straight_line, twice};
use crate::testing::ins_mutate::{arities, count_call_sites, edit_call_site, mutate, with_entry, with_record};
use Layer::{Shape, Walk};

type Build = Box<dyn Fn(&mut TermStore) -> Hash>;
/// The term the gate sees, its hash and its compiled fragment, built afresh at each call.
pub(super) type Subject<'a> = &'a dyn Fn() -> (TermStore, Hash, CompiledFragment);
type Edit = Box<dyn Fn(&Ins) -> Option<Ins>>;

/// A 2-to-1 row instruction.
fn row(name: &'static str) -> Ins {
    Ins::Row { name, operand: 0 }
}

/// A `local.get` row instruction.
pub(super) fn get(i: i64) -> Ins {
    Ins::Row { name: "local.get", operand: i }
}

/// A `const` row instruction.
pub(super) fn konst(v: i64) -> Ins {
    Ins::Row { name: "const", operand: v }
}

pub(super) fn clip(s: String) -> String {
    s.chars().take(300).collect()
}

/// `v` is `Rejected` at `layer`.
pub(super) fn rejected_by(v: Verdict, layer: Layer, what: &str) {
    match &v {
        Verdict::Rejected(l, why) if *l == layer => println!("{what}: {l:?}: {}", clip(why.clone())),
        other => panic!("{what}: wanted Rejected({layer:?}), got {}", clip(format!("{other:?}"))),
    }
}

/// The positive case's proof does not prove the mutant's statement. Only for a mutant `build` gives a statement of its
/// own: a mutant `build` refuses has nothing to forge against and is asserted with `rejected_by(.., Layer::Shape, ..)`.
pub(super) fn forged_rejected(table: &Table, pos: (&TermStore, Hash, &CompiledFragment), mutant: (&TermStore, Hash, &CompiledFragment)) {
    scoped(|| {
        let (stmt, proof) = build(table, pos.0, pos.1, pos.2).expect("the positive case builds");
        let proof = proof.expect("the generator proves the positive case");
        let (mutant_stmt, _) = build(table, mutant.0, mutant.1, mutant.2).unwrap_or_else(|v| panic!("build refused the mutant: {v:?}"));
        assert!(stmt != mutant_stmt, "the mutant's statement should differ from the positive case's");
        assert!(holds(&proof, &mutant_stmt).is_err(), "the positive proof was accepted against the mutant's statement");
    })
}

/// One mutant of the subject's entry body: `Rejected` at `layer` by the gate, and forged-rejected where `build` gives it
/// a statement (a mutant `build` refuses must be a shape rejection).
fn check(label: &str, subject: Subject, code: Vec<Ins>, layer: Layer) {
    check_frag(label, subject, with_entry(subject().2, |e| Entry { code, ..e }), layer)
}

/// `check` for a mutant module (any record or source edited), given whole. A mutant `build` refuses at the shape or
/// pairing check has no statement to forge against.
pub(super) fn check_frag(label: &str, subject: Subject, mutant: CompiledFragment, layer: Layer) {
    let (s, h, frag) = subject();
    let label = label.to_string();
    big(move || {
        let table = tatic_wasm::wasm::table();
        rejected_by(gate(table, &s, h, &mutant), layer, &label);
        match scoped(|| build(table, &s, h, &mutant).map(|_| ())) {
            Ok(()) => forged_rejected(table, (&s, h, &frag), (&s, h, &mutant)),
            Err(Verdict::Rejected(l @ (Shape | Layer::Pairing), _)) => assert_eq!(layer, l, "{label}"),
            Err(other) => panic!("{label}: build refused with {}", clip(format!("{other:?}"))),
        }
    })
}

/// Goal 1's five terms and factorial (spec S2c "Done when").
fn the_six() -> Vec<(&'static str, Build)> {
    let mut v: Vec<(&'static str, Build)> = the_five().into_iter().map(|(n, b, _)| (n, b)).collect();
    v.push(("factorial", Box::new(factorial)));
    v
}

fn code_of(subject: Subject) -> Vec<Ins> {
    subject().2.entry().code.clone()
}

#[test]
fn gate_rejects_mutations() {
    type Mutation = (&'static str, Edit, &'static [(&'static str, Layer)]);
    let mutations: Vec<Mutation> = vec![
        ("swap if arms", Box::new(|i| match i { Ins::If(t, e) => Some(Ins::If(e.clone(), t.clone())), _ => None }), &[("straight_line", Walk), ("factorial", Walk)]),
        ("lt -> lt_u", Box::new(|i| (i == &row("lt")).then_some(row("lt_u"))), &[("straight_line", Walk)]),
        (
            "add -> sub",
            Box::new(|i| (i == &row("add")).then_some(row("sub"))),
            &[("inc", Walk), ("doubling_4", Walk), ("straight_line", Walk), ("a_capturing_closure_call", Walk), ("a_pap_capturing", Walk)],
        ),
        ("mul -> add", Box::new(|i| (i == &row("mul")).then_some(row("add"))), &[("straight_line", Walk), ("factorial", Walk)]),
        (
            "const v -> const v + 1",
            Box::new(|i| match i {
                Ins::Row { name: "const", operand } => Some(konst(operand.wrapping_add(1))),
                _ => None,
            }),
            &[("inc", Walk), ("straight_line", Walk), ("a_capturing_closure_call", Walk), ("a_pap_capturing", Walk), ("factorial", Walk)],
        ),
        // a slot past the function's own width is a shape rejection (D2); on the two-parameter term it is another slot
        (
            "local.get 0 -> 1",
            Box::new(|i| (i == &get(0)).then_some(get(1))),
            &[("inc", Shape), ("doubling_4", Shape), ("straight_line", Walk), ("a_capturing_closure_call", Shape), ("a_pap_capturing", Shape), ("factorial", Shape)],
        ),
        ("local.get 1 -> 0", Box::new(|i| (i == &get(1)).then_some(get(0))), &[("straight_line", Walk)]),
    ];
    for (name, b) in the_six() {
        let subject = || compiled(&*b);
        let code = code_of(&subject);
        let (s, h, frag) = subject();
        assert_eq!(big(move || gate(tatic_wasm::wasm::table(), &s, h, &frag)), Verdict::Accepted, "{name}: the unmutated body should pass");
        for (what, f, applies) in &mutations {
            let mutated = mutate(&code, &**f);
            let layer = applies.iter().find(|(n, _)| *n == name).map(|(_, l)| *l);
            assert_eq!(mutated != code, layer.is_some(), "{name}: '{what}' {} the body", if layer.is_some() { "did not change" } else { "changed" });
            if let Some(layer) = layer {
                check(&format!("{name}: {what}"), &subject, mutated, layer);
            }
        }
        check(&format!("{name}: a Raw line"), &subject, [code.as_slice(), &[Ins::Raw("nop".into())]].concat(), Shape);
    }
}


/// `code` with the first instruction `f` maps replaced inside the last top-level `If`'s then arm (the base case).
fn in_then_arm(code: &[Ins], f: &dyn Fn(&Ins) -> Option<Ins>) -> Vec<Ins> {
    let mut out = code.to_vec();
    let Some(Ins::If(t, _)) = out.iter_mut().rev().find(|i| matches!(i, Ins::If(..))) else { panic!("no If in {code:?}") };
    *t = mutate(t, f);
    out
}

/// A term built from source text.
fn src(text: &'static str) -> Build {
    Box::new(move |s: &mut TermStore| source(s, text))
}

const SUM: &str = "rec f n acc = if n <= 0 then acc else f (n - 1) (acc + n)";

/// An edit of one call site: the block, the call's index and the argument ranges; false when it does not apply.
pub(super) type SiteEdit<'a> = &'a dyn Fn(&mut Vec<Ins>, usize, &[std::ops::Range<usize>]) -> bool;

/// Each site of `Call(0)` in the subject's body edited by `edit` (where it applies) is `Rejected` at `layer`; returns
/// how many sites it applied to.
fn at_each_site(name: &str, what: &str, subject: Subject, layer: Layer, edit: SiteEdit) -> usize {
    let (_, _, frag) = subject();
    let (code, arities) = (frag.entry().code.clone(), arities(&frag));
    let mut applied = 0;
    for site in 0..count_call_sites(&code, 0) {
        let changed = std::cell::Cell::new(false);
        let mutated = edit_call_site(&code, site, 0, &arities, tatic_wasm::wasm::table(), &|b, i, args| changed.set(edit(b, i, args)));
        if changed.get() {
            assert_ne!(mutated, code, "{name}: '{what}' at site {site} did not change the body");
            check(&format!("{name}: {what} (site {site})"), subject, mutated, layer);
            applied += 1;
        }
    }
    applied
}

/// A `local.get` index changed in the site's arguments: slot `i` read as slot `(i + 1) % 2`.
fn arg_local_get_changed(b: &mut Vec<Ins>, _call: usize, args: &[std::ops::Range<usize>]) -> bool {
    let Some(at) = args.iter().flat_map(|r| r.clone()).find(|j| matches!(&b[*j], Ins::Row { name: "local.get", .. })) else { return false };
    let Ins::Row { operand, .. } = &b[at] else { unreachable!() };
    b[at] = get((operand + 1) % 2);
    true
}

pub(super) fn args_swapped(b: &mut Vec<Ins>, _call: usize, args: &[std::ops::Range<usize>]) -> bool {
    let [first, second, ..] = args else { return false };
    let (x, y) = (b[first.clone()].to_vec(), b[second.clone()].to_vec());
    assert_eq!(first.end, second.start, "adjacent arguments");
    b.splice(first.start..second.end, y.into_iter().chain(x));
    true
}

pub(super) fn arg_instruction_dropped(b: &mut Vec<Ins>, _call: usize, args: &[std::ops::Range<usize>]) -> bool {
    b.remove(args.last().expect("an argument").end - 1);
    true
}

pub(super) fn arg_instruction_added(b: &mut Vec<Ins>, call: usize, _args: &[std::ops::Range<usize>]) -> bool {
    b.insert(call, konst(0));
    true
}

fn call_dropped(b: &mut Vec<Ins>, call: usize, _args: &[std::ops::Range<usize>]) -> bool {
    b.remove(call);
    true
}

/// `b` compiled and mapped back to the `Call` form (`loop_form::call_form_frag`): the lowering emits a tail self call
/// as the loop form, and these mutators edit `Call` sites.
fn call_formed(b: &Build) -> (TermStore, Hash, CompiledFragment) {
    let (s, h, f) = compiled(&**b);
    (s, h, super::loop_form::call_form_frag(f))
}

#[test]
fn self_call_site_mutants_are_rejected() {
    let terms: [(&str, Build, usize); 3] =
        [("factorial", Box::new(factorial), 1), ("fib", Box::new(fib), 1), ("capturing_closure_loop", Box::new(capturing_closure_loop), 2)];
    let mut applied = std::collections::BTreeMap::<&str, usize>::new();
    for (name, b, arity) in &terms {
        let subject = || call_formed(b);
        let mut run = |what: &'static str, layer: Layer, edit: SiteEdit| {
            *applied.entry(what).or_default() += at_each_site(name, what, &subject, layer, edit);
        };
        // slot 1 is past a one-parameter function's frame: a shape rejection; on two parameters it is another slot
        run("an argument's local.get index changed", if *arity == 1 { Shape } else { Walk }, &arg_local_get_changed);
        run("two arguments swapped", Walk, &args_swapped);
        // no statement exists for these two: the shape check refuses the stack they leave
        run("an argument instruction dropped", Shape, &arg_instruction_dropped);
        run("an argument instruction added", Shape, &arg_instruction_added);
        // two words left standing is a shape error; one word is a well-formed stack that parts from the source
        run("the Call dropped", if *arity == 2 { Shape } else { Walk }, &call_dropped);
    }
    // every mutator applied (the swap only at the two-parameter loop's one site; the others at the four sites)
    assert_eq!(applied["two arguments swapped"], 1);
    for k in ["an argument's local.get index changed", "an argument instruction dropped", "an argument instruction added", "the Call dropped"] {
        assert_eq!(applied[k], 4, "{k}");
    }
}

#[test]
fn an_if_arm_swap_is_rejected() {
    for (name, b) in [("straight_line", Box::new(straight_line) as Build), ("factorial", Box::new(factorial))] {
        let subject = || compiled(&*b);
        let swapped = mutate(&code_of(&subject), &|i| match i {
            Ins::If(t, e) => Some(Ins::If(e.clone(), t.clone())),
            _ => None,
        });
        check(&format!("{name}: if arms swapped"), &subject, swapped, Walk);
    }
}

/// The no-loop spike's control list (doc 15, "Tail self-calls as `return_call`, with no `loop` or `br`: a spike"), minus
/// its `return_call`-for-`call` mutant: the records carry `Call` only and the printer picks the form, so there is no such
/// mutant here (`call` for `return_call` proves, as it should). The subject is mapped back to the `Call` form
/// (`call_formed`); the shipped loop form's mutants are in `loop_form.rs`.
#[test]
fn no_loop_spike_controls_are_rejected() {
    let terms: [(&str, Build, usize); 3] = [("sum loop", src(SUM), 2), ("factorial", Box::new(factorial), 1), ("fib", Box::new(fib), 1)];
    for (name, b, arity) in &terms {
        let subject = || call_formed(b);
        let code = code_of(&subject);
        let holds_row = |r: &str| format!("{code:?}").contains(&format!("name: \"{r}\""));
        let mut seen = 0;
        let mut ctl = |what: &str, mutated: Vec<Ins>, layer: Layer| {
            assert_ne!(mutated, code, "{name}: '{what}' did not change the body");
            check(&format!("{name}: {what}"), &subject, mutated, layer);
            seen += 1;
        };
        // operator swaps, and `<=` / `<` exchanged
        for (from, to) in [("add", "sub"), ("sub", "add"), ("mul", "add"), ("le", "lt"), ("lt", "le")] {
            if holds_row(from) {
                ctl(&format!("{from} -> {to}"), mutate(&code, &|i| (i == &row(from)).then_some(row(to))), Walk);
            }
        }
        ctl("branches swapped", mutate(&code, &|i| match i { Ins::If(t, e) => Some(Ins::If(e.clone(), t.clone())), _ => None }), Walk);
        // a wrong local.get in the condition (the code before the If)
        let cond_end = code.iter().position(|i| matches!(i, Ins::If(..))).unwrap();
        let at = (0..cond_end).find(|j| matches!(&code[*j], Ins::Row { name: "local.get", .. })).unwrap();
        let mut wrong_cond = code.clone();
        wrong_cond[at] = get(1);
        ctl("a wrong local.get in the condition", wrong_cond, if *arity == 1 { Shape } else { Walk });
        // a wrong base case
        let wrong_base = in_then_arm(&code, &|i| match i {
            Ins::Row { name: "const", operand } => Some(konst(operand + 1)),
            Ins::Row { name: "local.get", .. } => Some(konst(0)),
            _ => None,
        });
        ctl("a wrong base case", wrong_base, Walk);
        assert!(seen >= 5, "{name}: only {seen} controls applied");
        // a call's constants off by one and by two (the first constant in a site's arguments), a wrong local.get in an
        // argument, and the call dropped
        for by in [1, 2] {
            let off = |b: &mut Vec<Ins>, _: usize, args: &[std::ops::Range<usize>]| {
                let Some(at) = args.iter().flat_map(|r| r.clone()).find(|j| matches!(&b[*j], Ins::Row { name: "const", .. })) else { return false };
                let Ins::Row { operand, .. } = &b[at] else { unreachable!() };
                b[at] = konst(operand + by);
                true
            };
            assert!(at_each_site(name, &format!("a call constant off by {by}"), &subject, Walk, &off) >= 1, "{name}: no call constant to move");
        }
        let layer = if *arity == 1 { Shape } else { Walk };
        assert!(at_each_site(name, "a wrong local.get in a call argument", &subject, layer, &arg_local_get_changed) >= 1);
        let dropped = if *arity == 2 { Shape } else { Walk };
        assert!(at_each_site(name, "the call dropped", &subject, dropped, &call_dropped) >= 1);
    }
}

/// The census term `i` as the gate sees it; `None` when it does not compile.
fn census_subject(i: usize) -> Option<(TermStore, Hash, CompiledFragment)> {
    let (_, s, h) = census().swap_remove(i);
    let c = compile_specialised(&s, h)?;
    Some(match c.specialised {
        Some((s2, h2)) => (s2, h2, c.frag),
        None => (s, h, c.frag),
    })
}

/// For each Word and Bit row `r` of the wasm table that has a source operator (not `shl`, `shr_u`, `or`), plus `lt_u`: `r` replaced by another row of its class in a covered term that
/// holds it is `Rejected`, forged too. The carriers are pinned census terms (checked here to hold `r` and be `Accepted`),
/// not "the first covered term that holds `r`": that rule picks `redundant_arithmetic_recursion` for `add`, whose
/// `x + 0` swapped to `x - 0` is the same function, which the gate neither accepts nor refuses within minutes (PARKED.md,
/// "the gate's time on an equivalent operator swap"). `lt_u` has no source operator, so its mutant is the code-level swap
/// `lt` to `lt_u` on `straight_line` (as v0.7 does), and no covered census term holds `eq`, so it takes a term local to
/// this test, swapped `eq` to `lt`.
#[test]
fn every_row_has_an_operator_swap_mutant() {
    let t = tatic_wasm::wasm::table();
    // `shl`, `shr_u` and `or` have no `PrimOp`, so no census term holds them and `carrier` cannot build a mutant; the swap
    // target is the next row among the carried ones, so each swap pair stays what it was before they joined the table
    let uncarried = ["shl", "shr_u", "or"];
    for r in uncarried {
        assert_eq!(t.row(r).map(|row| row.class), Some(Class::Word), "{r} is a Word row");
        assert!(crate::lang::term::PrimOp::ALL.iter().all(|p| p.name() != r), "{r} has a PrimOp now: give it a carrier");
    }
    let rows: Vec<&str> =
        t.names().into_iter().filter(|n| matches!(t.row(n).unwrap().class, Class::Word | Class::Bit) && !uncarried.contains(n)).collect();
    assert_eq!(rows, ["add", "sub", "mul", "mod", "lt", "le", "eq", "lt_u"], "no row built before is skipped");
    let next = |r: &str| {
        let class = t.row(r).unwrap().class;
        let same: Vec<&str> = rows.iter().copied().filter(|n| t.row(n).unwrap().class == class).collect();
        same[(same.iter().position(|n| *n == r).unwrap() + 1) % same.len()]
    };
    let carrier = |r: &str| -> Option<&'static str> {
        match r {
            "add" | "lt" => Some("fib"),
            "sub" | "mul" | "le" => Some("factorial"),
            "mod" => Some("gcd"),
            _ => None,
        }
    };
    let local: Build = src(r"\a b. if a == b then a else b");
    let straight: Build = Box::new(straight_line);
    for r in &rows {
        let (to, from) = (next(r), *r);
        match (carrier(r), *r) {
            (_, "lt_u") => {
                let subject = || compiled(&*straight);
                let mutated = mutate(&code_of(&subject), &|i| (i == &row("lt")).then_some(row("lt_u")));
                check("straight_line: lt -> lt_u", &subject, mutated, Walk);
            }
            (Some(name), _) => {
                let i = census().iter().position(|(n, ..)| *n == name).expect("a census term");
                let subject = || census_subject(i).unwrap();
                let code = code_of(&subject);
                assert!(format!("{code:?}").contains(&format!("name: \"{from}\"")), "{name} holds {from}");
                let (s, h, frag) = subject();
                assert_eq!(big(move || gate(tatic_wasm::wasm::table(), &s, h, &frag)), Verdict::Accepted, "{name} is covered");
                let mutated = mutate(&code, &|ins| (ins == &row(from)).then_some(row(to)));
                check(&format!("{name}: {from} -> {to}"), &subject, mutated, Walk);
            }
            (None, "eq") => {
                let subject = || compiled(&*local);
                let mutated = mutate(&code_of(&subject), &|ins| (ins == &row("eq")).then_some(row("lt")));
                check("a == b term: eq -> lt", &subject, mutated, Walk);
            }
            (None, other) => panic!("no carrier for the row {other}"),
        }
    }
}

#[test]
fn real_term_controls_are_rejected() {
    for (name, b, from, to) in [("factorial", Box::new(factorial) as Build, "mul", "add"), ("fib", Box::new(fib), "add", "sub")] {
        let subject = || compiled(&*b);
        let mutated = mutate(&code_of(&subject), &|i| (i == &row(from)).then_some(row(to)));
        check(&format!("{name}: {from} -> {to}"), &subject, mutated, Walk);
    }
}

/// The kernel negative for a self-call term: factorial's proof is not a proof of fib's statement.
#[test]
fn factorials_proof_does_not_prove_fibs_statement() {
    let ((sf, hf, ff), (sb, hb, fb)) = (compiled(&factorial), compiled(&fib));
    big(move || {
        scoped(|| {
            let table = tatic_wasm::wasm::table();
            let (_, proof) = build(table, &sf, hf, &ff).expect("factorial builds");
            let (fib_stmt, _) = build(table, &sb, hb, &fb).expect("fib builds");
            assert!(holds(&proof.expect("factorial's proof"), &fib_stmt).is_err());
        })
    });
}

/// `code` with `code[at..at + expect.len()]` (which must be `expect`) replaced by `with`.
fn splice_at(code: &[Ins], at: usize, expect: &[Ins], with: &[Ins]) -> Vec<Ins> {
    assert_eq!(&code[at..at + expect.len()], expect, "the edit's site moved: {code:?}");
    [&code[..at], with, &code[at + expect.len()..]].concat()
}

/// `code`'s last top-level `If`, its else arm rewritten by `f`.
fn in_else(code: &[Ins], f: impl FnOnce(&[Ins]) -> Vec<Ins>) -> Vec<Ins> {
    let (head, last) = code.split_at(code.len() - 1);
    let Ins::If(t, e) = &last[0] else { panic!("the last instruction is not an If: {code:?}") };
    [head, &[Ins::If(t.clone(), f(e))]].concat()
}

fn i32_const0() -> Ins {
    Ins::Row { name: "i32.const", operand: 0 }
}

/// Mutants of the closure convention on `non_tail_closure_carrying_recursion` (entry `$c2`, the recursion `$c0`, the
/// closure `$c1`; the entry packs the closure word as `i32.const 0; extend; konst 32; shl; konst 1; or`).
#[test]
fn closure_convention_mutants_are_rejected_on_the_carrying_recursion() {
    let subject = || compiled(&non_tail_closure_carrying_recursion);
    let (_, _, frag) = subject();
    let entry = frag.entry().code.clone();
    assert_eq!(frag.entry_pos, 2);
    let (pack, or, tail) = ([i32_const0(), row("extend"), konst(32), row("shl"), konst(1)], row("or"), 5);

    // index off by one: the `konst 1` before `or` (entry position 5) becomes `konst 2`
    assert_eq!(entry[tail + 1], or);
    check("index off by one", &subject, splice_at(&entry, tail, &[konst(1)], &[konst(2)]), Walk);

    // halves swapped: positions 1 and 5 exchanged (`konst 1` first as the environment half, `i32.const 0` the index)
    assert_eq!(&entry[1..6], &pack);
    let swapped = splice_at(&entry, 1, &pack, &[konst(1), row("extend"), konst(32), row("shl"), i32_const0()]);
    check("halves swapped", &subject, swapped, Walk);

    // closure body: `$c1`'s `konst 1` (position 1 of its code) becomes `konst 2`
    let c1 = with_record(subject().2, 1, |e| Entry { code: splice_at(&e.code, 1, &[konst(1)], &[konst(2)]), ..e });
    check_frag("closure body changed", &subject, c1, Walk);

    // argument replaced: in `$c0`'s else arm the closure call's argument, position 9, `get 2` becomes `get 0`
    let c0 = with_record(subject().2, 0, |e| Entry { code: in_else(&e.code, |a| splice_at(a, 9, &[get(2)], &[get(0)])), ..e });
    check_frag("argument replaced", &subject, c0, Walk);

    // closure call dropped: in `$c0`'s else arm positions 10..13, `get 1; wrap; call_indirect 1`, become `add`
    let drop = [get(1), row("wrap"), Ins::CallIndirect(1)];
    let c0 = with_record(subject().2, 0, |e| Entry { code: in_else(&e.code, |a| splice_at(a, 10, &drop, &[row("add")])), ..e });
    check_frag("closure call dropped", &subject, c0, Layer::Pairing);
}

/// `twice` (`\f x. f (f x)`) with one of its two closure calls gone: the inner call's `get 0; wrap; call_indirect 1`
/// (entry positions 9..12) becomes `add`, folding the inner call's environment half and argument into one word.
#[test]
fn a_twice_with_one_closure_call_is_rejected() {
    let subject = || compiled(&twice);
    let entry = subject().2.entry().code.clone();
    let inner = [get(0), row("wrap"), Ins::CallIndirect(1)];
    let mutant = with_entry(subject().2, |e| Entry { code: splice_at(&entry, 9, &inner, &[row("add")]), ..e });
    let (s, h, _) = subject();
    // `twice`'s dynamic set is empty, so every closure call answers `z` on both sides and the mutant is unobservable in
    // the closed module: its statement is `def_eq` to the positive one, so there is no forgery to refuse and the
    // walk's lockstep refusal is the only layer here
    big(move || {
        let table = tatic_wasm::wasm::table();
        rejected_by(gate(table, &s, h, &mutant), Walk, "one closure call of two");
        scoped(|| {
            let (pos, _) = build(table, &s, h, &subject().2).expect("the positive case builds");
            let (neg, _) = build(table, &s, h, &mutant).expect("the mutant builds");
            assert!(pos != neg && tatic_kernel::def_eq(&pos, &neg), "the mutant should differ only up to conversion");
        })
    });
}
