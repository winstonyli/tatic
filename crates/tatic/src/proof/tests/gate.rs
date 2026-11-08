//! The straight-line gate (`proof::gate`): the fragment terms' emitted bodies are accepted, mutated bodies are
//! rejected (spec Goal 2), and `in_fragment` keeps out what the gate does not cover.

use tatic_wasm::ops::Op;
use tatic_wasm::wasm::Ins;

use crate::jit::compile::{compile_specialised, CompiledFragment};
use crate::lang::term::{Hash, PrimOp, TermStore};
use crate::proof::gate::{gate, in_fragment, statement};
use crate::support::samples::{a_capturing_closure_call, a_pap_capturing, factorial, inc, source, straight_line, twice};
use crate::testing::ins_mutate::mutate;
use crate::testing::test_corpus::doubling;

/// The term the gate sees (the specialised one, if `specialise` changed it) and its compiled fragment.
fn compiled(build: &dyn Fn(&mut TermStore) -> Hash) -> (TermStore, Hash, CompiledFragment) {
    let mut s = TermStore::new();
    let h = build(&mut s);
    let c = compile_specialised(&s, h).expect("compiles");
    match c.specialised {
        Some((s2, h2)) => (s2, h2, c.frag),
        None => (s, h, c.frag),
    }
}

/// Goal 1's five terms, by name, with their arity.
fn the_five() -> Vec<(&'static str, Box<dyn Fn(&mut TermStore) -> Hash>, usize)> {
    vec![
        ("inc", Box::new(inc), 1),
        ("doubling_4", Box::new(|s: &mut TermStore| doubling(s, 4)), 1),
        ("straight_line", Box::new(straight_line), 2),
        ("a_capturing_closure_call", Box::new(a_capturing_closure_call), 1),
        ("a_pap_capturing", Box::new(a_pap_capturing), 1),
    ]
}

#[test]
fn gate_accepts_the_fragment_table() {
    let mut table = the_five();
    table.push(("a - b", Box::new(|s: &mut TermStore| source(s, r"\a b. a - b")), 2));
    table.push(("third", Box::new(|s: &mut TermStore| source(s, r"\a b c. c")), 3));
    // at the tree bound: 2^8 nodes
    table.push(("doubling_7", Box::new(|s: &mut TermStore| doubling(s, 7)), 1));
    table.push((
        "a + MIN",
        Box::new(|s: &mut TermStore| {
            let (a, m) = (s.var(0), s.lit(i64::MIN));
            let e = s.prim(PrimOp::Add, a, m);
            s.abs(e)
        }),
        1,
    ));
    for (name, build, arity) in table {
        let (s, h, frag) = compiled(&*build);
        assert!(in_fragment(&s, h, arity), "{name} should be in the fragment");
        assert!(gate(&s, h, arity, frag.entry()), "{name}: the gate should accept its emitted body");
    }
}

#[test]
fn gate_rejects_mutations() {
    type Mutation = (&'static str, Box<dyn Fn(&Ins) -> Option<Ins>>, &'static [&'static str]);
    let all: &[&str] = &["inc", "doubling_4", "straight_line", "a_capturing_closure_call", "a_pap_capturing"];
    let mutations: Vec<Mutation> = vec![
        ("swap if arms", Box::new(|i| match i { Ins::If(t, e) => Some(Ins::If(e.clone(), t.clone())), _ => None }), &["straight_line"]),
        ("LtS -> LtU", Box::new(|i| (i == &Ins::Op(Op::LtS)).then_some(Ins::Op(Op::LtU))), &["straight_line"]),
        ("Add -> Sub", Box::new(|i| (i == &Ins::Op(Op::Add)).then_some(Ins::Op(Op::Sub))), all),
        ("Mul -> Add", Box::new(|i| (i == &Ins::Op(Op::Mul)).then_some(Ins::Op(Op::Add))), &["straight_line"]),
        (
            "Push(v) -> Push(v + 1)",
            Box::new(|i| match i { Ins::Push(v) => Some(Ins::Push(v.wrapping_add(1))), _ => None }),
            &["inc", "straight_line", "a_capturing_closure_call", "a_pap_capturing"],
        ),
        ("LocalGet 0 -> 1", Box::new(|i| (i == &Ins::LocalGet(0)).then_some(Ins::LocalGet(1))), &["straight_line"]),
        ("LocalGet 1 -> 0", Box::new(|i| (i == &Ins::LocalGet(1)).then_some(Ins::LocalGet(0))), &["straight_line"]),
    ];
    for (name, build, arity) in the_five() {
        let (s, h, frag) = compiled(&*build);
        let code = frag.entry();
        assert!(gate(&s, h, arity, code), "{name}: the unmutated body should pass");
        for (what, f, applies) in &mutations {
            // arity-1 terms are skipped for LocalGet: another index reads an unbound frame slot (spec Goal 2)
            if what.starts_with("LocalGet") && arity < 2 {
                continue;
            }
            let mutated = mutate(code, &**f);
            let changed = mutated != code;
            let applies = applies.contains(&name);
            assert_eq!(changed, applies, "{name}: '{what}' {} the body", if changed { "changed" } else { "did not change" });
            if changed {
                assert!(!gate(&s, h, arity, &mutated), "{name}: the gate accepted '{what}': {mutated:?}");
            }
        }
        let Ins::Loop(body) = &code[0] else { panic!("{name}: entry is not a Loop") };
        let with_raw = vec![Ins::Loop([body.clone(), vec![Ins::Raw("nop".into())]].concat())];
        assert!(!gate(&s, h, arity, &with_raw), "{name}: the gate accepted a Raw line");
    }
}

/// `(build ms, check ms, accepted)` for one gate run, best of `reps`.
fn time_gate(s: &TermStore, h: Hash, arity: usize, code: &[Ins], fuel: usize, reps: usize) -> (f64, f64, bool) {
    let mut best = (f64::MAX, f64::MAX, true);
    for _ in 0..reps {
        let (b, c, ok) = tatic_kernel::scoped(|| {
            let t0 = std::time::Instant::now();
            let (p, st) = statement(s, h, arity, code, fuel);
            let t1 = std::time::Instant::now();
            let ok = tatic_wasm::encoding::holds(&p, &st).is_ok();
            ((t1 - t0).as_secs_f64() * 1e3, t1.elapsed().as_secs_f64() * 1e3, ok)
        });
        best = (best.0.min(b), best.1.min(c), best.2 && ok);
    }
    best
}

/// Section 8's measurements: fuel 1 against the bare body, `doubling(d)` up the tree cap, and `Mul`. Prints
/// `name build_ms check_ms ok` lines; run through the wrapper.
#[test]
#[ignore]
fn measure_gate_costs() {
    let (s, h, frag) = compiled(&inc);
    let code = frag.entry();
    let Ins::Loop(body) = &code[0] else { panic!("entry is not a Loop") };
    for (name, c, fuel) in [("inc fuel1", code, 1), ("inc bare", body.as_slice(), 0)] {
        let (b, k, ok) = time_gate(&s, h, 1, c, fuel, 5);
        println!("{name} {b:.2} {k:.2} {ok}");
    }
    for d in 1..=13u32 {
        let r = std::thread::Builder::new()
            .stack_size(256 << 20)
            .spawn(move || {
                let (s, h, frag) = compiled(&move |s: &mut TermStore| doubling(s, d));
                time_gate(&s, h, 1, frag.entry(), 1, 1)
            })
            .unwrap()
            .join()
            .unwrap();
        println!("doubling_{d} {:.2} {:.2} {}", r.0, r.1, r.2);
        if r.0 + r.1 > 60_000.0 {
            println!("doubling: skipped d > {d} (over 60 s)");
            break;
        }
    }
    for (name, src) in [("mul a b", r"\a b. a * b"), ("mul in an arm", r"\a b. if a < b then a * b else a")] {
        let (s, h, frag) = compiled(&move |s: &mut TermStore| source(s, src));
        let (b, k, ok) = time_gate(&s, h, 2, frag.entry(), 1, 1);
        println!("{name} {b:.2} {k:.2} {ok}");
    }
}

/// `doubling(13)` (the tree cap) on a default-size 2 MB thread. Alone, since an overflow aborts the exe.
#[test]
#[ignore]
fn measure_stack_2mb() {
    let r = std::thread::Builder::new()
        .stack_size(2 << 20)
        .spawn(|| {
            let (s, h, frag) = compiled(&|s: &mut TermStore| doubling(s, 13));
            time_gate(&s, h, 1, frag.entry(), 1, 1)
        })
        .unwrap()
        .join()
        .unwrap();
    println!("doubling_13 on 2 MB {:.2} {:.2} {}", r.0, r.1, r.2);
}

#[test]
fn in_fragment_rejects_the_rest() {
    let cases: Vec<(&str, Box<dyn Fn(&mut TermStore) -> Hash>, usize)> = vec![
        ("factorial (recursive)", Box::new(factorial), 1),
        ("twice (higher-order)", Box::new(twice), 2),
        ("a / b (no table row)", Box::new(|s: &mut TermStore| source(s, r"\a b. a / b")), 2),
        ("an If in an operand", Box::new(|s: &mut TermStore| source(s, r"\a b. 1 + (if a < b then a else b)")), 2),
        (
            "an If in a condition",
            Box::new(|s: &mut TermStore| source(s, r"\a b. if (if a < b then a else b) < 1 then 1 else 0")),
            2,
        ),
        ("arity 0", Box::new(|s: &mut TermStore| source(s, "5")), 0),
        ("doubling_8 (over the tree bound)", Box::new(|s: &mut TermStore| doubling(s, 8)), 1),
        ("\\f. f 1", Box::new(|s: &mut TermStore| source(s, r"\f. f 1")), 1),
    ];
    for (name, build, arity) in cases {
        let mut s = TermStore::new();
        let h = build(&mut s);
        assert!(!in_fragment(&s, h, arity), "{name} should be outside the fragment");
    }
}
