//! The straight-line gate (`proof::gate`): the fragment terms' emitted bodies are accepted, mutated bodies are
//! rejected (spec Goal 2), and `in_fragment` keeps out what the gate does not cover.

use tatic_wasm::machine::Ins;

use crate::jit::compile::{compile_specialised, CompiledFragment};
use crate::jit::shape::wasm_table;
use crate::lang::term::{Hash, PrimOp, TermStore};
use crate::proof::gate::{build, gate, in_fragment};
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

/// A 2-to-1 row instruction.
fn row(name: &'static str) -> Ins {
    Ins::Row { name, operand: 0 }
}

/// A `local.get` row instruction.
fn get(i: i64) -> Ins {
    Ins::Row { name: "local.get", operand: i }
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
    // at the tree bound: 2^13 nodes
    table.push(("doubling_12", Box::new(|s: &mut TermStore| doubling(s, 12)), 1));
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
        assert!(in_fragment(wasm_table(), &s, h, arity), "{name} should be in the fragment");
        assert!(gate(wasm_table(), &s, h, arity, frag.entry().code.as_slice()), "{name}: the gate should accept its emitted body");
    }
}

#[test]
fn gate_rejects_mutations() {
    type Mutation = (&'static str, Box<dyn Fn(&Ins) -> Option<Ins>>, &'static [&'static str]);
    let all: &[&str] = &["inc", "doubling_4", "straight_line", "a_capturing_closure_call", "a_pap_capturing"];
    let mutations: Vec<Mutation> = vec![
        ("swap if arms", Box::new(|i| match i { Ins::If(t, e) => Some(Ins::If(e.clone(), t.clone())), _ => None }), &["straight_line"]),
        ("lt -> lt_u", Box::new(|i| (i == &row("lt")).then_some(row("lt_u"))), &["straight_line"]),
        ("add -> sub", Box::new(|i| (i == &row("add")).then_some(row("sub"))), all),
        ("mul -> add", Box::new(|i| (i == &row("mul")).then_some(row("add"))), &["straight_line"]),
        (
            "const v -> const v + 1",
            Box::new(|i| match i {
                Ins::Row { name: "const", operand } => Some(Ins::Row { name: "const", operand: operand.wrapping_add(1) }),
                _ => None,
            }),
            &["inc", "straight_line", "a_capturing_closure_call", "a_pap_capturing"],
        ),
        ("local.get 0 -> 1", Box::new(|i| (i == &get(0)).then_some(get(1))), &["straight_line"]),
        ("local.get 1 -> 0", Box::new(|i| (i == &get(1)).then_some(get(0))), &["straight_line"]),
    ];
    for (name, build, arity) in the_five() {
        let (s, h, frag) = compiled(&*build);
        let code = frag.entry().code.as_slice();
        assert!(gate(wasm_table(), &s, h, arity, code), "{name}: the unmutated body should pass");
        for (what, f, applies) in &mutations {
            // arity-1 terms are skipped for local.get: another index reads past the frame (spec Goal 2; the shape check
            // that rejects it comes with the call rule)
            if what.starts_with("local.get") && arity < 2 {
                continue;
            }
            let mutated = mutate(code, &**f);
            let changed = mutated != code;
            let applies = applies.contains(&name);
            assert_eq!(changed, applies, "{name}: '{what}' {} the body", if changed { "changed" } else { "did not change" });
            if changed {
                assert!(!gate(wasm_table(), &s, h, arity, &mutated), "{name}: the gate accepted '{what}': {mutated:?}");
            }
        }
        let with_raw = [code, &[Ins::Raw("nop".into())]].concat();
        assert!(!gate(wasm_table(), &s, h, arity, &with_raw), "{name}: the gate accepted a Raw line");
    }
}

/// The check's kernel work (`tatic_kernel::work`) about doubles with the tree: a shift memo that skipped unshared
/// nodes re-shifted each program suffix at every step, 4x per doubling (doc 15, "Why the check grew 4x per doubling").
/// The bound is under 2.1, the log factor's size: the ratio rises toward 2.0 from below (1.68 to 1.97, doc 15, "Where
/// the check's wall time goes past linear").
#[test]
fn gate_check_work_is_linear_in_the_tree() {
    let work = |d: u32| {
        let (s, h, frag) = compiled(&move |s: &mut TermStore| doubling(s, d));
        tatic_kernel::scoped(|| {
            let (p, st) = built(&s, h, 1, frag.entry().code.as_slice());
            let w0 = tatic_kernel::work();
            assert!(tatic_wasm::encoding::holds(&p, &st).is_ok(), "doubling_{d} should check");
            tatic_kernel::work() - w0
        })
    };
    let w: Vec<u64> = (7..=9).map(work).collect();
    println!("check work, doubling_7 to doubling_9: {w:?}");
    for i in 1..w.len() {
        let r = w[i] as f64 / w[i - 1] as f64;
        assert!(r < 2.05, "check work grew {r:.2}x from doubling_{} to doubling_{}: {w:?}", 6 + i, 7 + i);
    }
}

/// The statement's kernel work (`tatic_kernel::work`) about doubles with the tree too: rebuilding each stack slot's word
/// type and each operator's circuit per instruction added a log factor, 2.1x per doubling (doc 15, "Why the build grew
/// 2.2x per doubling").
#[test]
fn gate_build_work_is_linear_in_the_tree() {
    let work = |d: u32| {
        let (s, h, frag) = compiled(&move |s: &mut TermStore| doubling(s, d));
        tatic_kernel::scoped(|| {
            let w0 = tatic_kernel::work();
            let _ = built(&s, h, 1, frag.entry().code.as_slice());
            tatic_kernel::work() - w0
        })
    };
    let w: Vec<u64> = (9..=11).map(work).collect();
    println!("build work, doubling_9 to doubling_11: {w:?}");
    for i in 1..w.len() {
        let r = w[i] as f64 / w[i - 1] as f64;
        assert!(r < 2.05, "build work grew {r:.2}x from doubling_{} to doubling_{}: {w:?}", 8 + i, 9 + i);
    }
}

/// `(proof, statement)` for a fragment term and its emitted body, built apart from the check.
fn built(s: &TermStore, h: Hash, arity: usize, code: &[Ins]) -> (tatic_kernel::Expr, tatic_kernel::Expr) {
    let (st, p) = build(wasm_table(), s, h, arity, code).expect("a fragment term with a well-formed body");
    (p.expect("the generator proves a fragment term"), st)
}

/// `(build ms, check ms, accepted)` for one gate run, best of `reps`.
fn time_gate(s: &TermStore, h: Hash, arity: usize, code: &[Ins], reps: usize) -> (f64, f64, bool) {
    let mut best = (f64::MAX, f64::MAX, true);
    for _ in 0..reps {
        let (b, c, ok) = tatic_kernel::scoped(|| {
            let t0 = std::time::Instant::now();
            let (p, st) = built(s, h, arity, code);
            let t1 = std::time::Instant::now();
            let ok = tatic_wasm::encoding::holds(&p, &st).is_ok();
            ((t1 - t0).as_secs_f64() * 1e3, t1.elapsed().as_secs_f64() * 1e3, ok)
        });
        best = (best.0.min(b), best.1.min(c), best.2 && ok);
    }
    best
}

/// Section 8's measurements: `inc`, `doubling(d)` up the tree cap, and `Mul`. Prints
/// `name build_ms check_ms ok` lines; run through the wrapper.
#[test]
#[ignore]
fn measure_gate_costs() {
    let (s, h, frag) = compiled(&inc);
    let (b, k, ok) = time_gate(&s, h, 1, &frag.entry().code, 5);
    println!("inc {b:.2} {k:.2} {ok}");
    for d in 1..=13u32 {
        let r = std::thread::Builder::new()
            .stack_size(tatic_kernel::CHECK_STACK)
            .spawn(move || {
                let (s, h, frag) = compiled(&move |s: &mut TermStore| doubling(s, d));
                time_gate(&s, h, 1, frag.entry().code.as_slice(), 3)
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
    let mut muls: Vec<(String, String)> = [
        ("mul a b", r"\a b. a * b"),
        ("mul in an arm", r"\a b. if a < b then a * b else a"),
        // a product of symbolic products, shared and not
        ("mul square shared", r"\a b. (a * b) * (a * b)"),
        ("mul square", r"\a b. (a * b) * (b * a)"),
    ]
    .map(|(n, s)| (n.to_string(), s.to_string()))
    .into();
    // a chain of k products, each operand already symbolic
    muls.extend((2..=8).map(|k| (format!("mul chain {k}"), format!(r"\a b. a{}", " * b".repeat(k)))));
    for (name, src) in muls {
        let (s, h, frag) = compiled(&move |s: &mut TermStore| source(s, &src));
        assert!(in_fragment(wasm_table(), &s, h, 2), "{name} should be in the fragment");
        let (b, k, ok) = time_gate(&s, h, 2, frag.entry().code.as_slice(), 1);
        println!("{name} {b:.2} {k:.2} {ok}");
        if b + k > 60_000.0 {
            println!("mul: skipped the rest after {name} (over 60 s)");
            break;
        }
    }
}

/// The go/no-go's measurement (docs/superpowers/plans/2026-11-11-v08-recursion-once.md, T9 step 5): `doubling(12)` built
/// and checked once on a `CHECK_STACK` thread; prints `build_ms <x> check_ms <y>`. Run timed, from a copied exe.
#[test]
#[ignore]
fn time_doubling_12() {
    let (b, k, ok) = std::thread::Builder::new()
        .stack_size(tatic_kernel::CHECK_STACK)
        .spawn(|| {
            let (s, h, frag) = compiled(&|s: &mut TermStore| doubling(s, 12));
            time_gate(&s, h, 1, frag.entry().code.as_slice(), 1)
        })
        .unwrap()
        .join()
        .unwrap();
    assert!(ok, "doubling(12) should check");
    println!("build_ms {b:.1} check_ms {k:.1}");
}

/// `doubling(13)` (the tree cap) on a default-size 2 MB thread. Alone, since an overflow aborts the exe.
#[test]
#[ignore]
fn measure_stack_2mb() {
    let r = std::thread::Builder::new()
        .stack_size(2 << 20)
        .spawn(|| {
            let (s, h, frag) = compiled(&|s: &mut TermStore| doubling(s, 13));
            time_gate(&s, h, 1, frag.entry().code.as_slice(), 1)
        })
        .unwrap()
        .join()
        .unwrap();
    println!("doubling_13 on 2 MB {:.2} {:.2} {}", r.0, r.1, r.2);
}

/// One `doubling(GATE_D)`, built, and checked `GATE_REPS` times (default 1) when `GATE_CHECK=1`: the target of
/// `docs/runs/2026-11-09/scripts/cg.sh` and of the profiles in `docs/runs/2026-11-09/scripts/`. cachegrind counts the
/// whole process, so the check's misses are the difference of the two runs. Each setting comes from the environment or
/// from a `NAME=value` test filter argument, since the elevated profiler runs the exe without the caller's environment
/// (an `--exact` filter that names no test is harmless).
#[test]
#[ignore]
fn measure_cachegrind() {
    let setting = |name: &str| {
        let arg = |a: String| a.strip_prefix(&format!("{name}=")).map(str::to_string);
        std::env::var(name).ok().or_else(|| std::env::args().find_map(arg))
    };
    let d: u32 = setting("GATE_D").expect("GATE_D").parse().unwrap();
    let check = setting("GATE_CHECK").as_deref() == Some("1");
    let reps: u32 = if check { setting("GATE_REPS").map_or(1, |r| r.parse().unwrap()) } else { 1 };
    std::thread::Builder::new()
        .stack_size(tatic_kernel::CHECK_STACK)
        .spawn(move || {
            let (s, h, frag) = compiled(&move |s: &mut TermStore| doubling(s, d));
            for _ in 0..reps {
                tatic_kernel::scoped(|| {
                    let (w, t) = (tatic_kernel::work(), std::time::Instant::now());
                    let (p, st) = built(&s, h, 1, frag.entry().code.as_slice());
                    if check {
                        assert!(tatic_wasm::encoding::holds(&p, &st).is_ok());
                    }
                    let ms = t.elapsed().as_secs_f64() * 1e3;
                    println!("d={d} check={check} work={} ms={ms:.1}", tatic_kernel::work() - w);
                });
            }
        })
        .unwrap()
        .join()
        .unwrap();
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
        ("doubling_13 (over the tree bound)", Box::new(|s: &mut TermStore| doubling(s, 13)), 1),
        ("\\f. f 1", Box::new(|s: &mut TermStore| source(s, r"\f. f 1")), 1),
    ];
    for (name, build, arity) in cases {
        let mut s = TermStore::new();
        let h = build(&mut s);
        assert!(!in_fragment(wasm_table(), &s, h, arity), "{name} should be outside the fragment");
    }
}
