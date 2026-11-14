//! The gate (`proof::gate`): the covered terms' emitted bodies are `Accepted`, mutated bodies `Rejected` (spec Goal 2),
//! and what the source reading does not take is `NotCovered`.

use tatic_wasm::machine::Ins;

use crate::jit::compile::{compile_specialised, CompiledFragment};
use crate::lang::term::{Hash, PrimOp, TermStore};
use crate::jit::JitEngine;
use crate::proof::gate::{build, gate, Layer, Verdict, CALL_WEIGHT, MAX_GATE_TREE};
use crate::support::samples::{
    a_capturing_closure_call, a_pap_capturing, capturing_closure_loop, factorial, fib, inc, partial_application_loop,
    redundant_arithmetic_recursion, source, straight_line,
    tail_recursive_loop_with_pap_producing_root_self_call_arg, twice, twice_inc_5,
};
use crate::testing::ins_mutate::with_entry;
use crate::testing::test_corpus::doubling;

/// The term the gate sees (the specialised one, if `specialise` changed it) and its compiled fragment.
pub(super) fn compiled(build: &dyn Fn(&mut TermStore) -> Hash) -> (TermStore, Hash, CompiledFragment) {
    let mut s = TermStore::new();
    let h = build(&mut s);
    let c = compile_specialised(&s, h).expect("compiles");
    match c.specialised {
        Some((s2, h2)) => (s2, h2, c.frag),
        None => (s, h, c.frag),
    }
}

/// Goal 1's five terms, by name, with their arity.
pub(super) fn the_five() -> Vec<(&'static str, Box<dyn Fn(&mut TermStore) -> Hash>, usize)> {
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
        assert_eq!(frag.arity, arity, "{name}");
        assert_eq!(gate(tatic_wasm::wasm::table(), &s, h, &frag), Verdict::Accepted, "{name}: the gate should accept its emitted body");
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
            let (p, st) = built(&s, h, &frag);
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
            let _ = built(&s, h, &frag);
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

/// `\a. if a == 0 then 7 else if a == 1 then 8 else ... else a` at depth `d`.
fn if_chain_src(d: usize) -> String {
    let mut e = "a".to_string();
    for k in (0..d).rev() {
        e = format!("if a == {k} then {} else {e}", k + 7);
    }
    format!(r"\a. {e}")
}

/// `\a b. a % (b % (a % .. b))` at depth `d`: every `%` holds the rest of the chain as its divisor.
fn right_mod_chain(d: usize) -> String {
    let mut e = "b".to_string();
    for k in 0..d {
        e = format!("({} % {e})", if k % 2 == 0 { "a" } else { "b" });
    }
    format!(r"\a b. {e}")
}

/// `\a b. ((b % a) % b) % ..` at depth `d`: every `%` holds the rest of the chain as its dividend.
fn left_mod_chain(d: usize) -> String {
    let mut e = "b".to_string();
    for k in 0..d {
        e = format!("({e} % {})", if k % 2 == 0 { "a" } else { "b" });
    }
    format!(r"\a b. {e}")
}

/// `src` at depths 16, 32, 64 is accepted, and its check and build work (`tatic_kernel::work`) each grow under 2.2x per
/// doubling of depth.
fn assert_linear(name: &str, src: fn(usize) -> String) {
    let w: Vec<(bool, u64, u64)> = [16, 32, 64]
        .into_iter()
        .map(|d| {
            let src = src(d);
            big(move || {
                let (s, h, frag) = compiled(&move |s: &mut TermStore| crate::support::samples::source(s, &src));
                tatic_kernel::scoped(|| {
                    let b0 = tatic_kernel::work();
                    let (p, st) = built(&s, h, &frag);
                    let b1 = tatic_kernel::work();
                    let ok = tatic_wasm::encoding::holds(&p, &st).is_ok();
                    (ok, tatic_kernel::work() - b1, b1 - b0)
                })
            })
        })
        .collect();
    println!("{name} (accepted, check work, build work), depths 16, 32, 64: {w:?}");
    assert!(w.iter().all(|x| x.0), "the {name} should check: {w:?}");
    for i in 1..w.len() {
        let (rc, rb) = (w[i].1 as f64 / w[i - 1].1 as f64, w[i].2 as f64 / w[i - 1].2 as f64);
        assert!(rc < 2.2, "{name}: check work grew {rc:.2}x from depth {} to depth {}: {w:?}", 8 << i, 16 << i);
        assert!(rb < 2.2, "{name}: build work grew {rb:.2}x from depth {} to depth {}: {w:?}", 8 << i, 16 << i);
    }
}

/// A nested if-else chain's check and build work double with its depth. Three costs made each 2.3x to 3.6x per doubling
/// (about 3.8x at depth 128 on main): `cong` put the proofs of a branch's two arms under three binders (J on each), so a
/// chain of `d` branches shifted `d` nested proofs `d` times; `choose` unfolded its arguments (a branch holds the rest of
/// the program) under its own binders; and the final comparison of the proof's type (the real choice at the probe) with
/// the statement then reduced both `choose`s, shifting the rest of the program at each branch again.
#[test]
fn gate_check_work_is_linear_in_an_if_chain() {
    assert_linear("if chain", if_chain_src);
}

/// A nested `%` chain, right and left, is linear too: every Word site is a guard the walk steps through, and the
/// guards nest as the if chain's branches do.
#[test]
fn gate_work_is_linear_in_a_mod_chain() {
    assert_linear("right % chain", right_mod_chain);
    assert_linear("left % chain", left_mod_chain);
}

/// `(proof, statement)` for a fragment term and its emitted body, built apart from the check.
pub(super) fn built(s: &TermStore, h: Hash, frag: &CompiledFragment) -> (tatic_kernel::Expr, tatic_kernel::Expr) {
    let (st, p) = build(tatic_wasm::wasm::table(), s, h, frag).expect("a covered term with a well-formed body");
    (p.expect("the generator proves a fragment term"), st)
}

/// `(build ms, check ms, accepted)` for one gate run, best of `reps`.
fn time_gate(s: &TermStore, h: Hash, frag: &CompiledFragment, reps: usize) -> (f64, f64, bool) {
    let mut best = (f64::MAX, f64::MAX, true);
    for _ in 0..reps {
        let (b, c, ok) = tatic_kernel::scoped(|| {
            let t0 = std::time::Instant::now();
            let (p, st) = built(s, h, frag);
            let t1 = std::time::Instant::now();
            let ok = tatic_wasm::encoding::holds(&p, &st).is_ok();
            ((t1 - t0).as_secs_f64() * 1e3, t1.elapsed().as_secs_f64() * 1e3, ok)
        });
        best = (best.0.min(b), best.1.min(c), best.2 && ok);
    }
    best
}

/// Section 8's measurements: `inc`, `doubling(d)` up to the tree cap (`MAX_GATE_TREE`, d = 12), and `Mul`. Prints
/// `name build_ms check_ms ok` lines; run through the wrapper.
#[test]
#[ignore]
fn measure_gate_costs() {
    let (s, h, frag) = compiled(&inc);
    let (b, k, ok) = time_gate(&s, h, &frag, 5);
    println!("inc {b:.2} {k:.2} {ok}");
    for d in 1..=12u32 {
        let r = std::thread::Builder::new()
            .stack_size(tatic_kernel::CHECK_STACK)
            .spawn(move || {
                let (s, h, frag) = compiled(&move |s: &mut TermStore| doubling(s, d));
                time_gate(&s, h, &frag, 3)
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
        let (b, k, ok) = time_gate(&s, h, &frag, 1);
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
            time_gate(&s, h, &frag, 1)
        })
        .unwrap()
        .join()
        .unwrap();
    assert!(ok, "doubling(12) should check");
    println!("build_ms {b:.1} check_ms {k:.1}");
}

/// T13 step 3, T14 step 3: `name cost build_ms check_ms` for the Goal 1 and Goal 2 targets, the five, `doubling(12)` and the held-out terms,
/// each best of 3 on a `CHECK_STACK` thread; `cost` is the gate's (tree plus `CALL_WEIGHT` per call site). Run timed,
/// from a copied exe.
#[test]
#[ignore]
fn time_targets() {
    use crate::testing::test_corpus::{held_out_a, held_out_b};
    type Build = Box<dyn Fn(&mut TermStore) -> Hash + Send>;
    let rows: Vec<(&'static str, Build)> = vec![
        ("capturing_closure_loop", Box::new(capturing_closure_loop)),
        ("partial_application_loop", Box::new(partial_application_loop)),
        ("factorial", Box::new(factorial)),
        ("redundant_arithmetic_recursion", Box::new(redundant_arithmetic_recursion)),
        ("fib", Box::new(fib)),
        ("held_out_a", Box::new(held_out_a)),
        ("held_out_b", Box::new(held_out_b)),
        ("doubling_12", Box::new(|s| doubling(s, 12))),
        ("inc", Box::new(inc)),
        ("doubling_4", Box::new(|s| doubling(s, 4))),
        ("straight_line", Box::new(straight_line)),
        ("a_capturing_closure_call", Box::new(a_capturing_closure_call)),
        ("a_pap_capturing", Box::new(a_pap_capturing)),
        ("twice_inc_5", Box::new(twice_inc_5)),
        ("let_bound_factorial_10", Box::new(crate::testing::test_corpus::let_bound_factorial_10)),
        ("tail_recursive_loop_with_pap_producing_root_self_call_arg", Box::new(tail_recursive_loop_with_pap_producing_root_self_call_arg)),
    ];
    for (name, b) in rows {
        let (cost, bm, cm, ok) = big(move || {
            let (s, h, frag) = compiled(&*b);
            let cost = crate::proof::gate::module_cost(&s, h, &frag);
            let (bm, cm, ok) = time_gate(&s, h, &frag, 3);
            (cost, bm, cm, ok)
        });
        assert!(ok, "{name} should check");
        assert!(cost <= MAX_GATE_TREE, "{name}: cost {cost} is over the budget");
        println!("{name} {cost} {bm:.1} {cm:.1}");
    }
}

/// `doubling(12)` (the tree cap, `MAX_GATE_TREE`) on a default-size 2 MB thread. Alone, since an overflow aborts the exe.
#[test]
#[ignore]
fn measure_stack_2mb() {
    let r = std::thread::Builder::new()
        .stack_size(2 << 20)
        .spawn(|| {
            let (s, h, frag) = compiled(&|s: &mut TermStore| doubling(s, 12));
            time_gate(&s, h, &frag, 1)
        })
        .unwrap()
        .join()
        .unwrap();
    println!("doubling_12 on 2 MB {:.2} {:.2} {}", r.0, r.1, r.2);
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
                    let (p, st) = built(&s, h, &frag);
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


/// `f` on a thread with the checker's stack, as the JIT's gate runs.
pub(super) fn big<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new().stack_size(tatic_kernel::CHECK_STACK).spawn(f).unwrap().join().unwrap()
}

/// `jit.apply` agrees with the evaluator at each argument list.
pub(super) fn applies_like_eval(s: &TermStore, h: Hash, argss: &[&[i64]]) {
    let mut jit = JitEngine::new();
    for args in argss {
        let (got, want) = (jit.apply(s, h, args), crate::proof::eval::apply_term(s, h, args));
        // a failure is a failure whichever kind the two report (the JIT traps where the evaluator says DivByZero)
        assert!(got == want || (got.is_err() && want.is_err()), "args={args:?}: {got:?} vs {want:?}");
    }
}

#[test]
fn gate_accepts_the_goal_1_targets() {
    type Build = fn(&mut TermStore) -> Hash;
    let targets: [(&str, Build); 5] = [
        ("capturing_closure_loop", capturing_closure_loop),
        ("partial_application_loop", partial_application_loop),
        ("factorial", factorial),
        ("redundant_arithmetic_recursion", redundant_arithmetic_recursion),
        ("fib", fib),
    ];
    for (name, b) in targets {
        let (v, secs) = big(move || {
            let (s, h, frag) = compiled(&b);
            let t = std::time::Instant::now();
            (gate(tatic_wasm::wasm::table(), &s, h, &frag), t.elapsed().as_secs_f64())
        });
        assert_eq!(v, Verdict::Accepted, "{name}");
        println!("{name}: gate {secs:.2} s");
        assert!(secs < 10.0, "{name} took {secs:.1} s");
    }
}

/// `%` is a partial row (`mod`, domain `y != 0`) guarded on both sides, so the gcd samples and a `%` inside an `If`
/// condition's operand are `Accepted`.
#[test]
fn gcd_is_accepted() {
    type Build = Box<dyn Fn(&mut TermStore) -> Hash + Send>;
    let cases: [(&str, Build); 3] = [
        ("gcd", Box::new(crate::support::samples::gcd)),
        ("gcd_with_two_base_cases", Box::new(crate::support::samples::gcd_with_two_base_cases)),
        ("a % b in a condition", Box::new(|s: &mut TermStore| source(s, r"\a b. if a % b == 0 then a else b"))),
    ];
    for (name, b) in cases {
        let v = big(move || {
            let (s, h, frag) = compiled(&*b);
            gate(tatic_wasm::wasm::table(), &s, h, &frag)
        });
        assert_eq!(v, Verdict::Accepted, "{name}");
    }
}

/// Builds `rec f <params> = <body>` from its open body: `Rec(Abs^arity(body))`.
fn rec_of(s: &mut TermStore, arity: usize, body: Hash) -> Hash {
    let mut t = body;
    for _ in 0..arity {
        t = s.abs(t);
    }
    s.rec(t)
}

/// Review Focus 1: a tail call that permutes its arguments.
#[test]
fn gate_accepts_a_permuting_tail_call() {
    let b = |s: &mut TermStore| source(s, "rec f a b = if a <= 0 then b else f b (a - 1)");
    let (s, h, frag) = compiled(&b);
    assert_eq!(big(move || gate(tatic_wasm::wasm::table(), &s, h, &frag)), Verdict::Accepted);
    let mut s = TermStore::new();
    let h = b(&mut s);
    applies_like_eval(&s, h, &[&[3, 7], &[0, 5]]);
}

/// Review Focus 2: literals at the ends of the `i64` range as call arguments.
#[test]
fn gate_accepts_extreme_literals_in_call_arguments() {
    let b = |s: &mut TermStore| {
        // inside `rec f n acc`: acc is Var(0), n Var(1), f Var(2)
        let (acc, n, f) = (s.var(0), s.var(1), s.var(2));
        let zero = s.lit(0);
        let c = s.prim(PrimOp::Le, n, zero);
        let (min, m1) = (s.lit(i64::MIN), s.lit(-1));
        let (a1, a2) = (s.prim(PrimOp::Add, n, min), s.prim(PrimOp::Add, acc, m1));
        let call = s.app2(f, a1, a2);
        let body = s.if_(c, acc, call);
        rec_of(s, 2, body)
    };
    let (s, h, frag) = compiled(&b);
    assert_eq!(big(move || gate(tatic_wasm::wasm::table(), &s, h, &frag)), Verdict::Accepted);
    let mut s = TermStore::new();
    let h = b(&mut s);
    applies_like_eval(&s, h, &[&[1, 0], &[-5, 9]]);
}

/// Review Focus 3: a self-call inside a condition.
#[test]
fn gate_accepts_a_call_in_a_condition() {
    let b = |s: &mut TermStore| source(s, "rec f n = if n <= 0 then 1 else if f (n - 1) < 5 then f (n - 1) + 1 else 0");
    let (s, h, frag) = compiled(&b);
    assert_eq!(big(move || gate(tatic_wasm::wasm::table(), &s, h, &frag)), Verdict::Accepted);
    let mut s = TermStore::new();
    let h = b(&mut s);
    applies_like_eval(&s, h, &[&[3], &[0], &[6]]);
}

/// Review Focus 4: a tail call whose argument holds a non-tail call.
#[test]
fn gate_accepts_mixed_tail_and_non_tail_calls() {
    let b = |s: &mut TermStore| source(s, "rec f n acc = if n <= 0 then acc else f (n - 1) (acc + f (n - 1) 0)");
    let (s, h, frag) = compiled(&b);
    assert_eq!(big(move || gate(tatic_wasm::wasm::table(), &s, h, &frag)), Verdict::Accepted);
    let mut s = TermStore::new();
    let h = b(&mut s);
    applies_like_eval(&s, h, &[&[4, 1], &[0, 3]]);
}

#[test]
fn a_record_with_an_env_parameter_is_rejected_by_the_shape_check() {
    let (s, h, frag) = compiled(&factorial);
    let frag = with_entry(frag, |e| tatic_wasm::machine::Entry { env: tatic_wasm::machine::EnvAccess::Params(1), ..e });
    assert!(matches!(gate(tatic_wasm::wasm::table(), &s, h, &frag), Verdict::Rejected(Layer::Shape, _)));
}

#[test]
fn covered_code_with_raw_or_ill_formed_is_rejected_and_not_installed() {
    let (s, h, frag) = compiled(&factorial);
    let code = frag.entry().code.clone();
    let raw = [code.clone(), vec![Ins::Raw("nop".into())]].concat();
    let short = code[..code.len() - 1].to_vec();
    for (what, bad) in [("a Raw line", raw), ("a dropped last instruction", short)] {
        let f = with_entry(compiled(&factorial).2, |e| tatic_wasm::machine::Entry { code: bad, ..e });
        let v = gate(tatic_wasm::wasm::table(), &s, h, &f);
        assert!(matches!(v, Verdict::Rejected(Layer::Shape, _)), "{what}: {v:?}");
        assert!(!JitEngine::prove_install(&s, h, &f), "{what} was installed");
    }
}

#[test]
fn what_cps_cannot_take_is_not_covered() {
    let cases: Vec<(&str, Box<dyn Fn(&mut TermStore) -> Hash>)> = vec![
        ("twice (higher-order)", Box::new(twice)),
        ("f applied to 1", Box::new(|s: &mut TermStore| source(s, r"\f. f 1"))),
        ("an If in an operand", Box::new(|s: &mut TermStore| source(s, r"\a b. 1 + (if a < b then a else b)"))),
        (
            "an If in a condition",
            Box::new(|s: &mut TermStore| source(s, r"\a b. if (if a < b then a else b) < 1 then 1 else 0")),
        ),
        ("a / b (no table row)", Box::new(|s: &mut TermStore| source(s, r"\a b. a / b"))),
        ("a / 0", Box::new(|s: &mut TermStore| source(s, r"\a. a / 0"))),
    ];
    for (name, b) in cases {
        let mut s = TermStore::new();
        let h = b(&mut s);
        let (s, h, frag) = match crate::jit::compile::compile_specialised(&s, h) {
            Some(c) => match c.specialised {
                Some((s2, h2)) => (s2, h2, Some(c.frag)),
                None => (s, h, Some(c.frag)),
            },
            None => (s, h, None),
        };
        // a term that does not compile has no fragment to gate: it goes to the chain on its own
        if let Some(frag) = frag {
            let v = gate(tatic_wasm::wasm::table(), &s, h, &frag);
            assert!(matches!(v, Verdict::NotCovered(_)), "{name}: {v:?}");
        }
        // and the chain decides it, as before: the JIT agrees with the evaluator
        let mut s = TermStore::new();
        let h = b(&mut s);
        let arity = crate::jit::shape::peel(&s, h).map_or(0, |p| p.0);
        applies_like_eval(&s, h, &[&vec![12; arity], &vec![5; arity]]);
    }
}

#[test]
fn a_term_over_the_budget_is_not_covered() {
    let (s, h, frag) = compiled(&|s: &mut TermStore| doubling(s, 13));
    assert!(crate::jit::compile::tree_size(&s, h) > MAX_GATE_TREE);
    assert!(matches!(gate(tatic_wasm::wasm::table(), &s, h, &frag), Verdict::NotCovered(_)));
    let mut s = TermStore::new();
    let h = doubling(&mut s, 13);
    applies_like_eval(&s, h, &[&[3]]);
    // the weight term of `cost`: a self-call term whose tree fits and whose tree plus the call weight does not
    assert!(CALL_WEIGHT > 0, "the fitted weight is a finding for T13 if 0");
    let mut found = false;
    for k in 1..4000usize {
        let src = format!("rec f n = if n <= 0 then 0 else {}", vec!["f (n - 1)"; k].join(" + "));
        let (s, h, frag) = compiled(&move |s: &mut TermStore| source(s, &src));
        let tree = crate::jit::compile::tree_size(&s, h);
        let sites = crate::proof::gate::call_sites(&s, h);
        if tree <= MAX_GATE_TREE && tree + CALL_WEIGHT * sites > MAX_GATE_TREE {
            assert!(matches!(gate(tatic_wasm::wasm::table(), &s, h, &frag), Verdict::NotCovered(_)), "k={k}");
            found = true;
            break;
        }
    }
    assert!(found, "no call family member sits between the tree bound and the weighted one");
}

#[test]
fn a_closed_straight_line_term_takes_the_gate() {
    let (s, h, frag) = compiled(&|s: &mut TermStore| source(s, "3 + 4"));
    assert_eq!(frag.arity, 0);
    assert_eq!(gate(tatic_wasm::wasm::table(), &s, h, &frag), Verdict::Accepted);
}

#[test]
fn extra_calls_in_covered_code_are_rejected_not_uncovered() {
    let (s, h, frag) = compiled(&factorial);
    let entry = frag.entry_pos;
    let code = frag.entry().code.clone();
    let calls = vec![Ins::Call(entry); 64];
    let appended = [code.clone(), calls.clone()].concat();
    let inserted = [&code[..code.len() - 1], &calls[..], &code[code.len() - 1..]].concat();
    for (what, bad) in [("appended", appended), ("inserted", inserted)] {
        let f = with_entry(compiled(&factorial).2, |e| tatic_wasm::machine::Entry { code: bad, ..e });
        let v = gate(tatic_wasm::wasm::table(), &s, h, &f);
        assert!(matches!(v, Verdict::Rejected(..)), "{what}: {v:?}");
        assert!(!JitEngine::prove_install(&s, h, &f), "{what} was installed");
    }
}

/// The `Call` weight's measurement (plan T12): `rec f n = if n <= 0 then 0 else f (n-1) + .. + f (n-1)` with `k` call
/// sites, `k` in 1, 2, 4 .. 64; prints `k tree_size build_ms check_ms` per `k`. Run from a copied exe through
/// `docs/runs/2026-11-11/scripts/v08-weight-fit.sh`. The fit ran at `CALL_WEIGHT` 0; with the fitted weight the
/// members past the budget are not covered, so the probe stops at the first one and says so.
#[test]
#[ignore]
fn time_call_family() {
    let mut k = 1usize;
    while k <= 64 {
        let src = format!("rec f n = if n <= 0 then 0 else {}", vec!["f (n - 1)"; k].join(" + "));
        let (tree, sites, timed) = std::thread::Builder::new()
            .stack_size(tatic_kernel::CHECK_STACK)
            .spawn(move || {
                let (s, h, frag) = compiled(&move |s: &mut TermStore| source(s, &src));
                let (tree, sites) = (crate::jit::compile::tree_size(&s, h), crate::proof::gate::call_sites(&s, h));
                let covered = tree + crate::proof::gate::CALL_WEIGHT * sites <= MAX_GATE_TREE;
                (tree, sites, covered.then(|| time_gate(&s, h, &frag, 1)))
            })
            .unwrap()
            .join()
            .unwrap();
        assert_eq!(sites, k as u64, "call_sites counts the f applications built");
        let Some((b, c, ok)) = timed else {
            println!("{k} {tree} over the budget of {MAX_GATE_TREE}; stopping");
            break;
        };
        assert!(ok, "k={k} should check");
        println!("{k} {tree} {b:.1} {c:.1}");
        k *= 2;
    }
}
