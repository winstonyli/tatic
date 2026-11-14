//! The generator on straight-line, `If` and self-call bodies: a mini source language mirrors what `tatic::proof::gate::source_fn`
//! reads from a `Term`, so these tests need no term store.
use super::*;
use crate::machine::statement::{statement, statement_with, Clauses, SEnv, SrcFn, FIXED};

#[derive(Clone, Debug)]
enum Src {
    Param(usize),
    Lit(u128),
    /// A word row on two operands.
    Prim(&'static str, Box<Src>, Box<Src>),
    /// `If(cmp, a, b, then, else)`: the bit row `cmp a b` chooses.
    If(&'static str, Box<Src>, Box<Src>, Box<Src>, Box<Src>),
    /// A call of the function itself on its arguments, evaluated left to right.
    SelfCall(Vec<Src>),
    /// A call of the callee at a module position.
    Callee(usize, Vec<Src>),
}
use Src::*;

fn pr(o: &'static str, a: Src, b: Src) -> Src {
    Prim(o, Box::new(a), Box::new(b))
}
fn iff(o: &'static str, a: Src, b: Src, t: Src, e: Src) -> Src {
    If(o, Box::new(a), Box::new(b), Box::new(t), Box::new(e))
}

/// The arguments of a self-call evaluated left to right, then `k` on their marks.
fn cps_list(w: &Machine, e: &SEnv, c: &mut Cx, args: &[Src], done: Vec<At>, k: &dyn Fn(&mut Cx, &[At]) -> Expr) -> Expr {
    match args.split_first() {
        None => k(c, &done),
        Some((a, rest)) => cps(w, e, c, a, &|c, x| {
            let mut d = done.clone();
            d.push(c.mark(x));
            cps_list(w, e, c, rest, d, k)
        }),
    }
}

fn cps(w: &Machine, e: &SEnv, c: &mut Cx, s: &Src, k: &dyn Fn(&mut Cx, Expr) -> Expr) -> Expr {
    tatic_kernel::grow(|| match s {
        Param(i) => k(c, c.at(e.params[*i])),
        Lit(v) => k(c, lit(e.n, *v)),
        Prim(o, a, b) => cps(w, e, c, a, &|c, x| {
            let x = c.mark(x);
            cps(w, e, c, b, &|c, y| {
                let op = (w.table.row(o).unwrap().meaning)(c, w, 0);
                let y = c.mark(y);
                let kk = k(c, app2(op, c.at(x), c.at(y)));
                let dom = constant_n(w.table.row(o).unwrap().dom.circuit, w.n);
                e.choose(c, app2(dom, c.at(x), c.at(y)), kk, c.at(e.z))
            })
        }),
        If(o, a, b, t, f) => cps(w, e, c, a, &|c, x| {
            let x = c.mark(x);
            cps(w, e, c, b, &|c, y| {
                let op = (w.table.row(o).unwrap().meaning)(c, w, 0);
                let cond = app2(op, c.at(x), y);
                let (t2, f2) = (cps(w, e, c, t, k), cps(w, e, c, f, k));
                e.choose(c, cond, t2, f2)
            })
        }),
        SelfCall(args) => cps_list(w, e, c, args, vec![], &|c, xs| e.call(c, e.own, xs, k)),
        Callee(pos, args) => cps_list(w, e, c, args, vec![], &|c, xs| e.call(c, *pos, xs, k)),
    })
}

fn get(i: i64) -> Ins {
    Ins::Row { name: "local.get", operand: i }
}
fn konst(v: i64) -> Ins {
    Ins::Row { name: "const", operand: v }
}
fn row(name: &'static str) -> Ins {
    Ins::Row { name, operand: 0 }
}

/// name, arity, code, source
type Case = (&'static str, usize, Vec<Ins>, Src);

/// `\a b. a - b`
fn minus() -> Case {
    ("a - b", 2, vec![get(0), get(1), row("sub")], pr("sub", Param(0), Param(1)))
}
/// `\a b. a % b`: the one partial row, its site guarded by `y != 0`
fn rem() -> Case {
    ("a % b", 2, vec![get(0), get(1), row("mod")], pr("mod", Param(0), Param(1)))
}
/// `\a b. if a < b then a * 2 else b + 1`
fn branch() -> Case {
    let code = vec![get(0), get(1), row("lt"), Ins::If(vec![get(0), konst(2), row("mul")], vec![get(1), konst(1), row("add")])];
    let src = iff("lt", Param(0), Param(1), pr("mul", Param(0), Lit(2)), pr("add", Param(1), Lit(1)));
    ("branch", 2, code, src)
}

/// Prove and check one case on a `CHECK_STACK` thread: `Err` is the generator's refusal or the kernel's.
fn run(n: usize, (_, arity, code, src): &Case) -> Result<(), String> {
    run_with(n, *arity, code, &|w| {
        let src = src.clone();
        Box::new(move |c: &mut Cx, e: &SEnv, k: &dyn Fn(&mut Cx, Expr) -> Expr| cps(w, e, c, &src, k))
    })
}

/// `run` with the source function built by `mk` from the machine (made on the checking thread), so a test can hand
/// the walk a source `cps` would not build.
fn run_with(n: usize, arity: usize, code: &[Ins], mk: &(dyn for<'m> Fn(&'m Machine<'static>) -> Box<SrcFn<'m>> + Sync)) -> Result<(), String> {
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .stack_size(tatic_kernel::CHECK_STACK)
            .spawn_scoped(s, || {
                let t = crate::wasm::table();
                let w = Machine { n, fw: 0, table: t };
                let entry = Entry { arity, env: EnvAccess::Params(0), code: code.to_vec() };
                let f = mk(&w);
                let module = [Some(ModEntry { entry: &entry, src: &*f })];
                let stmt = statement(&w, &module, 0);
                let proof = prove(&w, &module, 0)?;
                holds(&proof, &stmt)
            })
            .unwrap()
            .join()
            .unwrap()
    })
}

#[test]
fn prove_accepts_straight_line_and_if() {
    for n in [8, 64] {
        for case in [minus(), rem(), branch()] {
            run(n, &case).unwrap_or_else(|e| panic!("n={n} {}: {e}", case.0));
        }
    }
}

/// `\a b. a % b`'s source with a wrong guard, built as `cps` builds it (`y` marked, `k(op x y)` first): the condition
/// the literal 1 in place of `dom x y`, or (`vacuous`) the else `k(op x y)` in place of `z`.
fn wrong_guard<'m>(w: &'m Machine<'static>, vacuous: bool) -> Box<SrcFn<'m>> {
    Box::new(move |c: &mut Cx, e: &SEnv, k: &dyn Fn(&mut Cx, Expr) -> Expr| {
        let row = w.table.row("mod").unwrap();
        let x = e.params[0];
        let y = c.mark(c.at(e.params[1]));
        let op = (row.meaning)(c, w, 0);
        let kk = k(c, app2(op, c.at(x), c.at(y)));
        let dom = app2(constant_n(row.dom.circuit, w.n), c.at(x), c.at(y));
        if vacuous { e.choose(c, dom, kk, kk) } else { e.choose(c, lit(1, 1), kk, c.at(e.z)) }
    })
}
fn guard_always<'m>(w: &'m Machine<'static>) -> Box<SrcFn<'m>> {
    wrong_guard(w, false)
}
fn guard_vacuous<'m>(w: &'m Machine<'static>) -> Box<SrcFn<'m>> {
    wrong_guard(w, true)
}

/// The machine's guard is the table's; a source whose guard differs (always taken, or with no else of its own) is
/// refused by the walk.
#[test]
fn prove_refuses_a_wrong_guard() {
    let (_, arity, code, _) = rem();
    let cases = [
        ("condition 1", guard_always as for<'a> fn(&'a Machine<'static>) -> Box<SrcFn<'a>>, "body: the branch conditions differ"),
        ("else k(op x y)", guard_vacuous, "body/else: the machine is stuck but the source returns"),
    ];
    for (name, mk, want) in cases {
        let err = run_with(8, arity, &code, &mk).expect_err(name);
        assert_eq!(err.to_string(), want, "{name}");
    }
}

/// `z` pinned: out of `mod`'s domain the source side answers the statement's `z`, not `k(op x y)`. The gate shows the
/// machine equals the source, both reading `z` from one binder, so a wrong else on both sides would pass it.
#[test]
fn out_of_domain_answers_z() {
    std::thread::Builder::new()
        .stack_size(tatic_kernel::CHECK_STACK)
        .spawn(|| {
            let n = 8;
            let w0 = Machine { n, fw: 0, table: crate::wasm::table() };
            let (_, arity, code, src) = rem();
            let entry = Entry { arity, env: EnvAccess::Params(0), code };
            let f = |c: &mut Cx, e: &SEnv, k: &dyn Fn(&mut Cx, Expr) -> Expr| cps(&w0, e, c, &src, k);
            let module = [Some(ModEntry { entry: &entry, src: &f })];
            let w = widen(&w0, &module);
            // R z a ks
            let tys = vec![
                ty!(|_c, _x| sort(0)),
                ty!(|c, x| c.at(x[0])),
                ty!(|_c, _x| bv_ty(n)),
                ty!(|c, x| arrow(bv_ty(n), c.at(x[0]))),
            ];
            let got = tele(&mut Cx::default(), &tys, &mut vec![], &lam, &mut |c, x| {
                let fuel = c.mark(nat2_lit(2));
                let sc = Ctxt::new(c, w, &module, fuel, x[0], x[1]).real(c, 0).sc;
                app3(c.at(sc), c.at(x[2]), lit(n, 0), c.at(x[3]))
            });
            let want = tele(&mut Cx::default(), &tys, &mut vec![], &lam, &mut |c, x| c.at(x[1]));
            assert!(def_eq(&got, &want), "a % 0 does not answer z");
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn prove_refuses_a_swapped_if_and_a_wrong_row() {
    let mut swapped = branch();
    let Ins::If(t, e) = swapped.2.last_mut().unwrap() else { panic!() };
    std::mem::swap(t, e);
    let mut wrong = minus();
    wrong.2[2] = row("add");
    for case in [swapped, wrong] {
        let err = run(8, &case).expect_err(case.0);
        assert!(err.starts_with("body"), "{}: the refusal names the path: {err}", case.0);
    }
}

/// `rec f n acc = if n <= 0 then acc else f (n - 1) (acc + n)`, its code pushing the arguments left to right.
fn sum_loop() -> Case {
    let code = vec![
        get(0), konst(0), row("le"),
        Ins::If(vec![get(1)], vec![get(0), konst(1), row("sub"), get(1), get(0), row("add"), Ins::Call(0)]),
    ];
    let src = iff("le", Param(0), Lit(0), Param(1), SelfCall(vec![pr("sub", Param(0), Lit(1)), pr("add", Param(1), Param(0))]));
    ("sum loop", 2, code, src)
}
/// `rec f n = if n <= 1 then 1 else n * f (n - 1)`: a non-tail self-call.
fn factorial() -> Case {
    let code = vec![
        get(0), konst(1), row("le"),
        Ins::If(vec![konst(1)], vec![get(0), get(0), konst(1), row("sub"), Ins::Call(0), row("mul")]),
    ];
    let src = iff("le", Param(0), Lit(1), Lit(1), pr("mul", Param(0), SelfCall(vec![pr("sub", Param(0), Lit(1))])));
    ("factorial", 1, code, src)
}

#[test]
fn prove_accepts_a_sum_loop_and_factorial() {
    for n in [8, 64] {
        for case in [sum_loop(), factorial()] {
            run(n, &case).unwrap_or_else(|e| panic!("n={n} {}: {e}", case.0));
        }
    }
}

/// The sum loop's two argument computations exchanged: slot 0 then holds `acc + n`, not `n - 1`.
#[test]
fn prove_refuses_a_swapped_call_argument() {
    let mut swapped = sum_loop();
    let Ins::If(_, e) = swapped.2.last_mut().unwrap() else { panic!() };
    let (first, second) = (e[..3].to_vec(), e[3..6].to_vec());
    e.splice(..6, second.into_iter().chain(first));
    let err = run(8, &swapped).expect_err("swapped call arguments");
    assert!(err.starts_with("body") && err.contains("local 0"), "the refusal names the path and the slot: {err}");
}

/// A two-entry module: the callee `\a b. a - b` at position 0 and the entry `\x. (g x 1) * 2` at position 1, whose
/// callee law the entry's proof takes as a hypothesis and the callee's closed proof discharges. `swap` makes the entry's
/// code pass its arguments the other way round.
fn two_entries(n: usize, swap: bool) -> Result<(), String> {
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .stack_size(tatic_kernel::CHECK_STACK)
            .spawn_scoped(s, || {
                let t = crate::wasm::table();
                let w = Machine { n, fw: 0, table: t };
                let callee = Entry { arity: 2, env: EnvAccess::Params(0), code: vec![get(0), get(1), row("sub")] };
                let args = if swap { vec![konst(1), get(0)] } else { vec![get(0), konst(1)] };
                let main = Entry { arity: 1, env: EnvAccess::Params(0), code: [args, vec![Ins::Call(0), konst(2), row("mul")]].concat() };
                let g_src = pr("sub", Param(0), Param(1));
                let f_src = pr("mul", Callee(0, vec![Param(0), Lit(1)]), Lit(2));
                let gf = |c: &mut Cx, e: &SEnv, k: &dyn Fn(&mut Cx, Expr) -> Expr| cps(&w, e, c, &g_src, k);
                let ff = |c: &mut Cx, e: &SEnv, k: &dyn Fn(&mut Cx, Expr) -> Expr| cps(&w, e, c, &f_src, k);
                let module = [Some(ModEntry { entry: &callee, src: &gf }), Some(ModEntry { entry: &main, src: &ff })];
                let stmt = statement(&w, &module, 1);
                let proof = prove(&w, &module, 1)?;
                holds(&proof, &stmt)
            })
            .unwrap()
            .join()
            .unwrap()
    })
}

#[test]
fn prove_takes_a_callee_by_its_closed_proof() {
    for n in [8, 64] {
        two_entries(n, false).unwrap_or_else(|e| panic!("n={n}: {e}"));
    }
    let err = two_entries(8, true).expect_err("the entry passes its arguments the wrong way round");
    assert!(err.starts_with("body") && err.contains("local 0"), "{err}");
}

/// The sum loop's real proof against a statement stated under `cl`: the proof is built under the real clauses, so a
/// weakened statement is a different proposition and the kernel must refuse it (O3).
fn sum_loop_against(cl: &Clauses) -> Result<(), String> {
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .stack_size(tatic_kernel::CHECK_STACK)
            .spawn_scoped(s, || {
                let t = crate::wasm::table();
                let w = Machine { n: 8, fw: 0, table: t };
                let (_, arity, code, src) = sum_loop();
                let entry = Entry { arity, env: EnvAccess::Params(0), code };
                let f = |c: &mut Cx, e: &SEnv, k: &dyn Fn(&mut Cx, Expr) -> Expr| cps(&w, e, c, &src, k);
                let module = [Some(ModEntry { entry: &entry, src: &f })];
                holds(&prove(&w, &module, 0)?, &statement_with(&w, &module, 0, cl))
            })
            .unwrap()
            .join()
            .unwrap()
    })
}

/// A relation that never reads the machine's continuation: `ks a = ks a`.
fn relate_ignores_k(c: &mut Cx, r: At, _km: At, ks: At, a: At, _mu: At) -> Expr {
    id(c.at(r), app(c.at(ks), c.at(a)), app(c.at(ks), c.at(a)))
}

#[test]
fn the_fixed_clauses_state_what_the_proof_proves() {
    sum_loop_against(&FIXED).expect("the sum loop's proof against the unweakened statement");
}

#[test]
fn a_relation_that_ignores_the_continuation_breaks_the_proof() {
    let cl = Clauses { relate: relate_ignores_k, ..FIXED };
    sum_loop_against(&cl).expect_err("the proof is of the statement with the real relation");
}

#[test]
fn an_unquantified_fuel_breaks_the_proof() {
    let cl = Clauses { quantify_fuel: false, ..FIXED };
    sum_loop_against(&cl).expect_err("the proof is of the statement for every fuel");
}
