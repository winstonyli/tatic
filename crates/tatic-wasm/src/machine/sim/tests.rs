//! The generator on straight-line, `If` and self-call bodies: a mini source language mirrors what `tatic::proof::gate::source_fn`
//! reads from a `Term`, so these tests need no term store.
use super::*;
use crate::machine::statement::{statement, SEnv};

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
                k(c, app2(op, c.at(x), y))
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
/// `\a b. if a < b then a * 2 else b + 1`
fn branch() -> Case {
    let code = vec![get(0), get(1), row("lt"), Ins::If(vec![get(0), konst(2), row("mul")], vec![get(1), konst(1), row("add")])];
    let src = iff("lt", Param(0), Param(1), pr("mul", Param(0), Lit(2)), pr("add", Param(1), Lit(1)));
    ("branch", 2, code, src)
}

/// Prove and check one case on a `CHECK_STACK` thread: `Err` is the generator's refusal or the kernel's.
fn run(n: usize, (_, arity, code, src): &Case) -> Result<(), String> {
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .stack_size(tatic_kernel::CHECK_STACK)
            .spawn_scoped(s, || {
                let t = crate::wasm::table();
                let w = Machine { n, fw: 0, table: &t };
                let entry = Entry { arity: *arity, env: EnvAccess::Params(0), code: code.clone() };
                let f = |c: &mut Cx, e: &SEnv, k: &dyn Fn(&mut Cx, Expr) -> Expr| cps(&w, e, c, src, k);
                let module = [Some(ModEntry { entry: &entry, src: &f })];
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
        for case in [minus(), branch()] {
            run(n, &case).unwrap_or_else(|e| panic!("n={n} {}: {e}", case.0));
        }
    }
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
                let w = Machine { n, fw: 0, table: &t };
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
