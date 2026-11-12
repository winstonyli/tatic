//! The generator on straight-line and `If` bodies: a mini source language mirrors what `tatic::proof::gate::source_fn`
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
}
use Src::*;

fn pr(o: &'static str, a: Src, b: Src) -> Src {
    Prim(o, Box::new(a), Box::new(b))
}
fn iff(o: &'static str, a: Src, b: Src, t: Src, e: Src) -> Src {
    If(o, Box::new(a), Box::new(b), Box::new(t), Box::new(e))
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
