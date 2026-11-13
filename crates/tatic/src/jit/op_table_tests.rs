//! The wasm table (`tatic_wasm::wasm::table`) checked three ways per row:
//! the interpreter (`eval::apply_term`), the production lowering run under
//! wasmtime, and the row's kernel circuit (its `meaning`) by `def_eq`. A row
//! that prints the wrong line, or whose circuit means something else,
//! fails here. Out of a row's domain (`dom.holds`) wasmtime must trap and eval
//! must fail, and every row's domain circuit must equal `holds`: both sides of
//! the gate read the one table, so these are the domain's only checks. The
//! `lt_u` row has no source operator, so only its circuit is checked, against
//! Rust's unsigned `<`.

use std::time::Instant;

use tatic_kernel::{app2, def_eq};
use tatic_wasm::encoding::{constant_n, dom_true, lit, Cx};
use tatic_wasm::machine::{Class, Machine, Row, Table, K};
use tatic_wasm::ops::Dom;

use crate::jit::compile::try_compile;
use crate::jit::shape::is_comparison;
use crate::lang::eval::{apply_term, EvalError};
use crate::lang::term::{PrimOp, TermStore};

/// `ir_fuzz.rs`'s edges less `MIN + 1`, `-7` and `7`: the full set took 4-6 s
/// (`mul`'s circuit nearly all of it), against the plan's 1 s for a default
/// test, so it runs ignored (`op_table_agrees_at_n64_on_all_edges`).
const EDGES: [i64; 5] = [i64::MIN, -1, 0, 1, i64::MAX];
const SOURCE_OPS: [PrimOp; 8] =
    [PrimOp::Add, PrimOp::Sub, PrimOp::Mul, PrimOp::Div, PrimOp::Mod, PrimOp::Lt, PrimOp::Le, PrimOp::Eq];

/// A 2-to-1 row's circuit at width `n`, over the table `t`.
fn circuit(t: &Table, row: &Row, n: usize) -> tatic_kernel::Expr {
    (row.meaning)(&mut Cx::default(), &Machine { n, fw: 0, table: t }, 0)
}

fn mask(n: usize, v: u64) -> u64 {
    if n == 64 { v } else { v & ((1u64 << n) - 1) }
}

fn sign_extend(n: usize, v: u64) -> i64 {
    ((v << (64 - n)) as i64) >> (64 - n)
}

/// `\a b. a OP b` for a word row, `\a b. if a OP b then 1 else 0` for a bit row.
fn source(s: &mut TermStore, p: PrimOp, kind: K) -> crate::lang::term::Hash {
    let (a, b) = (s.var(1), s.var(0));
    let e = s.prim(p, a, b);
    let body = match kind {
        K::W => e,
        K::B => {
            let (one, zero) = (s.lit(1), s.lit(0));
            s.if_(e, one, zero)
        }
    };
    let inner = s.abs(body);
    s.abs(inner)
}

/// Runs every pair through each row of `t` at width `n`, then every row's domain circuit against its `holds`; prints
/// each row's time. The lowering and eval read the global table, so a modified `t` changes only the circuit and
/// domain checks.
fn agree(t: &Table, n: usize, pairs: &dyn Fn() -> Box<dyn Iterator<Item = (u64, u64)>>) {
    let engine = wasmtime::Engine::default();
    for p in SOURCE_OPS {
        let Some(o) = t.row(p.name()) else { continue };
        let start = Instant::now();
        let mut s = TermStore::new();
        let pushed = o.class.push().expect("a source operator's row pushes its result");
        let h = source(&mut s, p, pushed);
        let frag = try_compile(&s, h).unwrap_or_else(|| panic!("{p:?}: source should compile"));
        let bytes = wat::parse_str(&frag.wat()).expect("lowered WAT parses");
        let module = wasmtime::Module::new(&engine, &bytes).expect("lowered WAT validates");
        let mut store = wasmtime::Store::new(&engine, ());
        let instance = wasmtime::Instance::new(&mut store, &module, &[]).expect("instantiates");
        let f = instance.get_typed_func::<(i64, i64), i64>(&mut store, "f").expect("exports f");
        let term = circuit(t, o, n);
        let out_w = match pushed {
            K::W => n,
            K::B => 1,
        };
        for (x, y) in pairs() {
            let (x, y) = (mask(n, x), mask(n, y));
            let (sx, sy) = (sign_extend(n, x), sign_extend(n, y));
            // wasmtime first: it is the independent check of the domain
            let wasm = f.call(&mut store, (sx, sy));
            if !(o.dom.holds)(sx, sy) {
                let trap = wasm.expect_err("wasm should trap out of the domain").downcast::<wasmtime::Trap>();
                assert_eq!(trap.ok(), Some(wasmtime::Trap::IntegerDivisionByZero), "{} at ({x:#x}, {y:#x})", o.name);
                assert_eq!(apply_term(&s, h, &[sx, sy]), Err(EvalError::DivByZero), "{} at ({x:#x}, {y:#x})", o.name);
                continue;
            }
            let wasm = wasm.unwrap_or_else(|e| panic!("{} at ({x:#x}, {y:#x}): wasm disagrees with the domain: {e}", o.name));
            let r_wasm = mask(n, wasm as u64);
            let r_eval = mask(n, apply_term(&s, h, &[sx, sy]).expect("in the domain") as u64);
            assert_eq!(r_eval, r_wasm, "{} at n = {n}: ({x:#x}, {y:#x}): eval {r_eval:#x} vs wasm {r_wasm:#x}", o.name);
            let got = app2(term.clone(), lit(n, x as u128), lit(n, y as u128));
            assert!(def_eq(&got, &lit(out_w, r_eval as u128)), "{} at n = {n}: ({x:#x}, {y:#x}): circuit is not {r_eval:#x}", o.name);
        }
        println!("row {} done {} ms", o.name, start.elapsed().as_millis());
    }
    let start = Instant::now();
    let term = circuit(t, t.row("lt_u").expect("lt_u row"), n);
    for (x, y) in pairs() {
        let (x, y) = (mask(n, x), mask(n, y));
        let got = app2(term.clone(), lit(n, x as u128), lit(n, y as u128));
        assert!(def_eq(&got, &lit(1, (x < y) as u128)), "LtU at n = {n}: ({x:#x}, {y:#x})");
    }
    println!("row LtU done {} ms", start.elapsed().as_millis());
    for name in t.names() {
        let d = t.row(name).expect("a listed row").dom;
        let term = constant_n(d.circuit, n);
        for (x, y) in pairs() {
            let (x, y) = (mask(n, x), mask(n, y));
            let want = (d.holds)(sign_extend(n, x), sign_extend(n, y));
            let got = app2(term.clone(), lit(n, x as u128), lit(n, y as u128));
            assert!(def_eq(&got, &lit(1, want as u128)), "{name} at n = {n}: ({x:#x}, {y:#x}): domain circuit is not holds ({want})");
        }
    }
}

/// Every source operator but `Div` has a row, and `is_comparison` is the Bit class.
#[test]
fn every_prim_op_with_a_row_names_it() {
    for p in SOURCE_OPS {
        let row = tatic_wasm::wasm::table().row(p.name());
        assert_eq!(row.is_some(), !matches!(p, PrimOp::Div), "{p:?}");
        assert_eq!(is_comparison(p), row.is_some_and(|r| r.class == Class::Bit), "{p:?}");
    }
}

#[test]
fn op_table_agrees_at_n64_on_edges() {
    agree(tatic_wasm::wasm::table(), 64, &|| Box::new(EDGES.iter().flat_map(|&x| EDGES.iter().map(move |&y| (x as u64, y as u64)))));
}

/// Goal 4's 8 edges, every pair.
#[test]
#[ignore]
fn op_table_agrees_at_n64_on_all_edges() {
    use crate::testing::ir_fuzz::EDGES;
    agree(tatic_wasm::wasm::table(), 64, &|| Box::new(EDGES.iter().flat_map(|&x| EDGES.iter().map(move |&y| (x as u64, y as u64)))));
}

#[test]
#[ignore]
fn op_table_agrees_at_n8_exhaustive() {
    agree(tatic_wasm::wasm::table(), 8, &|| Box::new((0..256u64).flat_map(|x| (0..256u64).map(move |y| (x, y)))));
}

/// `table()`'s rows with `mod`'s domain replaced by `d`.
fn with_mod_dom(d: Dom) -> Table {
    let t = tatic_wasm::wasm::table();
    Table::new(t.names().into_iter().map(|n| {
        let r = *t.row(n).expect("a listed row");
        if n == "mod" { Row { dom: d, ..r } } else { r }
    }).collect())
}

/// `mod`'s `holds` on the wrong operand says (5, 0) is in the domain, where wasmtime traps.
#[test]
#[should_panic(expected = "wasm disagrees with the domain")]
fn agree_catches_a_domain_on_the_wrong_operand() {
    let t = with_mod_dom(Dom { holds: |x, _| x != 0, ..Dom::NONZERO_SECOND });
    agree(&t, 8, &|| Box::new([(5u64, 0u64)].into_iter()));
}

/// `mod`'s domain circuit constant true while `holds` keeps `y != 0`: the two disagree at (5, 0).
#[test]
#[should_panic(expected = "domain circuit is not holds")]
fn agree_catches_a_domain_circuit_that_is_not_holds() {
    let t = with_mod_dom(Dom { circuit: dom_true, ..Dom::NONZERO_SECOND });
    agree(&t, 8, &|| Box::new([(5u64, 0u64)].into_iter()));
}
