//! The wasm table (`shape::wasm_table`) checked three ways per row:
//! the interpreter (`eval::apply_term`), the production lowering run under
//! wasmtime, and the row's kernel circuit (its `meaning`) by `def_eq`. A row
//! that prints the wrong line, or whose circuit means something else,
//! fails here. The `lt_u` row has no source operator, so only its circuit is
//! checked, against Rust's unsigned `<`.

use std::time::Instant;

use tatic_kernel::{app2, def_eq};
use tatic_wasm::encoding::{lit, Cx};
use tatic_wasm::machine::{Class, Machine, Row, K};

use crate::jit::compile::try_compile;
use crate::jit::shape::{is_comparison, wasm_table};
use crate::lang::eval::apply_term;
use crate::lang::term::{PrimOp, TermStore};

/// `ir_fuzz.rs`'s edges less `MIN + 1`, `-7` and `7`: the full set took 4-6 s
/// (`mul`'s circuit nearly all of it), against the plan's 1 s for a default
/// test, so it runs ignored (`op_table_agrees_at_n64_on_all_edges`).
const EDGES: [i64; 5] = [i64::MIN, -1, 0, 1, i64::MAX];
const SOURCE_OPS: [PrimOp; 8] =
    [PrimOp::Add, PrimOp::Sub, PrimOp::Mul, PrimOp::Div, PrimOp::Mod, PrimOp::Lt, PrimOp::Le, PrimOp::Eq];

/// A 2-to-1 row's circuit at width `n`.
fn circuit(row: &Row, n: usize) -> tatic_kernel::Expr {
    (row.meaning)(&mut Cx::default(), &Machine { n, fw: 0, table: wasm_table() }, 0)
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

/// Runs every pair through each table row at width `n`; prints each row's time.
fn agree(n: usize, pairs: &dyn Fn() -> Box<dyn Iterator<Item = (u64, u64)>>) {
    let engine = wasmtime::Engine::default();
    for p in SOURCE_OPS {
        let Some(o) = wasm_table().row(p.name()) else { continue };
        let start = Instant::now();
        let mut s = TermStore::new();
        let h = source(&mut s, p, o.class.kind());
        let frag = try_compile(&s, h).unwrap_or_else(|| panic!("{p:?}: source should compile"));
        let bytes = wat::parse_str(&frag.wat()).expect("lowered WAT parses");
        let module = wasmtime::Module::new(&engine, &bytes).expect("lowered WAT validates");
        let mut store = wasmtime::Store::new(&engine, ());
        let instance = wasmtime::Instance::new(&mut store, &module, &[]).expect("instantiates");
        let f = instance.get_typed_func::<(i64, i64), i64>(&mut store, "f").expect("exports f");
        let term = circuit(o, n);
        let out_w = match o.class.kind() {
            K::W => n,
            K::B => 1,
        };
        for (x, y) in pairs() {
            let (x, y) = (mask(n, x), mask(n, y));
            let (sx, sy) = (sign_extend(n, x), sign_extend(n, y));
            let r_eval = mask(n, apply_term(&s, h, &[sx, sy]).expect("no division") as u64);
            let r_wasm = mask(n, f.call(&mut store, (sx, sy)).expect("no trap") as u64);
            assert_eq!(r_eval, r_wasm, "{} at n = {n}: ({x:#x}, {y:#x}): eval {r_eval:#x} vs wasm {r_wasm:#x}", o.name);
            let got = app2(term.clone(), lit(n, x as u128), lit(n, y as u128));
            assert!(def_eq(&got, &lit(out_w, r_eval as u128)), "{} at n = {n}: ({x:#x}, {y:#x}): circuit is not {r_eval:#x}", o.name);
        }
        println!("row {} done {} ms", o.name, start.elapsed().as_millis());
    }
    let start = Instant::now();
    let term = circuit(wasm_table().row("lt_u").expect("lt_u row"), n);
    for (x, y) in pairs() {
        let (x, y) = (mask(n, x), mask(n, y));
        let got = app2(term.clone(), lit(n, x as u128), lit(n, y as u128));
        assert!(def_eq(&got, &lit(1, (x < y) as u128)), "LtU at n = {n}: ({x:#x}, {y:#x})");
    }
    println!("row LtU done {} ms", start.elapsed().as_millis());
}

/// Exactly the six non-`Div`/`Mod` source operators have a row, and `is_comparison` is the Bit class.
#[test]
fn every_prim_op_with_a_row_names_it() {
    for p in SOURCE_OPS {
        let row = wasm_table().row(p.name());
        assert_eq!(row.is_some(), !matches!(p, PrimOp::Div | PrimOp::Mod), "{p:?}");
        assert_eq!(is_comparison(p), row.is_some_and(|r| r.class == Class::Bit), "{p:?}");
    }
}

#[test]
fn op_table_agrees_at_n64_on_edges() {
    agree(64, &|| Box::new(EDGES.iter().flat_map(|&x| EDGES.iter().map(move |&y| (x as u64, y as u64)))));
}

/// Goal 4's 8 edges, every pair.
#[test]
#[ignore]
fn op_table_agrees_at_n64_on_all_edges() {
    use crate::testing::ir_fuzz::EDGES;
    agree(64, &|| Box::new(EDGES.iter().flat_map(|&x| EDGES.iter().map(move |&y| (x as u64, y as u64)))));
}

#[test]
#[ignore]
fn op_table_agrees_at_n8_exhaustive() {
    agree(8, &|| Box::new((0..256u64).flat_map(|x| (0..256u64).map(move |y| (x, y)))));
}
