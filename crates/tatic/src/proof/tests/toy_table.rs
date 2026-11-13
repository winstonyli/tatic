//! S4 (v0.8): a toy second instruction table through the unchanged gate. Both the source reading and the machine read
//! the table given, so accepting a `sub` that no wasm row means (operands swapped, one added) shows the gate reads its
//! argument and not the wasm table.
use super::*;
use crate::jit::compile::{CompiledFragment, Item};
use crate::proof::gate::{gate, Verdict};
use crate::support::samples::source;
use tatic_kernel::{app2, lam};
use tatic_wasm::encoding::{add, constant_n, lit, sub};
use tatic_wasm::machine::{Class, Entry, EnvAccess, Ins, Row, Table};
use tatic_wasm::ops::Dom;

/// The wasm `name` row's meaning and line under the toy.
fn as_wasm(name: &'static str) -> Row {
    *tatic_wasm::wasm::table().row(name).unwrap_or_else(|| panic!("no wasm row {name:?}"))
}

/// `const`, `local.get` and `lt` as wasm's; `sub` means `\x y. add (sub y x) 1`.
fn toy() -> Table {
    Table::new(vec![
        as_wasm("const"),
        as_wasm("local.get"),
        Row {
            name: "sub",
            class: Class::Word,
            dom: Dom::TOTAL,
            meaning: |_c, m, _| lam(m.v(), lam(m.v(), app2(constant_n(add, m.n), app2(constant_n(sub, m.n), tatic_kernel::var(0), tatic_kernel::var(1)), lit(m.n, 1)))),
            line: |_| "toy.sub".to_string(),
        },
        as_wasm("lt"),
    ])
}

fn get(i: i64) -> Ins {
    Ins::Row { name: "local.get", operand: i }
}
fn row(name: &'static str) -> Ins {
    Ins::Row { name, operand: 0 }
}

/// The one-entry fragment of `h` with `code` as its body.
fn frag(h: Hash, arity: usize, code: Vec<Ins>) -> CompiledFragment {
    CompiledFragment {
        arity,
        module: vec![Item::Func { pos: 0, entry: Entry { arity, env: EnvAccess::Params(0), code }, source: Some(h) }],
        needs_hp_reset: false,
        entry_pos: 0,
    }
}

fn verdict(src: &'static str, code: Vec<Ins>) -> Verdict {
    super::gate::big(move || {
        let mut s = TermStore::new();
        let h = source(&mut s, src);
        gate(&toy(), &s, h, &frag(h, 2, code))
    })
}

#[test]
fn the_toy_table_accepts_its_terms() {
    let diff = || vec![get(0), get(1), row("sub")];
    assert_eq!(verdict(r"\a b. a - b", diff()), Verdict::Accepted);
    let branch = vec![get(0), get(1), row("lt"), Ins::If(diff(), vec![get(1)])];
    assert_eq!(verdict(r"\a b. if a < b then a - b else b", branch), Verdict::Accepted);
}

#[test]
fn the_toy_table_rejects_its_mutant() {
    let v = verdict(r"\a b. a - b", vec![get(1), get(0), row("sub")]);
    assert!(matches!(v, Verdict::Rejected(..)), "{v:?}");
}

/// A comparison the toy has no row for is read from the table given, so the term is not covered (it panicked when the
/// condition was checked against wasm's table and the row looked up in the toy's).
#[test]
fn a_comparison_the_toy_lacks_is_not_covered() {
    let code = vec![get(0), get(1), row("lt"), Ins::If(vec![get(0)], vec![get(1)])]; // well-formed, so the shape check passes
    let v = verdict(r"\a b. if a <= b then a else b", code);
    assert!(matches!(v, Verdict::NotCovered(..)), "{v:?}");
}
