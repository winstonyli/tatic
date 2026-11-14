//! The wasm `i64` rows' meaning builders and lines (spec 2026-11-08-v07-straight-line-gate-design.md, section 4;
//! `wasm::table` lists them). The lowering prints a row's line and the machine runs its meaning, so a row is the one
//! place the two meet; `wasm_rows_are_closed_and_typed` and tatic's table check guard it.
use super::*;
use machine::{Machine, Row};

/// Where a row has a value. `holds` decides it on the source's `i64` operands (eval and the table test read it);
/// `circuit` is the same as a closed `V -> V -> Bv_1` at width `n`, which the machine and the source side both put in
/// front of every Word site (`choose(dom x y, rest(op x y), z)`). Read only at Word sites.
#[derive(Clone, Copy)]
pub struct Dom {
    pub holds: fn(i64, i64) -> bool,
    pub circuit: fn(usize) -> Expr,
}

fn always(_: i64, _: i64) -> bool {
    true
}

impl Dom {
    /// A total row's domain: everywhere.
    pub const TOTAL: Dom = Dom { holds: always, circuit: dom_true };
    /// A divisor's domain: the second operand is not 0 (`mod`; `i64.rem_s` traps there, and the source errors).
    pub const NONZERO_SECOND: Dom = Dom { holds: |_, y| y != 0, circuit: nonzero_second };
}

/// The `const` row: operand `v` is the word, masked to the machine's width, constant in the frame (`\_:Fr. v`), and
/// prints `i64.const {v}`.
pub fn const_row() -> Row {
    Row {
        name: "const",
        class: machine::Class::Const,
        meaning: |c, m: &Machine, v| m.handing(c, &|_, _| lit(m.n, (v as u64 as u128) & low_bits(m.n))),
        dom: Dom::TOTAL,
        line: |v| format!("i64.const {v}"),
    }
}

/// The `i32.const` row: operand `v` is an `i32` constant, the word is its low 32 bits as an unsigned number (the width
/// of `i32.wrap_i64`'s result; `-1` is `0xffff_ffff`), constant in the frame, and it prints `i32.const {v}`.
pub fn i32_const_row() -> Row {
    Row {
        name: "i32.const",
        line: |v| format!("i32.const {v}"),
        meaning: |c, m: &Machine, v| m.handing(c, &|_, _| lit(m.n, (v as u32 as u128) & low_bits(m.n))),
        ..const_row()
    }
}

/// The `local.get` row: operand `i` is the frame slot, the meaning is the frame's projection at `i` (it fails at or
/// past the frame's width), and it prints `local.get $p{i}`.
pub fn local_get_row() -> Row {
    Row {
        name: "local.get",
        class: machine::Class::Const,
        meaning: |c, m: &Machine, i| m.getter(c, i as usize),
        dom: Dom::TOTAL,
        line: |i| format!("local.get $p{i}"),
    }
}

/// The `local.set` row: operand `i` is the parameter slot written; the meaning is the frame rebuilt with slot `i`
/// replaced (`Machine::setter`), and it prints `local.set $p{i}`.
pub fn local_set_row() -> Row {
    Row {
        name: "local.set",
        class: machine::Class::Set,
        meaning: |c, m: &Machine, i| m.setter(c, i as usize),
        dom: Dom::TOTAL,
        line: |i| format!("local.set $p{i}"),
    }
}

/// A 2-to-1 row whose meaning is the closed circuit `$build` at the machine's width (built once per width and
/// generation, `constant_n`) and whose line is the fixed `$line`; its domain is `$dom`, or `Dom::TOTAL` when omitted.
macro_rules! circuit_row {
    ($name:literal, $class:expr, $build:expr, $line:literal) => {
        circuit_row!($name, $class, $build, $line, $crate::ops::Dom::TOTAL)
    };
    ($name:literal, $class:expr, $build:expr, $line:literal, $dom:expr) => {
        machine::Row {
            name: $name,
            class: $class,
            meaning: |_c, m: &machine::Machine, _| constant_n($build, m.n),
            dom: $dom,
            line: |_| $line.to_string(),
        }
    };
}
pub(crate) use circuit_row;

/// A 1-to-1 row (`Class::Unary`) whose meaning is the closed circuit `$build : V -> V` at the machine's width and whose line is the
/// fixed `$line`. A unary site has no domain: it is unguarded, so the row's `dom` is `Dom::TOTAL` and never read.
macro_rules! unary_row {
    ($name:literal, $build:expr, $line:literal) => {
        machine::Row {
            name: $name,
            class: machine::Class::Unary,
            meaning: |_c, m: &machine::Machine, _| constant_n($build, m.n),
            dom: $crate::ops::Dom::TOTAL,
            line: |_| $line.to_string(),
        }
    };
}
pub(crate) use unary_row;
