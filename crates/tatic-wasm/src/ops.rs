//! The wasm `i64` rows' meaning builders and lines (spec 2026-11-08-v07-straight-line-gate-design.md, section 4;
//! `wasm::table` lists them). The lowering prints a row's line and the machine runs its meaning, so a row is the one
//! place the two meet; `wasm_rows_are_closed_and_typed` and tatic's table check guard it.
use super::*;
use machine::{Machine, Row};

/// The `const` row: operand `v` is the word, masked to the machine's width, constant in the frame (`\_:Fr. v`), and
/// prints `i64.const {v}`.
pub fn const_row() -> Row {
    Row {
        name: "const",
        class: machine::Class::Const,
        meaning: |c, m: &Machine, v| c.lam(m.fr(), |_, _| lit(m.n, (v as u64 as u128) & low_bits(m.n))),
        line: |v| format!("i64.const {v}"),
    }
}

/// The `local.get` row: operand `i` is the frame slot, the meaning is the frame's projection at `i` (it fails at or
/// past the frame's width), and it prints `local.get $p{i}`.
pub fn local_get_row() -> Row {
    Row {
        name: "local.get",
        class: machine::Class::Const,
        meaning: |c, m: &Machine, i| m.getter(c, i as usize),
        line: |i| format!("local.get $p{i}"),
    }
}

/// A 2-to-1 row whose meaning is the closed circuit `$build` at the machine's width (built once per width and
/// generation, `constant_n`) and whose line is the fixed `$line`.
macro_rules! circuit_row {
    ($name:literal, $class:expr, $build:expr, $line:literal) => {
        machine::Row {
            name: $name,
            class: $class,
            meaning: |_c, m: &machine::Machine, _| constant_n($build, m.n),
            line: |_| $line.to_string(),
        }
    };
}
pub(crate) use circuit_row;
