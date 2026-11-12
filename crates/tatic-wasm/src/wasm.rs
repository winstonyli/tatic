//! The wasm table: the `i64` rows the lowering emits and the machine runs (`ops.rs` builds them).
use super::*;
use machine::{Class, Table};
use ops::{circuit_row, const_row};

/// The wasm rows: `const`, the word rows `add` `sub` `mul`, and the bit rows `lt` `le` `eq` `lt_u` (`lt_u` has no
/// source operator; it serves the `lt`-for-`lt_u` control only).
pub fn table() -> Table {
    Table::new(vec![
        const_row(),
        circuit_row!("add", Class::Word, add, "i64.add"),
        circuit_row!("sub", Class::Word, sub, "i64.sub"),
        circuit_row!("mul", Class::Word, mul, "i64.mul"),
        circuit_row!("lt", Class::Bit, lt_s, "i64.lt_s"),
        circuit_row!("le", Class::Bit, le_s, "i64.le_s"),
        circuit_row!("eq", Class::Bit, eq_bit, "i64.eq"),
        circuit_row!("lt_u", Class::Bit, lt_u, "i64.lt_u"),
    ])
}

#[cfg(test)]
mod tests {
    use super::*;
    use machine::Machine;

    /// Every row of `table()` at n = 8: a `Word` row's meaning infers `V -> V -> V`, a `Bit` row's `V -> V -> Bv_1`,
    /// a `Const` row's (operand 3) `V`.
    #[test]
    fn wasm_rows_are_closed_and_typed() {
        let n = 8;
        let t = table();
        let m = Machine { n, table: &t };
        let v = bv_ty(n);
        for name in ["const", "add", "sub", "mul", "lt", "le", "eq", "lt_u"] {
            let row = t.row(name).unwrap_or_else(|| panic!("no row {name}"));
            let want = match row.class {
                Class::Const => v.clone(),
                Class::Word => arrow(v.clone(), arrow(v.clone(), v.clone())),
                Class::Bit => arrow(v.clone(), arrow(v.clone(), bv_ty(1))),
            };
            let term = (row.meaning)(&mut Cx::default(), &m, if row.class == Class::Const { 3 } else { 0 });
            let got = infer(&Ctx::new(), &term).unwrap_or_else(|e| panic!("{name}: {e}"));
            assert!(def_eq(&got, &want), "{name} ({}) has the wrong type", (row.line)(3));
        }
    }
}
