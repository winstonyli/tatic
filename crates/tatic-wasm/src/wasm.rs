//! The wasm table: the `i64` rows the lowering emits and the machine runs (`ops.rs` builds them).
use super::*;
use machine::{Class, Table};
use ops::{circuit_row, const_row, local_get_row, local_set_row, Dom};

/// The wasm rows: `const`, `local.get`, `local.set`, the word rows `add` `sub` `mul` `mod` (`mod` partial: `Dom::NONZERO_SECOND`), and the bit rows `lt` `le` `eq` `lt_u` (`lt_u` has no
/// source operator; it serves the `lt`-for-`lt_u` control only). Built once per process: every reader (the lowering,
/// the gate's two sides, the fragment predicate, eval) shares this one table.
pub fn table() -> &'static Table {
    static TABLE: std::sync::OnceLock<Table> = std::sync::OnceLock::new();
    TABLE.get_or_init(|| Table::new(vec![
        const_row(),
        local_get_row(),
        local_set_row(),
        circuit_row!("add", Class::Word, add, "i64.add"),
        circuit_row!("sub", Class::Word, sub, "i64.sub"),
        circuit_row!("mul", Class::Word, mul, "i64.mul"),
        circuit_row!("mod", Class::Word, rem_s, "i64.rem_s", Dom::NONZERO_SECOND),
        circuit_row!("lt", Class::Bit, lt_s, "i64.lt_s"),
        circuit_row!("le", Class::Bit, le_s, "i64.le_s"),
        circuit_row!("eq", Class::Bit, eq_bit, "i64.eq"),
        circuit_row!("lt_u", Class::Bit, lt_u, "i64.lt_u"),
    ]))
}

#[cfg(test)]
mod tests {
    use super::*;
    use machine::Machine;

    /// Every row of `table()` at n = 8, frame width 2: a `Word` row's meaning infers `V -> V -> V`, a `Bit` row's
    /// `V -> V -> Bv_1`, a `Const` row's (`const` at operand 3, `local.get` at operands 0 and 1) `Fr -> Pi R:Sort0. (V -> R) -> R` (`Machine::operand_ty`);
/// every row's domain circuit infers `V -> V -> Bv_1`.
    #[test]
    fn wasm_rows_are_closed_and_typed() {
        let n = 8;
        let t = table();
        let m = Machine { n, fw: 2, table: t };
        let v = bv_ty(n);
        assert_eq!(t.names(), ["const", "local.get", "local.set", "add", "sub", "mul", "mod", "lt", "le", "eq", "lt_u"]);
        let cases: [(&str, i64); 12] = [
            ("const", 3), ("local.get", 0), ("local.get", 1), ("local.set", 1), ("add", 0), ("sub", 0), ("mul", 0), ("mod", 0), ("lt", 0), ("le", 0), ("eq", 0), ("lt_u", 0),
        ];
        for (name, operand) in cases {
            let row = t.row(name).unwrap_or_else(|| panic!("no row {name}"));
            let want = match row.class {
                Class::Const => m.operand_ty(),
                Class::Set => m.setter_ty(),
                Class::Word => arrow(v.clone(), arrow(v.clone(), v.clone())),
                Class::Bit => arrow(v.clone(), arrow(v.clone(), bv_ty(1))),
            };
            let dom = infer(&Ctx::new(), &constant_n(row.dom.circuit, n)).unwrap_or_else(|e| panic!("{name} domain: {e}"));
            assert!(def_eq(&dom, &arrow(v.clone(), arrow(v.clone(), bv_ty(1)))), "{name}: domain has the wrong type");
            // Only Word sites are guarded (`ops::Dom`), so a partial row of any other class would run unguarded.
            if row.class != Class::Word {
                let total = constant_n(row.dom.circuit, n);
                assert!(def_eq(&total, &constant_n(dom_true, n)), "{name}: a {:?} row must be total", row.class);
            }
            let term = (row.meaning)(&mut Cx::default(), &m, operand);
            let got = infer(&Ctx::new(), &term).unwrap_or_else(|e| panic!("{name}: {e}"));
            assert!(def_eq(&got, &want), "{name} ({}) has the wrong type", (row.line)(operand));
        }
    }
}
