//! WAT text for a function body: each `Ins` prints one fixed line shape at its depth (spec
//! 2026-11-08-v07-straight-line-gate-design.md, section 5). Module scaffolding stays with the lowering in tatic.
use super::*;
use machine::{Ins, Table};

/// Appends `code`'s lines to `out`, each indented `depth` spaces: a row as its `line`, `If` flat (`if (result i64)` / `else` / `end`) with
/// its arms at +2, `Loop` folded (`(loop $L (result i64)` .. `)`), `Raw` as given. Panics on the machine-only
/// `Store` and `Load`, and on `Br(j)` for j other than 0 (the lowering's one label is `$L`).
pub fn print_body(table: &Table, code: &[Ins], depth: usize, out: &mut String) {
    let line = |out: &mut String, s: &str| {
        out.extend(std::iter::repeat_n(' ', depth));
        out.push_str(s);
        out.push('\n');
    };
    for ins in code {
        match ins {
            Ins::Row { name, operand } => {
                let row = table.row(name).unwrap_or_else(|| panic!("print_body: no row {name:?}"));
                line(out, &(row.line)(*operand))
            }
            Ins::LocalGet(i) => line(out, &format!("local.get $p{i}")),
            Ins::If(t, e) => {
                line(out, "if (result i64)");
                print_body(table, t, depth + 2, out);
                line(out, "else");
                print_body(table, e, depth + 2, out);
                line(out, "end");
            }
            Ins::Loop(body) => {
                line(out, "(loop $L (result i64)");
                print_body(table, body, depth + 2, out);
                line(out, ")");
            }
            Ins::Br(0) => line(out, "br $L"),
            Ins::Raw(s) => line(out, s),
            Ins::Br(_) | Ins::Store | Ins::Load => panic!("print_body: {ins:?} is never emitted"),
        }
    }
}

#[test]
fn print_body_shapes() {
    let konst = |v: i64| Ins::Row { name: "const", operand: v };
    let row = |name: &'static str| Ins::Row { name, operand: 0 };
    let code = [Ins::Loop(vec![
        Ins::LocalGet(0),
        konst(-1),
        row("add"),
        konst(0),
        konst(1),
        row("lt"),
        Ins::If(vec![konst(1)], vec![konst(2)]),
    ])];
    let mut out = String::new();
    print_body(&crate::wasm::table(), &code, 4, &mut out);
    let want = "    (loop $L (result i64)
      local.get $p0
      i64.const -1
      i64.add
      i64.const 0
      i64.const 1
      i64.lt_s
      if (result i64)
        i64.const 1
      else
        i64.const 2
      end
    )
";
    assert_eq!(out, want);
}
