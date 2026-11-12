//! WAT text for a function body: each `Ins` prints one fixed line shape at its depth (spec
//! 2026-11-08-v07-straight-line-gate-design.md, section 5). Module scaffolding stays with the lowering in tatic.
use super::*;
use machine::{EnvAccess, Entry, Ins, Table};

/// The label of module position `pos`: `$f` for the entry, `$c{pos}` otherwise.
fn label(pos: usize, entry_pos: usize) -> String {
    if pos == entry_pos { "$f".to_string() } else { format!("$c{pos}") }
}

/// Appends the function `e` at module position `pos` to `out`: its header (the label, the env access's parameters,
/// `$p{i}` parameters, the result, the four scratch declarations), its body at depth 4 (the whole body is a tail
/// position), then `  )`. A body that holds a `Br` is wrapped in `loop $top (result i64)` / `end` (the body then at
/// depth 6), which `br $top` names.
pub fn print_func(table: &Table, pos: usize, entry_pos: usize, e: &Entry, out: &mut String) {
    out.push_str(&format!("  (func {}", label(pos, entry_pos)));
    match e.env {
        EnvAccess::Params(k) => (0..k).for_each(|i| out.push_str(&format!(" (param $e{i} i64)"))),
        EnvAccess::Pointer => out.push_str(" (param $env i32)"),
    }
    (0..e.arity).for_each(|i| out.push_str(&format!(" (param $p{i} i64)")));
    out.push_str(" (result i64)\n");
    // Scratch locals, declared unconditionally (harmless if unused): `$envtmp` for closure environments, `$papenv`
    // for partial application and dynamic dispatch, `$diva`/`$divb` for wrapping div.
    out.push_str("    (local $envtmp i32)\n    (local $papenv i64)\n    (local $diva i64)\n    (local $divb i64)\n");
    if holds_br(&e.code) {
        out.push_str("    loop $top (result i64)\n");
        print_body(table, &e.code, 6, true, entry_pos, out);
        out.push_str("    end\n");
    } else {
        print_body(table, &e.code, 4, true, entry_pos, out);
    }
    out.push_str("  )\n");
}

/// Whether `code` holds a `Br` at any depth.
fn holds_br(code: &[Ins]) -> bool {
    code.iter().any(|i| match i {
        Ins::Br => true,
        Ins::If(t, e) => holds_br(t) || holds_br(e),
        _ => false,
    })
}

/// The tail rule: instruction `i` of a sequence of `len` is in tail position when the sequence is (`tail`) and it is
/// the last. A body is a tail sequence (inside the loop wrapper too: the loop's result is the function's), and an `If`
/// in tail position passes it to both arms.
fn tail_at(tail: bool, i: usize, len: usize) -> bool {
    tail && i + 1 == len
}

/// `code` (a body) with each `Call(j)` in tail position replaced by `f(j)` where that returns `Some`; the rest is
/// unchanged. The loop form's rewrite (`loop_form`) is this with `f` picking the function's own position.
pub fn map_tail_calls(code: &[Ins], f: &mut dyn FnMut(usize) -> Option<Vec<Ins>>) -> Vec<Ins> {
    fn walk(code: &[Ins], tail: bool, f: &mut dyn FnMut(usize) -> Option<Vec<Ins>>) -> Vec<Ins> {
        let mut out = Vec::with_capacity(code.len());
        for (i, ins) in code.iter().enumerate() {
            let last_tail = tail_at(tail, i, code.len());
            match ins {
                Ins::If(t, e) if last_tail => out.push(Ins::If(walk(t, true, f), walk(e, true, f))),
                Ins::Call(j) if last_tail => match f(*j) {
                    Some(repl) => out.extend(repl),
                    None => out.push(ins.clone()),
                },
                other => out.push(other.clone()),
            }
        }
        out
    }
    walk(code, true, f)
}

/// Appends `code`'s lines to `out`, each indented `depth` spaces: a row as its `line`, `If` flat (`if (result i64)` / `else` / `end`) with
/// its arms at +2, `Br` as `br $top`, `Raw` as given. A `Call(j)` prints `return_call` in tail position (`tail_at`),
/// `call` otherwise; `entry_pos` is the position printed `$f`.
pub fn print_body(table: &Table, code: &[Ins], depth: usize, tail: bool, entry_pos: usize, out: &mut String) {
    let line = |out: &mut String, s: &str| {
        out.extend(std::iter::repeat_n(' ', depth));
        out.push_str(s);
        out.push('\n');
    };
    for (i, ins) in code.iter().enumerate() {
        let last_tail = tail_at(tail, i, code.len());
        match ins {
            Ins::Row { name, operand } => {
                let row = table.row(name).unwrap_or_else(|| panic!("print_body: no row {name:?}"));
                line(out, &(row.line)(*operand))
            }
            Ins::If(t, e) => {
                line(out, "if (result i64)");
                print_body(table, t, depth + 2, last_tail, entry_pos, out);
                line(out, "else");
                print_body(table, e, depth + 2, last_tail, entry_pos, out);
                line(out, "end");
            }
            Ins::Call(j) => line(out, &format!("{} {}", if last_tail { "return_call" } else { "call" }, label(*j, entry_pos))),
            Ins::Br => line(out, "br $top"),
            Ins::Raw(s) => line(out, s),
        }
    }
}

#[test]
fn print_body_shapes() {
    let konst = |v: i64| Ins::Row { name: "const", operand: v };
    let row = |name: &'static str| Ins::Row { name, operand: 0 };
    let code = [
        Ins::Row { name: "local.get", operand: 0 },
        konst(-1),
        row("add"),
        konst(0),
        konst(1),
        row("lt"),
        Ins::If(vec![konst(1)], vec![konst(2)]),
    ];
    let mut out = String::new();
    print_body(&crate::wasm::table(), &code, 4, true, 1, &mut out);
    let want = "    local.get $p0
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
";
    assert_eq!(out, want);
}

/// A call prints `return_call` only as the last instruction of a tail position, and labels by module position.
#[test]
fn call_prints_by_the_tail_rule() {
    let konst = |v: i64| Ins::Row { name: "const", operand: v };
    let t = crate::wasm::table();
    let both = [konst(1), konst(2), Ins::Row { name: "lt", operand: 0 }, Ins::If(vec![Ins::Call(0)], vec![Ins::Call(2), Ins::Call(2)])];
    let mut out = String::new();
    print_body(&t, &both, 0, true, 2, &mut out);
    assert!(out.contains("else\n  call $f\n  return_call $f\nend"), "{out}");
    assert!(out.contains("if (result i64)\n  return_call $c0\n"), "{out}");
    let mut out = String::new();
    print_body(&t, &both, 0, false, 2, &mut out);
    assert!(!out.contains("return_call"), "{out}");
    let mut out = String::new();
    print_body(&t, &[Ins::Call(0), konst(1)], 0, true, 2, &mut out);
    assert!(out.starts_with("call $c0\n"), "{out}");
    let mut f = String::new();
    let e = Entry { arity: 2, env: EnvAccess::Params(1), code: vec![Ins::Call(1)] };
    print_func(&t, 1, 2, &e, &mut f);
    assert_eq!(
        f,
        "  (func $c1 (param $e0 i64) (param $p0 i64) (param $p1 i64) (result i64)\n    (local $envtmp i32)\n    (local $papenv i64)\n    (local $diva i64)\n    (local $divb i64)\n    return_call $c1\n  )\n"
    );
}
