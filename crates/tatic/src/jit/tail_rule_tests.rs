//! The printer's tail rule (`tatic_wasm::print`): a `Call` prints `return_call` when it is the last instruction of a
//! tail position and `call` otherwise, and the two forms answer alike wherever both run.

use tatic_wasm::machine::{out_stack, well_formed, Entry, EnvAccess, Ins, K};
use tatic_wasm::print::{print_body, print_func};

use crate::jit::shape::wasm_table;

fn konst(v: i64) -> Ins {
    Ins::Row { name: "const", operand: v }
}

fn row(name: &'static str) -> Ins {
    Ins::Row { name, operand: 0 }
}

/// The atoms every arm and body is built from.
fn atoms() -> Vec<Ins> {
    vec![konst(1), Ins::Row { name: "local.get", operand: 0 }, row("add"), Ins::Call(0)]
}

/// Whether `code` runs from an empty stack beside a one-argument callee at position 0.
fn runs(code: &[Ins]) -> bool {
    well_formed(wasm_table(), code, &[], &[Some(1)])
}

/// Whether `code` runs and leaves exactly one word.
fn ends_on_word(code: &[Ins]) -> bool {
    runs(code) && out_stack(wasm_table(), code, vec![], &[Some(1)]) == vec![K::W]
}

/// Arms that run alone under `if (result i64)`: from an empty stack to one word, at most 2 atoms.
fn arms() -> Vec<Vec<Ins>> {
    let a = atoms();
    let mut all = vec![vec![]];
    for x in &a {
        all.push(vec![x.clone()]);
        for y in &a {
            all.push(vec![x.clone(), y.clone()]);
        }
    }
    all.into_iter().filter(|c| ends_on_word(c)).collect()
}

/// The items a body is built from: an atom, or `lt` then an `If` over two arms.
fn items() -> Vec<Vec<Ins>> {
    let mut v: Vec<Vec<Ins>> = atoms().into_iter().map(|a| vec![a]).collect();
    let arms = arms();
    for t in &arms {
        for e in &arms {
            v.push(vec![row("lt"), Ins::If(t.clone(), e.clone())]);
        }
    }
    v
}

/// Every well-formed body of up to 4 items ending on one word, depth-first.
fn bodies() -> Vec<Vec<Ins>> {
    fn go(items: &[Vec<Ins>], code: &mut Vec<Ins>, left: usize, out: &mut Vec<Vec<Ins>>) {
        if ends_on_word(code) {
            out.push(code.clone());
        }
        if left == 0 {
            return;
        }
        for it in items {
            let n = code.len();
            code.extend(it.iter().cloned());
            // prune an ill-formed prefix (an underflow never recovers)
            if runs(code) {
                go(items, code, left - 1, out);
            }
            code.truncate(n);
        }
    }
    let mut out = Vec::new();
    go(&items(), &mut Vec::new(), 4, &mut out);
    out
}

fn instantiate(wat: &str) -> (wasmtime::Store<()>, wasmtime::Instance) {
    let bytes = wat::parse_str(wat).unwrap_or_else(|e| panic!("valid wat: {e}\n{wat}"));
    let engine = wasmtime::Engine::default();
    let module = wasmtime::Module::new(&engine, &bytes).unwrap();
    let mut store = wasmtime::Store::new(&engine, ());
    let instance = wasmtime::Instance::new(&mut store, &module, &[]).unwrap();
    (store, instance)
}

/// Every body, printed with the tail rule (`$a{i}`) and with every call a plain `call` (`$b{i}`), beside the callee
/// `$c0 = \x. x + 100`; the two answer alike at p0 in {0, 3}. Bodies that print the same either way are skipped, and
/// the ones that differ must be many: a wrong rule (a `return_call` before the `add` of `1 + f x`) skips code.
#[test]
fn tail_rule_matches_call_everywhere_under_wasmtime() {
    let t = wasm_table();
    let callee = Entry { arity: 1, env: EnvAccess::Params(0), code: vec![Ins::Row { name: "local.get", operand: 0 }, konst(100), row("add")] };
    let mut wat = String::from("(module\n");
    print_func(t, 0, usize::MAX, &callee, &mut wat);
    let mut differing = 0;
    for (i, code) in bodies().into_iter().enumerate() {
        let mut tailed = String::new();
        let e = Entry { arity: 1, env: EnvAccess::Params(0), code: code.clone() };
        print_func(t, 1 + i, usize::MAX, &e, &mut tailed);
        let mut plain = String::new();
        print_body(t, &code, 4, false, usize::MAX, &mut plain);
        let mut tail_body = String::new();
        print_body(t, &code, 4, true, usize::MAX, &mut tail_body);
        if plain == tail_body {
            continue;
        }
        differing += 1;
        wat.push_str(&tailed.replace(&format!("$c{}", 1 + i), &format!("$a{i}")));
        wat.push_str(&format!(
            "  (func $b{i} (param $p0 i64) (result i64)\n    (local $envtmp i32)\n    (local $papenv i64)\n    (local $diva i64)\n    (local $divb i64)\n{plain}  )\n"
        ));
        wat.push_str(&format!("  (export \"a{i}\" (func $a{i}))\n  (export \"b{i}\" (func $b{i}))\n"));
    }
    wat.push_str(")\n");
    assert!(differing > 50, "only {differing} bodies print differently");
    let (mut store, inst) = instantiate(&wat);
    let mut checked = 0;
    for i in 0..bodies().len() {
        let (Ok(a), Ok(b)) = (inst.get_typed_func::<i64, i64>(&mut store, &format!("a{i}")), inst.get_typed_func::<i64, i64>(&mut store, &format!("b{i}")))
        else {
            continue;
        };
        for p0 in [0, 3] {
            assert_eq!(a.call(&mut store, p0).unwrap(), b.call(&mut store, p0).unwrap(), "body {i} at p0 = {p0}");
        }
        checked += 1;
    }
    assert_eq!(checked, differing);
}

#[test]
fn tail_rule_prints_both_forms_in_one_body() {
    // Review Focus 4: the tail call returns, the non-tail call (under `+ 1`) does not.
    let mut s = crate::lang::term::TermStore::new();
    let h = crate::support::samples::source(&mut s, "rec f n = if n <= 0 then 0 else if n < 2 then f (n - 1) else f (n - 1) + 1");
    let frag = crate::jit::compile::try_compile(&s, h).unwrap();
    let wat = frag.wat();
    assert_eq!(wat.matches("return_call $f").count(), 1, "{wat}");
    assert_eq!(wat.matches("call $f").count() - 1, 1, "{wat}");
    let (mut store, inst) = instantiate(&wat);
    let f = inst.get_typed_func::<i64, i64>(&mut store, "f").unwrap();
    let mut jit = crate::jit::JitEngine::new();
    for n in [0, 1, 5] {
        let want = crate::lang::eval::apply_term(&s, h, &[n]);
        assert_eq!(Ok(f.call(&mut store, n).unwrap()), want, "n={n}");
        assert_eq!(jit.apply(&s, h, &[n]), want, "n={n}");
    }
}
