//! Compiles a restricted "first-order arithmetic with self-recursion"
//! fragment of the term language down to WebAssembly text (WAT) — our
//! formalization of the target machine. `wasmtime` then JIT-compiles that
//! WAT (via Cranelift) to native code.
//!
//! Only a subset of terms fall in this fragment: closed functions built
//! from `Var`/`Lit`/`Prim`/`If` and fully-saturated self-calls, optionally
//! wrapped in `Rec` for recursion. Anything else (general higher-order
//! terms, partial application, free variables, ...) is rejected by
//! returning `None`, and the caller falls back to the interpreter — the
//! JIT never has to be complete, only sound about what it accepts.
//!
//! Tail self-calls are compiled into a `loop`/`br`, turning tail recursion
//! into iteration (constant Wasm call-stack depth); non-tail self-calls
//! fall back to an ordinary Wasm `call`.

use crate::term::{Hash, PrimOp, Term, TermStore};

pub struct CompiledFragment {
    pub arity: usize,
    pub wat: String,
}

/// Try to compile `h` as an `arity`-ary numeric function. Returns `None` if
/// `h` (or any subterm reachable in "tail position" tracking) falls outside
/// the compilable fragment.
pub fn try_compile(store: &TermStore, h: Hash) -> Option<CompiledFragment> {
    let (arity, body, is_rec) = peel(store, h)?;
    if arity == 0 {
        return None;
    }
    let self_idx = if is_rec { Some(arity as u32) } else { None };

    let mut w = String::new();
    w.push_str("(module\n  (func $f");
    for i in 0..arity {
        w.push_str(&format!(" (param $p{i} i64)"));
    }
    w.push_str(" (result i64)\n");
    for i in 0..arity {
        w.push_str(&format!("    (local $t{i} i64)\n"));
    }
    w.push_str("    (loop $L (result i64)\n");
    compile_node(store, body, arity, self_idx, true, &mut w, 6)?;
    w.push_str("    )\n  )\n  (export \"f\" (func $f))\n)\n");

    Some(CompiledFragment { arity, wat: w })
}

/// Peel a term into `(arity, body, is_recursive)`:
/// - `Rec(Abs(Abs(...body)))` -> `(k, body, true)`, self bound at `Var(k)`.
/// - `Abs(Abs(...body))` (no `Rec`)              -> `(k, body, false)`.
pub(crate) fn peel(store: &TermStore, h: Hash) -> Option<(usize, Hash, bool)> {
    match store.resolve(h) {
        Term::Rec(inner) => {
            let (k, body) = peel_abs(store, *inner);
            (k > 0).then_some((k, body, true))
        }
        _ => {
            let (k, body) = peel_abs(store, h);
            (k > 0).then_some((k, body, false))
        }
    }
}

fn peel_abs(store: &TermStore, mut h: Hash) -> (usize, Hash) {
    let mut k = 0usize;
    loop {
        match store.resolve(h) {
            Term::Abs(body) => {
                k += 1;
                h = *body;
            }
            _ => return (k, h),
        }
    }
}

fn local_index(var: u32, arity: usize) -> Option<u32> {
    let a = arity as u32;
    (var < a).then_some(a - 1 - var)
}

/// If `h` is a fully-saturated self-application (`self a1 a2 .. a_arity`),
/// return the argument hashes in application order.
pub(crate) fn match_self_call(
    store: &TermStore,
    h: Hash,
    arity: usize,
    self_idx: Option<u32>,
) -> Option<Vec<Hash>> {
    let self_idx = self_idx?;
    let mut args_rev = Vec::with_capacity(arity);
    let mut cur = h;
    for _ in 0..arity {
        match store.resolve(cur) {
            Term::App(f, a) => {
                args_rev.push(*a);
                cur = *f;
            }
            _ => return None,
        }
    }
    match store.resolve(cur) {
        Term::Var(i) if *i == self_idx => {
            args_rev.reverse();
            Some(args_rev)
        }
        _ => None,
    }
}

fn push_line(w: &mut String, indent: usize, s: &str) {
    for _ in 0..indent {
        w.push(' ');
    }
    w.push_str(s);
    w.push('\n');
}

fn arith_instr(op: PrimOp) -> Option<&'static str> {
    use PrimOp::*;
    Some(match op {
        Add => "i64.add",
        Sub => "i64.sub",
        Mul => "i64.mul",
        Div => "i64.div_s",
        Mod => "i64.rem_s",
        Lt | Le | Eq => return None,
    })
}

fn cmp_instr(op: PrimOp) -> Option<&'static str> {
    use PrimOp::*;
    Some(match op {
        Lt => "i64.lt_s",
        Le => "i64.le_s",
        Eq => "i64.eq",
        Add | Sub | Mul | Div | Mod => return None,
    })
}

/// Compiles one node. `If`'s condition/branch structure, and everything
/// below a `Prim`, is identical whether or not we're in tail position (Wasm
/// typechecks an `if`/`else` the same way regardless of what's inside it) --
/// `tail` only changes what a self-call leaf compiles to: staged locals and
/// a loop-back (`br $L`, turning recursion into iteration) in tail position,
/// or an ordinary Wasm `call` otherwise.
fn compile_node(
    store: &TermStore,
    h: Hash,
    arity: usize,
    self_idx: Option<u32>,
    tail: bool,
    w: &mut String,
    indent: usize,
) -> Option<()> {
    if let Term::If(c, t, e) = store.resolve(h) {
        let (c, t, e) = (*c, *t, *e);
        compile_cond(store, c, arity, self_idx, w, indent)?;
        push_line(w, indent, "if (result i64)");
        compile_node(store, t, arity, self_idx, tail, w, indent + 2)?;
        push_line(w, indent, "else");
        compile_node(store, e, arity, self_idx, tail, w, indent + 2)?;
        push_line(w, indent, "end");
        return Some(());
    }

    if let Some(args) = match_self_call(store, h, arity, self_idx) {
        if tail {
            // Evaluate all new argument values into temporaries first, so a
            // recursive call like `f(b, a mod b)` doesn't clobber `a`
            // before `a mod b` is computed, then loop back.
            for (i, a) in args.iter().enumerate() {
                compile_node(store, *a, arity, self_idx, false, w, indent)?;
                push_line(w, indent, &format!("local.set $t{i}"));
            }
            for i in 0..arity {
                push_line(w, indent, &format!("local.get $t{i}"));
                push_line(w, indent, &format!("local.set $p{i}"));
            }
            push_line(w, indent, "br $L");
        } else {
            for a in &args {
                compile_node(store, *a, arity, self_idx, false, w, indent)?;
            }
            push_line(w, indent, "call $f");
        }
        return Some(());
    }

    match store.resolve(h) {
        Term::Var(i) => {
            let li = local_index(*i, arity)?;
            push_line(w, indent, &format!("local.get $p{li}"));
        }
        Term::Lit(n) => push_line(w, indent, &format!("i64.const {n}")),
        Term::Prim(op, a, b) => {
            let (a, b) = (*a, *b);
            let instr = arith_instr(*op)?;
            compile_node(store, a, arity, self_idx, false, w, indent)?;
            compile_node(store, b, arity, self_idx, false, w, indent)?;
            push_line(w, indent, instr);
        }
        // Abs, Rec, free App: outside the compilable fragment. (`If` was
        // already handled above.)
        Term::If(..) | Term::Abs(_) | Term::Rec(_) | Term::App(..) => return None,
    }
    Some(())
}

fn compile_cond(
    store: &TermStore,
    h: Hash,
    arity: usize,
    self_idx: Option<u32>,
    w: &mut String,
    indent: usize,
) -> Option<()> {
    match store.resolve(h) {
        Term::Prim(op, a, b) => {
            let (a, b) = (*a, *b);
            let instr = cmp_instr(*op)?;
            compile_node(store, a, arity, self_idx, false, w, indent)?;
            compile_node(store, b, arity, self_idx, false, w, indent)?;
            push_line(w, indent, instr);
            Some(())
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::eval::apply_term;
    use crate::term::PrimOp;

    fn factorial(s: &mut TermStore) -> Hash {
        let n = s.var(0);
        let f = s.var(1);
        let one = s.lit(1);
        let cond = s.prim(PrimOp::Le, n, one);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one);
        let rec_call = s.app(f, n_minus_1);
        let else_branch = s.prim(PrimOp::Mul, n, rec_call);
        let body = s.if_(cond, one, else_branch);
        let abs = s.abs(body);
        s.rec(abs)
    }

    fn gcd(s: &mut TermStore) -> Hash {
        // rec f a b = if b == 0 then a else f(b, a mod b)
        let b = s.var(0);
        let a = s.var(1);
        let f = s.var(2);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Eq, b, zero);
        let a_mod_b = s.prim(PrimOp::Mod, a, b);
        let rec_call = s.app2(f, b, a_mod_b);
        let body = s.if_(cond, a, rec_call);
        let inner = s.abs(body);
        let abs = s.abs(inner);
        s.rec(abs)
    }

    #[test]
    fn factorial_compiles_and_matches_interpreter() {
        let mut s = TermStore::new();
        let fact = factorial(&mut s);
        let frag = try_compile(&s, fact).expect("should be compilable");
        assert_eq!(frag.arity, 1);

        let bytes = wat::parse_str(&frag.wat).expect("valid wat");
        let engine = wasmtime::Engine::default();
        let module = wasmtime::Module::new(&engine, &bytes).unwrap();
        let mut store = wasmtime::Store::new(&engine, ());
        let instance = wasmtime::Instance::new(&mut store, &module, &[]).unwrap();
        let func = instance.get_typed_func::<i64, i64>(&mut store, "f").unwrap();

        for n in 0..15 {
            let compiled = func.call(&mut store, n).unwrap();
            let interpreted = apply_term(&s, fact, &[n]).unwrap();
            assert_eq!(compiled, interpreted, "mismatch at n={n}");
        }
    }

    #[test]
    fn gcd_two_arg_tail_recursion_compiles() {
        let mut s = TermStore::new();
        let g = gcd(&mut s);
        let frag = try_compile(&s, g).expect("should be compilable");
        assert_eq!(frag.arity, 2);

        let bytes = wat::parse_str(&frag.wat).expect("valid wat");
        let engine = wasmtime::Engine::default();
        let module = wasmtime::Module::new(&engine, &bytes).unwrap();
        let mut store = wasmtime::Store::new(&engine, ());
        let instance = wasmtime::Instance::new(&mut store, &module, &[]).unwrap();
        let func = instance
            .get_typed_func::<(i64, i64), i64>(&mut store, "f")
            .unwrap();

        for (a, b) in [(48, 18), (17, 5), (0, 7), (270, 192)] {
            let compiled = func.call(&mut store, (a, b)).unwrap();
            let interpreted = apply_term(&s, g, &[a, b]).unwrap();
            assert_eq!(compiled, interpreted, "mismatch at a={a} b={b}");
        }
    }

    #[test]
    fn genuinely_higher_order_terms_are_rejected() {
        // twice = \f. \x. f (f x) -- has no arithmetic body, not in the fragment.
        let mut s = TermStore::new();
        let f = s.var(1);
        let x = s.var(0);
        let fx = s.app(f, x);
        let ffx = s.app(f, fx);
        let inner = s.abs(ffx);
        let twice = s.abs(inner);
        assert!(try_compile(&s, twice).is_none());
    }
}
