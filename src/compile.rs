//! Compiles a restricted "first-order arithmetic with self-recursion and
//! non-capturing closures" fragment of the term language down to
//! WebAssembly text (WAT) — our formalization of the target machine.
//! `wasmtime` then JIT-compiles that WAT (via Cranelift) to native code.
//!
//! Only a subset of terms fall in this fragment: closed expressions built
//! from `Var`/`Lit`/`Prim`/`If`, fully-saturated self-calls (optionally
//! wrapped in `Rec` for recursion), and fully-saturated applications of
//! either a parameter or a literal lambda value ("combinator" below).
//! Anything else (partial application, free variables, a closure that
//! *captures* a variable from an enclosing scope, ...) is rejected by
//! returning `None`, and the caller falls back to the interpreter — the
//! JIT never has to be complete, only sound about what it accepts.
//!
//! Tail self-calls are compiled into a `loop`/`br`, turning tail recursion
//! into iteration (constant Wasm call-stack depth); non-tail self-calls
//! fall back to an ordinary Wasm `call`.
//!
//! ## Closures: known calls, not general closure conversion
//!
//! Every value in this fragment is a plain `i64` -- including a closure
//! value, which is simply the index of a *non-capturing* lambda ("known
//! function"/"known call" in the compiler literature) in a shared Wasm
//! function table. This needs no heap, no environment record, and no
//! change at all to how `Int` is represented: a lambda can only be
//! compiled this way if, peeled standalone, every one of its free
//! variables resolves within its *own* parameter range -- i.e. it
//! captures nothing from any enclosing scope. That's not a separate check
//! this module runs; it falls out for free from `local_index` already
//! rejecting an out-of-range `Var` the same way it always has, applied to
//! a lambda peeled in isolation from wherever it was found.
//!
//! A closure value can then be *applied* two ways: through a parameter
//! that's always called with the same number of arguments everywhere in
//! its own function (`infer_closure_arities` finds these, and application
//! compiles to Wasm's `call_indirect` through the shared table), or as a
//! literal lambda appearing directly in function position
//! (`Combinators::register` gives it a table slot and its call compiles
//! to an ordinary, statically-known `call`). Passing a lambda around as a
//! value it's never applied to (an argument, a branch's result, ...)
//! just needs its table index as a compile-time constant.
//!
//! What's still out of scope: partial application, a parameter applied
//! with inconsistent arities across call sites, and (structurally, not by
//! a special check) any *capturing* closure. `Combinators` also doesn't
//! statically check that a value passed into a closure-typed parameter
//! actually has the arity that parameter's own body expects of it --
//! `call_indirect`'s own dynamic type check catches a mismatch as a trap,
//! caught safely by `jit.rs`'s sample verification the same way any other
//! compiler bug would be.

use hashbrown::HashMap;

use crate::term::{Hash, PrimOp, Term, TermStore};

pub struct CompiledFragment {
    pub arity: usize,
    pub wat: String,
}

/// Discovers and compiles non-capturing lambda values found while
/// compiling a function (see module docs). `index`/`arities` describe
/// every combinator registered so far (in registration order, `arities`
/// parallel to a combinator's assigned index); `pending` holds ones not
/// yet compiled to Wat; `call_indirect_arities` accumulates every arity
/// actually used at a `call_indirect` site, for the `(type ...)`
/// declarations that need to exist once each, not once per site.
struct Combinators<'a> {
    store: &'a TermStore,
    index: HashMap<Hash, usize>,
    pending: Vec<Hash>,
    arities: Vec<usize>,
    call_indirect_arities: Vec<usize>,
}

impl<'a> Combinators<'a> {
    fn new(store: &'a TermStore) -> Self {
        Combinators { store, index: HashMap::new(), pending: Vec::new(), arities: Vec::new(), call_indirect_arities: Vec::new() }
    }

    /// Registers `h` (a lambda value, i.e. an `Abs`-chain) if not already
    /// known, returning its assigned table index either way. `None` if
    /// `h` doesn't even peel as a nonzero-arity function (a bare closure
    /// value always takes at least one argument -- if it didn't, there'd
    /// be nothing to apply).
    fn register(&mut self, h: Hash) -> Option<usize> {
        if let Some(&i) = self.index.get(&h) {
            return Some(i);
        }
        let (arity, _, _) = peel(self.store, h)?;
        if arity == 0 {
            return None;
        }
        let idx = self.arities.len();
        self.index.insert(h, idx);
        self.arities.push(arity);
        self.pending.push(h);
        Some(idx)
    }
}

/// Try to compile `h` as an `arity`-ary numeric function (or, for `arity`
/// `0`, a single closed expression to evaluate once). Returns `None` if
/// `h` (or any subterm reachable in "tail position" tracking, or any
/// combinator value it uses) falls outside the compilable fragment.
pub fn try_compile(store: &TermStore, h: Hash) -> Option<CompiledFragment> {
    let (arity, body, is_rec) = peel(store, h)?;
    let self_idx = if is_rec { Some(arity as u32) } else { None };

    let mut combinators = Combinators::new(store);
    let mut fn_wat = String::new();
    compile_function(store, "f", arity, self_idx, body, &mut combinators, &mut fn_wat)?;

    // Fixpoint: compiling one combinator's body can discover more.
    let mut combinator_wat = String::new();
    while let Some(h_c) = combinators.pending.pop() {
        let idx = combinators.index[&h_c];
        let (c_arity, c_body, c_is_rec) = peel(store, h_c)?;
        let c_self_idx = if c_is_rec { Some(c_arity as u32) } else { None };
        compile_function(store, &format!("c{idx}"), c_arity, c_self_idx, c_body, &mut combinators, &mut combinator_wat)?;
    }

    let mut w = String::new();
    w.push_str("(module\n");
    let mut used_arities = combinators.call_indirect_arities.clone();
    used_arities.sort_unstable();
    used_arities.dedup();
    for k in &used_arities {
        w.push_str(&format!("  (type $ty{k} (func"));
        for _ in 0..*k {
            w.push_str(" (param i64)");
        }
        w.push_str(" (result i64)))\n");
    }
    if !combinators.arities.is_empty() {
        w.push_str(&format!("  (table {} funcref)\n", combinators.arities.len()));
        w.push_str("  (elem (i32.const 0)");
        for i in 0..combinators.arities.len() {
            w.push_str(&format!(" $c{i}"));
        }
        w.push_str(")\n");
    }
    w.push_str(&combinator_wat);
    w.push_str(&fn_wat);
    w.push_str("  (export \"f\" (func $f))\n)\n");

    Some(CompiledFragment { arity, wat: w })
}

/// Compiles `body` (an `arity`-ary function, `self_idx` set iff it's
/// self-recursive) into a named Wasm function, appended to `w`. Shared by
/// the top-level term and every combinator `Combinators` discovers --
/// there's nothing structurally different between them, just where each
/// one is referenced from.
fn compile_function(
    store: &TermStore,
    name: &str,
    arity: usize,
    self_idx: Option<u32>,
    body: Hash,
    combinators: &mut Combinators,
    w: &mut String,
) -> Option<()> {
    let closure_arities = infer_closure_arities(store, body, arity, self_idx)?;
    let ctx = FnCtx { store, arity, self_idx, closure_arities: &closure_arities };

    w.push_str(&format!("  (func ${name}"));
    for i in 0..arity {
        w.push_str(&format!(" (param $p{i} i64)"));
    }
    w.push_str(" (result i64)\n");
    for i in 0..arity {
        w.push_str(&format!("    (local $t{i} i64)\n"));
    }
    w.push_str("    (loop $L (result i64)\n");
    compile_node(&ctx, combinators, body, true, w, 6)?;
    w.push_str("    )\n  )\n");
    Some(())
}

/// Peel a term into `(arity, body, is_recursive)`:
/// - `Rec(Abs(Abs(...body)))` -> `(k, body, true)`, self bound at `Var(k)`,
///   `k > 0` (a 0-ary self-recursive definition would have no base case
///   reachable via any argument -- out of scope, not just unlikely).
/// - `Abs(Abs(...body))` (no `Rec`) -> `(k, body, false)`, `k` possibly
///   `0` (a closed expression with no top-level `Abs` at all, e.g. a
///   fully-saturated application of a couple of combinators -- evaluated
///   once, not called with arguments).
pub(crate) fn peel(store: &TermStore, h: Hash) -> Option<(usize, Hash, bool)> {
    match store.resolve(h) {
        Term::Rec(inner) => {
            let (k, body) = peel_abs(store, *inner);
            (k > 0).then_some((k, body, true))
        }
        _ => {
            let (k, body) = peel_abs(store, h);
            Some((k, body, false))
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
    // `then_some` takes its argument by value, not lazily -- `a - 1 - var`
    // would underflow-panic for an out-of-range `var` before `then_some`
    // ever got to check the condition, so this needs an actual branch.
    let a = arity as u32;
    if var < a { Some(a - 1 - var) } else { None }
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

/// Unwinds a chain of `App` nodes into `(root, args)` -- `root` is the
/// first non-`App` node reached, `args` its arguments in application
/// order. `root == h` with `args` empty if `h` isn't an `App` at all.
pub(crate) fn unwind_app_spine(store: &TermStore, mut h: Hash) -> (Hash, Vec<Hash>) {
    let mut args = Vec::new();
    while let Term::App(f, a) = store.resolve(h) {
        args.push(*a);
        h = *f;
    }
    args.reverse();
    (h, args)
}

/// For each of `h`'s own `arity` parameters (indexed the same way
/// `local_index` does), finds whether it's ever used as an application's
/// callee and, if so, at what arity -- e.g. `f` in `f(f(x))` is `Some(1)`.
/// Used with an inconsistent arity across call sites (`f(x)` *and*
/// `f(x,y)`) fails the whole function (partial application isn't
/// supported); never applied at all (just read as a value) is `None`.
pub(crate) fn infer_closure_arities(store: &TermStore, h: Hash, arity: usize, self_idx: Option<u32>) -> Option<Vec<Option<usize>>> {
    let mut found = vec![None; arity];
    scan_for_closure_calls(store, h, arity, self_idx, &mut found)?;
    Some(found)
}

fn scan_for_closure_calls(
    store: &TermStore,
    h: Hash,
    arity: usize,
    self_idx: Option<u32>,
    found: &mut [Option<usize>],
) -> Option<()> {
    if let Term::If(c, t, e) = store.resolve(h) {
        let (c, t, e) = (*c, *t, *e);
        scan_for_closure_calls(store, c, arity, self_idx, found)?;
        scan_for_closure_calls(store, t, arity, self_idx, found)?;
        scan_for_closure_calls(store, e, arity, self_idx, found)?;
        return Some(());
    }
    if let Some(args) = match_self_call(store, h, arity, self_idx) {
        for a in args {
            scan_for_closure_calls(store, a, arity, self_idx, found)?;
        }
        return Some(());
    }
    if matches!(store.resolve(h), Term::App(..)) {
        let (root, args) = unwind_app_spine(store, h);
        match store.resolve(root) {
            Term::Var(i) if (*i as usize) < arity => {
                let li = local_index(*i, arity)? as usize;
                match found[li] {
                    None => found[li] = Some(args.len()),
                    Some(k) if k == args.len() => {}
                    Some(_) => return None, // inconsistent arity: partial application
                }
            }
            Term::Abs(_) => {} // a literal redex callee -- fine, checked again at codegen
            _ => return None,  // callee is neither a parameter nor a literal lambda
        }
        for a in &args {
            scan_for_closure_calls(store, *a, arity, self_idx, found)?;
        }
        return Some(());
    }
    match store.resolve(h) {
        Term::Var(_) | Term::Lit(_) => Some(()),
        Term::Prim(_, a, b) => {
            scan_for_closure_calls(store, *a, arity, self_idx, found)?;
            scan_for_closure_calls(store, *b, arity, self_idx, found)
        }
        Term::Abs(_) => Some(()), // a lambda used as a plain value (an argument, a branch result, ...)
        Term::If(..) | Term::App(..) | Term::Rec(_) => unreachable!("handled above"),
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

/// Everything about the function currently being compiled that stays fixed
/// across its whole body -- as opposed to `h`/`tail`/`w`/`indent`, which
/// vary at each recursive step. Bundled together mainly to keep
/// `compile_node`/`compile_cond`'s own argument counts down; `combinators`
/// stays separate since it's mutated across *all* functions being
/// compiled, not just this one.
struct FnCtx<'a, 'b> {
    store: &'a TermStore,
    arity: usize,
    self_idx: Option<u32>,
    closure_arities: &'b [Option<usize>],
}

/// Compiles one node. `If`'s condition/branch structure, and everything
/// below a `Prim`, is identical whether or not we're in tail position (Wasm
/// typechecks an `if`/`else` the same way regardless of what's inside it) --
/// `tail` only changes what a self-call leaf compiles to: staged locals and
/// a loop-back (`br $L`, turning recursion into iteration) in tail position,
/// or an ordinary Wasm `call` otherwise.
fn compile_node(
    ctx: &FnCtx,
    combinators: &mut Combinators,
    h: Hash,
    tail: bool,
    w: &mut String,
    indent: usize,
) -> Option<()> {
    let (store, arity, self_idx) = (ctx.store, ctx.arity, ctx.self_idx);

    if let Term::If(c, t, e) = store.resolve(h) {
        let (c, t, e) = (*c, *t, *e);
        compile_cond(ctx, combinators, c, w, indent)?;
        push_line(w, indent, "if (result i64)");
        compile_node(ctx, combinators, t, tail, w, indent + 2)?;
        push_line(w, indent, "else");
        compile_node(ctx, combinators, e, tail, w, indent + 2)?;
        push_line(w, indent, "end");
        return Some(());
    }

    if let Some(args) = match_self_call(store, h, arity, self_idx) {
        if tail {
            // Evaluate all new argument values into temporaries first, so a
            // recursive call like `f(b, a mod b)` doesn't clobber `a`
            // before `a mod b` is computed, then loop back.
            for (i, a) in args.iter().enumerate() {
                compile_node(ctx, combinators, *a, false, w, indent)?;
                push_line(w, indent, &format!("local.set $t{i}"));
            }
            for i in 0..arity {
                push_line(w, indent, &format!("local.get $t{i}"));
                push_line(w, indent, &format!("local.set $p{i}"));
            }
            push_line(w, indent, "br $L");
        } else {
            for a in &args {
                compile_node(ctx, combinators, *a, false, w, indent)?;
            }
            push_line(w, indent, "call $f");
        }
        return Some(());
    }

    if matches!(store.resolve(h), Term::App(..)) {
        let (root, args) = unwind_app_spine(store, h);
        match store.resolve(root) {
            Term::Var(i) if (*i as usize) < arity => {
                let li = local_index(*i, arity)?;
                let expected = ctx.closure_arities[li as usize]?;
                if args.len() != expected {
                    return None;
                }
                for a in &args {
                    compile_node(ctx, combinators, *a, false, w, indent)?;
                }
                push_line(w, indent, &format!("local.get $p{li}"));
                push_line(w, indent, "i32.wrap_i64");
                combinators.call_indirect_arities.push(expected);
                push_line(w, indent, &format!("call_indirect (type $ty{expected})"));
                return Some(());
            }
            Term::Abs(_) => {
                let idx = combinators.register(root)?;
                if args.len() != combinators.arities[idx] {
                    return None;
                }
                for a in &args {
                    compile_node(ctx, combinators, *a, false, w, indent)?;
                }
                push_line(w, indent, &format!("call $c{idx}"));
                return Some(());
            }
            _ => return None,
        }
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
            compile_node(ctx, combinators, a, false, w, indent)?;
            compile_node(ctx, combinators, b, false, w, indent)?;
            push_line(w, indent, instr);
        }
        Term::Abs(_) => {
            // A lambda used as a plain value (e.g. an argument): its
            // value is just its table index, a compile-time constant.
            let idx = combinators.register(h)?;
            push_line(w, indent, &format!("i64.const {idx}"));
        }
        // Rec, free App: outside the compilable fragment. (`If` and
        // known/combinator `App`s were already handled above.)
        Term::If(..) | Term::Rec(_) | Term::App(..) => return None,
    }
    Some(())
}

fn compile_cond(ctx: &FnCtx, combinators: &mut Combinators, h: Hash, w: &mut String, indent: usize) -> Option<()> {
    match ctx.store.resolve(h) {
        Term::Prim(op, a, b) => {
            let (a, b) = (*a, *b);
            let instr = cmp_instr(*op)?;
            compile_node(ctx, combinators, a, false, w, indent)?;
            compile_node(ctx, combinators, b, false, w, indent)?;
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

    /// `\f. \x. f (f x)` -- both `f` and `x` are its own parameters, no
    /// captures.
    fn twice(s: &mut TermStore) -> Hash {
        let f = s.var(1);
        let x = s.var(0);
        let fx = s.app(f, x);
        let ffx = s.app(f, fx);
        let inner = s.abs(ffx);
        s.abs(inner)
    }

    /// `\y. y + 1`.
    fn inc(s: &mut TermStore) -> Hash {
        let y = s.var(0);
        let one = s.lit(1);
        let y_plus_1 = s.prim(PrimOp::Add, y, one);
        s.abs(y_plus_1)
    }

    fn instantiate(wat: &str) -> (wasmtime::Store<()>, wasmtime::Instance) {
        let bytes = wat::parse_str(wat).expect("valid wat");
        let engine = wasmtime::Engine::default();
        let module = wasmtime::Module::new(&engine, &bytes).unwrap();
        let mut store = wasmtime::Store::new(&engine, ());
        let instance = wasmtime::Instance::new(&mut store, &module, &[]).unwrap();
        (store, instance)
    }

    #[test]
    fn factorial_compiles_and_matches_interpreter() {
        let mut s = TermStore::new();
        let fact = factorial(&mut s);
        let frag = try_compile(&s, fact).expect("should be compilable");
        assert_eq!(frag.arity, 1);

        let (mut store, instance) = instantiate(&frag.wat);
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

        let (mut store, instance) = instantiate(&frag.wat);
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
    fn twice_alone_compiles_with_a_closure_parameter() {
        // `twice` itself, as a standalone 2-ary function: `f` is a
        // closure parameter (always applied to exactly 1 argument), `x`
        // is a plain Int parameter -- exercises `call_indirect` without
        // going through a combinator table at all (nothing to register:
        // `f`'s VALUE is supplied by the caller, not a literal here).
        let mut s = TermStore::new();
        let t = twice(&mut s);
        let frag = try_compile(&s, t).expect("twice alone should be compilable");
        assert_eq!(frag.arity, 2);
        // Can't call it standalone from Rust (there's no way to pass "a
        // closure index" without a concrete table entry) -- covered
        // end-to-end by `applying_twice_to_a_literal_inc_compiles` below.
        assert!(frag.wat.contains("call_indirect"));
    }

    #[test]
    fn applying_twice_to_a_literal_inc_compiles_and_matches_interpreter() {
        // (twice inc) 5 -- the higher-order demo term main.rs uses.
        // `twice` and `inc` both become combinators in a shared function
        // table; the whole (closed, zero-arity) expression compiles to a
        // niladic function that calls `twice` directly (statically known)
        // and, inside `twice`, calls `inc` indirectly through the table.
        let mut s = TermStore::new();
        let t = twice(&mut s);
        let i = inc(&mut s);
        let five = s.lit(5);
        let applied = s.app2(t, i, five);

        let frag = try_compile(&s, applied).expect("should be compilable");
        assert_eq!(frag.arity, 0);

        let (mut store, instance) = instantiate(&frag.wat);
        let func = instance.get_typed_func::<(), i64>(&mut store, "f").unwrap();
        let compiled = func.call(&mut store, ()).unwrap();
        let interpreted = apply_term(&s, applied, &[]).unwrap();
        assert_eq!(compiled, 7);
        assert_eq!(compiled, interpreted);
    }

    #[test]
    fn a_capturing_closure_is_still_rejected() {
        // \x. if x > 0 then (\y. x + y) else 0 -- the inner lambda
        // references `x`, bound by the *outer* function, not its own
        // parameter range; peeled standalone (as any combinator is),
        // that's an out-of-bounds Var, so registering it fails and the
        // whole compile is rejected, not just that branch.
        let mut s = TermStore::new();
        let x = s.var(0);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Lt, zero, x);
        let y = s.var(0);
        let x_outer = s.var(1);
        let x_plus_y = s.prim(PrimOp::Add, x_outer, y);
        let capturing = s.abs(x_plus_y);
        let body = s.if_(cond, capturing, zero);
        let f = s.abs(body);

        assert!(try_compile(&s, f).is_none());
    }

    #[test]
    fn partial_application_is_still_rejected() {
        // \f. f(1) + f(1, 2) -- `f` called with inconsistent arities
        // (1 then 2) at different call sites -- not supported.
        let mut s = TermStore::new();
        let f1 = s.var(0);
        let one = s.lit(1);
        let call1 = s.app(f1, one);
        let f2 = s.var(0);
        let two = s.lit(2);
        let call2 = s.app2(f2, one, two);
        let body = s.prim(PrimOp::Add, call1, call2);
        let g = s.abs(body);

        assert!(try_compile(&s, g).is_none());
    }

    #[test]
    fn curried_application_is_indistinguishable_from_multi_arg_calls() {
        // \f. \x. (f x) x -- an honest boundary, not a bug: this *looks*
        // like `f` returning a genuine closure (from `f x`) which is then
        // applied to `x` again, but curried application in this term
        // representation has no arity tag at all -- `App(App(f,x),x)` is
        // exactly the same term shape as a plain 2-ary call `f(x,x)`.
        // `unwind_app_spine` can't tell those apart (nothing here could,
        // without adding real arity-annotated types), so this compiles as
        // "call f with 2 args" -- which is what it actually gets treated
        // as by every other part of this module (`infer_closure_arities`
        // included) too, not just an oversight in one place.
        let mut s = TermStore::new();
        let f = s.var(1);
        let x = s.var(0);
        let fx = s.app(f, x);
        let fxx = s.app(fx, x);
        let inner = s.abs(fxx);
        let g = s.abs(inner);
        let frag = try_compile(&s, g).expect("compiles as a 2-ary call to f");
        assert_eq!(frag.arity, 2);
        assert!(frag.wat.contains("call_indirect (type $ty2)"));
    }

    #[test]
    fn an_unbound_variable_is_rejected_not_a_panic() {
        // \x. y -- `y` (Var(3), arbitrary) is out of range for this
        // arity-1 function -- regression test for local_index's
        // then_some eagerly underflowing instead of returning None.
        let mut s = TermStore::new();
        let y = s.var(3);
        let f = s.abs(y);
        assert!(try_compile(&s, f).is_none());
    }
}
