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
//! ## Closures: real closure conversion, uniform representation
//!
//! Every value in this fragment is a plain `i64`, including a closure
//! value -- but a closure now packs *two* things into that one `i64`: a
//! table index (low 32 bits) identifying which compiled function to call,
//! and a pointer into linear memory (high 32 bits) to that closure's
//! *environment* -- the captured values it closed over, laid out as
//! consecutive `i64` slots and allocated by the bump allocator (see
//! `emit_allocator`) at the point the closure is created. A
//! *non-capturing* lambda ("known function"/"known call" in the compiler
//! literature) still needs no environment at all -- its pointer half is
//! just `0`, a constant, and its `$env` parameter goes unread -- so this
//! is one uniform representation, not two: every combinator takes an
//! `$env: i32` parameter first, whether or not its own body ever reads
//! from it, precisely so a `call_indirect` site never needs to know in
//! advance whether the closure it's calling captures anything.
//!
//! `free_vars` finds what a lambda literal captures, relative to its own
//! parameter range, by walking its body (following *into* further nested
//! lambdas too, since a closure nested inside another one still captures
//! from the very same enclosing scope) -- this becomes the environment's
//! slot layout. At every point a lambda literal is compiled (used as a
//! plain value, or as a call's callee), `push_closure_env` allocates that
//! layout's worth of memory and, slot by slot, reads each captured
//! value's *current* value out of whatever's compiling it right now
//! (`compile_var_read`, which itself resolves either to one of the
//! current function's own parameters or, recursively, to one of *its*
//! own environment slots -- so a closure nested several levels deep
//! captures through as many levels as it needs to, uniformly). A
//! self-recursive value's own self-reference is never treated as a
//! capture (it's bound by `Rec`, resolved separately by
//! `match_self_call`, and never itself a plain readable value) --
//! `free_vars` excludes it explicitly rather than have it (wrongly) show
//! up as an uncapturable free variable in every recursive function.
//!
//! A closure value can then be *applied* two ways: through a parameter
//! that's always called with the same number of arguments everywhere in
//! its own function (`infer_closure_arities` finds these, and application
//! compiles to Wasm's `call_indirect` through the shared table, unpacking
//! the environment pointer and table index back out of the packed `i64`
//! first), or as a literal lambda appearing directly in function position
//! (`Combinators::register` gives it a table slot and its call compiles
//! to an ordinary, statically-known `call`, with a freshly created
//! environment passed as that call's first argument). Passing a lambda
//! around as a value it's never applied to (an argument, a branch's
//! result, ...) packs its (possibly-empty) environment and table index
//! into a single `i64` the same way either path would.
//!
//! What's still out of scope: partial application, a parameter applied
//! with inconsistent arities across call sites, calling a closure reached
//! through a captured free variable rather than through one of the
//! current function's own parameters (`scan_for_closure_calls` only infers
//! closure-call arities for params), and capturing an enclosing
//! self-recursive binding's own self-reference as a plain value from a
//! *nested* closure (an honest, structural rejection -- see
//! `free_vars`'s self-exclusion -- rather than a special-cased check).
//! `Combinators` also doesn't statically check that a value passed into a
//! closure-typed parameter actually has the arity that parameter's own
//! body expects of it -- `call_indirect`'s own dynamic type check catches
//! a mismatch as a trap, caught safely by `jit.rs`'s sample verification
//! the same way any other compiler bug would be.

use hashbrown::HashMap;

use crate::term::{Hash, PrimOp, Term, TermStore};

pub struct CompiledFragment {
    pub arity: usize,
    pub wat: String,
}

/// Discovers and compiles lambda values found while compiling a function
/// (see module docs). `index`/`arities`/`captures` describe every
/// combinator registered so far (in registration order, parallel to a
/// combinator's assigned index -- `captures[idx]` is that combinator's
/// own environment slot layout, from `free_vars`); `pending` holds ones
/// not yet compiled to Wat; `call_indirect_arities` accumulates every
/// arity actually used at a `call_indirect` site, for the `(type ...)`
/// declarations that need to exist once each, not once per site.
struct Combinators<'a> {
    store: &'a TermStore,
    index: HashMap<Hash, usize>,
    pending: Vec<Hash>,
    arities: Vec<usize>,
    captures: Vec<Vec<u32>>,
    call_indirect_arities: Vec<usize>,
}

impl<'a> Combinators<'a> {
    fn new(store: &'a TermStore) -> Self {
        Combinators {
            store,
            index: HashMap::new(),
            pending: Vec::new(),
            arities: Vec::new(),
            captures: Vec::new(),
            call_indirect_arities: Vec::new(),
        }
    }

    /// Registers `h` (a lambda value, i.e. an `Abs`-chain -- or a named
    /// self-recursive value, an `Abs`-chain wrapped in `Rec`) if not
    /// already known, returning its assigned table index either way.
    /// `None` if `h` doesn't even peel as a nonzero-arity function (a bare
    /// closure value always takes at least one argument -- if it didn't,
    /// there'd be nothing to apply). `is_rec` isn't recorded here -- the
    /// fixpoint loop in `try_compile` re-`peel`s each pending combinator
    /// when it actually compiles its body, and determines `self_idx` from
    /// that; it's only needed here, transiently, for `free_vars` to
    /// correctly exclude a self-reference from the capture list.
    fn register(&mut self, h: Hash) -> Option<usize> {
        if let Some(&i) = self.index.get(&h) {
            return Some(i);
        }
        let (arity, body, is_rec) = peel(self.store, h)?;
        if arity == 0 {
            return None;
        }
        let captures = free_vars(self.store, body, arity, is_rec);
        let idx = self.arities.len();
        self.index.insert(h, idx);
        self.arities.push(arity);
        self.captures.push(captures);
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
    // `$f`, the synthetic entry point, is never itself referenced as a
    // value inside the term being compiled -- unlike every combinator, it
    // needs no `$env` parameter and (being the top of a closed term) has
    // no captures of its own to resolve free-variable reads against.
    let f_spec = FnSpec { name: "f", arity, self_idx, has_env: false, captures: &[] };
    compile_function(store, body, &f_spec, &mut combinators, &mut fn_wat)?;

    // Fixpoint: compiling one combinator's body can discover more.
    let mut combinator_wat = String::new();
    while let Some(h_c) = combinators.pending.pop() {
        let idx = combinators.index[&h_c];
        let (c_arity, c_body, c_is_rec) = peel(store, h_c)?;
        let c_self_idx = if c_is_rec { Some(c_arity as u32) } else { None };
        let captures = combinators.captures[idx].clone();
        let c_name = format!("c{idx}");
        let c_spec = FnSpec { name: &c_name, arity: c_arity, self_idx: c_self_idx, has_env: true, captures: &captures };
        compile_function(store, c_body, &c_spec, &mut combinators, &mut combinator_wat)?;
    }

    let mut w = String::new();
    w.push_str("(module\n");
    let mut used_arities = combinators.call_indirect_arities.clone();
    used_arities.sort_unstable();
    used_arities.dedup();
    for k in &used_arities {
        // Every combinator uniformly takes its environment pointer as its
        // first parameter (see module docs), so `call_indirect`'s type
        // must include it too, regardless of whether the callee at any
        // particular call actually captures anything.
        w.push_str(&format!("  (type $ty{k} (func (param i32)"));
        for _ in 0..*k {
            w.push_str(" (param i64)");
        }
        w.push_str(" (result i64)))\n");
    }
    if combinators.captures.iter().any(|c| !c.is_empty()) {
        emit_allocator(&mut w);
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

/// A function's own identity, everything `compile_function` needs about
/// it besides its body -- bundled together (rather than passed as five
/// separate arguments) purely to keep `compile_function`'s own signature
/// down. See `FnCtx`'s fields for what each of these means.
struct FnSpec<'b> {
    name: &'b str,
    arity: usize,
    self_idx: Option<u32>,
    has_env: bool,
    captures: &'b [u32],
}

/// Compiles `body` (an `arity`-ary function, `self_idx` set iff it's
/// self-recursive) into a named Wasm function, appended to `w`. Shared by
/// the top-level term and every combinator `Combinators` discovers --
/// there's nothing structurally different between them, just where each
/// one is referenced from. `has_env` is true for every combinator (never
/// for `$f`, see its call site) -- `captures` is that function's own
/// environment slot layout (empty for `$f` and any non-capturing
/// combinator), used to resolve a free-variable read within its body.
fn compile_function(store: &TermStore, body: Hash, spec: &FnSpec, combinators: &mut Combinators, w: &mut String) -> Option<()> {
    let FnSpec { name, arity, self_idx, has_env, captures } = *spec;
    let closure_arities = infer_closure_arities(store, body, arity, self_idx)?;
    let ctx = FnCtx { store, name, arity, self_idx, closure_arities: &closure_arities, has_env, captures };

    w.push_str(&format!("  (func ${name}"));
    if has_env {
        w.push_str(" (param $env i32)");
    }
    for i in 0..arity {
        w.push_str(&format!(" (param $p{i} i64)"));
    }
    w.push_str(" (result i64)\n");
    for i in 0..arity {
        w.push_str(&format!("    (local $t{i} i64)\n"));
    }
    // Scratch local for `push_closure_env`, holding an in-progress
    // environment's pointer while its slots are populated -- declared
    // unconditionally (harmless if unused) since whether *this* function
    // ever creates a capturing closure isn't known until its body is
    // walked below.
    w.push_str("    (local $envtmp i32)\n");
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

/// Finds what a lambda literal (peeled to `own_arity`/`body`/`is_rec`,
/// same shape `peel` returns) captures from its enclosing scope: every
/// `Var` in `body` that isn't bound within `body` itself, expressed as
/// how far *beyond* `own_arity` it reaches (`0` = the nearest enclosing
/// binding, `1` = the next one out, ...), deduped and sorted ascending --
/// this becomes the closure's environment slot layout (slot `j` holds
/// whatever denoted relative depth `result[j]` at the point the closure
/// was created). Follows into a lambda nested inside `body` and used
/// there as a plain value too (not just `body`'s own top level), since a
/// closure nested inside another one still captures from the very same
/// enclosing scope this one does.
///
/// A self-recursive value's own self-reference (`Var(own_arity)`, exactly
/// where `Rec`'s binder sits, whenever `is_rec`) is deliberately excluded
/// here, at every depth it's found, not just `body`'s own top level --
/// it's resolved separately by `match_self_call`/an ordinary recursive
/// `call`, and (like before this function existed at all) still can't be
/// read as a plain value; without this exclusion *every* self-recursive
/// function would show up as having an uncapturable "capture" the moment
/// it made its own recursive call.
pub(crate) fn free_vars(store: &TermStore, body: Hash, own_arity: usize, is_rec: bool) -> Vec<u32> {
    let mut found = std::collections::BTreeSet::new();
    collect_free_vars(store, body, own_arity as u32, is_rec, 0, &mut found);
    found.into_iter().collect()
}

fn collect_free_vars(
    store: &TermStore,
    h: Hash,
    own_arity: u32,
    is_rec: bool,
    depth: u32,
    found: &mut std::collections::BTreeSet<u32>,
) {
    match store.resolve(h) {
        Term::Var(i) => {
            let i = *i;
            if i < depth {
                return; // bound by a binder nested inside `body` itself
            }
            let rel = i - depth;
            if rel < own_arity {
                return; // bound by this lambda's own parameters
            }
            if is_rec && rel == own_arity {
                return; // the self-reference `Rec` binds, not a capture
            }
            let capture_base = if is_rec { own_arity + 1 } else { own_arity };
            found.insert(rel - capture_base);
        }
        Term::Lit(_) => {}
        Term::Abs(inner) => collect_free_vars(store, *inner, own_arity, is_rec, depth + 1, found),
        Term::Rec(inner) => collect_free_vars(store, *inner, own_arity, is_rec, depth + 1, found),
        Term::App(f, a) => {
            let (f, a) = (*f, *a);
            collect_free_vars(store, f, own_arity, is_rec, depth, found);
            collect_free_vars(store, a, own_arity, is_rec, depth, found);
        }
        Term::Prim(_, a, b) => {
            let (a, b) = (*a, *b);
            collect_free_vars(store, a, own_arity, is_rec, depth, found);
            collect_free_vars(store, b, own_arity, is_rec, depth, found);
        }
        Term::If(c, t, e) => {
            let (c, t, e) = (*c, *t, *e);
            collect_free_vars(store, c, own_arity, is_rec, depth, found);
            collect_free_vars(store, t, own_arity, is_rec, depth, found);
            collect_free_vars(store, e, own_arity, is_rec, depth, found);
        }
    }
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
            Term::Abs(_) | Term::Rec(_) => {} // a literal redex callee (possibly self-recursive) -- fine, checked again at codegen
            _ => return None,  // callee is neither a parameter nor a literal lambda/combinator
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
        // A lambda -- or a named self-recursive value, e.g. one bound by
        // `let fact = rec f n = .. in ..` and later called through that
        // binding -- used as a plain value (an argument, a branch
        // result, ...).
        Term::Abs(_) | Term::Rec(_) => Some(()),
        Term::If(..) | Term::App(..) => unreachable!("handled above"),
    }
}

/// Emits a bump allocator: one page (64KiB) of linear memory, a mutable
/// global `$hp` tracking the next free byte, and an `$alloc` function that
/// hands out `$n` bytes at a time, growing the memory (via `memory.grow`)
/// whenever `$hp` would run past the end of what's currently allocated.
/// Never reclaimed -- compiled instances are short-lived and per-call (see
/// `jit.rs`), so there's no GC here, just like there's no GC in the
/// combinator table above. `try_compile` emits this only when at least
/// one registered combinator actually has a non-empty environment
/// (`push_closure_env` is the only caller of `$alloc`) -- a compiled
/// fragment with no capturing closures at all gets no memory section.
fn emit_allocator(w: &mut String) {
    w.push_str("  (memory 1)\n");
    w.push_str("  (global $hp (mut i32) (i32.const 0))\n");
    w.push_str("  (func $alloc (param $n i32) (result i32)\n");
    w.push_str("    (local $base i32)\n");
    w.push_str("    (local $need i32)\n");
    push_line(w, 4, "global.get $hp");
    push_line(w, 4, "local.set $base");
    push_line(w, 4, "local.get $base");
    push_line(w, 4, "local.get $n");
    push_line(w, 4, "i32.add");
    push_line(w, 4, "local.set $need");
    // Grow if $need would exceed the current memory size in bytes.
    push_line(w, 4, "local.get $need");
    push_line(w, 4, "memory.size");
    push_line(w, 4, "i32.const 65536");
    push_line(w, 4, "i32.mul");
    push_line(w, 4, "i32.gt_u");
    push_line(w, 4, "if");
    // pages_needed = ceil(($need - current_bytes) / 65536)
    push_line(w, 6, "local.get $need");
    push_line(w, 6, "memory.size");
    push_line(w, 6, "i32.const 65536");
    push_line(w, 6, "i32.mul");
    push_line(w, 6, "i32.sub");
    push_line(w, 6, "i32.const 65535");
    push_line(w, 6, "i32.add");
    push_line(w, 6, "i32.const 65536");
    push_line(w, 6, "i32.div_u");
    push_line(w, 6, "memory.grow");
    push_line(w, 6, "drop");
    push_line(w, 4, "end");
    push_line(w, 4, "local.get $need");
    push_line(w, 4, "global.set $hp");
    push_line(w, 4, "local.get $base");
    w.push_str("  )\n");
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
    /// This function's own Wasm name (`f` for the main entry point, `c{idx}`
    /// for a combinator) -- a non-tail self-call needs this to call back
    /// into *this* function, not hardcode `$f`.
    name: &'b str,
    arity: usize,
    self_idx: Option<u32>,
    closure_arities: &'b [Option<usize>],
    /// Whether this function itself takes an `$env` parameter (true for
    /// every combinator, false for `$f` -- see `compile_function`'s call
    /// sites). A non-tail self-call needs to know this to decide whether
    /// to forward `$env` to itself.
    has_env: bool,
    /// This function's own environment slot layout (from `free_vars`,
    /// empty if it captures nothing) -- `compile_var_read` resolves a
    /// free-variable read (`Var(v)` with `v >= arity`) against this.
    captures: &'b [u32],
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
            // A non-tail self-call is a genuine, separate Wasm `call` back
            // into this same function's own activation -- it needs its
            // own `$env` forwarded unchanged (recursion stays within the
            // one closure instance that's already running; it never gets
            // a fresh environment of its own).
            if ctx.has_env {
                push_line(w, indent, "local.get $env");
            }
            for a in &args {
                compile_node(ctx, combinators, *a, false, w, indent)?;
            }
            push_line(w, indent, &format!("call ${}", ctx.name));
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
                // Unpack the callee's environment pointer (high 32 bits)
                // first -- it's `call_indirect`'s first operand, ahead of
                // the actual arguments -- then its table index (low 32
                // bits) last, as `call_indirect` itself requires.
                push_line(w, indent, &format!("local.get $p{li}"));
                push_line(w, indent, "i64.const 32");
                push_line(w, indent, "i64.shr_u");
                push_line(w, indent, "i32.wrap_i64");
                for a in &args {
                    compile_node(ctx, combinators, *a, false, w, indent)?;
                }
                push_line(w, indent, &format!("local.get $p{li}"));
                push_line(w, indent, "i32.wrap_i64");
                combinators.call_indirect_arities.push(expected);
                push_line(w, indent, &format!("call_indirect (type $ty{expected})"));
                return Some(());
            }
            Term::Abs(_) | Term::Rec(_) => {
                let idx = combinators.register(root)?;
                if args.len() != combinators.arities[idx] {
                    return None;
                }
                let captures = combinators.captures[idx].clone();
                push_closure_env(ctx, &captures, w, indent)?;
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
        Term::Var(i) => compile_var_read(ctx, *i, w, indent)?,
        Term::Lit(n) => push_line(w, indent, &format!("i64.const {n}")),
        Term::Prim(op, a, b) => {
            let (a, b) = (*a, *b);
            let instr = arith_instr(*op)?;
            compile_node(ctx, combinators, a, false, w, indent)?;
            compile_node(ctx, combinators, b, false, w, indent)?;
            push_line(w, indent, instr);
        }
        Term::Abs(_) | Term::Rec(_) => {
            // A lambda, or a named self-recursive value (e.g. one bound
            // by `let fact = rec f n = .. in ..`), used as a plain value
            // (e.g. an argument): packs its (possibly-empty) environment
            // and table index into one `i64`, high bits first -- see
            // module docs. `Combinators::register`/the fixpoint loop in
            // `try_compile` already re-`peel` whatever they register and
            // correctly compile a self-recursive combinator's own body
            // with its own `self_idx`, so nothing else here needs to
            // change to support this.
            let idx = combinators.register(h)?;
            let captures = combinators.captures[idx].clone();
            push_closure_env(ctx, &captures, w, indent)?;
            push_line(w, indent, "i64.extend_i32_u");
            push_line(w, indent, "i64.const 32");
            push_line(w, indent, "i64.shl");
            push_line(w, indent, &format!("i64.const {idx}"));
            push_line(w, indent, "i64.or");
        }
        // Free App: outside the compilable fragment. (`If` and
        // known/combinator `App`s were already handled above.)
        Term::If(..) | Term::App(..) => return None,
    }
    Some(())
}

/// Resolves a value read for absolute `Var` index `v` within `ctx`'s own
/// body (at `ctx`'s own top level, no additional binders passed): either
/// one of `ctx`'s own parameters (`v < ctx.arity`, exactly as before
/// closures could capture anything), or -- recursively, the same way any
/// other value read within `ctx` resolves -- one of `ctx`'s own
/// environment slots. `None` if `v` resolves to neither (out of range
/// entirely, or `ctx`'s own self-reference used as a plain value, which
/// was never supported and still isn't).
fn compile_var_read(ctx: &FnCtx, v: u32, w: &mut String, indent: usize) -> Option<()> {
    let arity = ctx.arity as u32;
    if v < arity {
        let li = local_index(v, ctx.arity)?;
        push_line(w, indent, &format!("local.get $p{li}"));
        return Some(());
    }
    let rel = v - arity;
    let slot = ctx.captures.iter().position(|&c| c == rel)?;
    push_line(w, indent, "local.get $env");
    push_line(w, indent, &format!("i64.load offset={}", slot * 8));
    Some(())
}

/// Pushes an `i32` environment pointer for a closure whose slot layout is
/// `captures` (from `free_vars`), reading each captured value's current
/// value out of `ctx` (`compile_var_read`, against `captures`'s own
/// relative indices directly -- `ctx` is exactly the scope those indices
/// were computed relative to, since a lambda literal is always found at
/// `ctx`'s own top level: `compile_node` never itself recurses into an
/// `Abs`'s body, every nested lambda is peeled off as its own separate
/// combinator instead). `i32.const 0` (no allocation at all) for an empty
/// layout -- there's nothing to capture, so `$alloc` isn't even needed.
fn push_closure_env(ctx: &FnCtx, captures: &[u32], w: &mut String, indent: usize) -> Option<()> {
    if captures.is_empty() {
        push_line(w, indent, "i32.const 0");
        return Some(());
    }
    push_line(w, indent, &format!("i32.const {}", captures.len() * 8));
    push_line(w, indent, "call $alloc");
    push_line(w, indent, "local.set $envtmp");
    for (slot, &rel) in captures.iter().enumerate() {
        push_line(w, indent, "local.get $envtmp");
        compile_var_read(ctx, rel, w, indent)?;
        push_line(w, indent, &format!("i64.store offset={}", slot * 8));
    }
    push_line(w, indent, "local.get $envtmp");
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

    /// `\g. g 5` -- calls its own closure-typed parameter.
    fn calls_its_closure_arg_with_5(s: &mut TermStore) -> Hash {
        let g = s.var(0);
        let five = s.lit(5);
        let call = s.app(g, five);
        s.abs(call)
    }

    #[test]
    fn a_capturing_closure_compiles_and_matches_interpreter() {
        // \x. (\g. g 5) (if 0 < x then (\y. x + y) else (\y. x - y)) --
        // both inner lambdas reference `x`, bound by the *outer* function
        // (`picker`), not their own parameter range: creating whichever
        // one the `if` picks allocates a fresh, heap-allocated
        // environment capturing `x` (`push_closure_env`); passing the
        // result into `inner`'s `g` parameter and calling it there
        // exercises the packed env+table-index representation and
        // unpacking it back out at a `call_indirect` site, all in one
        // compiled fragment.
        let mut s = TermStore::new();
        let x = s.var(0);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Lt, zero, x);
        let y_pos = s.var(0);
        let x_pos = s.var(1);
        let plus = s.prim(PrimOp::Add, x_pos, y_pos);
        let then_closure = s.abs(plus);
        let y_neg = s.var(0);
        let x_neg = s.var(1);
        let minus = s.prim(PrimOp::Sub, x_neg, y_neg);
        let else_closure = s.abs(minus);
        let body = s.if_(cond, then_closure, else_closure);
        let picker = s.abs(body);

        let inn = calls_its_closure_arg_with_5(&mut s);
        let x2 = s.var(0);
        let picked = s.app(picker, x2);
        let called = s.app(inn, picked);
        let f = s.abs(called);

        let frag = try_compile(&s, f).expect("a capturing closure should compile");
        assert_eq!(frag.arity, 1);
        assert!(frag.wat.contains("call $alloc"), "creating the capturing closure should need the allocator");

        let (mut store, instance) = instantiate(&frag.wat);
        let func = instance.get_typed_func::<i64, i64>(&mut store, "f").unwrap();

        for x in [-7, -1, 0, 1, 3, 100] {
            let compiled = func.call(&mut store, x).unwrap();
            let interpreted = apply_term(&s, f, &[x]).unwrap();
            assert_eq!(compiled, interpreted, "mismatch at x={x}");
        }
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

    /// Wraps `emit_allocator`'s output in a minimal module that exports
    /// `$alloc` directly, so the tests below can call it from Rust without
    /// needing any of the rest of `try_compile`'s machinery.
    fn instantiate_allocator() -> (wasmtime::Store<()>, wasmtime::Instance) {
        let mut w = String::new();
        w.push_str("(module\n");
        emit_allocator(&mut w);
        w.push_str("  (export \"alloc\" (func $alloc))\n");
        w.push_str("  (export \"memory\" (memory 0))\n");
        w.push_str(")\n");
        instantiate(&w)
    }

    #[test]
    fn alloc_bumps_the_pointer_by_the_requested_size_each_call() {
        let (mut store, instance) = instantiate_allocator();
        let alloc = instance.get_typed_func::<i32, i32>(&mut store, "alloc").unwrap();

        let a = alloc.call(&mut store, 8).unwrap();
        let b = alloc.call(&mut store, 16).unwrap();
        let c = alloc.call(&mut store, 4).unwrap();
        assert_eq!(a, 0);
        assert_eq!(b, 8);
        assert_eq!(c, 24);
    }

    #[test]
    fn alloc_grows_memory_once_the_initial_page_is_exhausted() {
        let (mut store, instance) = instantiate_allocator();
        let alloc = instance.get_typed_func::<i32, i32>(&mut store, "alloc").unwrap();
        let memory = instance.get_memory(&mut store, "memory").unwrap();

        assert_eq!(memory.size(&store), 1); // one 64KiB page to start

        // Exhaust the first page, forcing at least one `memory.grow`.
        let first = alloc.call(&mut store, 60_000).unwrap();
        let second = alloc.call(&mut store, 60_000).unwrap();
        assert_eq!(first, 0);
        assert_eq!(second, 60_000);
        assert!(memory.size(&store) > 1, "should have grown past the first page");

        // The allocation is actually usable: write through both pointers
        // and read the bytes back, including past the old page boundary.
        memory.data_mut(&mut store)[first as usize] = 0xAB;
        memory.data_mut(&mut store)[second as usize + 59_999] = 0xCD;
        assert_eq!(memory.data(&store)[first as usize], 0xAB);
        assert_eq!(memory.data(&store)[second as usize + 59_999], 0xCD);
    }

    #[test]
    fn a_let_bound_self_recursive_function_compiles_and_matches_interpreter() {
        // (\g. g 10) (rec f n = if n <= 1 then 1 else n * f (n - 1)) --
        // what `let fact = rec f n = .. in fact 10` desugars to: a named
        // recursive function passed through the *same* "combinator"
        // machinery a plain lambda value already uses (registered,
        // called via a shared table index), not a special case.
        // Regression test: scan_for_closure_calls used to panic
        // (`unreachable!`) the moment it encountered a bare `Rec` value
        // here -- `Rec` was never actually "handled above" the way its
        // own comment claimed, only `Abs` was.
        let mut s = TermStore::new();
        let fact = factorial(&mut s);
        let inner_var = s.var(0);
        let ten = s.lit(10);
        let call = s.app(inner_var, ten);
        let wrapper = s.abs(call);
        let applied = s.app(wrapper, fact);

        let frag = try_compile(&s, applied)
            .expect("a let-bound self-recursive function, called through the table, should compile");
        assert_eq!(frag.arity, 0);

        let (mut store, instance) = instantiate(&frag.wat);
        let func = instance.get_typed_func::<(), i64>(&mut store, "f").unwrap();
        let compiled = func.call(&mut store, ()).unwrap();
        assert_eq!(compiled, 3628800);
        assert_eq!(compiled, apply_term(&s, applied, &[]).unwrap());
    }
}
