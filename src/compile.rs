//! Compiles a restricted "first-order arithmetic with self-recursion and
//! closures" fragment of the term language down to WebAssembly text (WAT)
//! — our formalization of the target machine. `wasmtime` then
//! JIT-compiles that WAT (via Cranelift) to native code.
//!
//! Only a subset of terms fall in this fragment: closed expressions built
//! from `Var`/`Lit`/`Prim`/`If`, fully-saturated self-calls (optionally
//! wrapped in `Rec` for recursion), fully-saturated applications of
//! either a variable (a parameter *or* a captured free variable -- see
//! "Closures" below) or a literal lambda value ("combinator" below,
//! *capturing* or not) holding a closure, an *under*-applied literal
//! lambda (real partial application -- see "Partial application" below),
//! and an *over*-applied literal lambda (calling whatever its saturated
//! call returns with more arguments -- see "Over-application" below).
//! Anything else (a variable applied with inconsistent arities across
//! call sites, a genuinely free/unbound variable, ...) is rejected by
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
//! A closure value can then be *applied* two ways: through a variable
//! (a parameter *or* a captured free variable -- either resolves via
//! `compile_var_read` the same way, see above) that's always called with
//! the same number of arguments everywhere in its own function
//! (`infer_closure_arities` finds these, keyed by absolute `Var` index so
//! it doesn't need to distinguish the two, and application compiles to
//! Wasm's `call_indirect` through the shared table, unpacking the
//! environment pointer and table index back out of the packed `i64`
//! first), or as a literal lambda appearing directly in function position
//! (`Combinators::register` gives it a table slot and its call compiles
//! to an ordinary, statically-known `call`, with a freshly created
//! environment passed as that call's first argument). Passing a lambda
//! around as a value it's never applied to (an argument, a branch's
//! result, ...) packs its (possibly-empty) environment and table index
//! into a single `i64` the same way either path would.
//!
//! What's still out of scope: a variable (parameter or captured free
//! variable) applied with inconsistent arities across call sites (see
//! "Over-application" below for why an over-applied *literal lambda* is a
//! different, narrower problem that *is* in scope), and capturing an
//! enclosing self-recursive binding's own self-reference as a plain value
//! from a *nested* closure
//! (an honest, structural rejection -- see `free_vars`'s self-exclusion
//! -- rather than a special-cased check). `Combinators` also doesn't
//! statically check that a value passed into a closure-typed parameter
//! actually has the arity that parameter's own body expects of it --
//! `call_indirect`'s own dynamic type check catches a mismatch as a
//! trap, caught safely by `jit.rs`'s sample verification the same way
//! any other compiler bug would be.
//!
//! ## Partial application: compile-time desugaring, not a runtime object
//!
//! An *under*-applied literal lambda (`root`, own arity `n`, applied to
//! only `k < n` arguments) is a genuine partial application: the
//! expression's value is a fresh closure of arity `n - k`, waiting for
//! the rest. Since every call site in this fragment has a statically
//! known argument count (that's the whole premise `infer_closure_arities`
//! relies on), there's never a need for a fully general runtime
//! mechanism that dispatches on arity dynamically (the way, say, GHC's
//! PAP objects do) -- the missing argument count is always known at
//! compile time, so it's resolved then: `register_partial_app` registers
//! a synthesized wrapper combinator, keyed by `(root, k)` alone (*not*
//! the actual argument values supplied -- those only matter at each
//! creation site, not to the wrapper's own compiled code, which every
//! call site with the same `(root, k)` shares), and `compile_node`
//! creates a value of it (`push_pap_env`) exactly the way it creates a
//! value of any other closure. `emit_pap_wrapper` needs no
//! `compile_node`/`FnCtx` at all to compile the wrapper's own body --
//! its environment layout is entirely fixed by `(root, k)` (slot `0` is
//! `root`'s own environment pointer, slots `1..=k` are the already-
//! supplied arguments), so it's just a handful of fixed loads forwarded
//! into one statically-known `call`.
//!
//! What this doesn't handle: a variable (not a literal lambda) applied
//! with inconsistent arities -- compile.rs has no fixed arity for a
//! variable to compare against in the first place, only whatever it's
//! consistently called with, so there's no missing-argument count to
//! desugar around. Over-application of a literal lambda -- calling the
//! *result* of a saturated call with more arguments -- is a different,
//! *narrower* problem than that: `root`'s own identity and arity are
//! still statically known here (it's *what its body computes* that
//! isn't), so it doesn't need any of the runtime arity-dispatch mechanism
//! above -- see "Over-application" below.
//!
//! ## Over-application: dispatching a saturated call's own result
//!
//! An *over*-applied literal lambda (`root`, own arity `n`, applied to
//! `k > n` arguments) means the *first* `n` arguments saturate `root`
//! itself, and the remaining `k - n` are applied to whatever `root`'s own
//! body evaluates to once called -- which only makes sense if that's
//! itself a closure (e.g. `root = \a b. if a > 0 then (\c. ..) else (\c.
//! ..)`, returning one of two further, possibly-capturing closures
//! depending on `a`). Unlike partial application, this isn't resolved at
//! compile time via a synthesized wrapper: `root`'s own saturated call
//! (`root`'s first `n` arguments) is compiled exactly as an ordinary
//! saturated call would be, and the packed `i64` it returns is dispatched
//! through `call_indirect` on the remaining `k - n` arguments, exactly
//! the way calling a closure-typed *variable* already works (see above)
//! -- the only difference is that the callee here is a freshly computed
//! value rather than one read from a local or capture slot.
//!
//! This pass has no real type system, just term shape, so nothing here
//! checks that `root`'s body genuinely denotes a closure once applied --
//! an over-applied literal lambda whose body is a plain `Int` still
//! compiles, into a `call_indirect` on a garbage table index that either
//! traps or (astronomically unlikely) coincidentally lands on some
//! unrelated table entry. Either way, `jit.rs`'s sample verification
//! catches it: the interpreter genuinely type-errors on such a term, so
//! any disagreement -- a trap, or a wrong answer -- fails verification
//! and falls back to the interpreter, the same safety net every other
//! shape this fragment accepts already relies on (`compile.rs` only needs
//! to be sound, not complete, and this doesn't even need to be *sound* on
//! its own -- verification is).
//!
//! `call_indirect`'s own operand order needs `root`'s packed result split
//! across *both* ends of the call (environment pointer first, table index
//! last, with the `k - n` extra arguments' own compilation -- and any
//! nested closure/PAP construction it might trigger -- necessarily
//! happening in between). Rather than stash that result in a local across
//! the extra arguments' own recursive compilation (exactly the hazard
//! `push_pap_env`'s own docs describe, and that bit `push_pap_env` for
//! real once), `root`'s saturated call is simply compiled twice, once for
//! each half -- a pure, deterministic Wasm function call with no
//! observable side effect beyond bump-allocator growth (which doesn't
//! affect the result), so recomputing it is correct, if not free: a
//! deeply left-nested chain of over-applications would recompile its own
//! innermost saturated call once per enclosing over-application. Left as
//! a known, documented tradeoff rather than a `push_pap_env`-style
//! stack-based reordering, which would need `O(k - n)` dedicated scratch
//! storage per call site (not just the one or two locals a fixed-shape
//! wrapper needs) to reassemble the extra arguments in order after
//! popping them off to reach the callee underneath.

use hashbrown::HashMap;

use crate::term::{Hash, PrimOp, Term, TermStore};

pub struct CompiledFragment {
    pub arity: usize,
    pub wat: String,
    /// Whether the module exports a mutable `"hp"` global (the bump
    /// allocator's next-free-byte pointer) that `jit.rs` must reset to 0
    /// before *every* top-level call -- see `try_compile`'s docs on why
    /// this has to happen from the host, once per call, rather than
    /// inside the compiled function itself. `false` for a fragment with
    /// no capturing closures at all (no allocator, nothing to reset).
    pub needs_hp_reset: bool,
}

/// One entry of `Combinators::pending` -- either an ordinary lambda
/// literal (`register`), or a synthesized partial-application wrapper
/// (`register_partial_app`, see its own docs and `emit_pap_wrapper`).
/// Both share the same `arities`/`captures`/table-index space; this only
/// distinguishes *how* the fixpoint loop in `try_compile` compiles each
/// one's body once dequeued.
enum PendingCombinator {
    Literal(Hash),
    PartialApp { root: Hash, supplied: usize },
}

/// Discovers and compiles lambda values found while compiling a function
/// (see module docs). `index`/`arities`/`captures` describe every
/// combinator registered so far (in registration order, parallel to a
/// combinator's assigned index -- `captures[idx]` is that combinator's
/// own environment slot layout, from `free_vars`, meaningless for a
/// partial-application wrapper, which never reads it -- see
/// `emit_pap_wrapper`/`push_pap_env` instead); `pending` holds ones not
/// yet compiled to Wat; `call_indirect_arities` accumulates every arity
/// actually used at a `call_indirect` site, for the `(type ...)`
/// declarations that need to exist once each, not once per site.
/// `pap_index`/`has_pap_wrappers` are `register_partial_app`'s own
/// bookkeeping, kept separate from `index` since a wrapper's identity
/// (`root`, `supplied`) isn't a `Hash` at all.
struct Combinators<'a> {
    store: &'a TermStore,
    index: HashMap<Hash, usize>,
    pending: Vec<PendingCombinator>,
    arities: Vec<usize>,
    captures: Vec<Vec<u32>>,
    call_indirect_arities: Vec<usize>,
    pap_index: HashMap<(Hash, usize), usize>,
    has_pap_wrappers: bool,
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
            pap_index: HashMap::new(),
            has_pap_wrappers: false,
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
        self.pending.push(PendingCombinator::Literal(h));
        Some(idx)
    }

    /// Registers a synthesized wrapper for `root` (a literal combinator,
    /// already registered at `root_idx`) applied to only `supplied` of
    /// its own `arities[root_idx]` arguments -- the compile-time
    /// desugaring of partial application (see `compile_node`'s
    /// under-application handling in its `Term::Abs`/`Term::Rec`
    /// App-callee branch). `None` if this isn't actually a partial
    /// application (`supplied` is `0`, i.e. no arguments were supplied at
    /// all -- already handled as a plain value -- or `>=` `root`'s own
    /// arity -- fully saturated or over-applied, handled elsewhere).
    ///
    /// Deduplicated by `(root, supplied)` alone, *not* by the actual
    /// argument values supplied at any particular call site: the
    /// wrapper's own compiled body (`emit_pap_wrapper`) only depends on
    /// which function is being partially applied and how many of its
    /// arguments are already fixed, never on what those arguments
    /// actually evaluate to -- that happens at each creation site
    /// instead (`push_pap_env`), the same way any other closure's
    /// captured *values* are filled in fresh at its own creation site
    /// while its *code* is compiled once.
    fn register_partial_app(&mut self, root: Hash, root_idx: usize, supplied: usize) -> Option<usize> {
        if let Some(&idx) = self.pap_index.get(&(root, supplied)) {
            return Some(idx);
        }
        let root_arity = self.arities[root_idx];
        if supplied == 0 || supplied >= root_arity {
            return None;
        }
        let idx = self.arities.len();
        self.arities.push(root_arity - supplied);
        self.captures.push(Vec::new()); // unused by a PAP wrapper -- see struct docs
        self.pap_index.insert((root, supplied), idx);
        self.pending.push(PendingCombinator::PartialApp { root, supplied });
        self.has_pap_wrappers = true;
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
    while let Some(pc) = combinators.pending.pop() {
        match pc {
            PendingCombinator::Literal(h_c) => {
                let idx = combinators.index[&h_c];
                let (c_arity, c_body, c_is_rec) = peel(store, h_c)?;
                let c_self_idx = if c_is_rec { Some(c_arity as u32) } else { None };
                let captures = combinators.captures[idx].clone();
                let c_name = format!("c{idx}");
                let c_spec = FnSpec { name: &c_name, arity: c_arity, self_idx: c_self_idx, has_env: true, captures: &captures };
                compile_function(store, c_body, &c_spec, &mut combinators, &mut combinator_wat)?;
            }
            PendingCombinator::PartialApp { root, supplied } => {
                let idx = combinators.pap_index[&(root, supplied)];
                let root_idx = combinators.index[&root];
                let root_arity = combinators.arities[root_idx];
                emit_pap_wrapper(&format!("c{idx}"), root_idx, root_arity, supplied, &mut combinator_wat);
            }
        }
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
    let needs_alloc = combinators.captures.iter().any(|c| !c.is_empty()) || combinators.has_pap_wrappers;
    if needs_alloc {
        emit_allocator(&mut w);
        // Exported so `jit.rs` can reset it to 0 before every top-level
        // call (see `CompiledFragment::needs_hp_reset`'s docs for why:
        // in short, `jit.rs` caches and reuses *one* compiled instance
        // across many separate calls, so without a reset, every
        // capturing closure any call creates would leak its environment
        // forever). Resetting *inside* the compiled function itself
        // (e.g. at `$f`'s own entry) would be unsound: a non-tail
        // self-recursive call is an ordinary `call $f`, re-entering the
        // whole function from the top, which would reset `$hp` again
        // mid-computation and corrupt any closure created earlier in
        // the *same* top-level call that's still needed after the
        // recursive call returns. Resetting from outside, once per
        // top-level call, has no such hazard.
        w.push_str("  (export \"hp\" (global $hp))\n");
        // Exported too, purely so tests can observe that resetting `$hp`
        // between calls actually keeps memory bounded (`jit.rs` itself
        // never reads this export).
        w.push_str("  (export \"memory\" (memory 0))\n");
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

    Some(CompiledFragment { arity, wat: w, needs_hp_reset: needs_alloc })
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
    // No generic-dispatch mechanism exists yet (see `ArityUse`'s docs) --
    // any inconsistency anywhere in this function's body still rejects
    // the whole function, exactly as when `scan_for_closure_calls` used
    // to abort the scan outright the moment it found one.
    if closure_arities.values().any(|u| matches!(u, ArityUse::Inconsistent)) {
        return None;
    }
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
    // Second scratch local, for `push_pap_env`: once every value its own
    // environment needs (root's own environment plus each supplied
    // argument) has been computed and left safely on the value stack --
    // see its own docs for why it's the stack, not this or `$envtmp`,
    // that carries them across a supplied argument's own, possibly
    // recursive, evaluation -- this is reused purely as pop-scratch to
    // reorder each value for its own `i64.store`.
    w.push_str("    (local $papenv i64)\n");
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

/// The result of scanning every use of one absolute `Var` index as an
/// application's callee, anywhere within one function body:
/// `Consistent(k)` if every such use applied it to exactly `k` arguments;
/// `Inconsistent` if at least two uses disagreed (e.g. `f(x)` *and*
/// `f(x,y)`). A `Var` never used as a callee at all (just read as a
/// value) simply has no entry in the map `scan_for_closure_calls`
/// produces.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ArityUse {
    Consistent(usize),
    Inconsistent,
}

/// For every absolute `Var` index in `h` (a parameter of the function
/// being compiled, *or* a captured free variable -- this doesn't
/// distinguish the two, since a closure-typed value read resolves the
/// same way either way, see `compile_var_read`), classifies whether it's
/// ever used as an application's callee and, if so, whether every such
/// use agrees on the argument count (see `ArityUse`). This function
/// itself never rejects a whole scan just because one `Var` is used
/// inconsistently -- scanning continues, and every other `Var`'s own
/// classification is still reported -- so callers that don't yet handle
/// `ArityUse::Inconsistent` (everything as of this writing) must check
/// for it themselves and decline accordingly, exactly as they declined
/// on this function returning `None` before this classification existed.
/// `None` is still returned for a genuinely out-of-fragment callee shape
/// (neither a variable nor a literal lambda/combinator).
pub(crate) fn infer_closure_arities(store: &TermStore, h: Hash, arity: usize, self_idx: Option<u32>) -> Option<HashMap<u32, ArityUse>> {
    let mut found = HashMap::new();
    scan_for_closure_calls(store, h, arity, self_idx, &mut found)?;
    Some(found)
}

fn scan_for_closure_calls(
    store: &TermStore,
    h: Hash,
    arity: usize,
    self_idx: Option<u32>,
    found: &mut HashMap<u32, ArityUse>,
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
            // A parameter *or* a captured free variable used as a
            // callee -- both resolve to a packed closure value the same
            // way (`compile_var_read`), so both get tracked here
            // uniformly; whether `i` actually resolves to anything at
            // all is checked later, at codegen.
            Term::Var(i) => {
                match found.get(i) {
                    None => {
                        found.insert(*i, ArityUse::Consistent(args.len()));
                    }
                    Some(ArityUse::Consistent(k)) if *k == args.len() => {}
                    Some(ArityUse::Consistent(_)) => {
                        found.insert(*i, ArityUse::Inconsistent);
                    }
                    Some(ArityUse::Inconsistent) => {} // already marked; nothing new to record
                }
            }
            Term::Abs(_) | Term::Rec(_) => {} // a literal redex callee (possibly self-recursive) -- fine, checked again at codegen
            _ => return None,  // callee is neither a variable nor a literal lambda/combinator
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
    /// From `infer_closure_arities`: absolute `Var` index -> how it's
    /// used as a callee, whether that index resolves to one of this
    /// function's own parameters or to one of its captures.
    /// `compile_function` already rejects the whole function if any
    /// entry is `ArityUse::Inconsistent`, so every entry actually reached
    /// here is `ArityUse::Consistent`.
    closure_arities: &'b HashMap<u32, ArityUse>,
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
            // A closure-typed variable used as a callee -- a parameter
            // (`i < arity`) *or* a captured free variable (`i >= arity`):
            // `compile_var_read` resolves either the same way, so this
            // doesn't need to distinguish them; calling a closure reached
            // through a captured variable works exactly like calling one
            // reached through a parameter, just resolved differently.
            Term::Var(i) => {
                let expected = match ctx.closure_arities.get(i)? {
                    ArityUse::Consistent(k) => *k,
                    // `compile_function` already rejects the whole
                    // function before this is ever reached -- kept as an
                    // honest decline rather than an assert, matching this
                    // module's own "None, never a panic" convention.
                    ArityUse::Inconsistent => return None,
                };
                if args.len() != expected {
                    return None;
                }
                // Unpack the callee's environment pointer (high 32 bits)
                // first -- it's `call_indirect`'s first operand, ahead of
                // the actual arguments -- then its table index (low 32
                // bits) last, as `call_indirect` itself requires. Reading
                // the packed value twice (once per half) is fine -- it's
                // a pure local/memory read either way, nothing mutates
                // it in between.
                compile_var_read(ctx, *i, w, indent)?;
                push_line(w, indent, "i64.const 32");
                push_line(w, indent, "i64.shr_u");
                push_line(w, indent, "i32.wrap_i64");
                for a in &args {
                    compile_node(ctx, combinators, *a, false, w, indent)?;
                }
                compile_var_read(ctx, *i, w, indent)?;
                push_line(w, indent, "i32.wrap_i64");
                combinators.call_indirect_arities.push(expected);
                push_line(w, indent, &format!("call_indirect (type $ty{expected})"));
                return Some(());
            }
            Term::Abs(_) | Term::Rec(_) => {
                let idx = combinators.register(root)?;
                let root_arity = combinators.arities[idx];
                if args.len() == root_arity {
                    let captures = combinators.captures[idx].clone();
                    push_closure_env(ctx, &captures, w, indent)?;
                    for a in &args {
                        compile_node(ctx, combinators, *a, false, w, indent)?;
                    }
                    push_line(w, indent, &format!("call $c{idx}"));
                    return Some(());
                }
                if args.len() > root_arity {
                    // Over-application: `root`'s own saturated call
                    // (`root`'s first `root_arity` args) is compiled, then
                    // whatever it *returns* is called again, dynamically,
                    // through `call_indirect` -- exactly the same dispatch
                    // a closure-typed *variable* callee already uses (see
                    // the `Term::Var(i)` arm above), just with the callee
                    // itself freshly computed here instead of read from a
                    // local/capture slot. This only makes sense if the
                    // saturated call's own result genuinely is a packed
                    // `Clo` value (i.e. `root`'s body, once its own
                    // parameters are supplied, itself denotes a further
                    // closure) -- nothing here checks that statically
                    // (this pass has no real type system, just term
                    // shape), so an over-application of a plain
                    // `Int`-returning function still compiles, but
                    // produces a garbage `call_indirect` target that
                    // either traps or (extremely unlikely) coincidentally
                    // lands on some unrelated table entry -- caught either
                    // way by `jit.rs`'s sample verification disagreeing
                    // with the interpreter (which genuinely type-errors on
                    // such a term), the same safety net every other shape
                    // this fragment accepts already relies on.
                    //
                    // `call_indirect`'s own operand order needs the
                    // callee's env-ptr *before* the extra arguments and
                    // its table index *after* them (see the `Term::Var(i)`
                    // arm), so the extra arguments' own compilation -- and
                    // any nested closure/PAP construction it might
                    // trigger -- necessarily happens *between* the two
                    // halves. Rather than stash the saturated call's
                    // result in a local across that recursion (exactly
                    // the hazard `push_pap_env`'s own docs describe, and
                    // that bit `push_pap_env` for real once), the
                    // saturated call is simply compiled twice -- once for
                    // each half. It's a pure, deterministic Wasm function
                    // call (no observable side effect beyond bump-
                    // allocator growth, which doesn't affect the result),
                    // so recomputing it is correct, if not free; see this
                    // function's own module docs for the tradeoff.
                    let sat_args = &args[..root_arity];
                    let extra_args = &args[root_arity..];
                    let captures = combinators.captures[idx].clone();

                    push_closure_env(ctx, &captures, w, indent)?;
                    for a in sat_args {
                        compile_node(ctx, combinators, *a, false, w, indent)?;
                    }
                    push_line(w, indent, &format!("call $c{idx}"));
                    push_line(w, indent, "i64.const 32");
                    push_line(w, indent, "i64.shr_u");
                    push_line(w, indent, "i32.wrap_i64");

                    for a in extra_args {
                        compile_node(ctx, combinators, *a, false, w, indent)?;
                    }

                    push_closure_env(ctx, &captures, w, indent)?;
                    for a in sat_args {
                        compile_node(ctx, combinators, *a, false, w, indent)?;
                    }
                    push_line(w, indent, &format!("call $c{idx}"));
                    push_line(w, indent, "i32.wrap_i64");

                    combinators.call_indirect_arities.push(extra_args.len());
                    push_line(w, indent, &format!("call_indirect (type $ty{})", extra_args.len()));
                    return Some(());
                }
                // Under-applied: a genuine partial application. This
                // expression's *value* is a fresh closure over a
                // synthesized wrapper (see `register_partial_app`) --
                // not a call's result at all, since `root` isn't
                // actually being called here (only readied to be).
                let root_captures = combinators.captures[idx].clone();
                let wrapper_idx = combinators.register_partial_app(root, idx, args.len())?;
                push_pap_env(ctx, combinators, &root_captures, &args, w, indent)?;
                push_line(w, indent, "i64.extend_i32_u");
                push_line(w, indent, "i64.const 32");
                push_line(w, indent, "i64.shl");
                push_line(w, indent, &format!("i64.const {wrapper_idx}"));
                push_line(w, indent, "i64.or");
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
    // Must match `free_vars`'s own `capture_base` exactly: when `ctx` is
    // self-recursive, `Rec` binds one more slot (self, at exactly
    // `arity`) *before* any genuine outward capture begins, so a
    // capture's relative index in `ctx.captures` is offset by one beyond
    // `ctx`'s own parameters, not zero.
    let capture_base = if ctx.self_idx.is_some() { arity + 1 } else { arity };
    if v < capture_base {
        return None; // exactly `ctx`'s own self-reference, used as a plain value
    }
    let rel = v - capture_base;
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

/// Emits a synthesized partial-application wrapper (`name` = `$c{idx}`,
/// its assigned table index) -- `root` (a literal combinator, already
/// registered at `root_idx` with its own arity `root_arity`) was applied
/// to only `supplied` of its arguments (`compile_node`'s under-application
/// handling); this wrapper takes the remaining `root_arity - supplied`
/// arguments and completes the call. Its own environment layout is fixed
/// by `(root_idx, supplied)` alone -- slot `0` is `root`'s own
/// environment pointer (as an `i64`, zero-extended, for slot uniformity
/// with every other slot), slots `1..=supplied` are the values of the
/// arguments `root` was already applied to -- see `push_pap_env`, which
/// builds exactly this layout at each creation site. Entirely
/// self-contained (no `compile_node`/`FnCtx` needed, unlike an ordinary
/// combinator's body): every value here is just a fixed offset into
/// `$env`, or one of this function's own parameters, forwarded straight
/// into a single, statically-known `call`.
fn emit_pap_wrapper(name: &str, root_idx: usize, root_arity: usize, supplied: usize, w: &mut String) {
    let remaining = root_arity - supplied;
    w.push_str(&format!("  (func ${name} (param $env i32)"));
    for i in 0..remaining {
        w.push_str(&format!(" (param $p{i} i64)"));
    }
    w.push_str(" (result i64)\n");
    push_line(w, 4, "local.get $env");
    push_line(w, 4, "i64.load offset=0");
    push_line(w, 4, "i32.wrap_i64");
    for slot in 0..supplied {
        push_line(w, 4, "local.get $env");
        push_line(w, 4, &format!("i64.load offset={}", (slot + 1) * 8));
    }
    for i in 0..remaining {
        push_line(w, 4, &format!("local.get $p{i}"));
    }
    push_line(w, 4, &format!("call $c{root_idx}"));
    w.push_str("  )\n");
}

/// Creates the environment for a partial-application wrapper over `root`
/// (`root_captures`, `root`'s own environment slot layout) applied so far
/// to `args` -- the counterpart, at each creation site, to
/// `emit_pap_wrapper`'s fixed body: slot `0` = `root`'s own environment
/// pointer (`push_closure_env`, exactly as if creating a plain value of
/// `root` right here), slots `1..=args.len()` = each already-supplied
/// argument's *current* value, evaluated via `compile_node` in `ctx` --
/// not `compile_var_read`, since an already-supplied argument is an
/// arbitrary expression (`f(x + 1)`), not necessarily a bare variable.
///
/// Computes `root`'s own environment *before* starting this wrapper's
/// own allocation, stashing it in the dedicated `$papenv` local: both
/// that computation (`push_closure_env`) and this wrapper's own
/// slot-filling use `$envtmp` as scratch space, so they can't be "in
/// flight" at the same time.
fn push_pap_env(ctx: &FnCtx, combinators: &mut Combinators, root_captures: &[u32], args: &[Hash], w: &mut String, indent: usize) -> Option<()> {
    // Evaluate root's own environment and every supplied argument *before*
    // allocating this wrapper's own environment, leaving all
    // `1 + args.len()` values purely on the Wasm value stack rather than
    // round-tripping any of them through `$envtmp`/`$papenv`. A supplied
    // argument is an arbitrary expression (`f(g(x))`), so `compile_node`
    // here can itself recurse into more closure/PAP construction, which
    // reuses those same two locals as scratch -- a value already sitting
    // on the stack is immune to that (Wasm's stack is properly nested by
    // construction); a value stashed in either local is not, and an
    // earlier version of this function stashed *both* the newly-allocated
    // environment's own address (in `$envtmp`, across the whole loop
    // below) and, in the general multi-argument case, would have needed
    // to do the same for `$papenv` -- corrupted the moment any argument's
    // own evaluation happened to create a capturing closure or another
    // partial application, which a real fuzz-found regression traced back
    // to exactly this.
    push_closure_env(ctx, root_captures, w, indent)?;
    push_line(w, indent, "i64.extend_i32_u");
    for &a in args {
        compile_node(ctx, combinators, a, false, w, indent)?;
    }

    // Nothing from here on recurses, so `$envtmp`/`$papenv` are ordinary,
    // safe-to-reuse scratch again.
    push_line(w, indent, &format!("i32.const {}", (1 + args.len()) * 8));
    push_line(w, indent, "call $alloc");
    push_line(w, indent, "local.set $envtmp");

    // The stack now holds, deepest to shallowest, root's own environment
    // followed by each argument's value in order -- pop them off from the
    // top (last argument first) into `$papenv`, pairing each with a fresh
    // `$envtmp` read for its own store: `i64.store` wants (address, value)
    // with the address pushed first, which the values' own stack order
    // doesn't already match, so each one is round-tripped through
    // `$papenv` to fix that up.
    for slot in (0..=args.len()).rev() {
        push_line(w, indent, "local.set $papenv");
        push_line(w, indent, "local.get $envtmp");
        push_line(w, indent, "local.get $papenv");
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
    fn self_recursion_creating_a_fresh_capturing_closure_every_iteration_compiles() {
        // rec f n acc = if n <= 0 then acc else f (n - 1) ((\y. acc + y) n)
        // -- a tail loop where *each iteration* creates and immediately
        // calls a fresh closure capturing the current `acc`: exercises
        // `$env` staying correctly untouched across the tail loop's own
        // `br $L` (the closure creation/call happens compiling one of the
        // *new* argument values, not the self-call itself) while
        // `push_closure_env`/`$alloc` still runs freshly every iteration.
        let mut s = TermStore::new();
        let y = s.var(0);
        let acc_captured = s.var(1);
        let sum = s.prim(PrimOp::Add, acc_captured, y);
        let closure = s.abs(sum);
        let n_ref = s.var(1);
        let new_acc = s.app(closure, n_ref);
        let n = s.var(1);
        let acc = s.var(0);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Le, n, zero);
        let one = s.lit(1);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one);
        let f = s.var(2);
        let rec_call = s.app2(f, n_minus_1, new_acc);
        let body = s.if_(cond, acc, rec_call);
        let inner = s.abs(body);
        let abs = s.abs(inner);
        let term = s.rec(abs);

        let frag = try_compile(&s, term).expect("should compile");
        assert_eq!(frag.arity, 2);

        let (mut store, instance) = instantiate(&frag.wat);
        let func = instance.get_typed_func::<(i64, i64), i64>(&mut store, "f").unwrap();

        for (n, acc) in [(0, 0), (1, 0), (5, 0), (10, 100)] {
            let compiled = func.call(&mut store, (n, acc)).unwrap();
            let interpreted = apply_term(&s, term, &[n, acc]).unwrap();
            assert_eq!(compiled, interpreted, "mismatch at n={n} acc={acc}");
        }
    }

    #[test]
    fn resetting_hp_between_calls_keeps_memory_bounded_across_many_calls() {
        // Same term as the test above, but this one exercises the actual
        // mechanism `jit.rs` relies on: `needs_hp_reset`/the exported
        // `"hp"` global. Without resetting `hp` to 0 before every call,
        // repeatedly calling the *same* compiled instance -- exactly
        // what `jit.rs`'s cache does -- would leak every capturing
        // closure's environment forever, growing linear memory without
        // bound across the instance's whole lifetime. This confirms both
        // halves: memory genuinely does grow within a single call large
        // enough to cross a page, and resetting `hp` between repeated
        // calls (what `jit.rs`'s `invoke` now does) keeps it bounded no
        // matter how many times the instance is called.
        let mut s = TermStore::new();
        let y = s.var(0);
        let acc_captured = s.var(1);
        let sum = s.prim(PrimOp::Add, acc_captured, y);
        let closure = s.abs(sum);
        let n_ref = s.var(1);
        let new_acc = s.app(closure, n_ref);
        let n = s.var(1);
        let acc = s.var(0);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Le, n, zero);
        let one = s.lit(1);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one);
        let f = s.var(2);
        let rec_call = s.app2(f, n_minus_1, new_acc);
        let body = s.if_(cond, acc, rec_call);
        let inner = s.abs(body);
        let abs = s.abs(inner);
        let term = s.rec(abs);

        let frag = try_compile(&s, term).expect("should compile");
        assert!(frag.needs_hp_reset, "this term creates capturing closures, so it should need a reset");

        let (mut store, instance) = instantiate(&frag.wat);
        let func = instance.get_typed_func::<(i64, i64), i64>(&mut store, "f").unwrap();
        let memory = instance.get_memory(&mut store, "memory").unwrap();
        let hp = instance.get_global(&mut store, "hp").unwrap();

        // One call large enough to allocate past the first page (10,000
        // closures * 8 bytes each = 80,000 bytes > 65,536).
        func.call(&mut store, (10_000, 0)).unwrap();
        let size_after_one_call = memory.size(&store);
        assert!(size_after_one_call > 1, "a single large call should grow memory past the first page");

        // Reset "hp" (what jit.rs's invoke does before every call) and
        // call again, many times, with the same large n -- memory should
        // NOT keep growing call over call.
        for _ in 0..50 {
            hp.set(&mut store, wasmtime::Val::I32(0)).unwrap();
            func.call(&mut store, (10_000, 0)).unwrap();
        }
        let size_after_many_resetting_calls = memory.size(&store);
        assert_eq!(
            size_after_one_call, size_after_many_resetting_calls,
            "resetting hp between calls should let memory be reused, not keep growing"
        );

        // Without resetting: a further call keeps growing it, showing
        // growth (not the reset) is what caps it above.
        func.call(&mut store, (10_000, 0)).unwrap();
        assert!(
            memory.size(&store) > size_after_many_resetting_calls,
            "without a reset, one more call should grow memory further"
        );
    }

    #[test]
    fn a_self_recursive_combinator_can_also_capture_from_an_enclosing_scope() {
        // \z. (\h. h 5) (rec f n = if n <= 0 then z else n + f (n - 1)) --
        // `f` is both self-recursive *and* captures `z` from `g`'s own
        // scope (two levels out: past its own `n` param and past `Rec`'s
        // own self-binder). Regression test for a real bug found while
        // re-deriving this indexing by hand: `compile_var_read`'s own
        // capture-resolution formula didn't account for the extra slot
        // `Rec` binds for self, so it disagreed with `free_vars`'s
        // (which does) -- silently reading the *wrong* environment slot
        // whenever a self-recursive combinator captured more than one
        // outward value, or failing to resolve a genuine capture
        // (falling back to the interpreter) with exactly one.
        let mut s = TermStore::new();
        let n = s.var(0);
        let f_self = s.var(1);
        let z = s.var(2);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Le, n, zero);
        let one = s.lit(1);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one);
        let rec_call = s.app(f_self, n_minus_1);
        let else_branch = s.prim(PrimOp::Add, n, rec_call);
        let body = s.if_(cond, z, else_branch);
        let abs = s.abs(body);
        let f_term = s.rec(abs);

        let h = s.var(0);
        let five = s.lit(5);
        let call = s.app(h, five);
        let h_wrapper = s.abs(call);

        let applied = s.app(h_wrapper, f_term);
        let g = s.abs(applied);

        let frag = try_compile(&s, g).expect("a self-recursive capturing combinator should compile");
        assert_eq!(frag.arity, 1);

        let (mut store, instance) = instantiate(&frag.wat);
        let func = instance.get_typed_func::<i64, i64>(&mut store, "f").unwrap();

        for z in [-10, 0, 1, 7, 100] {
            let compiled = func.call(&mut store, z).unwrap();
            let interpreted = apply_term(&s, g, &[z]).unwrap();
            assert_eq!(compiled, interpreted, "mismatch at z={z}");
        }
    }

    #[test]
    fn calling_a_closure_reached_through_a_captured_free_variable_compiles() {
        // g = \cb. \x. (\y. cb y) x -- the nested closure `\y. cb y`
        // calls `cb`, a variable captured from g's own scope (not `y`,
        // its own parameter) -- exercises the widened call-site support:
        // calling a closure reached through a captured free variable,
        // not just through one of the calling function's own parameters
        // (see `infer_closure_arities`'s docs).
        let mut s = TermStore::new();
        let y = s.var(0);
        // `cb` needs to skip both `y`'s own binder (1) and reach `cb`'s
        // own slot in g's 2-var scope (1 more, since `cb` is g's outer/
        // first-bound, hence-higher-indexed param) -- var(2), not var(1).
        let cb_captured = s.var(2);
        let cb_call = s.app(cb_captured, y);
        let inner_closure = s.abs(cb_call);
        let x = s.var(0);
        let applied = s.app(inner_closure, x);
        let inner = s.abs(applied);
        let g = s.abs(inner);

        // inc = \z. z + 1
        let z = s.var(0);
        let one = s.lit(1);
        let z_plus_1 = s.prim(PrimOp::Add, z, one);
        let inc = s.abs(z_plus_1);

        let five = s.lit(5);
        let top = s.app2(g, inc, five);

        let frag = try_compile(&s, top).expect("calling a closure through a capture should compile");
        assert_eq!(frag.arity, 0);
        assert!(frag.wat.contains("call_indirect"), "cb y should still compile to call_indirect");

        let (mut store, instance) = instantiate(&frag.wat);
        let func = instance.get_typed_func::<(), i64>(&mut store, "f").unwrap();
        let compiled = func.call(&mut store, ()).unwrap();
        let interpreted = apply_term(&s, top, &[]).unwrap();
        assert_eq!(compiled, 6);
        assert_eq!(compiled, interpreted);
    }

    #[test]
    fn inconsistent_call_arity_for_a_parameter_is_still_rejected() {
        // \f. f(1) + f(1, 2) -- `f`, a *parameter*, called with
        // inconsistent arities (1 then 2) at different call sites --
        // still not supported: unlike a literal lambda (see
        // `partial_application_of_a_literal_lambda_compiles` below),
        // compile.rs has no fixed arity for a parameter to compare
        // against in the first place, only what it's consistently
        // called with, so there's nothing to desugar around here.
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
    fn partial_application_of_a_literal_lambda_compiles() {
        // add = \x y. x + y; partial = add(3) (under-applied by one
        // argument); caller = \g. g(4); top = caller(partial) -- `add(3)`
        // used as a value (an argument to `caller`, not immediately
        // re-applied at the same App-chain, so `unwind_app_spine` can't
        // collapse it into a single 2-ary call the way curried
        // application normally would -- see
        // `curried_application_is_indistinguishable_from_multi_arg_calls`)
        // is a genuine under-application: exercises the compile-time
        // desugaring into a synthesized wrapper (`register_partial_app`),
        // creating one closure value that, once called with the
        // remaining argument through `caller`'s own `call_indirect`,
        // completes the call.
        let mut s = TermStore::new();
        let x = s.var(1);
        let y = s.var(0);
        let sum = s.prim(PrimOp::Add, x, y);
        let inner_add = s.abs(sum);
        let add = s.abs(inner_add);

        let three = s.lit(3);
        let partial = s.app(add, three);

        let g = s.var(0);
        let four = s.lit(4);
        let call_g = s.app(g, four);
        let caller = s.abs(call_g);

        let top = s.app(caller, partial);

        let frag = try_compile(&s, top).expect("a partially applied literal lambda should compile");
        assert_eq!(frag.arity, 0);

        let (mut store, instance) = instantiate(&frag.wat);
        let func = instance.get_typed_func::<(), i64>(&mut store, "f").unwrap();
        let compiled = func.call(&mut store, ()).unwrap();
        let interpreted = apply_term(&s, top, &[]).unwrap();
        assert_eq!(compiled, 7);
        assert_eq!(compiled, interpreted);
    }

    #[test]
    fn partial_application_of_a_capturing_literal_lambda_compiles() {
        // g = \z. (\g2. g2(4)) ((\x y. x + y + z)(3)) -- the literal
        // lambda being partially applied (`\x y. x + y + z`) itself
        // captures `z`, from `g`'s own scope -- exercises the trickiest
        // part of `push_pap_env`: the wrapper's own environment needs
        // both the already-supplied argument (`3`) *and* a copy of
        // `root`'s own environment (holding `z`), computed at the
        // partial-application site and forwarded to `root`'s own call
        // once the wrapper is completed.
        let mut s = TermStore::new();
        let y = s.var(0);
        let x = s.var(1);
        let z_captured = s.var(2);
        let xy = s.prim(PrimOp::Add, x, y);
        let xyz = s.prim(PrimOp::Add, xy, z_captured);
        let inner = s.abs(xyz);
        let capturing_add = s.abs(inner);

        let three = s.lit(3);
        let partial = s.app(capturing_add, three);

        let g2 = s.var(0);
        let four = s.lit(4);
        let call_g2 = s.app(g2, four);
        let caller = s.abs(call_g2);

        let called = s.app(caller, partial);
        let g = s.abs(called);

        let frag = try_compile(&s, g).expect("a partially applied capturing lambda should compile");
        assert_eq!(frag.arity, 1);

        let (mut store, instance) = instantiate(&frag.wat);
        let func = instance.get_typed_func::<i64, i64>(&mut store, "f").unwrap();

        for z in [-5, 0, 1, 100] {
            let compiled = func.call(&mut store, z).unwrap();
            let interpreted = apply_term(&s, g, &[z]).unwrap();
            assert_eq!(compiled, 7 + z, "mismatch at z={z}");
            assert_eq!(compiled, interpreted, "mismatch at z={z}");
        }
    }

    #[test]
    fn a_pap_wrappers_own_supplied_argument_creating_more_closures_does_not_corrupt_its_environment() {
        // Regression test for a real bug `tests/compile_fuzz.rs` found when
        // stress-tested well past its own default seed count (250; this
        // reproduces at seed 2117, only reachable at 3,000+): a partially-
        // applied literal lambda whose *supplied* argument itself creates
        // more closures/partial applications -- exactly the general shape
        // `partial_application_of_a_capturing_literal_lambda_compiles`
        // above already covers for the *root*'s own captures, but not
        // for an arbitrary supplied-argument expression.
        //
        // `push_pap_env`'s own docs explain the mechanism: it used to
        // stash the newly-allocated environment's own address in
        // `$envtmp` across the whole loop building it, relying on that
        // local surviving each supplied argument's own `compile_node`
        // call -- but a supplied argument is an arbitrary expression, so
        // that call can itself recurse into more `push_closure_env`/
        // `push_pap_env` emission, which reuses `$envtmp` as scratch too,
        // silently corrupting the *outer* wrapper's own remembered
        // address. Fixed by keeping every value the environment needs on
        // the Wasm value stack instead of round-tripping any of it
        // through a local.
        //
        // Reproduces the exact random term `compile_fuzz.rs`'s own
        // generator builds at seed 2117 (its `gen_tail_recursive`, whose
        // `payload` is a `gen_closure_block` under-applying a literal
        // lambda whose own supplied argument is itself another
        // `gen_closure_block`) -- embedded here, self-contained, as a
        // permanent regression rather than relying on stumbling into
        // this seed again during a future stress run.
        struct Rng(u64);
        impl Rng {
            fn below(&mut self, n: u32) -> u32 {
                self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
                let mut z = self.0;
                z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
                z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
                ((z ^ (z >> 31)) % n as u64) as u32
            }
            fn i64_range(&mut self, lo: i64, hi: i64) -> i64 {
                self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
                let mut z = self.0;
                z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
                z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
                lo + ((z ^ (z >> 31)) % ((hi - lo + 1) as u64)) as i64
            }
        }
        const MAX_LIT: i64 = 50;
        fn random_arith_op(rng: &mut Rng) -> PrimOp {
            [PrimOp::Add, PrimOp::Sub, PrimOp::Mul][rng.below(3) as usize]
        }
        fn random_cmp_op(rng: &mut Rng) -> PrimOp {
            [PrimOp::Lt, PrimOp::Le, PrimOp::Eq][rng.below(3) as usize]
        }
        fn gen_leaf(rng: &mut Rng, s: &mut TermStore, scope: u32) -> Hash {
            if scope > 0 && rng.below(2) == 0 {
                s.var(rng.below(scope))
            } else {
                s.lit(rng.i64_range(-MAX_LIT, MAX_LIT))
            }
        }
        fn gen_cond(rng: &mut Rng, s: &mut TermStore, scope: u32, fuel: u32) -> Hash {
            let a = gen_expr(rng, s, scope, fuel);
            let b = gen_expr(rng, s, scope, fuel);
            let op = random_cmp_op(rng);
            s.prim(op, a, b)
        }
        fn gen_expr(rng: &mut Rng, s: &mut TermStore, scope: u32, fuel: u32) -> Hash {
            if fuel == 0 || rng.below(3) == 0 {
                return gen_leaf(rng, s, scope);
            }
            match rng.below(4) {
                0 => {
                    let a = gen_expr(rng, s, scope, fuel - 1);
                    let b = gen_expr(rng, s, scope, fuel - 1);
                    let op = random_arith_op(rng);
                    s.prim(op, a, b)
                }
                1 => {
                    let c = gen_cond(rng, s, scope, fuel - 1);
                    let t = gen_expr(rng, s, scope, fuel - 1);
                    let e = gen_expr(rng, s, scope, fuel - 1);
                    s.if_(c, t, e)
                }
                _ => gen_closure_block(rng, s, scope, fuel - 1),
            }
        }
        fn gen_closure_block(rng: &mut Rng, s: &mut TermStore, scope: u32, fuel: u32) -> Hash {
            let inner_arity = 1 + rng.below(2);
            let inner_scope = scope + inner_arity;
            let inner_body = gen_expr(rng, s, inner_scope, fuel);
            let mut inner = inner_body;
            for _ in 0..inner_arity {
                inner = s.abs(inner);
            }
            let supplied = rng.below(inner_arity + 1);
            let mut applied = inner;
            for _ in 0..supplied {
                let arg = gen_expr(rng, s, scope, fuel);
                applied = s.app(applied, arg);
            }
            if supplied == inner_arity {
                return applied;
            }
            let remaining = inner_arity - supplied;
            let mut remaining_args = Vec::new();
            for _ in 0..remaining {
                remaining_args.push(gen_expr(rng, s, scope, fuel));
            }
            let g_var = s.var(remaining);
            let mut call_g = g_var;
            for i in 0..remaining {
                let y_i = s.var(remaining - 1 - i);
                call_g = s.app(call_g, y_i);
            }
            let mut caller = call_g;
            for _ in 0..(1 + remaining) {
                caller = s.abs(caller);
            }
            let mut call_caller = s.app(caller, applied);
            for r in remaining_args {
                call_caller = s.app(call_caller, r);
            }
            call_caller
        }

        let mut rng = Rng(0x00C0_FFEE_1E55_u64 ^ 2117);
        let choice = rng.below(4); // gen_program's own dispatch draw -- must be consumed first to match its RNG state exactly
        assert_eq!(choice, 1, "seed 2117 should still pick gen_tail_recursive first");
        let mut s = TermStore::new();
        let n = s.var(1);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Le, n, zero);
        let base = s.var(0);
        let n2 = s.var(1);
        let one = s.lit(1);
        let n_minus_1 = s.prim(PrimOp::Sub, n2, one);
        let f = s.var(2);
        let payload = gen_expr(&mut rng, &mut s, 2, 3);
        let op = random_arith_op(&mut rng);
        let acc2 = s.var(0);
        let new_acc = s.prim(op, acc2, payload);
        let rec_call = s.app2(f, n_minus_1, new_acc);
        let body = s.if_(cond, base, rec_call);
        let inner = s.abs(body);
        let abs = s.abs(inner);
        let h = s.rec(abs);

        assert_eq!(
            apply_term(&s, h, &[10, -20]).unwrap(),
            -370,
            "interpreter itself should still agree with this hand-derivation"
        );

        let frag = try_compile(&s, h).expect("this term should still compile");
        let (mut store, instance) = instantiate(&frag.wat);
        let func = instance.get_typed_func::<(i64, i64), i64>(&mut store, "f").unwrap();
        let compiled = func.call(&mut store, (10, -20)).unwrap();
        assert_eq!(compiled, -370, "compiled and interpreted must agree");
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
    fn an_over_applied_literal_lambda_returning_a_closure_compiles_and_matches_interpreter() {
        // f = \a b. if 0 < a then (\c. a+b+c) else (\c. a-b+c); f(x,y,z) --
        // `f`'s own arity is 2 (`peel` stops there: its body is an `If`,
        // not a further bare `Abs`, so the two branches don't get folded
        // into `f`'s own combinator the way `\a b c. ..` would), and each
        // branch is itself a fresh, arity-1 closure -- already compiled
        // correctly today as an `If`-between-closures *value* (see
        // `a_capturing_closure_compiles_and_matches_interpreter`). What's
        // new is over-applying `f` with a 3rd argument `z`: `f`'s own
        // saturated call (`f(x,y)`) is compiled, then whatever it
        // *returns* is called again through `call_indirect`, exactly like
        // calling a closure-typed variable -- see `compile_node`'s own
        // docs on the exact mechanism (evaluating the saturated call
        // twice rather than stashing it in a local across the extra
        // argument's own compilation). Tried at both a positive and a
        // negative `x` so both branches -- and hence both closures
        // registered as separate combinators -- actually get exercised.
        let mut s = TermStore::new();
        let c1 = s.var(0);
        let b1 = s.var(1);
        let a1 = s.var(2);
        let ab1 = s.prim(PrimOp::Add, a1, b1);
        let abc1 = s.prim(PrimOp::Add, ab1, c1);
        let closure1 = s.abs(abc1); // \c. a+b+c

        let c2 = s.var(0);
        let b2 = s.var(1);
        let a2 = s.var(2);
        let amb2 = s.prim(PrimOp::Sub, a2, b2);
        let ambc2 = s.prim(PrimOp::Add, amb2, c2);
        let closure2 = s.abs(ambc2); // \c. a-b+c

        let a_body = s.var(1);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Lt, zero, a_body);
        let body = s.if_(cond, closure1, closure2);
        let b_binder = s.abs(body);
        let f = s.abs(b_binder); // \a b. if 0 < a then closure1 else closure2

        for (a_val, b_val, c_val, expected) in [(10i64, 3i64, 100i64, 113i64), (-5, 3, 100, 92)] {
            let xa = s.lit(a_val);
            let yb = s.lit(b_val);
            let zc = s.lit(c_val);
            let fx = s.app(f, xa);
            let fxy = s.app(fx, yb);
            let fxyz = s.app(fxy, zc);

            let frag = try_compile(&s, fxyz).expect("an over-applied literal lambda returning a closure should compile");
            assert_eq!(frag.arity, 0);
            assert!(frag.wat.contains("call_indirect"));

            let (mut store, instance) = instantiate(&frag.wat);
            let func = instance.get_typed_func::<(), i64>(&mut store, "f").unwrap();
            let compiled = func.call(&mut store, ()).unwrap();
            let interpreted = apply_term(&s, fxyz, &[]).unwrap();
            assert_eq!(compiled, expected, "a={a_val} b={b_val} c={c_val}");
            assert_eq!(compiled, interpreted, "a={a_val} b={b_val} c={c_val}");
        }
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
