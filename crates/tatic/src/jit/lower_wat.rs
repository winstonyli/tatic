//! Lowers `ir::Module` to WebAssembly text (WAT), one template per IR node
//! (`Lowering::node`). Also home to wrapping div and the comparison and
//! arithmetic instruction tables; the module-level templates (the bump
//! allocator, the partial-application wrapper and the curried stage chain)
//! are in `lower_wat/templates.rs`. Every representation choice lives here;
//! `compile.rs` decides only term shape and builds the IR.
//!
//! Every call (`SelfCall`, `CallKnown`) lowers to `Ins::Call(position)`; then
//! each function's tail self calls are rewritten to the loop form (`loop_form`:
//! the arguments written to the parameter slots by `local.set`, then `Br`),
//! which the printer wraps in `loop $top` and the gate proves like a call. A
//! remaining call prints as `return_call` in tail position and `call` otherwise
//! (`tatic_wasm::print`'s tail rule), so tail recursion runs in constant Wasm
//! call-stack depth.
//!
//! ## Closures: real closure conversion, uniform representation
//!
//! Every value in this fragment is a plain `i64`, including a closure
//! value -- but a closure packs *two* things into that one `i64`: a
//! table index (low 32 bits) identifying which compiled function to call,
//! and a pointer into linear memory (high 32 bits) to that closure's
//! *environment* -- the captured values it closed over, laid out as
//! consecutive `i64` slots and allocated by the bump allocator (see
//! `emit_allocator`) at the point the closure is created. A
//! *non-capturing* lambda ("known function"/"known call" in the compiler
//! literature) still needs no environment at all -- its pointer half is
//! just `0`, a constant, and its `$env` parameter goes unread -- so this
//! is one uniform representation, not two: every combinator that can be
//! reached through the table takes an `$env: i32` parameter first,
//! whether or not its own body ever reads from it, precisely so a
//! `call_indirect` site never needs to know in advance whether the
//! closure it's calling captures anything. The exception is a capturing
//! combinator nothing reaches through the table -- never packed into a
//! value, never a partial-application root (`direct_only`). It is lambda
//! lifted: it takes its captures as leading `i64` parameters `$e0 ..`
//! instead, so calling it allocates nothing.
//!
//! `shape::free_vars` finds what a lambda literal captures, relative to
//! its own parameter range, by walking its body (following *into* further
//! nested lambdas too, since a closure nested inside another one still
//! captures from the very same enclosing scope) -- this becomes the
//! environment's slot layout (`ir::Func::env_len`, and the `env` of every
//! `MakeClosure`/`CallKnown` that creates one). Wherever the IR creates a
//! closure, `push_closure_env` allocates that layout's worth of memory
//! and, slot by slot, stores each captured value's *current* value, one
//! `ir::Read` per slot (`compile::build_read` resolved each to either one
//! of the current function's own parameters or one of *its* own
//! environment slots -- so a closure nested several levels deep captures
//! through as many levels as it needs to, uniformly). A self-recursive
//! value's own self-reference is never treated as a capture (it's bound
//! by `Rec`, resolved separately by `match_self_call`, and never itself a
//! plain readable value) -- `free_vars` excludes it explicitly rather than
//! have it (wrongly) show up as an uncapturable free variable in every
//! recursive function.
//!
//! A closure value can then be *applied* two ways. `CallUnknown` calls one
//! through a `Read` (a parameter *or* a captured free variable, the same
//! either way) that's always called with the same number of arguments
//! everywhere in its own function (`shape::infer_closure_arities` finds
//! these, keyed by absolute `Var` index so it doesn't need to distinguish
//! the two); its template is Wasm's `call_indirect` through the shared
//! table, unpacking the environment pointer and table index back out of
//! the packed `i64` first. `CallKnown` calls a literal lambda appearing
//! directly in function position (the builder's registry gives it a table
//! slot); its template is an ordinary, statically-known `call`, with a
//! freshly created environment passed as that call's first argument --
//! or, for a lambda-lifted (`direct_only`) callee, the captured values
//! themselves.
//! `MakeClosure`, a lambda passed around as a value it's never applied to
//! (an argument, a branch's result, ...), packs its (possibly-empty)
//! environment and table index into a single `i64` the same way.
//!
//! What's out of scope: capturing an enclosing self-recursive binding's
//! own self-reference as a plain value from a *nested* closure (an honest,
//! structural rejection -- see `free_vars`'s self-exclusion -- rather than
//! a special-cased check). Nothing statically checks that a value passed
//! into a closure-typed parameter actually has the arity that parameter's
//! own body expects of it -- `call_indirect`'s own dynamic type check
//! catches a mismatch as a trap, caught safely by `jit.rs`'s sample
//! verification the same way any other compiler bug would be.
//!
//! ## Partial application: compile-time desugaring, not a runtime object
//!
//! An *under*-applied literal lambda (`root`, own arity `n`, applied to
//! only `k < n` arguments) is a genuine partial application: the
//! expression's value is a fresh closure of arity `n - k`, waiting for
//! the rest. Since every call site in this fragment has a statically
//! known argument count, there's never a need for a fully general runtime
//! mechanism that dispatches on arity dynamically (the way, say, GHC's
//! PAP objects do) -- the missing argument count is always known at
//! compile time, so it's resolved then: the builder registers a
//! synthesized wrapper combinator (`ir::Combinator::Pap`), keyed by
//! `(root, k)` alone (*not* the actual argument values supplied -- those
//! only matter at each creation site, not to the wrapper's own compiled
//! code, which every call site with the same `(root, k)` shares), and
//! `MakePap`'s template creates a value of it (`Lowering::pap_env`)
//! exactly the way any other closure value is created. `emit_pap_wrapper`
//! needs no IR body at all for the wrapper's own code -- its environment
//! layout is entirely fixed by `(root, k)` (slot `0` is `root`'s own
//! environment pointer, slots `1..=k` are the already-supplied
//! arguments), so it's just a handful of fixed loads forwarded into one
//! statically-known `call`.
//!
//! A variable (not a literal lambda) applied with inconsistent arities has
//! no fixed arity to compare against, so there's no missing-argument count
//! to desugar around this way; that case is handled by a separate,
//! fragment-wide fallback -- see "Generic closure dispatch" below.
//! Over-application of a literal lambda is a different, *narrower*
//! problem: `root`'s own identity and arity are still statically known
//! (it's *what its body computes* that isn't) -- see "Over-application"
//! below.
//!
//! ## Over-application: dispatching a saturated call's own result
//!
//! An *over*-applied literal lambda (`root`, own arity `n`, applied to
//! `k > n` arguments) means the *first* `n` arguments saturate `root`
//! itself, and the remaining `k - n` are applied to whatever `root`'s own
//! body evaluates to once called -- which only makes sense if that's
//! itself a closure (e.g. `root = \a b. if a > 0 then (\c. ..) else (\c.
//! ..)`, returning one of two further, possibly-capturing closures
//! depending on `a`). The builder expresses it as a `CallUnknown` whose
//! callee is the saturated `CallKnown`, so it lowers exactly the way
//! calling a closure-typed *variable* does (see above) -- the only
//! difference is that the callee is a freshly computed value rather than
//! one read from a local or capture slot.
//!
//! Nothing here checks that `root`'s body genuinely denotes a closure once
//! applied -- an over-applied literal lambda whose body is a plain `Int`
//! still compiles, into a `call_indirect` on a garbage table index that
//! either traps or (astronomically unlikely) coincidentally lands on some
//! unrelated table entry. `jit.rs` never installs such a term: it isn't
//! simply typed, so `typing::well_typed` declines it before the sample
//! battery runs (`docs/related-work/` §38). Sample verification alone was
//! not enough: it only sees the ill-typed code when a sample reaches it.
//!
//! `call_indirect`'s own operand order needs the callee's packed value
//! split across *both* ends of the call (environment pointer first, table
//! index last, with the `k - n` extra arguments' own lowering -- and any
//! nested closure/PAP construction it might trigger -- necessarily
//! happening in between). Rather than stash that value in a local across
//! the extra arguments' own lowering (exactly the hazard
//! `Lowering::pap_env`'s docs describe, and that bit its predecessor for
//! real once), the `Fast`-mode `CallUnknown` template lowers its callee
//! twice, once for each half. For a saturated call that is a pure,
//! deterministic Wasm function call with no observable side effect beyond
//! bump-allocator growth (which doesn't affect the result), so recomputing
//! it is correct, if not free: a deeply left-nested chain of
//! over-applications recomputes its own innermost saturated call once per
//! enclosing over-application. Left as a known, documented tradeoff
//! rather than a `pap_env`-style stack-based reordering, which would need
//! `O(k - n)` dedicated scratch storage per call site (not just the one or
//! two locals a fixed-shape wrapper needs) to reassemble the extra
//! arguments in order after popping them off to reach the callee
//! underneath.
//!
//! ## Generic closure dispatch: a curried fallback for inconsistent arities
//!
//! A closure-typed variable called with a genuinely different number of
//! arguments at different call sites has no single fixed arity to desugar
//! around (`ArityUse::Consistent(k)`/`ArityUse::Inconsistent`,
//! `infer_closure_arities`'s widened classification). Rather than reject
//! such a term outright, every combinator (literal or PAP wrapper) reached
//! as a bare value additionally gets a curried "stage chain" -- `n`
//! further functions `stage_0..stage_{n-1}`, all of one shared type
//! `(func (param $env i32) (param $arg i64) (result i64))`, each taking
//! exactly one more argument and either forwarding to the combinator's own
//! ordinary, fixed-arity entry (once all `n` are collected) or returning a
//! fresh closure pointing at the next stage (`emit_curried_stages`). Every
//! `CallUnknown` -- through a variable or at an over-application site --
//! then dispatches one argument at a time through this chain via
//! `call_indirect (type $ty1)` (`Lowering::dynamic_apply`) instead of the
//! ordinary per-arity `call_indirect (type $tyK)` fast path.
//!
//! This is a *fragment-wide*, not per-call-site, decision (`ir::Dispatch`):
//! there is no real type system, so once any variable anywhere in a
//! compiled fragment is called inconsistently, no other closure value in
//! that same fragment can be locally proven safe from also reaching it.
//! The dispatch mode is known once the IR is built, before any WAT is
//! written, so there is no discovery pass. Under `Dispatch::Fast` (every
//! term that doesn't use this capability) lowering is the ordinary fast
//! path -- this is an additive fallback, not a replacement, and its real
//! per-call cost (roughly 1.5x on an otherwise fast-path-eligible hot
//! loop) is paid only by a fragment that actually needs it -- see
//! `docs/related-work/` §9 for the measured numbers.
//!
//! A *recursive* (`Rec`-wrapped) use of this mechanism gets kernel-proof
//! backing too, per instance rather than universally (the loop-carried
//! parameter still has no honest static type across iterations) --
//! `proof::eval_dyn_tail_recursive` for a *tail*-recursive shape, and
//! `proof::eval_dyn`'s own `self_ctx`-threaded recursion (mutually with
//! `eval_dyn_tail_recursive`) for a *non*-tail-recursive one, including
//! branching (e.g. an embedded self-call inside `1 + f(n-1)`, or two in
//! one leaf as in naive Fibonacci). See `docs/related-work/` §14 for what's
//! still open: a universal (not just per-instance) proof for either
//! shape needs a real dependent sum in the kernel's own type theory.

use hashbrown::{HashMap, HashSet};

use tatic_wasm::machine::{Class, EnvAccess, Entry, Ins};
use tatic_wasm::print::map_tail_calls;

use crate::jit::compile::{CompiledFragment, Item};
use crate::jit::ir::{Combinator, Dispatch, Func, Module, Node, Read};
use crate::lang::term::PrimOp;

mod templates;
use templates::*;

/// Lowers a well-formed module (`ir::check`) to WAT. It cannot fail: every
/// rejection happens in `compile::build` or `ir::check`, never here.
pub(crate) fn lower(m: &Module) -> CompiledFragment {
    let n = m.combinators.len();
    let curried = m.dispatch == Dispatch::Curried;
    let bare = used_as_bare_value(m);

    // Stage chains exist only for a combinator that is packed into a value
    // somewhere. One only ever called directly and saturated never has its
    // index packed. Table indices are allocated densely after the
    // combinators' own slots, in index order.
    let mut stage0 = HashMap::new();
    let mut stage_wat = String::new();
    if curried {
        let mut next_table_index = n;
        for idx in 0..n {
            if !bare.contains(&idx) {
                continue;
            }
            let indices = emit_curried_stages(idx, comb_arity(m, idx), env_len(m, idx), next_table_index, &mut stage_wat);
            next_table_index += indices.len();
            stage0.insert(idx, indices[0]);
        }
    }

    let direct = direct_only(m, &bare);
    let mut lw = Lowering { m, stage0, direct, call_indirect_arities: Vec::new() };
    // `$f` is lowered first (the type lines below depend on what lowering
    // records) but printed last.
    let entry = lw.function(n, &m.entry, EnvAccess::Params(0));
    let mut combinators = Vec::new();
    for (idx, c) in m.combinators.iter().enumerate() {
        combinators.push(match c {
            Combinator::Lifted(f) => {
                let env = if lw.direct.contains(&idx) { EnvAccess::Params(f.env_len) } else { EnvAccess::Pointer };
                lw.function(idx, f, env)
            }
            Combinator::Pap { root, supplied } => {
                let mut t = String::new();
                emit_pap_wrapper(&format!("c{idx}"), *root, comb_arity(m, *root), *supplied, &mut t);
                Item::Text(t)
            }
        });
    }
    if !stage_wat.is_empty() {
        combinators.push(Item::Text(stage_wat));
    }

    let mut w = String::new();
    w.push_str("(module\n");
    let mut used_arities = lw.call_indirect_arities.clone();
    used_arities.sort_unstable();
    used_arities.dedup();
    for k in &used_arities {
        // Every combinator takes its environment pointer first, so every
        // `call_indirect` type includes it. A curried stage's
        // `call_indirect (type $ty1)` shares this family.
        w.push_str(&format!("  (type $ty{k} (func (param i32)"));
        for _ in 0..*k {
            w.push_str(" (param i64)");
        }
        w.push_str(" (result i64)))\n");
    }
    let stage_needs_alloc = curried && bare.iter().any(|&idx| comb_arity(m, idx) > 1);
    let needs_alloc = m.combinators.iter().enumerate().any(|(idx, c)| match c {
        Combinator::Lifted(f) => f.env_len > 0 && !lw.direct.contains(&idx),
        Combinator::Pap { .. } => true,
    }) || stage_needs_alloc;
    if needs_alloc {
        emit_allocator(&mut w);
        // Exported so `jit.rs` can reset it before every top-level call.
        // Resetting inside `$f` would be unsound: a non-tail self-call
        // re-enters `$f` and would free closures still in use. See
        // `CompiledFragment::needs_hp_reset`.
        w.push_str("  (export \"hp\" (global $hp))\n");
        // Exported only so tests can watch memory stay bounded.
        w.push_str("  (export \"memory\" (memory 0))\n");
    }
    let total_table_len = n + if curried { bare.iter().map(|&idx| comb_arity(m, idx)).sum() } else { 0 };
    if total_table_len > 0 {
        w.push_str(&format!("  (table {total_table_len} funcref)\n"));
        w.push_str("  (elem (i32.const 0)");
        for i in 0..n {
            w.push_str(&format!(" $c{i}"));
        }
        if curried {
            for idx in 0..n {
                if !bare.contains(&idx) {
                    continue;
                }
                for i in 0..comb_arity(m, idx) {
                    w.push_str(&format!(" $s{idx}_{i}"));
                }
            }
        }
        w.push_str(")\n");
    }
    let mut module = vec![Item::Text(w)];
    module.extend(combinators);
    module.push(entry);
    module.push(Item::Text("  (export \"f\" (func $f))\n)\n".to_string()));

    CompiledFragment { arity: m.entry.arity, module, needs_hp_reset: needs_alloc, entry_pos: n }
}

/// A combinator's own arity. A wrapper takes whatever its root still needs.
/// Bytes per value slot (an `i64`): the stride of environments and call frames in linear memory.
const WORD_BYTES: usize = 8;
/// A WebAssembly memory page.
const PAGE_BYTES: usize = 65536;

fn comb_arity(m: &Module, idx: usize) -> usize {
    match &m.combinators[idx] {
        Combinator::Lifted(f) => f.arity,
        Combinator::Pap { root, supplied } => comb_arity(m, *root) - supplied,
    }
}

/// A combinator's environment length in `i64` slots. A wrapper's is
/// `[root's env pointer, each supplied argument]` (see `Lowering::pap_env`).
fn env_len(m: &Module, idx: usize) -> usize {
    match &m.combinators[idx] {
        Combinator::Lifted(f) => f.env_len,
        Combinator::Pap { supplied, .. } => 1 + supplied,
    }
}

/// Every combinator that is packed into a closure value somewhere, as
/// opposed to only ever being called directly.
fn used_as_bare_value(m: &Module) -> HashSet<usize> {
    fn go(n: &Node, out: &mut HashSet<usize>) {
        match n {
            Node::MakeClosure { f, .. } => {
                out.insert(*f);
            }
            Node::MakePap { wrapper, .. } => {
                out.insert(*wrapper);
            }
            _ => {}
        }
        for c in n.children() {
            go(c, out);
        }
    }
    let mut out = HashSet::new();
    for f in m.funcs() {
        go(&f.body, &mut out);
    }
    out
}

/// Every combinator that is only ever called directly: never packed into a
/// value and never the root a partial-application wrapper calls. Nothing
/// reaches one through the table, so it takes its captures (none, for a
/// closed one) as `i64` parameters (`$e0`, `$e1`, ...) ahead of its
/// arguments instead of an environment pointer, and a call to it allocates
/// nothing.
fn direct_only(m: &Module, bare: &HashSet<usize>) -> HashSet<usize> {
    let pap_roots: HashSet<usize> = m
        .combinators
        .iter()
        .filter_map(|c| match c {
            Combinator::Pap { root, .. } => Some(*root),
            Combinator::Lifted(_) => None,
        })
        .collect();
    m.combinators
        .iter()
        .enumerate()
        .filter(|(idx, c)| matches!(c, Combinator::Lifted(_)) && !bare.contains(idx) && !pap_roots.contains(idx))
        .map(|(idx, _)| idx)
        .collect()
}

struct Lowering<'m> {
    m: &'m Module,
    /// A combinator's `stage_0` table index. It is filled only under
    /// `Dispatch::Curried`, where every bare value is packed with it
    /// instead of the combinator's own index.
    stage0: HashMap<usize, usize>,
    /// The combinators that take their captures as parameters
    /// (`direct_only`).
    direct: HashSet<usize>,
    /// Every arity used at a `call_indirect` site, for the module's `(type
    /// ...)` declarations.
    call_indirect_arities: Vec<usize>,
}

/// The function currently being lowered.
struct FnCx {
    /// Its module position (`Ins::Call`'s operand).
    pos: usize,
    env: EnvAccess,
}

impl Lowering<'_> {
    /// A lowered function at module position `pos`: its record (arity, env access, body); the printer derives the header.
    fn function(&mut self, pos: usize, f: &Func, env: EnvAccess) -> Item {
        let cx = FnCx { pos, env };
        let mut code = Vec::new();
        self.node(&cx, &f.body, &mut code);
        let code = loop_form(&code, pos, &rev_slots(f.arity));
        Item::Func { pos, entry: Entry { arity: f.arity, env, code }, source: None }
    }

    /// The table index a closure value of combinator `idx` is packed with.
    fn table_value(&self, idx: usize) -> usize {
        match self.m.dispatch {
            Dispatch::Curried => self.stage0[&idx],
            Dispatch::Fast => idx,
        }
    }

    fn node(&mut self, cx: &FnCx, n: &Node, w: &mut Vec<Ins>) {
        match n {
            Node::Lit(v) => w.push(konst(*v)),
            Node::Read(r) => read(cx, *r, w),
            Node::Arith(op, a, b) => {
                self.node(cx, a, w);
                self.node(cx, b, w);
                match *op {
                    PrimOp::Div => emit_wrapping_div(w),
                    op => w.push(row_of(op, Class::Word, "ir::check: Arith carries an arithmetic op (wasm::table)")),
                }
            }
            Node::If { cmp, a, b, then, els } => {
                self.node(cx, a, w);
                self.node(cx, b, w);
                w.push(row_of(*cmp, Class::Bit, "ir::check: If carries a comparison (wasm::table)"));
                let (mut t, mut e) = (Vec::new(), Vec::new());
                self.node(cx, then, &mut t);
                self.node(cx, els, &mut e);
                w.push(Ins::If(t, e));
            }
            Node::SelfCall { args } => {
                // A real call back into this function. Recursion stays
                // inside the running closure instance, so its captures are
                // forwarded unchanged.
                match cx.env {
                    EnvAccess::Pointer => raw(w, "local.get $env"),
                    EnvAccess::Params(env_len) => {
                        for k in 0..env_len {
                            raw(w, &format!("local.get $e{k}"));
                        }
                    }
                }
                for a in args {
                    self.node(cx, a, w);
                }
                w.push(Ins::Call(cx.pos));
            }
            Node::CallKnown { f, env, args } => {
                if self.direct.contains(f) {
                    for r in env {
                        read(cx, *r, w);
                    }
                } else {
                    push_closure_env(cx, env, w);
                }
                for a in args {
                    self.node(cx, a, w);
                }
                w.push(Ins::Call(*f));
            }
            Node::CallUnknown { callee, args } => match self.m.dispatch {
                Dispatch::Fast => {
                    // `call_indirect` needs the environment pointer (high 32
                    // bits) before the arguments and the table index (low 32
                    // bits) after them. Rather than hold `callee` in a local
                    // across the arguments' own lowering, which may reuse
                    // every scratch local (see `pap_env`), `callee` is
                    // lowered twice. For a `Read` that is two local or
                    // memory reads. For an over-application's saturated
                    // `CallKnown` it is two pure calls, and the only side
                    // effect is bump-allocator growth.
                    self.node(cx, callee, w);
                    raw(w, "i64.const 32");
                    raw(w, "i64.shr_u");
                    raw(w, "i32.wrap_i64");
                    for a in args {
                        self.node(cx, a, w);
                    }
                    self.node(cx, callee, w);
                    raw(w, "i32.wrap_i64");
                    self.call_indirect_arities.push(args.len());
                    raw(w, &format!("call_indirect (type $ty{})", args.len()));
                }
                Dispatch::Curried => {
                    self.node(cx, callee, w);
                    self.dynamic_apply(cx, args, w);
                }
            },
            Node::MakeClosure { f, env } => {
                push_closure_env(cx, env, w);
                raw(w, "i64.extend_i32_u");
                raw(w, "i64.const 32");
                raw(w, "i64.shl");
                raw(w, &format!("i64.const {}", self.table_value(*f)));
                raw(w, "i64.or");
            }
            Node::MakePap { wrapper, root_env, args } => {
                self.pap_env(cx, root_env, args, w);
                raw(w, "i64.extend_i32_u");
                raw(w, "i64.const 32");
                raw(w, "i64.shl");
                raw(w, &format!("i64.const {}", self.table_value(*wrapper)));
                raw(w, "i64.or");
            }
        }
    }

    /// Builds a partial-application wrapper's environment: slot `0` is the
    /// root's environment pointer, then one slot per supplied argument.
    /// Every value is computed onto the Wasm value stack *before* this
    /// allocation. An argument's own lowering may build more closures,
    /// which reuse `$envtmp`/`$papenv` as scratch. A value on the stack
    /// survives that; a value held in either local does not. A fuzz-found
    /// regression once came from exactly this.
    fn pap_env(&mut self, cx: &FnCx, root_env: &[Read], args: &[Node], w: &mut Vec<Ins>) {
        push_closure_env(cx, root_env, w);
        raw(w, "i64.extend_i32_u");
        for a in args {
            self.node(cx, a, w);
        }
        // Nothing below recurses, so the scratch locals are safe again.
        raw(w, &format!("i32.const {}", (1 + args.len()) * WORD_BYTES));
        raw(w, "call $alloc");
        raw(w, "local.set $envtmp");
        // `i64.store` wants the address below the value, so each value is
        // popped (last argument first) into `$papenv` and pushed again
        // after a fresh address.
        for slot in (0..=args.len()).rev() {
            raw(w, "local.set $papenv");
            raw(w, "local.get $envtmp");
            raw(w, "local.get $papenv");
            raw(w, &format!("i64.store offset={}", slot * WORD_BYTES));
        }
        raw(w, "local.get $envtmp");
    }

    /// Applies `args` one at a time, through the curried stage chains, to
    /// the packed closure on top of the stack. The only things held across
    /// an argument's own lowering are the current step's env-pointer half
    /// and a raw copy of the packed value. Both live on the operand stack,
    /// never in a scratch local (see `pap_env`).
    fn dynamic_apply(&mut self, cx: &FnCx, args: &[Node], w: &mut Vec<Ins>) {
        for a in args {
            raw(w, "local.tee $papenv");
            raw(w, "i64.const 32");
            raw(w, "i64.shr_u");
            raw(w, "i32.wrap_i64");
            raw(w, "local.get $papenv");
            self.node(cx, a, w);
            raw(w, "local.set $papenv"); // this argument's value
            raw(w, "i32.wrap_i64"); // the raw copy below it becomes the table index
            raw(w, "local.set $envtmp");
            raw(w, "local.get $papenv");
            raw(w, "local.get $envtmp");
            self.call_indirect_arities.push(1);
            raw(w, "call_indirect (type $ty1)");
        }
    }
}

fn read(cx: &FnCx, r: Read, w: &mut Vec<Ins>) {
    match (r, cx.env) {
        (Read::Param(li), _) => w.push(Ins::Row { name: "local.get", operand: i64::from(li) }),
        (Read::Env(k), EnvAccess::Params(_)) => raw(w, &format!("local.get $e{k}")),
        (Read::Env(k), _) => {
            raw(w, "local.get $env");
            raw(w, &format!("i64.load offset={}", k as usize * WORD_BYTES));
        }
    }
}

/// Pushes an `i32` environment pointer holding `env`'s values in slot
/// order, or `i32.const 0` (no allocation at all) for an empty environment.
fn push_closure_env(cx: &FnCx, env: &[Read], w: &mut Vec<Ins>) {
    if env.is_empty() {
        raw(w, "i32.const 0");
        return;
    }
    raw(w, &format!("i32.const {}", env.len() * WORD_BYTES));
    raw(w, "call $alloc");
    raw(w, "local.set $envtmp");
    for (slot, r) in env.iter().enumerate() {
        raw(w, "local.get $envtmp");
        read(cx, *r, w);
        raw(w, &format!("i64.store offset={}", slot * WORD_BYTES));
    }
    raw(w, "local.get $envtmp");
}

/// The slots a self call's arguments are written to, top of the stack first: the last argument first.
pub(crate) fn rev_slots(arity: usize) -> Vec<i64> {
    (0..arity as i64).rev().collect()
}

/// The loop form (spec 2026-11-12-proved-loop-form-design.md, B1): `code` with each tail `Call(own)` replaced by a
/// `local.set` at each of `slots` (in order) then `Br`; other calls are left alone.
pub(crate) fn loop_form(code: &[Ins], own: usize, slots: &[i64]) -> Vec<Ins> {
    let set = |i: &i64| Ins::Row { name: "local.set", operand: *i };
    map_tail_calls(code, &mut |j| (j == own).then(|| slots.iter().map(set).chain([Ins::Br]).collect()))
}

/// The `const` row with operand `v`.
fn konst(v: i64) -> Ins {
    Ins::Row { name: "const", operand: v }
}

/// The table row of `op`, which must be of class `class`; `what` is the panic message otherwise.
fn row_of(op: PrimOp, class: Class, what: &str) -> Ins {
    let row = tatic_wasm::wasm::table().row(op.name()).filter(|r| r.class == class).expect(what);
    Ins::Row { name: row.name, operand: 0 }
}

/// A line the machine does not model (`Ins::Raw`), printed as given.
fn raw(w: &mut Vec<Ins>, s: &str) {
    w.push(Ins::Raw(s.to_string()));
}

/// Emits `Div`'s own operator, in place of a bare `i64.div_s` (`Div` has
/// no `wasm::table` row) -- that single instruction traps on exactly one input
/// (`i64::MIN / -1`, the one case where the mathematical quotient
/// overflows `i64`), per the WebAssembly spec, while `eval.rs`'s
/// reference semantics use `wrapping_div` there, silently wrapping back
/// to `i64::MIN`, the same non-trapping convention `Add`/`Sub`/`Mul`
/// already use uniformly (`Mod`/`i64.rem_s` needs no such case: both
/// sides already agree, wrapping to `0`). Left as a bare `i64.div_s`,
/// this is a real, if narrow, disagreement between compiled and
/// interpreted code that `jit.rs`'s own sample-verification battery
/// only happens to catch when a term's structure embeds `i64::MIN`
/// directly -- a runtime-computed `i64::MIN` divided by a sampled `-1`
/// would otherwise slip through `verify()` unnoticed.
///
/// Needs the stack's top two values (`a`, `b`, already compiled) copied
/// into scratch locals rather than duplicated in place, since Wasm's
/// MVP instruction set has no stack-only "dup" -- `$diva`/`$divb`,
/// declared unconditionally by the printer (harmless if unused,
/// matching `$envtmp`/`$papenv`'s own convention).
fn emit_wrapping_div(w: &mut Vec<Ins>) {
    raw(w, "local.set $divb");
    raw(w, "local.tee $diva");
    w.push(konst(i64::MIN));
    raw(w, "i64.eq");
    raw(w, "local.get $divb");
    w.push(konst(-1));
    raw(w, "i64.eq");
    raw(w, "i32.and");
    let mut e = Vec::new();
    raw(&mut e, "local.get $diva");
    raw(&mut e, "local.get $divb");
    raw(&mut e, "i64.div_s");
    w.push(Ins::If(vec![konst(i64::MIN)], e));
}

#[cfg(test)]
mod tests {
    use super::*;

    pub(super) fn instantiate(wat: &str) -> (wasmtime::Store<()>, wasmtime::Instance) {
        let bytes = wat::parse_str(wat).expect("valid wat");
        let engine = wasmtime::Engine::default();
        let module = wasmtime::Module::new(&engine, &bytes).unwrap();
        let mut store = wasmtime::Store::new(&engine, ());
        let instance = wasmtime::Instance::new(&mut store, &module, &[]).unwrap();
        (store, instance)
    }

    use crate::jit::compile::try_compile;
    use crate::jit::ir::fixtures::{factorial, twice, twice_inc};

    /// The hand-built fixture IR lowers to the same WAT as the builder's IR
    /// for the term (`try_compile` is `lower(build(..))`). This overlaps
    /// `compile::tests::build_produces_the_hand_built_ir_for_each_fixture`;
    /// the independent pin on the lowering is `tests/golden_wat.rs`.
    fn assert_lowers_like_the_builder(fixture: (crate::lang::term::TermStore, crate::lang::term::Hash, crate::jit::ir::Module)) {
        let (s, h, m) = fixture;
        crate::jit::ir::check(&m).unwrap();
        let built = try_compile(&s, h).expect("the builder accepts every fixture");
        let lowered = lower(&m);
        assert_eq!(lowered.wat(), built.wat());
        assert_eq!(lowered.arity, built.arity);
        assert_eq!(lowered.needs_hp_reset, built.needs_hp_reset);
    }

    #[test]
    fn a_directly_called_capturing_combinator_takes_its_captures_as_parameters() {
        // `capturing_closure_loop`'s `\y. acc + y` is only ever called
        // directly, so `acc` travels as a Wasm parameter and nothing in the
        // module allocates.
        let (_, s, h) = crate::support::samples::corpus().into_iter().find(|(name, ..)| *name == "capturing_closure_loop").unwrap();
        let frag = crate::jit::compile::try_compile(&s, h).unwrap();
        assert!(!frag.needs_hp_reset, "{}", frag.wat());
        assert!(!frag.wat().contains("$alloc"), "{}", frag.wat());
        assert!(frag.wat().contains("(func $c0 (param $e0 i64) (param $p0 i64)"), "{}", frag.wat());
        let (mut store, instance) = instantiate(&frag.wat());
        let f = instance.get_typed_func::<(i64, i64), i64>(&mut store, "f").unwrap();
        for (n, acc) in [(0, 0), (1, 0), (5, 3), (100, -7)] {
            assert_eq!(f.call(&mut store, (n, acc)).unwrap(), crate::lang::eval::apply_term(&s, h, &[n, acc]).unwrap(), "n={n} acc={acc}");
        }
    }

    #[test]
    fn factorial_lowers_like_the_builder() {
        assert_lowers_like_the_builder(factorial());
    }

    #[test]
    fn a_closure_parameter_call_lowers_like_the_builder() {
        assert_lowers_like_the_builder(twice());
    }

    #[test]
    fn a_known_call_passing_a_closure_value_lowers_like_the_builder() {
        assert_lowers_like_the_builder(twice_inc());
    }

    /// Only a tail self call becomes the loop form: one followed by more code, one to another position, and one in
    /// the tail of a nested `If` are told apart.
    #[test]
    fn loop_form_rewrites_only_tail_self_calls() {
        let get = |i| Ins::Row { name: "local.get", operand: i };
        let set = |i| Ins::Row { name: "local.set", operand: i };
        let cond = vec![get(0), konst(0), Ins::Row { name: "le", operand: 0 }];
        let lf = |c: &[Ins]| loop_form(c, 0, &rev_slots(2));
        let with = |tail: Vec<Ins>| [cond.clone(), vec![Ins::If(vec![konst(0)], [vec![get(0), get(1)], tail].concat())]].concat();
        let call0 = with(vec![Ins::Call(0)]);
        assert_eq!(lf(&call0), with(vec![set(1), set(0), Ins::Br]));
        let not_tail = [vec![konst(1)], call0.clone(), vec![Ins::Row { name: "add", operand: 0 }]].concat();
        assert_eq!(lf(&not_tail), not_tail);
        let other = with(vec![Ins::Call(1)]);
        assert_eq!(lf(&other), other);
        let nested = |tail: Vec<Ins>| [cond.clone(), vec![Ins::If(vec![konst(0)], with(tail))]].concat();
        assert_eq!(lf(&nested(vec![Ins::Call(0)])), nested(vec![set(1), set(0), Ins::Br]));
    }

    /// The loop form over env words: a loop `g` reading a capture `k`, called directly (its env as a parameter) and
    /// through `call_indirect` (its env behind a pointer), runs its own body as `br $top` and agrees with `eval`. These
    /// terms are `NotCovered`, so the text runs here rather than through `JitEngine::apply`.
    #[test]
    fn env_word_loops_run_and_match_eval() {
        let terms = [
            (r"\k n. (rec g m acc = if m <= 0 then acc else g (m - 1) (acc + k)) n 0", false),
            (r"\k n. (rec f i h = if i <= 0 then h n 0 else f (i - 1) h) 1 (rec g m acc = if m <= 0 then acc else g (m - 1) (acc + k))", true),
        ];
        for (src, indirect) in terms {
            let mut s = crate::lang::term::TermStore::new();
            let h = crate::support::samples::source(&mut s, src);
            let frag = try_compile(&s, h).unwrap_or_else(|| panic!("{src}: compiles"));
            let wat = frag.wat();
            let records = frag.records();
            let g = if indirect {
                let ptr: Vec<usize> = (0..records.len()).filter(|&p| records[p].is_some_and(|e| e.env == EnvAccess::Pointer)).collect();
                assert_eq!(ptr.len(), 1, "{src}: one record behind a pointer: {ptr:?}\n{wat}");
                ptr[0]
            } else {
                0
            };
            let want = if indirect { EnvAccess::Pointer } else { EnvAccess::Params(1) };
            assert_eq!(records[g].expect("g is a record").env, want, "{src}\n{wat}");
            let label = if g == frag.entry_pos { "$f".to_string() } else { format!("$c{g}") };
            let start = wat.find(&format!("(func {label} ")).unwrap_or_else(|| panic!("{src}: {label}\n{wat}"));
            let text = &wat[start..wat[start + 1..].find("(func").map_or(wat.len(), |i| start + 1 + i)];
            assert!(text.contains("br $top"), "{src}: g loops\n{wat}");
            let (mut store, instance) = instantiate(&wat);
            let f = instance.get_typed_func::<(i64, i64), i64>(&mut store, "f").unwrap();
            for k in [-3, 0, 7] {
                for n in (0..20).chain([100_000]) {
                    let got = f.call(&mut store, (k, n)).unwrap();
                    assert_eq!(Ok(got), crate::lang::eval::apply_term(&s, h, &[k, n]), "{src}: k={k} n={n}");
                }
            }
        }
    }
}
