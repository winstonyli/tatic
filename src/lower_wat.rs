//! Lowers `ir::Module` to WebAssembly text (WAT), one template per IR node,
//! each copied from the matching arm of legacy `compile::compile_node`. Also
//! home to the fixed emitters (the bump allocator, wrapping div, comparison
//! and arithmetic instruction tables, the partial-application wrapper, and
//! the curried stage chain) shared with the legacy path in `compile.rs`.
#![cfg_attr(not(test), allow(dead_code))] // wired into try_compile in JIT IR step 1, Task 3

use std::collections::HashSet;

use hashbrown::HashMap;

use crate::compile::CompiledFragment;
use crate::ir::{Combinator, Dispatch, Func, Module, Node, Read};
use crate::term::PrimOp;

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

    let mut lw = Lowering { m, stage0, call_indirect_arities: Vec::new() };
    let mut fn_wat = String::new();
    lw.function("f", &m.entry, false, &mut fn_wat);
    let mut combinator_wat = String::new();
    for (idx, c) in m.combinators.iter().enumerate() {
        match c {
            Combinator::Lifted(f) => lw.function(&format!("c{idx}"), f, true, &mut combinator_wat),
            Combinator::Pap { root, supplied } => emit_pap_wrapper(&format!("c{idx}"), *root, comb_arity(m, *root), *supplied, &mut combinator_wat),
        }
    }
    combinator_wat.push_str(&stage_wat);

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
    let needs_alloc = m.combinators.iter().any(|c| match c {
        Combinator::Lifted(f) => f.env_len > 0,
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
    w.push_str(&combinator_wat);
    w.push_str(&fn_wat);
    w.push_str("  (export \"f\" (func $f))\n)\n");

    CompiledFragment { arity: m.entry.arity, wat: w, needs_hp_reset: needs_alloc }
}

/// A combinator's own arity. A wrapper takes whatever its root still needs.
fn comb_arity(m: &Module, idx: usize) -> usize {
    match &m.combinators[idx] {
        Combinator::Lifted(f) => f.arity,
        Combinator::Pap { root, supplied } => comb_arity(m, *root) - supplied,
    }
}

/// A combinator's environment length in `i64` slots. A wrapper's is
/// `[root's env pointer, each supplied argument]` (see `push_pap_env`).
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

struct Lowering<'m> {
    m: &'m Module,
    /// A combinator's `stage_0` table index. It is filled only under
    /// `Dispatch::Curried`, where every bare value is packed with it
    /// instead of the combinator's own index.
    stage0: HashMap<usize, usize>,
    /// Every arity used at a `call_indirect` site, for the module's `(type
    /// ...)` declarations.
    call_indirect_arities: Vec<usize>,
}

/// The function currently being lowered.
struct FnCx<'a> {
    name: &'a str,
    arity: usize,
    has_env: bool,
}

impl Lowering<'_> {
    fn function(&mut self, name: &str, f: &Func, has_env: bool, w: &mut String) {
        w.push_str(&format!("  (func ${name}"));
        if has_env {
            w.push_str(" (param $env i32)");
        }
        for i in 0..f.arity {
            w.push_str(&format!(" (param $p{i} i64)"));
        }
        w.push_str(" (result i64)\n");
        for i in 0..f.arity {
            w.push_str(&format!("    (local $t{i} i64)\n"));
        }
        // Scratch locals, declared unconditionally (harmless if unused):
        // `$envtmp` for `push_closure_env`, `$papenv` for `pap_env` and
        // `dynamic_apply`, `$diva`/`$divb` for `emit_wrapping_div`.
        w.push_str("    (local $envtmp i32)\n");
        w.push_str("    (local $papenv i64)\n");
        w.push_str("    (local $diva i64)\n");
        w.push_str("    (local $divb i64)\n");
        w.push_str("    (loop $L (result i64)\n");
        let cx = FnCx { name, arity: f.arity, has_env };
        self.node(&cx, &f.body, w, 6);
        w.push_str("    )\n  )\n");
    }

    /// The table index a closure value of combinator `idx` is packed with.
    fn table_value(&self, idx: usize) -> usize {
        match self.m.dispatch {
            Dispatch::Curried => self.stage0[&idx],
            Dispatch::Fast => idx,
        }
    }

    fn node(&mut self, cx: &FnCx, n: &Node, w: &mut String, indent: usize) {
        match n {
            Node::Lit(v) => push_line(w, indent, &format!("i64.const {v}")),
            Node::Read(r) => read(*r, w, indent),
            Node::Arith(op, a, b) => {
                self.node(cx, a, w, indent);
                self.node(cx, b, w, indent);
                if *op == PrimOp::Div {
                    emit_wrapping_div(w, indent);
                } else {
                    push_line(w, indent, arith_instr(*op).expect("ir::check: Arith carries an arithmetic op"));
                }
            }
            Node::If { cmp, a, b, then, els } => {
                self.node(cx, a, w, indent);
                self.node(cx, b, w, indent);
                push_line(w, indent, cmp_instr(*cmp).expect("ir::check: If carries a comparison"));
                push_line(w, indent, "if (result i64)");
                self.node(cx, then, w, indent + 2);
                push_line(w, indent, "else");
                self.node(cx, els, w, indent + 2);
                push_line(w, indent, "end");
            }
            Node::SelfCall { args, tail: true } => {
                // Stage every new argument in a temporary first, so
                // `f(b, a mod b)` doesn't overwrite `a` before `a mod b` is
                // computed. Then loop back.
                for (i, a) in args.iter().enumerate() {
                    self.node(cx, a, w, indent);
                    push_line(w, indent, &format!("local.set $t{i}"));
                }
                for i in 0..cx.arity {
                    push_line(w, indent, &format!("local.get $t{i}"));
                    push_line(w, indent, &format!("local.set $p{i}"));
                }
                push_line(w, indent, "br $L");
            }
            Node::SelfCall { args, tail: false } => {
                // A real call back into this function. Recursion stays
                // inside the running closure instance, so `$env` is
                // forwarded unchanged.
                if cx.has_env {
                    push_line(w, indent, "local.get $env");
                }
                for a in args {
                    self.node(cx, a, w, indent);
                }
                push_line(w, indent, &format!("call ${}", cx.name));
            }
            Node::CallKnown { f, env, args } => {
                push_closure_env(env, w, indent);
                for a in args {
                    self.node(cx, a, w, indent);
                }
                push_line(w, indent, &format!("call $c{f}"));
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
                    self.node(cx, callee, w, indent);
                    push_line(w, indent, "i64.const 32");
                    push_line(w, indent, "i64.shr_u");
                    push_line(w, indent, "i32.wrap_i64");
                    for a in args {
                        self.node(cx, a, w, indent);
                    }
                    self.node(cx, callee, w, indent);
                    push_line(w, indent, "i32.wrap_i64");
                    self.call_indirect_arities.push(args.len());
                    push_line(w, indent, &format!("call_indirect (type $ty{})", args.len()));
                }
                Dispatch::Curried => {
                    self.node(cx, callee, w, indent);
                    self.dynamic_apply(cx, args, w, indent);
                }
            },
            Node::MakeClosure { f, env } => {
                push_closure_env(env, w, indent);
                push_line(w, indent, "i64.extend_i32_u");
                push_line(w, indent, "i64.const 32");
                push_line(w, indent, "i64.shl");
                push_line(w, indent, &format!("i64.const {}", self.table_value(*f)));
                push_line(w, indent, "i64.or");
            }
            Node::MakePap { wrapper, root_env, args } => {
                self.pap_env(cx, root_env, args, w, indent);
                push_line(w, indent, "i64.extend_i32_u");
                push_line(w, indent, "i64.const 32");
                push_line(w, indent, "i64.shl");
                push_line(w, indent, &format!("i64.const {}", self.table_value(*wrapper)));
                push_line(w, indent, "i64.or");
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
    fn pap_env(&mut self, cx: &FnCx, root_env: &[Read], args: &[Node], w: &mut String, indent: usize) {
        push_closure_env(root_env, w, indent);
        push_line(w, indent, "i64.extend_i32_u");
        for a in args {
            self.node(cx, a, w, indent);
        }
        // Nothing below recurses, so the scratch locals are safe again.
        push_line(w, indent, &format!("i32.const {}", (1 + args.len()) * 8));
        push_line(w, indent, "call $alloc");
        push_line(w, indent, "local.set $envtmp");
        // `i64.store` wants the address below the value, so each value is
        // popped (last argument first) into `$papenv` and pushed again
        // after a fresh address.
        for slot in (0..=args.len()).rev() {
            push_line(w, indent, "local.set $papenv");
            push_line(w, indent, "local.get $envtmp");
            push_line(w, indent, "local.get $papenv");
            push_line(w, indent, &format!("i64.store offset={}", slot * 8));
        }
        push_line(w, indent, "local.get $envtmp");
    }

    /// Applies `args` one at a time, through the curried stage chains, to
    /// the packed closure on top of the stack. The only things held across
    /// an argument's own lowering are the current step's env-pointer half
    /// and a raw copy of the packed value. Both live on the operand stack,
    /// never in a scratch local (see `pap_env`).
    fn dynamic_apply(&mut self, cx: &FnCx, args: &[Node], w: &mut String, indent: usize) {
        for a in args {
            push_line(w, indent, "local.tee $papenv");
            push_line(w, indent, "i64.const 32");
            push_line(w, indent, "i64.shr_u");
            push_line(w, indent, "i32.wrap_i64");
            push_line(w, indent, "local.get $papenv");
            self.node(cx, a, w, indent);
            push_line(w, indent, "local.set $papenv"); // this argument's value
            push_line(w, indent, "i32.wrap_i64"); // the raw copy below it becomes the table index
            push_line(w, indent, "local.set $envtmp");
            push_line(w, indent, "local.get $papenv");
            push_line(w, indent, "local.get $envtmp");
            self.call_indirect_arities.push(1);
            push_line(w, indent, "call_indirect (type $ty1)");
        }
    }
}

fn read(r: Read, w: &mut String, indent: usize) {
    match r {
        Read::Param(li) => push_line(w, indent, &format!("local.get $p{li}")),
        Read::Env(k) => {
            push_line(w, indent, "local.get $env");
            push_line(w, indent, &format!("i64.load offset={}", k * 8));
        }
    }
}

/// Pushes an `i32` environment pointer holding `env`'s values in slot
/// order, or `i32.const 0` (no allocation at all) for an empty environment.
fn push_closure_env(env: &[Read], w: &mut String, indent: usize) {
    if env.is_empty() {
        push_line(w, indent, "i32.const 0");
        return;
    }
    push_line(w, indent, &format!("i32.const {}", env.len() * 8));
    push_line(w, indent, "call $alloc");
    push_line(w, indent, "local.set $envtmp");
    for (slot, r) in env.iter().enumerate() {
        push_line(w, indent, "local.get $envtmp");
        read(*r, w, indent);
        push_line(w, indent, &format!("i64.store offset={}", slot * 8));
    }
    push_line(w, indent, "local.get $envtmp");
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
pub(crate) fn emit_allocator(w: &mut String) {
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

pub(crate) fn push_line(w: &mut String, indent: usize, s: &str) {
    for _ in 0..indent {
        w.push(' ');
    }
    w.push_str(s);
    w.push('\n');
}

pub(crate) fn arith_instr(op: PrimOp) -> Option<&'static str> {
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

/// Emits `Div`'s own operator, in place of a bare `arith_instr`-driven
/// `i64.div_s` -- that single instruction traps on exactly one input
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
/// declared unconditionally in `compile_function` (harmless if unused,
/// matching `$envtmp`/`$papenv`'s own convention).
pub(crate) fn emit_wrapping_div(w: &mut String, indent: usize) {
    push_line(w, indent, "local.set $divb");
    push_line(w, indent, "local.tee $diva");
    push_line(w, indent, &format!("i64.const {}", i64::MIN));
    push_line(w, indent, "i64.eq");
    push_line(w, indent, "local.get $divb");
    push_line(w, indent, "i64.const -1");
    push_line(w, indent, "i64.eq");
    push_line(w, indent, "i32.and");
    push_line(w, indent, "if (result i64)");
    push_line(w, indent + 2, &format!("i64.const {}", i64::MIN));
    push_line(w, indent, "else");
    push_line(w, indent + 2, "local.get $diva");
    push_line(w, indent + 2, "local.get $divb");
    push_line(w, indent + 2, "i64.div_s");
    push_line(w, indent, "end");
}

pub(crate) fn cmp_instr(op: PrimOp) -> Option<&'static str> {
    use PrimOp::*;
    Some(match op {
        Lt => "i64.lt_s",
        Le => "i64.le_s",
        Eq => "i64.eq",
        Add | Sub | Mul | Div | Mod => return None,
    })
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
pub(crate) fn emit_pap_wrapper(name: &str, root_idx: usize, root_arity: usize, supplied: usize, w: &mut String) {
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

/// Emits a curried "stage chain" for the combinator registered at `idx`
/// (own arity `arity`, its own environment already `env_len` `i64` slots
/// long -- for an ordinary literal combinator that's `captures.len()`,
/// for a partial-application wrapper it's `1 + supplied`; this function
/// only ever copies those slots byte-for-byte, so it doesn't need to
/// know or care what's actually in them, the same way `emit_pap_wrapper`
/// doesn't need `compile_node`/`FnCtx` for its own fixed-offset body).
/// Called from `try_compile`'s own stage-generation loop, once per
/// combinator the fragment both needs generic dispatch for
/// (`Combinators::needs_generic_dispatch`) and actually reaches as a bare
/// value (`Combinators::used_as_bare_value` -- a combinator only ever
/// called directly and saturated gets no stage chain, even in a fragment
/// where generic dispatch is on for some *other* combinator) -- see the
/// module docs above `Combinators` for why that decision has to be made
/// fragment-wide, before any call site can choose between the ordinary
/// `call_indirect`/`$tyK` fast path and this mechanism.
///
/// Produces `arity` new one-argument-at-a-time functions, `$s{idx}_0 ..
/// $s{idx}_{arity-1}`, each of the shape `(param $env i32) (param $arg
/// i64) (result i64)` -- exactly `$ty1`'s own shape, so a call site
/// dispatching through this mechanism can share that already-declared
/// type rather than needing a new one. Returns their table indices,
/// `base_table_index .. base_table_index + arity` (the caller is
/// responsible for actually placing these functions' names in the
/// module's `elem` segment at exactly those indices, in order).
///
/// `stage_0`'s own table index is what a "generically dispatchable" bare
/// value of this combinator should be packed with -- *alongside this
/// combinator's own, ordinarily-built environment* (`push_closure_env`
/// for a literal, `push_pap_env`'s own root-env-pointer-first layout for
/// a wrapper), unchanged -- instead of `idx` itself: `stage_0`'s own
/// environment layout, before any argument has been supplied, coincides
/// exactly with this combinator's own ordinary one (zero accumulated
/// arguments appended yet), so no new environment-construction code is
/// needed at a value's *creation* site at all, only at each dispatch
/// step past the first.
///
/// `stage_i` (`i >= 1`)'s own environment is this combinator's own
/// `env_len`-slot prefix *followed by* the `i` arguments already
/// supplied, in application order -- not a level of indirection through
/// a separately stored environment pointer (contrast `emit_pap_wrapper`'s
/// own `(root's env pointer, supplied args)` layout): since this
/// combinator's own fast entry (`$c{idx}`) only ever reads its own
/// leading `env_len` slots and never looks past them, any longer buffer
/// sharing that same prefix satisfies it directly. So the last stage
/// (`i + 1 == arity`) simply forwards its own `$env` pointer *unchanged*
/// to `call $c{idx}`, alongside the `i` accumulated arguments (read back
/// out of the very same buffer, right after that prefix) and its own new
/// argument; every earlier stage allocates one slot more than it itself
/// received, copies its own prefix across verbatim, appends the new
/// argument, and returns a packed value pointing at the next stage.
pub(crate) fn emit_curried_stages(idx: usize, arity: usize, env_len: usize, base_table_index: usize, w: &mut String) -> Vec<usize> {
    let table_indices: Vec<usize> = (0..arity).map(|i| base_table_index + i).collect();
    for i in 0..arity {
        w.push_str(&format!("  (func $s{idx}_{i} (param $env i32) (param $arg i64) (result i64)\n"));
        // Declared unconditionally (harmless if unused, matching
        // `compile_function`'s own convention for `$envtmp`) -- only the
        // not-yet-saturated branch below actually needs it.
        w.push_str("    (local $envtmp i32)\n");
        if i + 1 == arity {
            push_line(w, 4, "local.get $env");
            for slot in 0..i {
                push_line(w, 4, "local.get $env");
                push_line(w, 4, &format!("i64.load offset={}", (env_len + slot) * 8));
            }
            push_line(w, 4, "local.get $arg");
            push_line(w, 4, &format!("call $c{idx}"));
        } else {
            push_line(w, 4, &format!("i32.const {}", (env_len + i + 1) * 8));
            push_line(w, 4, "call $alloc");
            push_line(w, 4, "local.set $envtmp");
            for slot in 0..(env_len + i) {
                push_line(w, 4, "local.get $envtmp");
                push_line(w, 4, "local.get $env");
                push_line(w, 4, &format!("i64.load offset={}", slot * 8));
                push_line(w, 4, &format!("i64.store offset={}", slot * 8));
            }
            push_line(w, 4, "local.get $envtmp");
            push_line(w, 4, "local.get $arg");
            push_line(w, 4, &format!("i64.store offset={}", (env_len + i) * 8));
            push_line(w, 4, "local.get $envtmp");
            push_line(w, 4, "i64.extend_i32_u");
            push_line(w, 4, "i64.const 32");
            push_line(w, 4, "i64.shl");
            push_line(w, 4, &format!("i64.const {}", table_indices[i + 1]));
            push_line(w, 4, "i64.or");
        }
        w.push_str("  )\n");
    }
    table_indices
}

#[cfg(test)]
mod tests {
    use super::*;

    fn instantiate(wat: &str) -> (wasmtime::Store<()>, wasmtime::Instance) {
        let bytes = wat::parse_str(wat).expect("valid wat");
        let engine = wasmtime::Engine::default();
        let module = wasmtime::Module::new(&engine, &bytes).unwrap();
        let mut store = wasmtime::Store::new(&engine, ());
        let instance = wasmtime::Instance::new(&mut store, &module, &[]).unwrap();
        (store, instance)
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

    /// Unpacks a closure value's `(env_ptr, table_idx)` halves the same
    /// way the compiler's own generated code does (see module docs).
    fn unpack(v: i64) -> (i32, i32) {
        ((v >> 32) as i32, (v & 0xFFFF_FFFF) as i32)
    }

    /// `emit_curried_stages` is reachable from `try_compile` now (gated on
    /// `Combinators::needs_generic_dispatch`, see its own docs), with a
    /// full end-to-end test exercising that real path
    /// (`inconsistent_call_arity_for_a_parameter_now_compiles_via_curried_dispatch`).
    /// These tests still earn their keep independently: driving
    /// `emit_curried_stages` directly, exporting each generated stage
    /// function by name and calling it straight from Rust with no
    /// `call_indirect`/table involved at all, isolates this mechanism's
    /// own correctness from `call_indirect`/table-wiring concerns
    /// entirely, rather than re-testing both at once.
    #[test]
    fn curried_stage_chain_reproduces_a_two_ary_non_capturing_call() {
        let mut w = String::new();
        w.push_str("(module\n");
        emit_allocator(&mut w);
        w.push_str("  (export \"memory\" (memory 0))\n");
        // c0(env, p0, p1) = p0 + p1 -- arity 2, no captures (env_len 0).
        w.push_str("  (func $c0 (param $env i32) (param $p0 i64) (param $p1 i64) (result i64)\n");
        w.push_str("    local.get $p0\n    local.get $p1\n    i64.add)\n");
        let table_indices = emit_curried_stages(0, 2, 0, 1, &mut w);
        assert_eq!(table_indices, vec![1, 2]);
        w.push_str("  (export \"s0_0\" (func $s0_0))\n");
        w.push_str("  (export \"s0_1\" (func $s0_1))\n");
        w.push_str(")\n");

        let (mut store, instance) = instantiate(&w);
        let stage0 = instance.get_typed_func::<(i32, i64), i64>(&mut store, "s0_0").unwrap();
        let stage1 = instance.get_typed_func::<(i32, i64), i64>(&mut store, "s0_1").unwrap();

        // "The bare value of c0, generically dispatchable" is (env = 0,
        // no captures; table_idx = stage_0's own index) -- stage_0 is
        // called directly with env=0 here for exactly that reason.
        let packed = stage0.call(&mut store, (0, 3)).unwrap();
        let (env1, tidx1) = unpack(packed);
        assert_eq!(tidx1, 2, "should point at stage_1");
        let result = stage1.call(&mut store, (env1, 4)).unwrap();
        assert_eq!(result, 7);
    }

    /// A capturing, 3-ary combinator, with a distinct weight on the
    /// capture and each argument so a swapped argument order or a
    /// captured value mixed up with an accumulated argument produces a
    /// visibly wrong number rather than an accidental pass -- the same
    /// discipline `eval_and_prove_call_over`'s own regression tests use
    /// for the analogous hazard in `proof.rs`.
    #[test]
    fn curried_stage_chain_handles_a_capturing_three_ary_combinator_without_mixing_up_slots() {
        let mut w = String::new();
        w.push_str("(module\n");
        emit_allocator(&mut w);
        w.push_str("  (export \"memory\" (memory 0))\n");
        w.push_str("  (export \"alloc\" (func $alloc))\n");
        // c0(env, p0, p1, p2) = cap + p0*100 - p1*10 + p2 -- arity 3, one
        // capture (cap, at slot 0) -- env_len 1.
        w.push_str("  (func $c0 (param $env i32) (param $p0 i64) (param $p1 i64) (param $p2 i64) (result i64)\n");
        w.push_str("    local.get $env\n    i64.load offset=0\n");
        w.push_str("    local.get $p0\n    i64.const 100\n    i64.mul\n    i64.add\n");
        w.push_str("    local.get $p1\n    i64.const 10\n    i64.mul\n    i64.sub\n");
        w.push_str("    local.get $p2\n    i64.add)\n");
        let table_indices = emit_curried_stages(0, 3, 1, 1, &mut w);
        assert_eq!(table_indices, vec![1, 2, 3]);
        w.push_str("  (export \"s0_0\" (func $s0_0))\n");
        w.push_str("  (export \"s0_1\" (func $s0_1))\n");
        w.push_str("  (export \"s0_2\" (func $s0_2))\n");
        w.push_str(")\n");

        let (mut store, instance) = instantiate(&w);
        let alloc = instance.get_typed_func::<i32, i32>(&mut store, "alloc").unwrap();
        let memory = instance.get_memory(&mut store, "memory").unwrap();
        let stage0 = instance.get_typed_func::<(i32, i64), i64>(&mut store, "s0_0").unwrap();
        let stage1 = instance.get_typed_func::<(i32, i64), i64>(&mut store, "s0_1").unwrap();
        let stage2 = instance.get_typed_func::<(i32, i64), i64>(&mut store, "s0_2").unwrap();

        // c0's own capturing environment, built by hand: one slot, cap = 5.
        let cap_env = alloc.call(&mut store, 8).unwrap();
        memory.data_mut(&mut store)[cap_env as usize..cap_env as usize + 8].copy_from_slice(&5i64.to_le_bytes());

        let packed1 = stage0.call(&mut store, (cap_env, 2)).unwrap();
        let (env1, tidx1) = unpack(packed1);
        assert_eq!(tidx1, 2, "should point at stage_1");
        let packed2 = stage1.call(&mut store, (env1, 3)).unwrap();
        let (env2, tidx2) = unpack(packed2);
        assert_eq!(tidx2, 3, "should point at stage_2");
        let result = stage2.call(&mut store, (env2, 7)).unwrap();
        assert_eq!(result, 5 + 2 * 100 - 3 * 10 + 7);
    }

    use crate::compile::try_compile;
    use crate::ir::fixtures::{factorial, twice, twice_inc};

    fn assert_lowers_like_legacy(fixture: (crate::term::TermStore, crate::term::Hash, crate::ir::Module)) {
        let (s, h, m) = fixture;
        crate::ir::check(&m).unwrap();
        let legacy = try_compile(&s, h).expect("the legacy path compiles every fixture");
        let lowered = lower(&m);
        assert_eq!(lowered.wat, legacy.wat);
        assert_eq!(lowered.arity, legacy.arity);
        assert_eq!(lowered.needs_hp_reset, legacy.needs_hp_reset);
    }

    #[test]
    fn factorial_lowers_to_the_legacy_wat() {
        assert_lowers_like_legacy(factorial());
    }

    #[test]
    fn a_closure_parameter_call_lowers_to_the_legacy_wat() {
        assert_lowers_like_legacy(twice());
    }

    #[test]
    fn a_known_call_passing_a_closure_value_lowers_to_the_legacy_wat() {
        assert_lowers_like_legacy(twice_inc());
    }
}
