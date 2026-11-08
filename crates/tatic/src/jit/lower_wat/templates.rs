//! The module-level templates of the lowering: the bump allocator, the
//! partial-application wrapper and the curried stage chain. Each is fixed
//! text with no IR body, so it stays text when function bodies become
//! `Ins` lists (`lower_wat.rs` emits the bodies).
use super::*;

/// Emits a bump allocator: one page (64KiB) of linear memory, a mutable
/// global `$hp` tracking the next free byte, and an `$alloc` function that
/// hands out `$n` bytes at a time, growing the memory (via `memory.grow`)
/// whenever `$hp` would run past the end of what's currently allocated.
/// Never reclaimed -- compiled instances are short-lived and per-call (see
/// `jit.rs`), so there's no GC here, just like there's no GC in the
/// combinator table above. `lower` emits this only when something
/// allocates: a combinator with a non-empty environment
/// (`push_closure_env`), a partial-application wrapper (`Lowering::pap_env`)
/// or a stage chain that accumulates arguments -- a compiled fragment with
/// none of those gets no memory section.
pub(super) fn emit_allocator(w: &mut String) {
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
    push_line(w, 4, &format!("i32.const {PAGE_BYTES}"));
    push_line(w, 4, "i32.mul");
    push_line(w, 4, "i32.gt_u");
    push_line(w, 4, "if");
    // pages_needed = ceil(($need - current_bytes) / PAGE_BYTES)
    push_line(w, 6, "local.get $need");
    push_line(w, 6, "memory.size");
    push_line(w, 6, &format!("i32.const {PAGE_BYTES}"));
    push_line(w, 6, "i32.mul");
    push_line(w, 6, "i32.sub");
    push_line(w, 6, "i32.const 65535");
    push_line(w, 6, "i32.add");
    push_line(w, 6, &format!("i32.const {PAGE_BYTES}"));
    push_line(w, 6, "i32.div_u");
    push_line(w, 6, "memory.grow");
    push_line(w, 6, "drop");
    push_line(w, 4, "end");
    push_line(w, 4, "local.get $need");
    push_line(w, 4, "global.set $hp");
    push_line(w, 4, "local.get $base");
    w.push_str("  )\n");
}

/// Emits a synthesized partial-application wrapper (`name` = `$c{idx}`,
/// its assigned table index) -- `root` (a literal combinator, already
/// registered at `root_idx` with its own arity `root_arity`) was applied
/// to only `supplied` of its arguments (an `ir::Combinator::Pap`, built
/// from an under-application); this wrapper takes the remaining
/// `root_arity - supplied` arguments and completes the call. Its own
/// environment layout is fixed by `(root_idx, supplied)` alone -- slot `0`
/// is `root`'s own environment pointer (as an `i64`, zero-extended, for
/// slot uniformity with every other slot), slots `1..=supplied` are the
/// values of the arguments `root` was already applied to -- see
/// `Lowering::pap_env`, which builds exactly this layout at each creation
/// site. Entirely self-contained (no IR body, unlike an ordinary
/// combinator's): every value here is just a fixed offset into
/// `$env`, or one of this function's own parameters, forwarded straight
/// into a single, statically-known `call`.
pub(super) fn emit_pap_wrapper(name: &str, root_idx: usize, root_arity: usize, supplied: usize, w: &mut String) {
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
        push_line(w, 4, &format!("i64.load offset={}", (slot + 1) * WORD_BYTES));
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
/// doesn't need an IR body for its own fixed-offset one).
/// Called from `lower`'s stage-generation loop, once per combinator of a
/// `Dispatch::Curried` module that is actually reached as a bare value
/// (`used_as_bare_value` -- a combinator only ever called directly and
/// saturated gets no stage chain, even in a fragment where generic
/// dispatch is on) -- see "Generic closure dispatch" in the module docs
/// for why that decision has to be made fragment-wide, before any call
/// site can choose between the ordinary `call_indirect`/`$tyK` fast path
/// and this mechanism.
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
/// for a literal, `Lowering::pap_env`'s root-env-pointer-first layout for
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
pub(super) fn emit_curried_stages(idx: usize, arity: usize, env_len: usize, base_table_index: usize, w: &mut String) -> Vec<usize> {
    let table_indices: Vec<usize> = (0..arity).map(|i| base_table_index + i).collect();
    for i in 0..arity {
        w.push_str(&format!("  (func $s{idx}_{i} (param $env i32) (param $arg i64) (result i64)\n"));
        // Declared unconditionally (harmless if unused, matching
        // `Lowering::function`'s convention for `$envtmp`) -- only the
        // not-yet-saturated branch below actually needs it.
        w.push_str("    (local $envtmp i32)\n");
        if i + 1 == arity {
            push_line(w, 4, "local.get $env");
            for slot in 0..i {
                push_line(w, 4, "local.get $env");
                push_line(w, 4, &format!("i64.load offset={}", (env_len + slot) * WORD_BYTES));
            }
            push_line(w, 4, "local.get $arg");
            push_line(w, 4, &format!("call $c{idx}"));
        } else {
            push_line(w, 4, &format!("i32.const {}", (env_len + i + 1) * WORD_BYTES));
            push_line(w, 4, "call $alloc");
            push_line(w, 4, "local.set $envtmp");
            for slot in 0..(env_len + i) {
                push_line(w, 4, "local.get $envtmp");
                push_line(w, 4, "local.get $env");
                push_line(w, 4, &format!("i64.load offset={}", slot * WORD_BYTES));
                push_line(w, 4, &format!("i64.store offset={}", slot * WORD_BYTES));
            }
            push_line(w, 4, "local.get $envtmp");
            push_line(w, 4, "local.get $arg");
            push_line(w, 4, &format!("i64.store offset={}", (env_len + i) * WORD_BYTES));
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
    use crate::jit::lower_wat::tests::instantiate;

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

    /// A refused `memory.grow` (here a 2-page cap, standing in for the 4 GiB
    /// edge) is dropped by the allocator, so `alloc` still returns a pointer,
    /// but its block lies past the end of memory: a later access traps
    /// instead of reading a wrong value. (Does not exercise the `i32` wrap
    /// itself, which needs 4 GiB.)
    #[test]
    fn alloc_past_a_refused_grow_hands_out_an_out_of_bounds_block() {
        let mut w = String::new();
        w.push_str("(module\n");
        emit_allocator(&mut w);
        w.push_str("  (export \"alloc\" (func $alloc))\n");
        w.push_str("  (export \"memory\" (memory 0))\n");
        w.push_str(")\n");
        let engine = wasmtime::Engine::default();
        let module = wasmtime::Module::new(&engine, wat::parse_str(&w).unwrap()).unwrap();
        let limits = wasmtime::StoreLimitsBuilder::new().memory_size(2 * PAGE_BYTES).build();
        let mut store = wasmtime::Store::new(&engine, limits);
        store.limiter(|l| l);
        let instance = wasmtime::Instance::new(&mut store, &module, &[]).unwrap();
        let alloc = instance.get_typed_func::<i32, i32>(&mut store, "alloc").unwrap();
        let memory = instance.get_memory(&mut store, "memory").unwrap();

        let ok = alloc.call(&mut store, 100_000).unwrap(); // grows to 2 pages, allowed
        assert!(ok as usize + 100_000 <= memory.data_size(&store));
        let bad = alloc.call(&mut store, 100_000).unwrap(); // needs 4 pages, refused
        assert_eq!(memory.size(&store), 2);
        assert!(bad as usize + 100_000 > memory.data_size(&store), "block must lie out of bounds");
    }

    /// Unpacks a closure value's `(env_ptr, table_idx)` halves the same
    /// way the compiler's own generated code does (see module docs).
    fn unpack(v: i64) -> (i32, i32) {
        ((v >> 32) as i32, (v & 0xFFFF_FFFF) as i32)
    }

    /// `emit_curried_stages` is reachable from `try_compile` now (gated on
    /// `Dispatch::Curried`, see "Generic closure dispatch"), with a
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
    /// discipline the over-application proof tests in `proof/tests/closures.rs` use
    /// for the analogous hazard.
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
}
