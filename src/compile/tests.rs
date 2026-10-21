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
    // the capture staying correctly untouched across the tail loop's own
    // `br $L` (the closure creation/call happens compiling one of the
    // *new* argument values, not the self-call itself) while the
    // closure is called directly, so it is lambda lifted and receives
    // `acc` as a parameter (`lower_wat::direct_only`).
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
    // Like the test above, but the closure escapes -- it is passed to
    // `\g. g n` rather than called directly -- so its environment is
    // allocated every iteration (a directly called one takes its
    // capture as a parameter; see `lower_wat::direct_only`). This one
    // exercises the actual
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
    // `\g. g n`: inside it g = Var(0) and n = Var(2).
    let g = s.var(0);
    let n_in = s.var(2);
    let g_n = s.app(g, n_in);
    let apply_to_n = s.abs(g_n);
    let new_acc = s.app(apply_to_n, closure);
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
    assert!(frag.needs_hp_reset, "this term creates escaping capturing closures, so it should need a reset");
    for (n, acc) in [(0, 0), (5, 3)] {
        let (mut store, instance) = instantiate(&frag.wat);
        let func = instance.get_typed_func::<(i64, i64), i64>(&mut store, "f").unwrap();
        assert_eq!(func.call(&mut store, (n, acc)).unwrap(), apply_term(&s, term, &[n, acc]).unwrap());
    }

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
    // re-deriving this indexing by hand: `build_read`'s (then
    // `compile_var_read`'s) own
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
fn inconsistent_call_arity_for_a_parameter_now_compiles_via_curried_dispatch() {
    // \f. f(1) + f(1, 2) -- `f`, a *parameter*, called with
    // inconsistent arities (1 then 2) at different call sites.
    // Unlike a literal lambda (see
    // `partial_application_of_a_literal_lambda_compiles` below),
    // compile.rs has no fixed arity for a parameter to compare
    // against in the first place -- this used to mean rejection
    // outright; it now means every closure-typed-variable call site
    // in this fragment (not just this one -- see `Combinators`'s own
    // docs for why) goes through the curried, one-argument-at-a-time
    // fallback instead. See
    // `an_inconsistently_called_parameter_of_a_bound_closure_still_agrees_with_the_interpreter`
    // below for the fully closed, runnable version of this same
    // shape.
    let mut s = TermStore::new();
    let f1 = s.var(0);
    let one = s.lit(1);
    let call1 = s.app(f1, one);
    let f2 = s.var(0);
    let two = s.lit(2);
    let call2 = s.app2(f2, one, two);
    let body = s.prim(PrimOp::Add, call1, call2);
    let g = s.abs(body);

    let frag = try_compile(&s, g).expect("an inconsistently-called parameter should now compile");
    assert!(frag.wat.contains("call_indirect (type $ty1)"), "should dispatch through the curried fallback:\n{}", frag.wat);
}

#[test]
fn a_combinator_never_reached_as_a_bare_value_gets_no_stage_chain_even_when_the_fragment_needs_generic_dispatch() {
    // `top = (\f. (if 0<1 then f(1,2) else f(1)) + helper(3,4)) f_lit`,
    // `f_lit = \a b. a+b`, `helper = \x y. x*y` (a *distinct* literal,
    // so it gets its own combinator index, not `f_lit`'s -- confirmed
    // via `Mul` vs `Add` rather than two structurally identical, and
    // therefore hash-consing-deduplicated, bodies). `f`'s own
    // inconsistent call sites make this whole fragment need generic
    // dispatch (same shape as the acceptance test just above), and
    // `f_lit` genuinely needs a stage chain -- it's passed as `top`'s
    // own argument, a bare value. `helper`, though, is *only* ever
    // called directly and saturated (`helper(3,4)`, never passed
    // around, never under-applied) -- it never gets its own index
    // packed into an `i64` anywhere in this fragment, so it should
    // never get a `stage_0` to pack instead. Regression guard for
    // `lower_wat`'s `used_as_bare_value`: reverting the `0..n` filter
    // back to unconditional makes this assertion fail (`helper`'s own
    // `$s{idx}_0`/`$s{idx}_1` show up in the generated WAT even though
    // nothing ever calls through them).
    let mut s = TermStore::new();
    let x = s.var(1);
    let y = s.var(0);
    let xy = s.prim(PrimOp::Mul, x, y);
    let helper_inner = s.abs(xy);
    let helper = s.abs(helper_inner); // \x y. x*y

    let three = s.lit(3);
    let four = s.lit(4);
    let helper_call = s.app2(helper, three, four);

    let f1 = s.var(0);
    let one1 = s.lit(1);
    let two1 = s.lit(2);
    let call_2 = s.app2(f1, one1, two1);
    let f2 = s.var(0);
    let one2 = s.lit(1);
    let call_1 = s.app(f2, one2);
    let zero = s.lit(0);
    let one_c = s.lit(1);
    let cond = s.prim(PrimOp::Lt, zero, one_c);
    let if_expr = s.if_(cond, call_2, call_1);

    let main_body = s.prim(PrimOp::Add, if_expr, helper_call);
    let main = s.abs(main_body);

    let a = s.var(1);
    let b = s.var(0);
    let add = s.prim(PrimOp::Add, a, b);
    let inner = s.abs(add);
    let f_lit = s.abs(inner); // \a b. a+b

    let top = s.app(main, f_lit);

    let frag = try_compile(&s, top).expect("should compile via the curried fallback");
    assert!(frag.wat.contains("call_indirect (type $ty1)"), "f should still dispatch through the curried fallback:\n{}", frag.wat);
    // f_lit's own stage chain must exist (it's genuinely used as a
    // bare value) -- sanity check that the pruning isn't just
    // dropping every stage chain wholesale.
    assert!(frag.wat.contains("(func $s"), "f_lit should still get a stage chain:\n{}", frag.wat);
    // helper is only ever called directly and saturated -- its own
    // combinator index must not have a matching `$s{idx}_` stage
    // chain anywhere in the output. Find helper's own `$c{idx}` block
    // (the one whose body contains `i64.mul`, unlike f_lit's `i64.add`)
    // to learn its index directly, rather than inferring it indirectly.
    let mut helper_idx = None;
    for block in frag.wat.split("  (func $c").skip(1) {
        let idx_str: String = block.chars().take_while(|c| c.is_ascii_digit()).collect();
        let end = block.find("\n  )").unwrap_or(block.len());
        if block[..end].contains("i64.mul") {
            helper_idx = Some(idx_str);
            break;
        }
    }
    let helper_idx = helper_idx.expect("helper's own $c{idx} function should exist in the output");
    assert!(
        !frag.wat.contains(&format!("$s{helper_idx}_")),
        "helper is never used as a bare value and should get no stage chain:\n{}",
        frag.wat
    );

    let (mut store, instance) = instantiate(&frag.wat);
    let func = instance.get_typed_func::<(), i64>(&mut store, "f").unwrap();
    let compiled = func.call(&mut store, ()).unwrap();
    assert_eq!(compiled, apply_term(&s, top, &[]).unwrap());
}

/// A single, fixed real closure value has exactly one true arity, so
/// a term where the *same* call site pair (`f(1)`/`f(1,2)`) is well-
/// typed no matter which one gets called is structurally impossible
/// (confirmed while designing these tests: `f(1)` under-applying a
/// real 2-ary `f` gives a `Clo`, never an `Int`, so summing it with
/// `f(1,2)` the way the acceptance test above does can never itself
/// be well-typed for any single value of `f`). Every runnable test
/// below instead wraps both calls in an `if` whose condition is a
/// *constant* (`0 < 1` or its negation) -- `f` still gets classified
/// `ArityUse::Inconsistent` (the scan walks both branches
/// structurally, unconditionally, regardless of which one a constant
/// condition will actually take at runtime), so the curried fallback
/// still gets exercised in full, but only the one, well-typed branch
/// ever actually *executes* -- exactly the same "only one branch's
/// instructions run" laziness this compiler's `if`/`else` codegen
/// (and the interpreter's own `If` evaluation) already has.
#[test]
fn an_inconsistently_called_parameter_matching_its_own_saturating_arity_agrees_with_the_interpreter() {
    // (\f. if 0<1 then f(1,2) else f(1)) (\a b. a+b) -- f's own real
    // arity (2) matches the *taken* branch's own call exactly.
    let mut s = TermStore::new();
    let a = s.var(1);
    let b = s.var(0);
    let add = s.prim(PrimOp::Add, a, b);
    let inner = s.abs(add); // \b. a+b
    let f_lit = s.abs(inner); // \a b. a+b

    let f1 = s.var(0);
    let one1 = s.lit(1);
    let two1 = s.lit(2);
    let call_2 = s.app2(f1, one1, two1);
    let f2 = s.var(0);
    let one2 = s.lit(1);
    let call_1 = s.app(f2, one2);
    let zero = s.lit(0);
    let one_c = s.lit(1);
    let cond = s.prim(PrimOp::Lt, zero, one_c);
    let inner_body = s.if_(cond, call_2, call_1);
    let f_abs = s.abs(inner_body);
    let top = s.app(f_abs, f_lit);

    let frag = try_compile(&s, top).expect("should compile via the curried fallback");
    assert!(frag.wat.contains("call_indirect (type $ty1)"), "should dispatch through the curried fallback:\n{}", frag.wat);
    let (mut store, instance) = instantiate(&frag.wat);
    let func = instance.get_typed_func::<(), i64>(&mut store, "f").unwrap();
    let compiled = func.call(&mut store, ()).unwrap();
    assert_eq!(compiled, 3);
    assert_eq!(compiled, apply_term(&s, top, &[]).unwrap());
}

#[test]
fn an_inconsistently_called_parameter_matching_its_own_under_applying_arity_agrees_with_the_interpreter() {
    // (\f. if 1<0 then f(1,2) else f(1)) (\a. a+100) -- the *other*
    // shape: f's own real arity (1) matches the taken branch (the
    // `else`, this time -- the condition is always false), and the
    // never-taken `f(1,2)` would over-apply f(1)'s own plain `Int`
    // result, which is never actually evaluated.
    let mut s = TermStore::new();
    let a = s.var(0);
    let hundred = s.lit(100);
    let a_plus_100 = s.prim(PrimOp::Add, a, hundred);
    let f_lit = s.abs(a_plus_100); // \a. a+100

    let f1 = s.var(0);
    let one1 = s.lit(1);
    let two1 = s.lit(2);
    let call_2 = s.app2(f1, one1, two1);
    let f2 = s.var(0);
    let one2 = s.lit(1);
    let call_1 = s.app(f2, one2);
    let one_c = s.lit(1);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Lt, one_c, zero); // always false
    let inner_body = s.if_(cond, call_2, call_1);
    let f_abs = s.abs(inner_body);
    let top = s.app(f_abs, f_lit);

    let frag = try_compile(&s, top).expect("should compile via the curried fallback");
    let (mut store, instance) = instantiate(&frag.wat);
    let func = instance.get_typed_func::<(), i64>(&mut store, "f").unwrap();
    let compiled = func.call(&mut store, ()).unwrap();
    assert_eq!(compiled, 101);
    assert_eq!(compiled, apply_term(&s, top, &[]).unwrap());
}

#[test]
fn a_capturing_closure_reached_through_an_inconsistently_called_parameter_agrees_with_the_interpreter() {
    // \k. (\f. if 0<1 then f(1,2) else f(1)) (\a b. k+a+b) -- f's own
    // captured value (`k`, from the enclosing scope) has to survive
    // being packed as a `stage_0`-addressed value and read back
    // through a curried dispatch step, not just an ordinary one.
    // Checked at two different `k` values so a stale/wrong capture
    // offset would show up as a k-independent (wrong) result, not
    // just a rejection.
    let mut s = TermStore::new();
    let k = s.var(2);
    let a = s.var(1);
    let b = s.var(0);
    let k_plus_a = s.prim(PrimOp::Add, k, a);
    let sum = s.prim(PrimOp::Add, k_plus_a, b);
    let inner = s.abs(sum); // \b. k+a+b
    let f_lit = s.abs(inner); // \a b. k+a+b (captures k)

    let f1 = s.var(0);
    let one1 = s.lit(1);
    let two1 = s.lit(2);
    let call_2 = s.app2(f1, one1, two1);
    let f2 = s.var(0);
    let one2 = s.lit(1);
    let call_1 = s.app(f2, one2);
    let zero = s.lit(0);
    let one_c = s.lit(1);
    let cond = s.prim(PrimOp::Lt, zero, one_c);
    let inner_body = s.if_(cond, call_2, call_1);
    let f_abs = s.abs(inner_body);
    let app = s.app(f_abs, f_lit);
    let top = s.abs(app); // \k. (\f. ..) f_lit

    let frag = try_compile(&s, top).expect("should compile via the curried fallback");
    assert!(frag.wat.contains("call $alloc"), "creating the capturing closure should need the allocator");
    let (mut store, instance) = instantiate(&frag.wat);
    let func = instance.get_typed_func::<i64, i64>(&mut store, "f").unwrap();
    for k_val in [100i64, -7] {
        let compiled = func.call(&mut store, k_val).unwrap();
        assert_eq!(compiled, k_val + 1 + 2, "k={k_val}");
        assert_eq!(compiled, apply_term(&s, top, &[k_val]).unwrap(), "k={k_val}");
    }
}

#[test]
fn a_parameters_own_value_arriving_via_an_if_between_two_literals_still_agrees_once_dispatched_generically() {
    // \pick. (\f. if 0<1 then f(1,2) else f(1)) (if 0<pick then add
    // else sub) -- the sharpest regression guard against silently
    // reverting to a mechanism that only covers a *traced*, single
    // literal root: `f`'s own concrete identity here isn't known
    // until runtime at all, chosen by an ordinary `If` between two
    // *different* literal lambdas, exactly the case a call-site-
    // traced "pre-generate every (root,k) wrapper" mechanism could
    // never have covered (see `RELATED_WORK.md`'s own discussion of
    // why that narrower alternative was rejected).
    let mut s = TermStore::new();
    let a1 = s.var(1);
    let b1 = s.var(0);
    let add_body = s.prim(PrimOp::Add, a1, b1);
    let add_inner = s.abs(add_body);
    let add_lit = s.abs(add_inner); // \a b. a+b

    let a2 = s.var(1);
    let b2 = s.var(0);
    let sub_body = s.prim(PrimOp::Sub, a2, b2);
    let sub_inner = s.abs(sub_body);
    let sub_lit = s.abs(sub_inner); // \a b. a-b

    let pick = s.var(0);
    let zero_p = s.lit(0);
    let pick_cond = s.prim(PrimOp::Lt, zero_p, pick);
    let f_value = s.if_(pick_cond, add_lit, sub_lit);

    let f1 = s.var(0);
    let one1 = s.lit(1);
    let two1 = s.lit(2);
    let call_2 = s.app2(f1, one1, two1);
    let f2 = s.var(0);
    let one2 = s.lit(1);
    let call_1 = s.app(f2, one2);
    let zero_c = s.lit(0);
    let one_c = s.lit(1);
    let cond = s.prim(PrimOp::Lt, zero_c, one_c);
    let inner_body = s.if_(cond, call_2, call_1);
    let f_abs = s.abs(inner_body);
    let app = s.app(f_abs, f_value);
    let top = s.abs(app); // \pick. (\f. ..) (if 0<pick then add else sub)

    let frag = try_compile(&s, top).expect("should compile via the curried fallback");
    let (mut store, instance) = instantiate(&frag.wat);
    let func = instance.get_typed_func::<i64, i64>(&mut store, "f").unwrap();

    let compiled_add = func.call(&mut store, 1).unwrap();
    assert_eq!(compiled_add, 3); // add selected: 1+2
    assert_eq!(compiled_add, apply_term(&s, top, &[1]).unwrap());

    let compiled_sub = func.call(&mut store, -1).unwrap();
    assert_eq!(compiled_sub, -1); // sub selected: 1-2
    assert_eq!(compiled_sub, apply_term(&s, top, &[-1]).unwrap());
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
    // part of `Lowering::pap_env`: the wrapper's own environment needs
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
    // `Lowering::pap_env`'s docs explain the mechanism: it (then
    // `push_pap_env`) used to stash the newly-allocated environment's
    // own address in `$envtmp` across the whole loop building it,
    // relying on that local surviving each supplied argument's own
    // lowering -- but a supplied argument is an arbitrary expression,
    // so that can itself recurse into more `push_closure_env`/
    // `pap_env` emission, which reuses `$envtmp` as scratch too,
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
    // calling a closure-typed variable -- see "Over-application" in
    // `lower_wat.rs`'s module docs on the exact mechanism (evaluating the saturated call
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

/// `classify` is the one place both `build_node` and every
/// `proof.rs` walker learn which case a node is, so its two
/// non-obvious rules are pinned here: a saturated self-call wins over
/// a plain variable call (and only when saturated), and a `Rec` that
/// doesn't peel to a function is no callee at all.
#[test]
fn classify_recognizes_only_a_saturated_self_call_and_only_a_peelable_callee() {
    let mut s = TermStore::new();
    // Inside `rec f a b = ..`: `a` is Var(1), `b` Var(0), `f` Var(2).
    let (a, b, f) = (s.var(1), s.var(0), s.var(2));
    let saturated = s.app2(f, a, b);
    let partial = s.app(f, a);
    let over = s.app(saturated, b);
    let (arity, self_idx) = (2, Some(2));

    assert!(matches!(classify(&s, saturated, arity, self_idx), Shape::SelfCall(ref args) if *args == vec![a, b]));
    assert!(matches!(classify(&s, partial, arity, self_idx), Shape::VarCall { var: 2, ref args, .. } if args.len() == 1));
    assert!(matches!(classify(&s, over, arity, self_idx), Shape::VarCall { var: 2, ref args, .. } if args.len() == 3));
    // Outside a recursive function the same term is just a variable call.
    assert!(matches!(classify(&s, saturated, arity, None), Shape::VarCall { var: 2, .. }));

    let five = s.lit(5);
    let not_a_function = s.rec(five);
    let bad_call = s.app(not_a_function, a);
    assert!(matches!(classify(&s, bad_call, arity, None), Shape::OtherCall));
    let id_body = s.var(0);
    let id = s.abs(id_body);
    let good_call = s.app(id, a);
    assert!(matches!(classify(&s, good_call, arity, None), Shape::CombinatorCall { arity: 1, .. }));
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

#[test]
fn build_produces_the_hand_built_ir_for_each_fixture() {
    use crate::ir::fixtures::{factorial, twice, twice_inc};
    for (s, h, want) in [factorial(), twice(), twice_inc()] {
        assert_eq!(build(&s, h).expect("every fixture builds"), want);
    }
}

fn corpus(name: &str) -> (TermStore, Hash) {
    let (_, s, h) = crate::test_corpus::terms().into_iter().find(|(n, ..)| *n == name).unwrap();
    (s, h)
}

#[test]
fn compile_specialised_compiles_the_checked_specialisation() {
    let (s, h) = corpus("partial_application_loop");
    let c = compile_specialised(&s, h).unwrap();
    assert!(c.specialised.is_some());
    // No closure is left: no table dispatch and no allocator.
    assert!(!c.frag.wat.contains("call_indirect"), "{}", c.frag.wat);
    assert!(!c.frag.wat.contains("$alloc"), "{}", c.frag.wat);
    let (mut store, instance) = instantiate(&c.frag.wat);
    let f = instance.get_typed_func::<(i64, i64), i64>(&mut store, "f").unwrap();
    for (n, acc) in [(0, 0), (1, 0), (5, 3), (100, -7)] {
        assert_eq!(f.call(&mut store, (n, acc)).unwrap(), crate::eval::apply_term(&s, h, &[n, acc]).unwrap(), "n={n} acc={acc}");
    }
}

#[test]
fn a_term_with_nothing_to_specialise_compiles_exactly_as_try_compile_does() {
    let (s, h) = corpus("factorial");
    let c = compile_specialised(&s, h).unwrap();
    assert!(c.specialised.is_none());
    assert_eq!(c.frag.wat, try_compile(&s, h).unwrap().wat);
}

#[test]
fn a_checked_specialisation_that_does_not_compile_falls_back_to_h() {
    // `h` is `f 10 3 100`, `f = \a b. if 0 < a then \c. .. else \c. ..`.
    // Its two βv steps leave `(if 0 < 10 then \c. .. else \c. ..) 100`,
    // an application headed by an `If`, which `build` doesn't cover.
    let (s, h) = corpus("over_application_if_between_closures");
    let sp = crate::specialise::specialise(&s, h);
    assert!(!sp.trace.is_empty());
    assert_eq!(crate::spec_check::check(&s, h, &sp.trace, sp.term), Ok(()));
    assert!(try_compile(&sp.store, sp.term).is_none(), "h' now compiles; this test needs another term");
    let c = compile_specialised(&s, h).expect("h compiles");
    assert!(c.specialised.is_none());
    assert_eq!(c.frag.wat, try_compile(&s, h).unwrap().wat);
}

/// A specialisation whose trace is real but whose claim is not what the
/// trace reaches, so the checker rejects it.
fn a_rejected_candidate() -> (TermStore, Hash, crate::specialise::Specialised) {
    let (s, h) = corpus("partial_application_loop");
    let mut sp = crate::specialise::specialise(&s, h);
    assert!(!sp.trace.is_empty());
    sp.term = sp.store.lit(0); // a real term in the store, but not what the trace reaches
    (s, h, sp)
}

#[test]
#[cfg_attr(not(debug_assertions), ignore = "the panic is debug-only; see the release twin below")]
#[should_panic(expected = "the specialiser produced a trace the checker rejects")]
fn a_trace_the_checker_rejects_panics_in_debug() {
    let (s, h, sp) = a_rejected_candidate();
    compile_candidate(&s, h, sp);
}

#[test]
#[cfg(not(debug_assertions))]
fn a_trace_the_checker_rejects_falls_back_to_h_and_is_counted_in_release() {
    let (s, h, sp) = a_rejected_candidate();
    // The counter is process-wide, so compare before and after.
    let before = builder_bugs(BuilderBug::BadTrace);
    let c = compile_candidate(&s, h, sp).expect("h itself compiles");
    assert_eq!(builder_bugs(BuilderBug::BadTrace), before + 1);
    assert!(c.specialised.is_none());
    assert_eq!(c.frag.wat, try_compile(&s, h).unwrap().wat);
}

/// `\x. t_d`, where `t_0 = x` and `t_{i+1} = t_i + t_i`: `d + 2`
/// distinct nodes, `2^(d+1)` as a tree.
fn doubling(s: &mut TermStore, d: u32) -> Hash {
    let mut t = s.var(0);
    for _ in 0..d {
        t = s.prim(PrimOp::Add, t, t);
    }
    s.abs(t)
}

#[test]
fn a_term_is_compiled_only_up_to_a_tree_size() {
    // Everything downstream walks the tree, and the emitted code is as
    // big as it, so sharing can't shrink the cost (RELATED_WORK.md §47).
    let mut s = TermStore::new();
    let at_the_cap = doubling(&mut s, 13);
    assert_eq!(tree_size(&s, at_the_cap), MAX_TREE_NODES);
    assert!(try_compile(&s, at_the_cap).is_some());
    let over = doubling(&mut s, 14);
    assert!(try_compile(&s, over).is_none());
    // Counted without overflow, far past the cap.
    let huge = doubling(&mut s, 200);
    assert_eq!(tree_size(&s, huge), MAX_TREE_NODES + 1);
}

#[test]
fn an_oversized_source_compiles_without_consulting_the_checker() {
    // Before the specialiser's early size test, this got a one-step
    // trace the checker rejects, a debug panic here.
    let mut s = TermStore::new();
    let h = crate::test_corpus::oversized_source_with_a_shrinking_step(&mut s);
    if let Some(c) = compile_specialised(&s, h) {
        assert!(c.specialised.is_none());
    }
}
