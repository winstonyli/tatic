//! Term builders shared by the benchmarks -- the same terms `main.rs` uses
//! for its demo, kept in one place so `execution.rs` and `proofs.rs` don't
//! each carry their own copy.
//!
//! Included into both bench binaries via `#[path]`; each one only uses a
//! subset, hence the blanket `dead_code` allow rather than one per binary.
#![allow(dead_code)]

use tatic::term::{Hash, PrimOp, TermStore};

/// `rec f n = if n <= 1 then 1 else n * f(n - 1)`
pub fn factorial(s: &mut TermStore) -> Hash {
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

/// `rec f n = if n < 2 then n else f(n - 1) + f(n - 2)` (naive, exponential;
/// not tail-recursive, so `compile.rs` emits a plain `call`, not a loop).
pub fn fib(s: &mut TermStore) -> Hash {
    let n = s.var(0);
    let f = s.var(1);
    let two = s.lit(2);
    let cond = s.prim(PrimOp::Lt, n, two);
    let one = s.lit(1);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one);
    let n_minus_2 = s.prim(PrimOp::Sub, n, two);
    let call1 = s.app(f, n_minus_1);
    let call2 = s.app(f, n_minus_2);
    let else_branch = s.prim(PrimOp::Add, call1, call2);
    let body = s.if_(cond, n, else_branch);
    let abs = s.abs(body);
    s.rec(abs)
}

/// `rec f a b = if b == 0 then a else f(b, a mod b)` (tail-recursive, 2-ary
/// -- `compile.rs` turns the self-call into a `loop`/`br`).
pub fn gcd(s: &mut TermStore) -> Hash {
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

/// `rec f a b = if a == 0 then b else if b == 0 then a else f(b, a mod b)`
/// -- deeper than `gcd` above: two base leaves and one tail leaf reached
/// via a depth-2 path, exercising `prove_tail_recursive_universal`'s
/// per-leaf `Ev` construction instead of the single-base/single-tail
/// special case.
pub fn gcd_with_two_base_cases(s: &mut TermStore) -> Hash {
    let b = s.var(0);
    let a = s.var(1);
    let f = s.var(2);
    let zero = s.lit(0);
    let cond_a = s.prim(PrimOp::Eq, a, zero);
    let cond_b = s.prim(PrimOp::Eq, b, zero);
    let a_mod_b = s.prim(PrimOp::Mod, a, b);
    let rec_call = s.app2(f, b, a_mod_b);
    let inner_if = s.if_(cond_b, a, rec_call);
    let body = s.if_(cond_a, b, inner_if);
    let inner = s.abs(body);
    let abs = s.abs(inner);
    s.rec(abs)
}

/// `rec f n acc = if n <= 0 then acc else f (n - 1) ((\y. acc + y) n)` --
/// tail-recursive, but each iteration creates *and immediately calls* a
/// fresh capturing closure (`\y. acc + y`, capturing `acc`, `f`'s own
/// second parameter, which changes every iteration) as a literal callee
/// -- a direct-call site (`push_closure_env` then `call`, no
/// `call_indirect`), so this isolates the cost of `compile.rs`'s new
/// closure-conversion path -- one bump-allocator call per iteration --
/// from `call_indirect`'s own unpacking overhead.
pub fn capturing_closure_loop(s: &mut TermStore) -> Hash {
    // `\y. acc + y`, referenced at body's own top level (f=Var(2),
    // n=Var(1), acc=Var(0)) -- inside the closure's own body, one more
    // binder (y) has been passed, so acc is Var(1), y is Var(0).
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
    s.rec(abs)
}

/// `rec f n acc = if n <= 0 then acc else f (n - 1) (caller (add acc) n)`
/// where `add = \x y. x + y` and `caller = \g z. g z` -- tail-recursive,
/// and each iteration partially applies `add` to `acc` (one argument
/// short), then completes that partial application through `caller`
/// (avoiding the curried-application ambiguity the same way
/// `capturing_closure_loop` avoids it for a plain capturing closure). The
/// wrapper combinator `register_partial_app` synthesizes for `(add, 1)`
/// compiles once and is shared across every iteration -- only its
/// environment (holding `add`'s own, empty, environment plus the current
/// `acc`) gets allocated fresh each time, via `push_pap_env` -- so this
/// isolates the partial-application path's own per-iteration allocation
/// cost, the same way `capturing_closure_loop` isolates a plain
/// capturing closure's.
pub fn partial_application_loop(s: &mut TermStore) -> Hash {
    // add = \x y. x + y
    let x = s.var(1);
    let y = s.var(0);
    let add_body = s.prim(PrimOp::Add, x, y);
    let add_inner = s.abs(add_body);
    let add = s.abs(add_inner);

    // caller = \g z. g z
    let g = s.var(1);
    let z = s.var(0);
    let call_gz = s.app(g, z);
    let caller_inner = s.abs(call_gz);
    let caller = s.abs(caller_inner);

    let n = s.var(1);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Le, n, zero);
    let base = s.var(0);
    let n2 = s.var(1);
    let one = s.lit(1);
    let n_minus_1 = s.prim(PrimOp::Sub, n2, one);
    let f = s.var(2);

    let acc2 = s.var(0);
    let partial = s.app(add, acc2); // add(acc) -- under-applied by one arg
    let n3 = s.var(1);
    let new_acc = s.app2(caller, partial, n3); // caller(partial, n) = add(acc, n)

    let rec_call = s.app2(f, n_minus_1, new_acc);
    let body = s.if_(cond, base, rec_call);
    let inner = s.abs(body);
    let abs = s.abs(inner);
    s.rec(abs)
}

/// `rec f n g x = if n <= 0 then x else f(n-1, g, g x)`, with `inc = \y. y+1`
/// baked in as the initial `g` and `n`/`x` baked in too, so the whole term
/// is closed (arity 0) -- a closure-typed *parameter* threaded through
/// every iteration and called (`call_indirect`) each time, unlike
/// `capturing_closure_loop`'s own shape above, which creates a fresh
/// closure every iteration instead of reusing one passed in. Same depth as
/// the other two loop benchmarks (see `execution.rs`'s own comment on
/// `capturing_closure_loop` for why 20,000 rather than some other number).
pub fn closure_typed_loop_carried_parameter_loop(s: &mut TermStore) -> Hash {
    let x = s.var(0);
    let g = s.var(1);
    let n = s.var(2);
    let f = s.var(3);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Le, n, zero);
    let one = s.lit(1);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one);
    let gx = s.app(g, x);
    let f_n1_g = s.app2(f, n_minus_1, g);
    let rec_call = s.app(f_n1_g, gx);
    let body = s.if_(cond, x, rec_call);
    let g_binder = s.abs(body);
    let n_binder = s.abs(g_binder);
    let abs = s.abs(n_binder);
    let it = s.rec(abs);

    let y = s.var(0);
    let one2 = s.lit(1);
    let inc_body = s.prim(PrimOp::Add, y, one2);
    let inc = s.abs(inc_body);

    let n_lit = s.lit(20_000);
    let x0 = s.lit(0);
    let partial = s.app2(it, n_lit, inc);
    s.app(partial, x0)
}

/// Identical to `closure_typed_loop_carried_parameter_loop` above --
/// same loop, same 20,000 iterations, same hot `g(x)` call each one --
/// with exactly one addition: a dead (never-reached, `1<0` is always
/// false) extra call site for `g` at arity 2, `rec f n g x = if 1<0
/// then g(x,999) else (if n<=0 then x else f(n-1,g,g(x)))`. That's
/// enough to make `g` `ArityUse::Inconsistent`, which -- per compile.rs's
/// own docs on `Combinators::needs_generic_dispatch` -- switches the
/// *whole* fragment to curried dispatch, including the hot, live
/// `g(x)` call the dead branch has nothing to do with. This isolates
/// exactly the cost `RELATED_WORK.md`'s own design discussion flagged
/// but never measured: what a single, syntactically-present-but-never-
/// taken inconsistent call site costs an otherwise fast-path loop.
pub fn inconsistent_arity_loop_carried_parameter_loop(s: &mut TermStore) -> Hash {
    let x_dead = s.var(0);
    let nine_ninety_nine = s.lit(999);
    let g_dead = s.var(1);
    let dead_call = s.app2(g_dead, x_dead, nine_ninety_nine);

    let x = s.var(0);
    let g = s.var(1);
    let n = s.var(2);
    let f = s.var(3);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Le, n, zero);
    let one = s.lit(1);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one);
    let gx = s.app(g, x);
    let f_n1_g = s.app2(f, n_minus_1, g);
    let rec_call = s.app(f_n1_g, gx);
    let live_body = s.if_(cond, x, rec_call);

    let one_c = s.lit(1);
    let zero_c = s.lit(0);
    let dead_cond = s.prim(PrimOp::Lt, one_c, zero_c); // always false
    let body = s.if_(dead_cond, dead_call, live_body);

    let g_binder = s.abs(body);
    let n_binder = s.abs(g_binder);
    let abs = s.abs(n_binder);
    let it = s.rec(abs);

    let y = s.var(0);
    let one2 = s.lit(1);
    let inc_body = s.prim(PrimOp::Add, y, one2);
    let inc = s.abs(inc_body);

    let n_lit = s.lit(20_000);
    let x0 = s.lit(0);
    let partial = s.app2(it, n_lit, inc);
    s.app(partial, x0)
}

/// `\a b. if a < b then a * 2 else b + 1` -- straight-line, no recursion.
pub fn straight_line(s: &mut TermStore) -> Hash {
    let a = s.var(1);
    let b = s.var(0);
    let cond = s.prim(PrimOp::Lt, a, b);
    let two = s.lit(2);
    let then_branch = s.prim(PrimOp::Mul, a, two);
    let one = s.lit(1);
    let else_branch = s.prim(PrimOp::Add, b, one);
    let body = s.if_(cond, then_branch, else_branch);
    let inner = s.abs(body);
    s.abs(inner)
}

/// `(twice inc) 5` -- non-capturing closures, no recursion (arity 0). The
/// higher-order demo term `main.rs` itself uses, and the baseline the
/// other closures-fragment shapes below are measured against.
pub fn twice_inc_5(s: &mut TermStore) -> Hash {
    let f = s.var(1);
    let x = s.var(0);
    let fx = s.app(f, x);
    let ffx = s.app(f, fx);
    let inner = s.abs(ffx);
    let twice = s.abs(inner);

    let y = s.var(0);
    let one = s.lit(1);
    let y_plus_1 = s.prim(PrimOp::Add, y, one);
    let inc = s.abs(y_plus_1);

    let five = s.lit(5);
    s.app2(twice, inc, five)
}

/// `\x. (\y. x + y)(5)` -- a capturing closure, created and directly
/// called (`mk_clo_h`/`Env_n`/`build_env_expr`), unlike `twice_inc_5`'s
/// non-capturing one (`combinator_value`).
pub fn a_capturing_closure_call(s: &mut TermStore) -> Hash {
    let y = s.var(0);
    let x_captured = s.var(1);
    let sum = s.prim(PrimOp::Add, x_captured, y);
    let closure = s.abs(sum);
    let five = s.lit(5);
    let called = s.app(closure, five);
    s.abs(called)
}

/// `add = \x y. x + y; partial = add(3); caller = \g. g(4); caller(partial)`
/// -- partial application of a non-capturing literal lambda (`pap_ref`'s
/// simplest case).
pub fn a_pap_non_capturing(s: &mut TermStore) -> Hash {
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

    s.app(caller, partial)
}

/// `\z. (\g2. g2(4)) ((\x y. x + y + z)(3))` -- partial application of a
/// *capturing* literal lambda, exercising `pap_ref`'s leading-`Env_n`
/// path on top of the plain PAP case above.
pub fn a_pap_capturing(s: &mut TermStore) -> Hash {
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
    s.abs(called)
}

/// `rec f n g x = if n <= 0 then x else f(n-1, g, g x)` -- bare, not
/// wrapped with an initial closure baked in (unlike
/// `closure_typed_loop_carried_parameter_loop` above, which is built for
/// *execution*): `prove_tail_recursive_universal`'s own proof-construction
/// cost depends only on the self-recursive function's own leaf/call
/// structure, never on a concrete argument value, so there's no need to
/// supply one here at all.
pub fn iterate(s: &mut TermStore) -> Hash {
    let x = s.var(0);
    let g = s.var(1);
    let n = s.var(2);
    let f = s.var(3);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Le, n, zero);
    let one = s.lit(1);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one);
    let gx = s.app(g, x);
    let f_n1_g = s.app2(f, n_minus_1, g);
    let rec_call = s.app(f_n1_g, gx);
    let body = s.if_(cond, x, rec_call);
    let g_binder = s.abs(body);
    let n_binder = s.abs(g_binder);
    let abs = s.abs(n_binder);
    s.rec(abs)
}

/// `rec f n g x = if n<=0 then x else 1 + f(n-1,g,g(x))`, `n` baked to `20`
/// -- the same shape as `proof.rs`'s own
/// `a_non_tail_self_call_carrying_an_inconsistently_classified_closure_parameter_gets_a_per_instance_proof`
/// test, fully saturated (arity 0 remaining) so `prove_closure_expr_instance`
/// can be called with `&[]` directly. `n=20` sits well under
/// `DynBudget::recursion_depth`'s own bound (`50`, see `proof.rs`), giving
/// this its own real, if modest, non-tail recursion depth without risking
/// a decline.
pub fn non_tail_closure_carrying_recursion(s: &mut TermStore) -> Hash {
    let x = s.var(0);
    let g = s.var(1);
    let n = s.var(2);
    let f = s.var(3);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Le, n, zero);
    let one = s.lit(1);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one);
    let gx = s.app(g, x);
    let f_n1_g = s.app2(f, n_minus_1, g);
    let rec_call = s.app(f_n1_g, gx); // f(n-1, g, g(x))
    let one_addend = s.lit(1);
    let non_tail_call = s.prim(PrimOp::Add, one_addend, rec_call); // 1 + f(n-1,g,g(x))
    let body = s.if_(cond, x, non_tail_call);
    let g_binder = s.abs(body);
    let n_binder = s.abs(g_binder);
    let abs = s.abs(n_binder);
    let it = s.rec(abs);

    let y = s.var(0);
    let one2 = s.lit(1);
    let inc_body = s.prim(PrimOp::Add, y, one2);
    let inc = s.abs(inc_body);

    let n_lit = s.lit(20);
    let x0 = s.lit(0);
    let partial = s.app2(it, n_lit, inc);
    s.app(partial, x0)
}

/// `rec f n g = if n<=1 then g(n) else f(n-1,g) + f(n-2,g)`, `n` baked to
/// `6` -- the same shape as `proof.rs`'s own
/// `branching_non_tail_self_calls_carrying_an_inconsistently_classified_closure_parameter_get_a_per_instance_proof`
/// test: a genuinely *branching* non-tail trace (naive-Fibonacci-style,
/// two self-calls per interior leaf). Unlike the single-embedded-call
/// shape above, `DynBudget::recursion_depth` here bounds the *total*
/// number of self-calls across the whole trace (the budget never refunds
/// on return), which grows with the size of the recursion tree, not its
/// depth -- `n=6` keeps that total (`2 * fib(n+1) - 1 = 25`) safely under
/// the shared bound of `50`.
pub fn branching_non_tail_closure_carrying_recursion(s: &mut TermStore) -> Hash {
    let g_base = s.var(0);
    let n_base = s.var(1);
    let base_call = s.app(g_base, n_base); // g(n)

    let g1 = s.var(0);
    let n1 = s.var(1);
    let f1 = s.var(2);
    let one1 = s.lit(1);
    let n_minus_1 = s.prim(PrimOp::Sub, n1, one1);
    let call_n1 = s.app2(f1, n_minus_1, g1); // f(n-1, g)

    let g2 = s.var(0);
    let n2 = s.var(1);
    let f2 = s.var(2);
    let two2 = s.lit(2);
    let n_minus_2 = s.prim(PrimOp::Sub, n2, two2);
    let call_n2 = s.app2(f2, n_minus_2, g2); // f(n-2, g)

    let branch_sum = s.prim(PrimOp::Add, call_n1, call_n2);

    let n_cond = s.var(1);
    let one_c2 = s.lit(1);
    let cond = s.prim(PrimOp::Le, n_cond, one_c2); // n <= 1
    let body = s.if_(cond, base_call, branch_sum);

    let g_binder = s.abs(body); // innermost -- binds g (Var(0))
    let n_binder = s.abs(g_binder); // outermost -- binds n (Var(1))
    let it = s.rec(n_binder);

    let y = s.var(0);
    let one2 = s.lit(1);
    let inc_body = s.prim(PrimOp::Add, y, one2);
    let inc = s.abs(inc_body);

    let n_lit = s.lit(6);
    s.app2(it, n_lit, inc)
}
