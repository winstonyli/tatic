use super::*;

#[test]
fn tail_recursive_call_gets_a_per_execution_proof() {
    let mut s = TermStore::new();
    let g = gcd(&mut s);

    for (a, b) in [(48, 18), (270, 192), (17, 5), (0, 7)] {
        let proof = prove_closure_expr_instance(&s, g, &[a, b])
            .unwrap_or_else(|| panic!("gcd({a},{b}) should get a per-execution proof"));
        assert_eq!(proof.arity, 2);
        kernel::check_in(
            &proof.globals,
            &Ctx::new(),
            &proof.proof,
            &kernel::id(proof.result_ty, proof.denotation, proof.denotation),
        )
        .expect("the recorded proof should independently re-typecheck");
    }
}

#[test]
fn a_closure_created_and_called_inside_a_self_call_argument_gets_a_universal_proof() {
    let mut s = TermStore::new();
    let h = capturing_closure_loop(&mut s);

    let proof = prove_tail_recursive_universal(&s, h)
        .expect("a self-recursive loop creating a fresh capturing closure each iteration should get a universal proof");
    assert_eq!(proof.arity, 2);
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.theorem_proof, &proof.theorem_ty)
        .expect("the recorded theorem should independently re-typecheck");

    // The per-execution proof (`kernel_verified` never depended on it, see `jit.rs`'s own docs)
    // covers this shape too: a self-call argument that creates and calls a *capturing* literal
    // lambda (`root`'s own single capture, `acc`) whose body is a single `Prim` node.
    assert_eq!(eval::apply_term(&s, h, &[5, 0]).unwrap(), 15, "interpreter sanity check: 5+4+3+2+1");
    let instance = prove_closure_expr_instance(&s, h, &[5, 0])
        .expect("a self-call argument creating and calling a capturing closure should get a concrete instance");
    check_instance_proof(&instance);

    assert!(compile::try_compile(&s, h).is_some());
}

#[test]
fn a_self_call_inside_a_nested_if_branch_gets_a_universal_proof_and_a_correct_instance() {
    // The recursive leaf's own `If` isn't the whole branch body
    // either (it's the right-hand operand of the outer `+`), and this
    // time each of its two branches contains its own self-call
    // occurrence: `find_self_calls` must find both (in the same
    // left-to-right order placeholder-mode `denote_closure` substitutes them
    // in), each becoming its own placeholder of the leaf's `combine`
    // function.
    let mut s = TermStore::new();
    let g = source(
        &mut s,
        "rec f n = if n <= 0 then 0 else n + (if n % 2 == 0 then f (n - 1) else f (n - 1) + 1)",
    );

    let proof = prove_tail_recursive_universal(&s, g).expect("a nested If with a self-call in each branch should still get a universal proof");
    assert_eq!(proof.arity, 1);
    kernel::check_in(&proof.globals, &Ctx::new(), &proof.theorem_proof, &proof.theorem_ty)
        .expect("the recorded theorem should independently re-typecheck");

    // f(0)=0, f(1)=1+(f(0)+1)=2, f(2)=2+f(1)=4, f(3)=3+(f(2)+1)=8,
    // f(4)=4+f(3)=12, f(5)=5+(f(4)+1)=18.
    assert_eq!(eval::apply_term(&s, g, &[5]).unwrap(), 18, "interpreter sanity check");

    let instance = prove_closure_expr_instance(&s, g, &[5]).expect("f(5) should get an instance");
    check_instance_proof(&instance);
}

/// A long-running tail recursion used to take the *process* down.
///
/// `prove_closure_expr_instance` accumulates an expression that deepens
/// a couple of levels per trace step, and both the kernel's recursive
/// traversals and the recursive `Drop` of the resulting `Expr`
/// chain have finite stack. With the old 10,000-step budget a loop
/// like this built a ~40,000-level expression and died with
/// `STATUS_STACK_OVERFLOW` -- not a failed proof, a crashed process,
/// reachable from `jit::JitEngine::apply`. See `docs/related-work/` §30.
///
/// Declining is the correct outcome here; surviving to decline is the
/// point of the test.
#[test]
fn a_long_running_trace_declines_instead_of_overflowing_the_stack() {
    // 20,000 iterations -- far past any budget, which is exactly the
    // case that used to crash rather than return.
    let mut s = TermStore::new();
    let h = source(&mut s, "rec f n x = if n <= 0 then x else f (n - 1) (x + 1)");

    assert_eq!(eval::apply_term(&s, h, &[20_000, 0]).unwrap(), 20_000);
    assert!(prove_closure_expr_instance(&s, h, &[20_000, 0]).is_none());

    // And a trace short enough to stay under every ceiling still
    // proves, so the bound above isn't simply switching the strategy
    // off.
    assert!(prove_closure_expr_instance(&s, h, &[10, 0]).is_some());
}

#[test]
fn an_instance_whose_branch_divides_by_zero_gets_no_proof() {
    // `eval` fails with DivByZero and the Wasm traps, so no branch is taken.
    // The instance prover once picked one by its own `x / 0 = 0` (cleanup plan CU1),
    // in a plain `If` and in a tail-recursive loop's condition alike.
    for (src, args) in [(r"if 7 / 0 then 1 else 2", &[][..]), (r"rec go n = if 10 / n then go (n - 1) else 0", &[3][..])] {
        let mut s = TermStore::new();
        let h = crate::lang::syntax::parse(&mut s, src).unwrap();
        assert_eq!(eval::apply_term(&s, h, args), Err(eval::EvalError::DivByZero), "{src}");
        assert!(prove_closure_expr_instance(&s, h, args).is_none(), "{src}");
    }
}

#[test]
fn non_tail_recursion_gets_a_per_instance_proof() {
    let mut s = TermStore::new();
    let fact = factorial(&mut s);
    for n in [0, 1, 5, 10] {
        let proof = prove_closure_expr_instance(&s, fact, &[n]).unwrap_or_else(|| panic!("factorial({n}) should get a per-instance proof"));
        assert_eq!(proof.arity, 1);
        check_instance_proof(&proof);
    }
}

#[test]
fn fibonacci_branching_leaves_get_per_instance_proofs() {
    let mut s = TermStore::new();
    let fib = fib(&mut s);
    // The proof follows the whole call tree, so it grows with it (171 nodes at fib(8), 446 at fib(10)) and the step
    // budget declines from fib(11); the deleted memoized witness stayed linear and reached fib(16).
    for n in [1, 2, 8, 10] {
        let proof = prove_closure_expr_instance(&s, fib, &[n]).unwrap_or_else(|| panic!("fib({n}) should get a per-instance proof"));
        assert_eq!(proof.arity, 1);
        check_instance_proof(&proof);
    }
}

#[test]
fn one_functions_instance_proof_is_rejected_against_anothers_type() {
    // Same adversarial shape as one_functions_theorem_proof_is_rejected_against_anothers_type,
    // one level down: a per-instance proof built for one call must not typecheck against another's
    // (different function, different denotation).
    let mut s = TermStore::new();
    let g = gcd(&mut s);
    let gcd_proof = prove_closure_expr_instance(&s, g, &[48, 18]).expect("gcd instance proof");
    let fact = factorial(&mut s);
    let fact_proof = prove_closure_expr_instance(&s, fact, &[5]).expect("factorial instance proof");

    assert!(
        kernel::check_in(
            &gcd_proof.globals,
            &Ctx::new(),
            &gcd_proof.proof,
            &kernel::id(fact_proof.result_ty, fact_proof.denotation, fact_proof.denotation),
        )
        .is_err(),
        "gcd's instance proof should be rejected against factorial's instance type"
    );
}

#[test]
fn prove_closure_expr_declines_where_the_instance_proof_picks_up() {
    // Same shape as compile.rs's
    // `an_inconsistently_called_parameter_matching_its_own_saturating_arity_agrees_with_the_interpreter`
    // -- documents exactly why the new strategy is needed: the
    // universal, structural proof still declines this shape (`f`'s
    // own inconsistent arity has no honest static type), even though
    // it's now perfectly provable per-instance.
    let mut s = TermStore::new();
    let top = inconsistent_arity_saturating_instance(&mut s);

    assert!(prove_closure_expr(&s, top).is_none());
    let proof = prove_closure_expr_instance(&s, top, &[]).expect("should be provable per-instance");
    assert_eq!(proof.arity, 0);
    check_instance_proof(&proof);
}

#[test]
fn an_under_applying_instance_gets_a_per_instance_proof_too() {
    // compile.rs's
    // `an_inconsistently_called_parameter_matching_its_own_under_applying_arity_agrees_with_the_interpreter`.
    let mut s = TermStore::new();
    let top = inconsistent_arity_under_applying_instance(&mut s);

    assert!(prove_closure_expr(&s, top).is_none());
    let proof = prove_closure_expr_instance(&s, top, &[]).expect("should be provable per-instance");
    check_instance_proof(&proof);
}

#[test]
fn a_captured_value_reached_through_an_inlined_call_gets_a_per_instance_proof() {
    // compile.rs's
    // `a_capturing_closure_reached_through_an_inconsistently_called_parameter_agrees_with_the_interpreter`
    // -- exercises the two-frame fix directly: `\a b. k + a + b`'s own
    // capture of `k` must resolve against `top`'s own (outer) frame, not
    // whatever frame is active once `\f. ...`'s body is inlined.
    let mut s = TermStore::new();
    let top = inconsistent_arity_capturing_instance(&mut s);

    assert!(prove_closure_expr(&s, top).is_none());
    for k_val in [100i64, -7] {
        let proof = prove_closure_expr_instance(&s, top, &[k_val]).unwrap_or_else(|| panic!("k={k_val} should be provable per-instance"));
        check_instance_proof(&proof);
    }
}

#[test]
fn a_runtime_chosen_literal_gets_a_per_instance_proof() {
    // compile.rs's
    // `a_parameters_own_value_arriving_via_an_if_between_two_literals_still_agrees_once_dispatched_generically`
    // -- the sharpest case: `f`'s own concrete identity isn't known
    // until `eval_dyn` concretely resolves the `If` choosing between
    // `\a b. a + b` and `\a b. a - b`, *before* `\f. ...`'s own body is
    // even reached.
    let mut s = TermStore::new();
    let top = inconsistent_arity_runtime_chosen_instance(&mut s);

    assert!(prove_closure_expr(&s, top).is_none());
    for pick_val in [1i64, -1] {
        let proof = prove_closure_expr_instance(&s, top, &[pick_val]).unwrap_or_else(|| panic!("pick={pick_val} should be provable per-instance"));
        check_instance_proof(&proof);
    }
}

#[test]
fn a_tail_recursive_loop_carrying_an_inconsistently_classified_closure_parameter_gets_a_per_instance_proof() {
    // Same shape as jit::tests::
    // a_tail_recursive_loop_compiles_and_is_kernel_verified_once_its_own_closure_parameter_turns_inconsistent
    // (and samples::inconsistent_arity_loop_carried_parameter_loop),
    // `g` baked in as `inc`. The dead `g x 999` call site
    // makes `param_types_for(it)` classify `g` as `Inconsistent` (->
    // `None`, same as an absent one) even though every call actually
    // taken passes it exactly one argument -- exactly the gap
    // `eval_dyn_direct_call` used to decline outright for a
    // `Rec`-wrapped root (`root_is_rec` check), and that
    // `eval_dyn_tail_recursive` now closes by following the loop's
    // own tail self-calls concretely instead of trying (and failing)
    // to classify `g` statically.
    let mut s = TermStore::new();
    let it = inconsistent_arity_iterate(&mut s);

    assert!(param_types_for(&s, it).unwrap().contains(&None));
    assert!(prove_closure_expr(&s, it).is_none(), "it itself has no fixed arity to prove universally over g's own slot");

    for n_val in [0i64, 1, 10] {
        let top = inconsistent_arity_loop_carried_parameter_loop(&mut s, n_val);
        assert!(prove_closure_expr(&s, top).is_none(), "n={n_val}: top's own call to it still can't be classified statically");
        let proof = prove_closure_expr_instance(&s, top, &[]).unwrap_or_else(|| panic!("n={n_val} should be provable per-instance"));
        check_instance_proof(&proof);
        assert_eq!(eval::apply_term(&s, top, &[]).unwrap(), n_val, "n={n_val}: sanity check against the interpreter");
    }
}

#[test]
fn a_loop_carried_call_result_that_itself_gates_termination_gets_a_per_instance_proof() {
    // `g` baked in as `\y. y - 1` -- unlike the test
    // just above (where the loop-carried call's own result, `g(x)`,
    // never itself influences which branch a later iteration takes,
    // only `n` does), here `g(x)`'s own concrete value is exactly
    // what the next iteration's own `x<=0` branches on. This is the
    // sharper regression guard `eval_dyn_tail_recursive`'s own
    // `eval_concrete_dyn` call needs: deliberately corrupting
    // `dyn_frame_to_env`'s own reversal (dropping its `.rev()`) is
    // *not* caught by the test above at all (nothing there ever reads
    // `x`'s own concrete numeral back), but *is* caught here, via the
    // sanity check against the interpreter below -- confirmed by
    // hand before trusting this test to mean anything.
    let mut s = TermStore::new();
    let it_src = r"rec f g x = if 1 < 0 then g x 999 else if x <= 0 then x else f g (g x)";
    let it = source(&mut s, it_src);

    assert!(param_types_for(&s, it).unwrap().contains(&None));

    for x_val in [0i64, 1, 5] {
        let top = source(&mut s, &format!(r"({it_src}) (\y. y - 1) ({x_val})"));

        let proof = prove_closure_expr_instance(&s, top, &[]).unwrap_or_else(|| panic!("x={x_val} should be provable per-instance"));
        check_instance_proof(&proof);
        assert_eq!(eval::apply_term(&s, top, &[]).unwrap(), 0, "x={x_val}: sanity check against the interpreter");
    }
}

#[test]
fn a_closure_argument_arriving_via_a_separate_saturated_call_that_itself_returns_a_clo_gets_a_per_instance_proof() {
    // `pick` (arity 1, its own saturated call returns a further Clo_2 -- `combinator_return_type`
    // recognizes an `If` between two same-arity literal lambdas, same
    // as `denote_closure`'s own `ite_clo` case does structurally);
    // `f` (arity 1, `k` called at
    // two different arities -- `Inconsistent`, same trick as every
    // other per-instance test); `top = f(pick(3))`. `pick(3)`'s own
    // result never arrives as a bare literal lambda value the way
    // every other per-instance test's closure argument does -- it's
    // the result of a *separate* saturated call, so `eval_dyn_direct_call`
    // must inline *that* call too (previously declined outright via
    // its own `return_ty.is_some()` check) before `f`'s own
    // needs-inline logic even gets a `Clo` to work with at all.
    let mut s = TermStore::new();
    let pick_src = r"\s. if 0 < s then (\a b. a + b) else (\a b. a - b)";
    let pick = source(&mut s, pick_src);

    let f_src = r"\k. if 0 < 1 then k 1 2 else k 1";
    let f = source(&mut s, f_src);

    assert!(param_types_for(&s, f).unwrap().contains(&None) && combinator_return_type(&s, pick).unwrap() == Some(2));

    for s_val in [3i64, -3] {
        let top = source(&mut s, &format!(r"({f_src}) (({pick_src}) ({s_val}))"));

        assert!(prove_closure_expr(&s, top).is_none(), "s={s_val}: f's own inconsistent k still can't be classified statically");
        let proof = prove_closure_expr_instance(&s, top, &[]).unwrap_or_else(|| panic!("s={s_val} should be provable per-instance"));
        check_instance_proof(&proof);
        let expected = if s_val > 0 { 1 + 2 } else { 1 - 2 };
        assert_eq!(eval::apply_term(&s, top, &[]).unwrap(), expected, "s={s_val}: sanity check against the interpreter");
    }
}

#[test]
fn a_non_tail_self_call_carrying_an_inconsistently_classified_closure_parameter_gets_a_per_instance_proof() {
    // Same dead-call-site trick as the tail-recursive precedent
    // (`a_tail_recursive_loop_carrying_an_inconsistently_classified_closure_parameter_gets_a_per_instance_proof`
    // above), but the self-call now sits *inside* `1 + ..`, not in
    // tail position. `classify_step`'s own
    // `match_self_call` only recognizes a self-call that's the
    // *entire* remaining leaf, so this leaf -- `1 + f(...)` -- is a
    // `Base` case as far as `eval_dyn_tail_recursive`'s own loop is
    // concerned; the embedded self-call inside it is only reachable
    // via `eval_dyn`'s own new recognition, calling back into
    // `eval_dyn_tail_recursive` one Rust stack frame at a time.
    let mut s = TermStore::new();
    let it_src = r"rec f n g x = if 1 < 0 then g x 999 else if n <= 0 then x else 1 + f (n - 1) g (g x)";
    let it = source(&mut s, it_src);

    assert!(param_types_for(&s, it).unwrap().contains(&None));

    for n_val in [0i64, 1, 3, 10, 100] {
        let top = source(&mut s, &format!(r"({it_src}) ({n_val}) (\y. y + 1) 0"));

        assert!(prove_closure_expr(&s, top).is_none(), "n={n_val}: top's own call to it still can't be classified statically");
        let proof = prove_closure_expr_instance(&s, top, &[]).unwrap_or_else(|| panic!("n={n_val} should be provable per-instance"));
        check_instance_proof(&proof);
        // x reaches n_val (one increment per level) by the time the
        // base case returns it, and "1 +" is added back once per
        // level on the way out -- n_val of each.
        assert_eq!(eval::apply_term(&s, top, &[]).unwrap(), 2 * n_val, "n={n_val}: sanity check against the interpreter");
    }

    // Past `DynBudget::steps`, this must
    // decline *cleanly* (a graceful `None`, the same "sound, not
    // complete" tolerance every other bounded search in this module
    // already has) rather than actually overflowing the native Rust
    // stack that many real embedded self-calls would otherwise
    // recurse through -- confirms the bound is a genuine safety net,
    // not just delaying a crash to a slightly deeper input.
    let top = source(&mut s, &format!(r"({it_src}) (1000000) (\y. y + 1) 0"));
    assert!(
        prove_closure_expr_instance(&s, top, &[]).is_none(),
        "n=1_000_000 exceeds DynBudget::steps and should decline cleanly, not overflow the stack"
    );
}

#[test]
fn a_self_application_reached_only_through_a_captured_closure_is_bounded_by_the_step_budget() {
    // `top` applies `step` to itself -- a plain (non-`Rec`) Y-combinator-
    // style self-application. Every recursive step reaches "step" again
    // only by reading `g` back out of the frame as an ordinary captured
    // `Clo` value, never via `eval_dyn`'s own `self_ctx`-based
    // embedded-self-call recognition (there is no `self_ctx` here at
    // all -- `eval_dyn_direct_call` always inlines with a *fresh* `None`
    // self_ctx for whatever combinator it steps into, per its own
    // docs) and never via `eval_dyn_tail_recursive`'s flat loop (`step`
    // isn't `Rec`-wrapped). The dead `g(999)` call site (arity 1)
    // against the live `g(g, n-1)` call site (arity 2) makes
    // `param_types_for(step)` classify `g` as `Inconsistent`, so every
    // level goes through `eval_dyn_direct_call`'s own `needs_inline`
    // branch -- one genuine native Rust stack frame per level, via
    // `eval_dyn_direct_call` -> `eval_dyn` -> (App spine) ->
    // `eval_dyn_direct_call` again. This is the regression guard for
    // `budget.steps` actually being charged on *that* path: a non-
    // `Rec` body is the one descent `eval_dyn_tail_recursive`'s loop
    // never counts.
    let mut s = TermStore::new();
    let step_src = r"\g n. if 1 < 0 then g 999 else if n <= 0 then n else g g (n - 1)";
    let step = source(&mut s, step_src);

    assert!(
        param_types_for(&s, step).unwrap().contains(&None),
        "g's own dead call site at a different arity should make it Inconsistent"
    );

    for n_val in [0i64, 1, 3, 10, 100] {
        let top = source(&mut s, &format!(r"({step_src}) ({step_src}) ({n_val})"));

        assert!(prove_closure_expr(&s, top).is_none(), "n={n_val}: top's own call to step still can't be classified statically");
        let proof = prove_closure_expr_instance(&s, top, &[]).unwrap_or_else(|| panic!("n={n_val} should be provable per-instance"));
        check_instance_proof(&proof);
        assert_eq!(eval::apply_term(&s, top, &[]).unwrap(), 0, "n={n_val}: sanity check -- counts down to 0 either way");
    }

    // Past `DynBudget::steps`, this must
    // decline *cleanly* rather than actually overflowing the native
    // Rust stack that many real inlined levels would otherwise
    // recurse through -- unlike the embedded-self-call boundary test
    // above, this path goes entirely through `eval_dyn_direct_call`'s
    // own inline branch, never `eval_dyn`'s `self_ctx` recognition.
    let top = source(&mut s, &format!(r"({step_src}) ({step_src}) (1000000)"));
    assert!(
        prove_closure_expr_instance(&s, top, &[]).is_none(),
        "n=1_000_000 exceeds DynBudget::steps via eval_dyn_direct_call's own inline path and should decline cleanly, not overflow the stack"
    );
}

#[test]
fn a_capturing_clo_returning_root_declines_without_evaluating_its_own_argument() {
    // `eval_dyn_direct_call` used to evaluate every argument (each its
    // own, possibly expensive, recursive `eval_dyn` call) *before*
    // checking whether `root` even qualifies for the `needs_inline`
    // path it's about to take -- wasted work whenever `return_ty`
    // alone (a fact about `root`'s own static structure, entirely
    // independent of the arguments) already forces `needs_inline` and
    // that path is about to decline anyway (`root`'s own captures are
    // non-empty -- out of this function's own scope, see its docs).
    //
    // `pick_a = \s. if s>0 then add5cap else sub5cap`, where
    // `add5cap`/`sub5cap` are 2-ary lambdas referencing `cap` from an
    // *outer* scope -- so `pick_a` itself both returns a further `Clo`
    // (`combinator_return_type` recognizes the `If`-between-lambdas
    // shape, same as `add5cap`/`sub5cap` in the plain
    // `a_closure_argument_arriving_via_a_separate_saturated_call...`
    // test above) *and* captures `cap` (unlike that test's two
    // closures, which are fully closed) -- exactly the combination this
    // function declines on. `\cap. if 0 < 1 then pick_a else pick_a`
    // supplies `cap` and hands back `pick_a` as a genuine `Clo` value;
    // a `let`-bound call `g (huge_sum)` (the usual dead-call
    // trick forces `g`'s own classification `Inconsistent`, so this
    // whole chain is actually traced via `eval_dyn` rather than
    // deferred to the opaque, non-executing postulate path) then
    // reaches `pick_a` as `root` with a needlessly expensive argument.
    //
    // Confirmed directly (not just by code reading) that this isn't
    // merely a performance nicety: with the early check reverted back
    // to living inside `eval_dyn_inline_call` (checked only *after*
    // every argument is evaluated, its original position), this exact
    // term reliably overflowed the native stack in an unoptimized
    // debug-build test thread -- `huge_sum`'s own 301-deep, genuinely
    // non-tail `Prim` chain is bounded by no `DynBudget` counter at
    // all (unlike the self-call/inline-call paths those bound), so
    // evaluating it wastefully was a real crash risk, not just wasted
    // cycles, whenever it was about to be thrown away regardless. Since
    // `eval_dyn` runs through `kernel::grow` (`docs/related-work/` 32) it
    // is only wasted cycles; the test still pins the early decline.
    let mut s = TermStore::new();
    // Open on `cap`, used alone: the parser rejects it.
    // add5cap = \a b. a + b + cap  (cap = var(3) from inside here)
    let a1 = s.var(1);
    let b1 = s.var(0);
    let ab = s.prim(PrimOp::Add, a1, b1);
    let cap1 = s.var(3);
    let add5cap_body = s.prim(PrimOp::Add, ab, cap1);
    let add5cap_inner = s.abs(add5cap_body); // binds b
    let add5cap = s.abs(add5cap_inner); // binds a

    // sub5cap = \a b. a - b + cap
    let a2 = s.var(1);
    let b2 = s.var(0);
    let asubb = s.prim(PrimOp::Sub, a2, b2);
    let cap2 = s.var(3);
    let sub5cap_body = s.prim(PrimOp::Add, asubb, cap2);
    let sub5cap_inner = s.abs(sub5cap_body);
    let sub5cap = s.abs(sub5cap_inner);

    // pick_a = \s. if s>0 then add5cap else sub5cap
    let s_var = s.var(0);
    let zero_p = s.lit(0);
    let pick_cond = s.prim(PrimOp::Lt, zero_p, s_var);
    let pick_a_body = s.if_(pick_cond, add5cap, sub5cap);
    let pick_a = s.abs(pick_a_body);

    assert_eq!(combinator_return_type(&s, pick_a), Some(Some(2)), "pick_a should itself return a further arity-2 Clo");
    let (pa_arity, pa_body, pa_is_rec) = shape::peel(&s, pick_a).unwrap();
    assert!(
        !shape::free_vars(&s, pa_body, pa_arity, pa_is_rec).is_empty(),
        "pick_a should genuinely capture cap from outside its own scope"
    );

    let huge_sum = std::iter::repeat("1").take(301).collect::<Vec<_>>().join(" + ");
    let wrapper_src = format!(r"\g. if 1 < 0 then g 999 888 else g ({huge_sum})");
    let let_wrapper = source(&mut s, &wrapper_src);

    assert!(
        param_types_for(&s, let_wrapper).unwrap().contains(&None),
        "g's own dead call site at a different arity should make it Inconsistent, forcing this whole chain to be traced via eval_dyn rather than deferred"
    );

    let pick_src = r"(\s. if 0 < s then (\a b. a + b + cap) else (\a b. a - b + cap))";
    let top = source(&mut s, &format!(r"({wrapper_src}) ((\cap. if 0 < 1 then {pick_src} else {pick_src}) 7)"));
    // Must decline (pick_a's own captures put it out of this
    // function's scope) without overflowing the stack getting there.
    assert!(prove_closure_expr_instance(&s, top, &[]).is_none());
}

#[test]
fn branching_non_tail_self_calls_carrying_an_inconsistently_classified_closure_parameter_get_a_per_instance_proof() {
    // A genuinely *branching* non-tail shape (two self-calls in the
    // same leaf, Fibonacci-style), not just one embedded call,
    // `g` baked in as `\y. y + 1`. Each
    // occurrence of `f ..` is just another embedded self-call as far
    // as `eval_dyn`'s own recognition is concerned -- this test
    // exists specifically to confirm that claim (from `eval_dyn`'s
    // own doc comment) holds for a real branching trace, not just a
    // single non-tail one.
    let mut s = TermStore::new();
    let it_src = r"rec f n g = if 1 < 0 then g 0 999 else if n <= 1 then g n else f (n - 1) g + f (n - 2) g";
    let it = source(&mut s, it_src);

    assert!(param_types_for(&s, it).unwrap().contains(&None));

    for n_val in [0i64, 1, 2, 3, 4] {
        let top = source(&mut s, &format!(r"({it_src}) ({n_val}) (\y. y + 1)"));

        assert!(prove_closure_expr(&s, top).is_none(), "n={n_val}: top's own call to it still can't be classified statically");
        let proof = prove_closure_expr_instance(&s, top, &[]).unwrap_or_else(|| panic!("n={n_val} should be provable per-instance"));
        check_instance_proof(&proof);
        // f(n) = inc(n) for n<=1, else f(n-1)+f(n-2) -- 1,2,3,5,8 for
        // n=0..4, hand-computed independently rather than derived
        // from the term itself, so this is a real cross-check.
        let expected = [1i64, 2, 3, 5, 8][n_val as usize];
        assert_eq!(eval::apply_term(&s, top, &[]).unwrap(), expected, "n={n_val}: sanity check against the interpreter");
    }
}

