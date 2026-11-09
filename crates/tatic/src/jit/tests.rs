
#[test]
fn the_verify_battery_probes_zero_negatives_and_a_loop_that_runs_many_times() {
    // Outside the gate's fragment, `verify` is the only check that runs the
    // emitted code, and that depends on the battery reaching these; the cap
    // at 12 (docs/related-work/ §71) must not shrink it below them.
    let samples: Vec<i64> = sample_arg_vectors(1).into_iter().map(|v| v[0]).collect();
    assert!(samples.contains(&0), "no zero");
    assert!(samples.iter().any(|&a| a < 0), "no negative");
    assert!(samples.iter().any(|&a| a >= 10), "no input that iterates 10+ times");
}
use super::*;
use crate::support::samples::{
    a_pap_capturing, a_pap_non_capturing, capturing_closure_loop, closure_typed_loop_carried_parameter_loop,
    factorial, fib, gcd, inc, inconsistent_arity_loop_carried_parameter_loop, iterate, source, twice_inc_5,
};
use crate::testing::test_corpus::{
    a_pap_of_a_capturing_self_recursive_combinator, a_pap_of_a_self_recursive_combinator,
    inconsistent_arity_capturing_instance, inconsistent_arity_iterate, inconsistent_arity_runtime_chosen_instance,
    inconsistent_arity_saturating_instance, inconsistent_arity_under_applying_instance,
    iterate_creating_a_closure_over_g, let_bound_factorial_10, over_application_if_between_closures_of_params,
};
use crate::lang::term::TermStore;

#[test]
fn a_closure_of_the_wrong_arity_off_the_samples_is_not_installed() {
    let mut s = TermStore::new();
    let h = source(
        &mut s,
        r"\n. (\g. if n == 777 then (\k. k n) (g 1) + (\k. k n) (g 2) else n) (\x y. x + y + n)",
    );
    // Well typed, but `g` is called with one argument everywhere and
    // bound to a two-argument closure, so the fragment dispatches at the
    // wrong arity: it traps at n = 777, which no sample reaches. Types
    // don't see arity, so typing.rs accepts it. What keeps it out is the
    // universal-proof gate: the kernel types a closure by its exact
    // arity (`Clo_k`), so no proof can exist (docs/related-work/ §40).
    assert!(crate::verify::typing::well_typed(&s, h, 1));
    let c = crate::jit::compile::compile_specialised(&s, h).unwrap();
    assert!(c.specialised.is_none());
    let mut raw = JitEngine::new();
    let (_module, f, hp) = raw.instantiate(&c.frag.wat()).unwrap();
    assert_eq!(raw.invoke(f, hp, &[777]), Err(EvalError::Trap));
    let mut jit = JitEngine::new();
    for n in [0, 1, 776, 777, 778] {
        assert_eq!(jit.apply(&s, h, &[n]), eval::apply_term(&s, h, &[n]), "n={n}");
    }
    assert_eq!((jit.stats.compiled, jit.stats.declined_no_universal_proof), (0, 1));
}

#[test]
fn a_parameter_that_is_only_called_gets_no_universal_proof() {
    // The JIT passes only `Int`s, so a theorem that types a called
    // parameter as a closure covers none of its calls
    // (docs/related-work/ §42). Both provers produced one: the closure
    // prover for the first term, the tail-recursive one for the second.
    for src in [
        r"\a. \f. if a == 777 then f 5 else a",
        r"rec go g n x = if n <= 0 then x else go g (n - 1) (g x)",
    ] {
        let mut s = TermStore::new();
        let h = crate::lang::syntax::parse(&mut s, src).unwrap();
        let arity = crate::jit::shape::peel(&s, h).unwrap().0;
        assert!(!JitEngine::kernel_verify(&s, h, arity), "{src}");
    }
}

#[test]
fn an_ill_typed_branch_off_the_samples_is_not_miscompiled() {
    // `g 1 + g` adds a closure to an Int: `eval` fails with TypeError
    // at n = 777, which no sample hits.
    let mut s = TermStore::new();
    let h = source(&mut s, r"\n. (\g. if n == 777 then g 1 + g else n) (\x. x + n)");
    let mut jit = JitEngine::new();
    for n in [0, 1, 776, 777, 778] {
        assert_eq!(jit.apply(&s, h, &[n]), eval::apply_term(&s, h, &[n]), "n={n}");
    }
    assert_eq!((jit.stats.compiled, jit.stats.declined_ill_typed), (0, 1));
}

#[test]
fn a_closure_argument_of_the_wrong_arity_gets_no_proof() {
    let mut s = TermStore::new();
    let h = source(&mut s, r"\n. (\g. g 1) (\x y. x + y) n");
    // `\g. g 1` gives `g : Clo_1`, but the argument is a `Clo_2`. The
    // proof walkers used to compose them anyway, which the kernel
    // rejects (and a debug build panicked on).
    let mut jit = JitEngine::new();
    assert!(!JitEngine::kernel_verify(&s, h, 1));
    // The gate skips the per-execution prover above arity 0, so ask it directly.
    for sample in sample_arg_vectors(1) {
        assert!(proof::prove_closure_expr_instance(&s, h, &sample).is_none());
    }
    // The JIT proves the specialisation `\n. 1 + n` instead.
    assert_eq!(jit.apply(&s, h, &[4]), Ok(5));
    assert_eq!(jit.stats.specialised, 1);
}

#[test]
fn an_open_redex_is_not_contracted_away_by_the_jit() {
    // Final review's probe: before the checker required a closed
    // source, `(\x. 0) v5` was contracted to `0`, `h'` compiled, no
    // sample hit 777, the universal proof on `h'` installed it, and
    // the JIT returned Ok(0) where `eval` fails. Whatever the JIT does
    // with this term, it must agree with `eval`.
    let mut s = TermStore::new();
    let h = crate::testing::test_corpus::open_redex_probe(&mut s);
    let mut jit = JitEngine::new();
    for n in [0, 1, 776, 777, 778, -777] {
        assert_eq!(jit.apply(&s, h, &[n]), eval::apply_term(&s, h, &[n]), "n={n}");
    }
    assert_eq!(eval::apply_term(&s, h, &[777]), Err(EvalError::UnboundVariable));
}

#[test]
fn the_installation_proof_is_about_the_specialised_term() {
    // No `kernel_verify` strategy proves `(\g. g) (\x. x + 1) n`
    // universally (asserted below), but its specialisation `n + 1` is
    // plain arithmetic. So installing it at all depends on proving
    // `h'`, not `h`.
    let mut s = TermStore::new();
    let h = crate::lang::syntax::parse(&mut s, r"\n. (\g. g) (\x. x + 1) n").unwrap();
    let sp = crate::jit::specialise::specialise(&s, h);
    let mut jit = JitEngine::new();
    assert!(!JitEngine::kernel_verify(&s, h, 1));
    // `n + 1` is a fragment term: the gate proves its emitted body
    let c = crate::jit::compile::compile_specialised(&sp.store, sp.term).expect("n + 1 compiles");
    assert!(JitEngine::prove_install(&sp.store, sp.term, 1, c.frag.entry()));
    for n in [0, 5, -7] {
        assert_eq!(jit.apply(&s, h, &[n]), Ok(n + 1));
    }
    assert_eq!((jit.stats.compiled, jit.stats.specialised, jit.stats.declined_no_universal_proof), (1, 1, 0));
}

#[test]
fn sample_arg_vectors_for_arity_zero_is_a_single_trivial_sample() {
    // `vec![a; 0]` is `[]` regardless of `a` -- without the dedicated
    // `0` arm, the `_` catch-all would push the same empty sample
    // once per `SAMPLE_ARGS[..6]` entry (see `sample_arg_vectors`'s
    // own comment and `docs/related-work/` §9 for the redundant-proof-
    // search cost this was causing).
    assert_eq!(sample_arg_vectors(0), vec![Vec::<i64>::new()]);
}

#[test]
fn sample_arg_vectors_for_higher_arity_includes_a_genuinely_distinct_sample() {
    // Before this fix, the `_` (arity >= 3) arm only ever generated
    // `vec![a; arity]` -- every position the *same* value -- despite
    // its own comment claiming an "all-small-distinct" diagonal too.
    // A compiled-code bug that swaps or misindexes two argument
    // positions is structurally invisible to an all-equal sample
    // (swapping equal values changes nothing), so `verify()` would
    // have missed
    // exactly that bug class for every arity->=3 term. Confirm at
    // least one generated sample now has genuinely different values
    // at different positions, for a couple of arities.
    for arity in [3, 4, 5] {
        let samples = sample_arg_vectors(arity);
        assert!(
            samples.iter().any(|s| s.iter().collect::<hashbrown::HashSet<_>>().len() > 1),
            "arity {arity}: no sample has distinct argument values: {samples:?}"
        );
    }
}

#[test]
fn invoke_agrees_with_the_interpreter_past_the_stack_buffer_threshold() {
    // `invoke`'s own `STACK_ARGS` bound (8) is meant to be transparent:
    // a call with more arguments than that must still agree with the
    // interpreter via the heap-`Vec` fallback, not just avoid crashing.
    // A 10-ary sum is the simplest term whose arity exceeds the bound.
    let mut s = TermStore::new();
    let top = source(&mut s, r"\a b c d e f g h i j. j + i + h + g + f + e + d + c + b + a");
    let args: Vec<i64> = (1..=10).collect();

    let mut jit = JitEngine::new();
    assert_eq!(jit.apply(&s, top, &args).unwrap(), eval::apply_term(&s, top, &args).unwrap());
    // Without this, a broken `invoke` wouldn't necessarily show up as a
    // wrong *value* here: `verify()` itself calls `invoke` on its own
    // sample battery, so a corrupted heap-fallback call would just make
    // verification disagree and safely blacklist the term to the
    // interpreter (confirmed directly: a deliberately truncated
    // heap-fallback buffer made this assertion fail with compiled=0,
    // not a wrong sum) -- this assertion is what actually forces the
    // comparison above through the compiled path.
    assert_eq!(jit.stats.compiled, 1, "must actually exercise the compiled path, not silently fall back to the interpreter");
}

#[test]
fn a_mismatched_arg_count_does_not_poison_the_cache_and_is_served_by_the_interpreter() {
    // `eval::apply_term` is fully generic over arg count -- under-
    // applying `factorial` (arity 1) with 0 args is a legitimate
    // shape it handles (evaluates to an unapplied closure, then
    // fails the final `Value::Int` match with a clean `TypeError`,
    // not a panic). This call's arity not matching `h`'s own must
    // not get cached as permanently `NotCompilable`, conflating "is
    // `h` compilable at all" with "did this one call's arg count
    // match".
    let mut s = TermStore::new();
    let fact = factorial(&mut s);
    let mut jit = JitEngine::new();

    assert!(jit.apply(&s, fact, &[]).is_err());
    assert_eq!(jit.stats.compiled, 0, "a mismatched call must not poison the cache");

    // A later, correctly-sized call must still compile normally.
    assert_eq!(jit.apply(&s, fact, &[5]).unwrap(), 120);
    assert_eq!(jit.stats.compiled, 1);

    // A further mismatched call against the now-cached, *compiled*
    // entry must fall back to the interpreter cleanly too, not
    // panic via `call_compiled`'s own debug_assert or return a
    // spurious `Trap` from feeding the compiled function's fixed
    // Wasm signature the wrong number of arguments.
    assert_eq!(jit.apply(&s, fact, &[]).unwrap_err(), eval::apply_term(&s, fact, &[]).unwrap_err());
}

#[test]
fn a_term_too_big_as_a_tree_is_interpreted() {
    // Past `compile.rs`'s `MAX_TREE_NODES` as a tree.
    let mut s = TermStore::new();
    let h = crate::testing::test_corpus::doubling(&mut s, 16);
    let mut jit = JitEngine::new();
    assert_eq!(jit.apply(&s, h, &[3]).unwrap(), 3 << 16);
    assert_eq!((jit.stats.compiled, jit.stats.interpreted), (0, 1));
}

#[test]
fn first_call_compiles_later_calls_hit_cache() {
    let mut s = TermStore::new();
    let fact = factorial(&mut s);
    let mut jit = JitEngine::new();

    assert_eq!(jit.apply(&s, fact, &[10]).unwrap(), 3628800);
    assert_eq!(jit.stats.compiled, 1);
    assert_eq!(jit.stats.cache_hits, 1);

    for n in 0..10 {
        assert_eq!(jit.apply(&s, fact, &[n]).unwrap(), eval::apply_term(&s, fact, &[n]).unwrap());
    }
    assert_eq!(jit.stats.compiled, 1, "should not recompile on repeat calls");
    assert!(jit.stats.cache_hits > 1);
}

#[test]
fn division_agrees_with_the_interpreter_at_i64_min_over_negative_one() {
    // `i64::MIN / -1` is the one input where `i64.div_s` traps per
    // the WebAssembly spec (the mathematical quotient overflows
    // `i64`), while `eval.rs`'s own `wrapping_div` silently wraps
    // back to `i64::MIN` -- the same non-trapping convention
    // `Add`/`Sub`/`Mul` already use uniformly. `compile.rs`'s
    // `emit_wrapping_div` special-cases exactly this combination so
    // the compiled fragment doesn't disagree with the interpreter on
    // an input `SAMPLE_ARGS` doesn't happen to include.
    let mut s = TermStore::new();
    let div = source(&mut s, r"\a b. a / b");

    let mut jit = JitEngine::new();
    let args = [i64::MIN, -1];
    let interpreted = eval::apply_term(&s, div, &args).unwrap();
    let compiled = jit.apply(&s, div, &args).unwrap();
    assert_eq!(interpreted, i64::MIN);
    assert_eq!(compiled, interpreted, "compiled and interpreted must agree on i64::MIN / -1");
    assert_eq!(jit.stats.compiled, 1, "should have compiled, not fallen back to the interpreter");
}

#[test]
fn kernel_proof_recorded_for_straight_line_and_tail_recursive_terms() {
    // Straight-line, no Rec.
    let mut s = TermStore::new();
    let straight_line = crate::support::samples::straight_line(&mut s);

    let mut jit = JitEngine::new();
    assert_eq!(jit.apply(&s, straight_line, &[3, 5]).unwrap(), 6);
    assert!(jit.is_kernel_verified(straight_line));
    assert_eq!(jit.stats.compiled, 1);

    // gcd is Rec-wrapped and tail-recursive (a single self-call in tail
    // position): it gets the universal theorem.
    let gcd_term = gcd(&mut s);
    assert_eq!(jit.apply(&s, gcd_term, &[48, 18]).unwrap(), 6);
    assert!(jit.is_kernel_verified(gcd_term));
    assert_eq!(jit.stats.compiled, 2);

    // factorial is Rec-wrapped and *not* tail-recursive (the self-call
    // is nested inside a multiplication), but prove_tail_recursive_universal
    // covers leaves with any number of self-calls combined
    // arithmetically (via kernel::cong_n), so it gets the universal
    // theorem too.
    let fact = factorial(&mut s);
    assert_eq!(jit.apply(&s, fact, &[5]).unwrap(), 120);
    assert!(jit.is_kernel_verified(fact));
    assert_eq!(jit.stats.compiled, 3);
}

#[test]
fn branching_recursion_gets_the_universal_theorem() {
    // Naive Fibonacci's else-branch leaf has two self-calls; the
    // universal theorem covers it. Its per-call instances are
    // proof::tests::fibonacci_branching_leaves_get_per_instance_proofs.
    let mut s = TermStore::new();
    let fibonacci = fib(&mut s);

    let mut jit = JitEngine::new();
    assert_eq!(jit.apply(&s, fibonacci, &[10]).unwrap(), 55);
    assert!(jit.is_kernel_verified(fibonacci));
    assert_eq!(jit.stats.compiled, 1);
}

#[test]
fn non_capturing_higher_order_terms_now_compile() {
    // Both twice and inc are non-capturing, so compile.rs's known-call
    // closure support (twice becomes a combinator calling `f` through
    // a Wasm table, inc becomes another combinator) now compiles this
    // instead of falling back to the interpreter, and proof.rs's
    // prove_closure_expr gives it a kernel-checked proof too.
    let mut s = TermStore::new();
    let applied = twice_inc_5(&mut s);

    let mut jit = JitEngine::new();
    assert_eq!(jit.apply(&s, applied, &[]).unwrap(), 7);
    assert_eq!(jit.stats.compiled, 1);
    assert_eq!(jit.stats.interpreted, 0);
    assert!(jit.is_kernel_verified(applied));
    assert_eq!(jit.stats.compiled, 1);
}

#[test]
fn a_let_bound_self_recursive_function_compiles_and_is_kernel_verified() {
    // `let fact = rec f n = .. in fact 10` desugars to
    // `(\g. g 10) (rec f n = ..)` (found via the REPL, see
    // syntax.rs/repl.rs): a named recursive function
    // called through the same combinator table a plain closure value
    // uses. compile.rs handles this (a bug fix -- see its own tests),
    // and prove_closure_expr now does too: a call to a combinator is
    // always postulated opaque (never denoted by looking inside its
    // own body), so widening `Term::Abs`-only call/value sites to also
    // accept `Term::Rec` needed no new proof machinery, just the wider
    // pattern -- see proof.rs's own denote_closure docs.
    let mut s = TermStore::new();
    let applied = let_bound_factorial_10(&mut s);

    let mut jit = JitEngine::new();
    assert_eq!(jit.apply(&s, applied, &[]).unwrap(), 3628800);
    assert_eq!(jit.stats.compiled, 1);
    assert_eq!(jit.stats.interpreted, 0);
    assert!(jit.is_kernel_verified(applied));
}

#[test]
fn a_returned_closure_now_compiles_via_over_application() {
    // The literal lambda `\x. ...` applied to 3, then 4:
    // `unwind_app_spine` can't distinguish this from "the lambda takes
    // 2 arguments" (see `compile::tests::
    // curried_application_is_indistinguishable_from_multi_arg_calls`),
    // and the lambda is declared 1-ary, so this reads as it
    // over-applied by one argument: its own saturated call (on 3) is
    // compiled, and whatever it returns -- one of two
    // *capturing* closures, depending on `x` -- is dispatched via
    // `call_indirect` the same way a closure-typed variable would be
    // (see `compile.rs`'s module docs on over-application). Was
    // previously rejected outright, falling back to the interpreter;
    // now compiles and gets the right, sample-verified answer --
    // *and* proof.rs's own `denote_closure`/`combinator_return_type`
    // widening (see `proof::tests::
    // an_over_applied_literal_lambda_returning_a_closure_gets_a_closure_proof`)
    // covers this shape too, so it's kernel-verified as well.
    let mut s = TermStore::new();
    let applied = source(&mut s, r"(\x. if 0 < x then (\y. x + y) else (\y. x - y)) 3 4");

    let mut jit = JitEngine::new();
    assert_eq!(jit.apply(&s, applied, &[]).unwrap(), 7); // 3 > 0, so 3 + 4
    assert_eq!(jit.stats.compiled, 1);
    assert_eq!(jit.stats.interpreted, 0);
    assert!(jit.is_kernel_verified(applied));
}

#[test]
fn content_addressing_shares_the_cache_across_independently_built_terms() {
    let mut s = TermStore::new();
    let fact_a = factorial(&mut s);
    let fact_b = factorial(&mut s); // rebuilt from scratch, same structure
    assert_eq!(fact_a, fact_b);

    let mut jit = JitEngine::new();
    jit.apply(&s, fact_a, &[6]).unwrap();
    assert_eq!(jit.stats.compiled, 1);
    jit.apply(&s, fact_b, &[7]).unwrap();
    assert_eq!(jit.stats.compiled, 1, "same hash must reuse the compiled entry");
}

#[test]
fn repeated_calls_to_a_capturing_closure_term_stay_correct_and_cached() {
    // The same cached compiled instance gets called many times here
    // (that's the whole point of the cache) -- each call creates a
    // fresh capturing closure, so this exercises the `hp` reset
    // `invoke` does before every call (see compile.rs's own
    // `resetting_hp_between_calls_keeps_memory_bounded_across_many_calls`
    // for the lower-level mechanism this relies on). Not a memory
    // measurement itself (jit.rs has no public way to inspect Wasm
    // linear memory) -- just confirms behavior stays correct and the
    // cache, not recompilation, serves every repeated call.
    let mut s = TermStore::new();
    let h = capturing_closure_loop(&mut s);
    let mut jit = JitEngine::new();

    for i in 0..500 {
        let n = (i % 50) + 1;
        let result = jit.apply(&s, h, &[n, 0]).unwrap();
        let expected = n * (n + 1) / 2; // sum 1..=n
        assert_eq!(result, expected, "mismatch at n={n}");
    }
    assert_eq!(jit.stats.compiled, 1, "should compile once, not once per call");
    assert_eq!(jit.stats.cache_hits, 500);
}

#[test]
fn a_self_recursive_closure_created_and_called_each_iteration_is_kernel_verified() {
    // Same term as capturing_closure_loop above -- rec f n acc = if
    // n <= 0 then acc else f(n-1, (\y. acc+y)(n)) -- but now checked
    // directly against proof.rs: prove_tail_recursive_universal covers
    // a closure *created and called* inside a self-call argument too,
    // not just a closure-typed *parameter* (see proof.rs's own
    // denote_closure/prime_closure_postulates docs), so this
    // gets the universal theorem, not just per-sample relational
    // proofs.
    let mut s = TermStore::new();
    let h = capturing_closure_loop(&mut s);
    let mut jit = JitEngine::new();

    assert_eq!(jit.apply(&s, h, &[5, 0]).unwrap(), 15); // sum 1..=5
    assert!(jit.is_kernel_verified(h));
    assert_eq!(jit.stats.compiled, 1);
}

#[test]
fn a_closure_typed_loop_carried_parameter_compiles_and_is_kernel_verified() {
    // `it` is `samples::iterate`, here actually run: a closure-typed
    // *parameter* threaded through every iteration and called
    // (call_indirect) rather than a fresh closure created each
    // iteration (capturing_closure_loop's own shape above). Since `g`
    // is Clo-typed, `it` can't be called directly through jit.apply's
    // plain-i64 args the way gcd/fib/capturing_closure_loop are --
    // there's no way to hand it a real packed closure value from the
    // outside -- so `inc` (a non-capturing literal lambda) is baked in
    // as the initial `g` and wrapped in a fully-applied outer call
    // (`top`), making the whole term closed (arity 0).
    //
    // That wrapping matters for *which* proof `is_kernel_verified`
    // below actually reflects: `kernel_verify` tries
    // `prove_closure_expr` before `prove_tail_recursive_universal`,
    // and `top` -- an application whose root resolves to `it`, fully
    // applied -- is exactly the "self-recursive combinator called
    // directly" shape `prove_closure_expr` already covers opaquely
    // (`call_ref`, never unfolding `it`'s own body), so *that* is what
    // succeeds here, not the universal theorem `it` gets on its own
    // (checked directly below) -- an honest distinction, not a
    // weaker guarantee: `jit.rs`'s own sample-based `verify()` against
    // the interpreter is still the actual trust gate installing the
    // compiled form either way (see this module's own docs).
    let mut s = TermStore::new();
    let it = iterate(&mut s);
    let top = closure_typed_loop_carried_parameter_loop(&mut s, 10);

    let mut jit = JitEngine::new();
    assert_eq!(jit.apply(&s, top, &[]).unwrap(), 10); // 0 incremented 10 times
    assert_eq!(jit.stats.compiled, 1);
    assert_eq!(jit.stats.interpreted, 0);
    assert!(jit.is_kernel_verified(top));

    // The universal theorem this recursion path is actually about --
    // checked directly against `it`, not through `top`'s own opaque
    // wrapping call.
    assert!(proof::prove_tail_recursive_universal(&s, it).is_some());
}

#[test]
fn a_tail_recursive_loop_compiles_and_is_kernel_verified_once_its_own_closure_parameter_turns_inconsistent() {
    // Same shape as
    // a_closure_typed_loop_carried_parameter_compiles_and_is_kernel_verified
    // just above, with one addition: a dead (never-reached, since
    // `1 < 0` is always false) extra call site `g x 999` for `g` at
    // arity 2, alongside the live, tail-recursive arity-1
    // call. `g` is now `ArityUse::Inconsistent`, which -- per
    // compile.rs's own docs -- makes the *whole* fragment (not just
    // this one dead call site) switch to curried dispatch, including
    // the hot, tail-recursive `g(x)` call every iteration actually
    // takes. `proof::eval_dyn_tail_recursive` now covers this too
    // (see its own docs): every call `g` actually takes, along this
    // one concrete trace, happens to be exactly saturated, so the
    // per-instance methodology proves it despite `g`'s own static
    // classification staying `Inconsistent`.
    let mut s = TermStore::new();
    let it = inconsistent_arity_iterate(&mut s);
    let top = inconsistent_arity_loop_carried_parameter_loop(&mut s, 10);

    let frag = crate::jit::compile::try_compile(&s, it).expect("should compile via curried dispatch, per compile.rs alone");
    assert!(frag.wat().contains("call_indirect (type $ty1)"), "the hot, consistent g(x) call should also go through the curried fallback:\n{}", frag.wat());

    let mut jit = JitEngine::new();
    assert_eq!(jit.apply(&s, top, &[]).unwrap(), 10); // 0 incremented 10 times, same as the baseline shape
    assert_eq!(jit.stats.compiled, 1);
    assert_eq!(jit.stats.interpreted, 0);
    // `prove_closure_expr_instance`'s own inlining (via
    // `eval_dyn_tail_recursive`) now covers a recursive use of the
    // curried-dispatch capability too -- previously the standing gap
    // this whole test existed to document (see `docs/related-work/` §9).
    // `jit.rs`'s own sample-based `verify()` is still the actual
    // trust gate installing the compiled form regardless.
    assert!(jit.is_kernel_verified(top));
    assert_eq!(jit.stats.compiled, 1);
}

#[test]
fn a_closure_created_in_a_self_call_argument_capturing_a_closure_typed_loop_parameter_compiles_and_gets_a_universal_proof() {
    // Same shape as proof::tests::
    // a_closure_created_in_a_self_call_argument_capturing_a_closure_typed_loop_parameter_gets_a_universal_proof,
    // run for real here: each iteration creates a
    // fresh closure that captures `g` itself (a Clo-typed value, not
    // an Int). `g x` (a direct call) is what makes `it`'s own scan
    // classify `g` as Clo-typed in the first place -- `infer_closure_arities`
    // never looks inside the wrapper's own body, matching
    // `denote_closure`'s own "never look inside a body" discipline.
    let mut s = TermStore::new();
    let it = iterate_creating_a_closure_over_g(&mut s);
    let inc = inc(&mut s);
    let (five, zero) = (source(&mut s, "5"), source(&mut s, "0"));
    let partial = s.app2(it, five, inc);
    let top = s.app(partial, zero);

    let mut jit = JitEngine::new();
    // new_x = g(x) + (g(x)+1) = 2*inc(x)+1 = 2x+3; from x=0: 3, 9,
    // 21, 45, 93 after 1..5 iterations (same derivation as proof.rs's
    // own test).
    assert_eq!(jit.apply(&s, top, &[]).unwrap(), 93);
    assert_eq!(jit.stats.compiled, 1);
    assert_eq!(jit.stats.interpreted, 0);
    assert!(proof::prove_tail_recursive_universal(&s, it).is_some());
}

#[test]
fn partial_application_of_a_non_capturing_root_compiles_and_is_kernel_verified() {
    // compile.rs desugars this at compile time (a synthesized wrapper
    // combinator), and proof.rs's own denote_closure now covers a
    // partial application of a *non-capturing* literal too (pap_ref),
    // so this gets a kernel-checked proof, not just empirical sample
    // verification -- see proof::tests::
    // a_partially_applied_literal_lambda_used_as_a_value_gets_a_closure_proof
    // for the same shape checked directly against proof.rs.
    let mut s = TermStore::new();
    let top = a_pap_non_capturing(&mut s);

    let mut jit = JitEngine::new();
    assert_eq!(jit.apply(&s, top, &[]).unwrap(), 7);
    assert_eq!(jit.stats.compiled, 1);
    assert_eq!(jit.stats.interpreted, 0);
    assert!(jit.is_kernel_verified(top));
}

#[test]
fn partial_application_of_a_capturing_root_compiles_and_is_kernel_verified() {
    // lower_wat.rs's Lowering::pap_env composes the wrapper's own environment
    // with a copy of the (capturing) root's environment, and proof.rs's
    // pap_ref now mirrors that (a leading Env_n parameter when the root
    // captures, built at every call site via build_env_expr) -- see
    // proof::tests::a_partially_applied_capturing_literal_lambda_used_as_a_value_gets_a_closure_proof
    // for the same shape checked directly against proof.rs -- so this
    // now gets a kernel-checked proof, not just empirical sample
    // verification.
    let mut s = TermStore::new();
    let g = a_pap_capturing(&mut s);

    let mut jit = JitEngine::new();
    assert_eq!(jit.apply(&s, g, &[10]).unwrap(), 17); // (3 + 4 + 10)
    assert_eq!(jit.stats.compiled, 1);
    assert_eq!(jit.stats.interpreted, 0);
    assert!(jit.is_kernel_verified(g));
}

#[test]
fn partial_application_of_a_self_recursive_root_compiles_and_is_kernel_verified() {
    // The combinator is partially applied: under-applied by one argument.
    // compile.rs's register_partial_app/lower_wat.rs's emit_pap_wrapper
    // never special-cased is_rec (a PAP wrapper only ever forwards a static
    // call to its root, indifferent to whether that root's own codegen
    // happens to loop), and now neither does proof.rs's pap_ref, so
    // this gets a kernel-checked proof too.
    let mut s = TermStore::new();
    let top = a_pap_of_a_self_recursive_combinator(&mut s);

    let mut jit = JitEngine::new();
    assert_eq!(jit.apply(&s, top, &[]).unwrap(), 6); // 3*2*1
    assert_eq!(jit.stats.compiled, 1);
    assert_eq!(jit.stats.interpreted, 0);
    assert!(jit.is_kernel_verified(top));
}

#[test]
fn partial_application_of_a_capturing_self_recursive_root_compiles_and_is_kernel_verified() {
    // Combines the two pap_ref restrictions lifted independently this
    // session (a capturing root, then a self-recursive root) in one
    // term, run for real. The combinator at n=3, acc=1 unrolls to
    // acc=6+4z, so top(z) = 6 + 4*z.
    let mut s = TermStore::new();
    let top = a_pap_of_a_capturing_self_recursive_combinator(&mut s);

    let mut jit = JitEngine::new();
    assert_eq!(jit.apply(&s, top, &[0]).unwrap(), 6);
    assert_eq!(jit.apply(&s, top, &[10]).unwrap(), 46);
    assert_eq!(jit.stats.compiled, 1);
    assert_eq!(jit.stats.interpreted, 0);
    assert!(jit.is_kernel_verified(top));
}

#[test]
fn an_over_applied_literal_lambda_returning_a_closure_compiles_and_is_kernel_verified() {
    // Same shape as compile::tests::
    // an_over_applied_literal_lambda_returning_a_closure_compiles_and_matches_interpreter,
    // run through the real cache (compile + sample-verify) rather than
    // raw wasmtime, at both a positive and a negative `a` so both
    // branches get exercised. `denote_closure`'s own `Term::Abs | Term::Rec`
    // case now covers over-application too, gated by
    // `combinator_return_type` correctly classifying `f`'s own
    // saturated call as `Clo`-typed (the `If` between the two
    // `\c. ...` closures) -- see proof::tests::
    // an_over_applied_literal_lambda_returning_a_closure_gets_a_closure_proof.
    let mut s = TermStore::new();
    let top = over_application_if_between_closures_of_params(&mut s);

    let mut jit = JitEngine::new();
    assert_eq!(jit.apply(&s, top, &[10, 3, 100]).unwrap(), 113);
    assert_eq!(jit.apply(&s, top, &[-5, 3, 100]).unwrap(), 92);
    assert_eq!(jit.stats.compiled, 1);
    assert_eq!(jit.stats.interpreted, 0);
    assert!(jit.is_kernel_verified(top));
}

// The four shapes below are the `samples::inconsistent_arity_*_instance`
// terms that compile.rs's own canonical capability tests use too -- this is where the actual
// stated goal of `proof::prove_closure_expr_instance` gets checked
// end to end: before it existed, `kernel_verify` had no strategy at
// all for a closure-typed parameter called with genuinely
// inconsistent arities, so `is_kernel_verified` was unconditionally
// `false` for every one of these; it's `true` now.

#[test]
fn an_inconsistently_called_parameters_saturating_instance_is_kernel_verified() {
    let mut s = TermStore::new();
    let top = inconsistent_arity_saturating_instance(&mut s);

    let mut jit = JitEngine::new();
    assert_eq!(jit.apply(&s, top, &[]).unwrap(), 3);
    assert_eq!(jit.stats.interpreted, 0);
    assert!(jit.is_kernel_verified(top));
}

#[test]
fn an_inconsistently_called_parameters_under_applying_instance_is_kernel_verified() {
    let mut s = TermStore::new();
    let top = inconsistent_arity_under_applying_instance(&mut s);

    let mut jit = JitEngine::new();
    assert_eq!(jit.apply(&s, top, &[]).unwrap(), 101);
    assert_eq!(jit.stats.interpreted, 0);
    assert!(jit.is_kernel_verified(top));
}

#[test]
fn a_captured_value_through_an_inconsistently_called_parameter_is_declined_for_want_of_a_universal_proof() {
    let mut s = TermStore::new();
    let top = inconsistent_arity_capturing_instance(&mut s);

    let mut jit = JitEngine::new();
    assert_eq!(jit.apply(&s, top, &[100]).unwrap(), 103);
    assert_eq!(jit.apply(&s, top, &[-7]).unwrap(), -4);
    // Those answers came from the interpreter. `prove_closure_expr_
    // instance` is a per-call certificate, and at arity 1 the battery
    // it runs on is a finite probe of `i64`, so the installation gate
    // declines this term outright and every call falls back. `100`
    // isn't even in `SAMPLE_ARGS`: before the gate it was served by
    // compiled code on the strength of `verify()`'s agreement at nine
    // *other* points, which is exactly what the gate exists to stop.
    assert!(!jit.is_kernel_verified(top));
    assert_eq!(jit.stats.declined_no_universal_proof, 1);
    assert_eq!(jit.stats.compiled, 0);
    assert_eq!(jit.stats.interpreted, 2);
}

#[test]
fn a_runtime_chosen_literals_own_instance_is_declined_for_want_of_a_universal_proof() {
    let mut s = TermStore::new();
    let top = inconsistent_arity_runtime_chosen_instance(&mut s);

    let mut jit = JitEngine::new();
    assert_eq!(jit.apply(&s, top, &[1]).unwrap(), 3);
    assert_eq!(jit.apply(&s, top, &[-1]).unwrap(), -1);
    // Per-call certificates at arity 1, so the gate declines it and
    // the interpreter answers both calls -- see the sibling test
    // above for why that's `Samples` rather than `Universal`. Note
    // both arguments here *are* in `SAMPLE_ARGS`; the gate is a
    // property of the term, not of which arguments happen to show up.
    assert!(!jit.is_kernel_verified(top));
    assert_eq!(jit.stats.declined_no_universal_proof, 1);
    assert_eq!(jit.stats.compiled, 0);
    assert_eq!(jit.stats.interpreted, 2);
}

#[test]
fn a_known_partial_application_is_installed_specialised_with_a_universal_proof() {
    let (_, s, h) = crate::support::samples::corpus().into_iter().find(|(n, ..)| *n == "partial_application_loop").unwrap();
    let mut jit = JitEngine::new();
    for args in [[0, 0], [1, 0], [5, 3], [100, -7]] {
        assert_eq!(jit.apply(&s, h, &args), eval::apply_term(&s, h, &args), "args={args:?}");
    }
    assert_eq!((jit.stats.compiled, jit.stats.specialised), (1, 1));
    assert!(jit.is_kernel_verified(h));
}

/// The goal-1 terms in the gate's fragment, with an argument list of their arity.
fn fragment_terms() -> Vec<(&'static str, fn(&mut TermStore) -> Hash, Vec<i64>)> {
    vec![
        ("inc", crate::support::samples::inc, vec![41]),
        ("doubling_4", |s| crate::testing::test_corpus::doubling(s, 4), vec![3]),
        ("straight_line", crate::support::samples::straight_line, vec![3, 5]),
        ("a_capturing_closure_call", crate::support::samples::a_capturing_closure_call, vec![7]),
        ("a_pap_capturing", crate::support::samples::a_pap_capturing, vec![7]),
    ]
}

#[test]
fn the_gates_verdict_is_final_for_fragment_terms() {
    use tatic_wasm::wasm::Ins;
    let mut s = TermStore::new();
    let h = crate::support::samples::straight_line(&mut s);
    let crate::jit::compile::Compiled { frag, specialised } =
        crate::jit::compile::compile_specialised(&s, h).expect("straight_line compiles");
    let (s, h) = specialised.unwrap_or((s, h));
    assert!(JitEngine::prove_install(&s, h, 2, frag.entry()));
    let swapped = crate::testing::ins_mutate::mutate(frag.entry(), &|i| match i {
        Ins::If(t, e) => Some(Ins::If(e.clone(), t.clone())),
        _ => None,
    });
    assert_ne!(swapped, frag.entry());
    // the chain would accept the term; for a fragment term it is not consulted
    assert!(JitEngine::kernel_verify(&s, h, 2));
    assert!(!JitEngine::prove_install(&s, h, 2, &swapped));
}

#[test]
fn fragment_terms_install() {
    for (name, build, args) in fragment_terms() {
        let mut s = TermStore::new();
        let h = build(&mut s);
        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, h, &args), eval::apply_term(&s, h, &args), "{name}");
        assert_eq!(jit.stats.compiled, 1, "{name} should install");
        assert!(jit.is_kernel_verified(h), "{name}");
    }
}

#[test]
fn an_operand_if_installs_through_the_chain() {
    let mut s = TermStore::new();
    let h = crate::support::samples::source(&mut s, r"\a b. 1 + (if a < b then a else b)");
    assert!(!crate::proof::gate::in_fragment(&s, h, 2));
    let mut jit = JitEngine::new();
    for args in [[1, 2], [5, 3], [-4, -4]] {
        assert_eq!(jit.apply(&s, h, &args), eval::apply_term(&s, h, &args), "args={args:?}");
    }
    assert_eq!(jit.stats.compiled, 1);
}
