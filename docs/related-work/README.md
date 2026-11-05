# Related work

> Note: the specs and plans cited below are in `docs/superpowers/` (some superseded or deleted ones only in git history, as each pointer says); the experiment scripts under `scripts/experiments/` are not tracked in this repository.

> Note (2026-10-26, "CU3"): `prove_tail_recursive_instance` and the concrete-witness engine only it used (`build_ev_witness`, `eval_and_prove*`, `resolve_closure_shape_to_leaf`, `build_clo_call_bridge`, the `*_eq_ref` computation-rule axioms, `assume_prim_fact`/`assume_ite_fact`, `ClosureRhsShape`, `src/proof/instance.rs`) were deleted; `build_universal` is now `prove_tail_recursive_universal` itself. Sections below that describe them are the record of what they did, not of current code. Per-call proofs come from `prove_closure_expr_instance`.

This document is not a design proposal — it's a record of the formal-logic
and compiler-runtime landscape surveyed while scoping possible future work
(see `PARKED.md`, and `docs/types.md` for what this
project's own type system actually is), kept for whoever picks one of
those directions up next. Every connection below is drawn deliberately:
either "this is the established solution to a problem tatic currently has
no good answer for" or "this is a different point on the same tradeoff
tatic itself makes."

One file per section, named by its `§` number, which every cite in code and docs uses: `§37` is `37-*.md`. Sections marked (survey) cover the wider landscape; the rest are implementation notes on tatic itself, in the order they were written.

- [01-where-tatic-s-own-kernel.md](01-where-tatic-s-own-kernel.md): 1. Where tatic's own kernel sits (survey)
- [02-the-historical-root-combinatory.md](02-the-historical-root-combinatory.md): 2. The historical root: combinatory logic (survey)
- [03-guarded-recursion-the-generic-tool-ev-reinvents-ad.md](03-guarded-recursion-the-generic-tool-ev-reinvents-ad.md): 3. Guarded recursion — the generic tool `Ev` reinvents ad hoc (survey)
- [04-higher-order-abstract-syntax-logical-frameworks-the-fix-for.md](04-higher-order-abstract-syntax-logical-frameworks-the-fix-for.md): 4. Higher-order abstract syntax / logical frameworks — the fix for this session's own recurring bug class (survey)
- [05-self-types-cedille-the-same-postulate-your-way-to-power.md](05-self-types-cedille-the-same-postulate-your-way-to-power.md): 5. Self-types / Cedille — the same "postulate your way to power" tradeoff, one level down (survey)
- [06-observational-type-theory-setoid-type-theory-equality.md](06-observational-type-theory-setoid-type-theory-equality.md): 6. Observational Type Theory / Setoid Type Theory — equality without the heavy machinery (survey)
- [07-homotopy-type-theory-cubical-type-theory-the-maximal-end-of.md](07-homotopy-type-theory-cubical-type-theory-the-maximal-end-of.md): 7. Homotopy Type Theory / Cubical Type Theory — the maximal end of the same axis (survey)
- [08-quantitative-type-theory-usage-tracking-not-arity.md](08-quantitative-type-theory-usage-tracking-not-arity.md): 8. Quantitative Type Theory — usage tracking, not arity tracking (survey)
- [09-the-arity-polymorphism-investigation-compile-rs-findings.md](09-the-arity-polymorphism-investigation-compile-rs-findings.md): 9. The arity-polymorphism investigation (compile.rs) — findings worth keeping
- [10-making-kernel-with-shift-cache-automatic-and-why-locally.md](10-making-kernel-with-shift-cache-automatic-and-why-locally.md): 10. Making `kernel::with_shift_cache` automatic — and why locally-nameless wasn't the fix
- [11-deriving-clo-k-instead-of-postulating-it-a-real-primitive.md](11-deriving-clo-k-instead-of-postulating-it-a-real-primitive.md): 11. Deriving `Clo_k` instead of postulating it — a real primitive-count win, confirmed by a standalone prototype
- [12-clo-eq-ref-s-clo-typed-parameter-decline-larger-than-it.md](12-clo-eq-ref-s-clo-typed-parameter-decline-larger-than-it.md): 12. `clo_eq_ref`'s `Clo`-typed-parameter decline: larger than it looked, investigated not attempted
- [13-a-call-shaped-iftree-leaf-targeting-a-further-iftree.md](13-a-call-shaped-iftree-leaf-targeting-a-further-iftree.md): 13. A `Call`-shaped `IfTree` leaf targeting a further `IfTree` — already worked, confirmed rather than built
- [14-adding-sigma-dependent-sums-as-a-fifth-kernel.md](14-adding-sigma-dependent-sums-as-a-fifth-kernel.md): 14. Adding `Sigma` (dependent sums) as a fifth kernel primitive
- [15-why-over-application-proofs-cost-1000x-a-plain-arithmetic.md](15-why-over-application-proofs-cost-1000x-a-plain-arithmetic.md): 15. Why over-application proofs cost ~1000x a plain arithmetic call — investigated to root cause
- [16-div-s-compiled-and-interpreted-semantics-silently-disagreed.md](16-div-s-compiled-and-interpreted-semantics-silently-disagreed.md): 16. `Div`'s compiled and interpreted semantics silently disagreed at one input — found and fixed
- [17-a-structural-verification-coverage-gap-in-sample-arg.md](17-a-structural-verification-coverage-gap-in-sample-arg.md): 17. A structural verification-coverage gap in `sample_arg_vectors` for arity >= 3 -- found and fixed
- [18-a-mismatched-call-arity-could-permanently-poison-the-jit.md](18-a-mismatched-call-arity-could-permanently-poison-the-jit.md): 18. A mismatched call arity could permanently poison the JIT cache -- found and fixed
- [19-eval-dyn-direct-call-s-cross-combinator-inlining-could-grow.md](19-eval-dyn-direct-call-s-cross-combinator-inlining-could-grow.md): 19. `eval_dyn_direct_call`'s cross-combinator inlining could grow the native stack without bound -- found and fixed
- [20-eval-dyn-direct-call-wastefully-evaluated-arguments-before.md](20-eval-dyn-direct-call-wastefully-evaluated-arguments-before.md): 20. `eval_dyn_direct_call` wastefully evaluated arguments before a cheap, args-independent scoping check -- found to be a crash risk, not just a performance one
- [21-try-compile-generated-a-curried-stage-chain-for-every.md](21-try-compile-generated-a-curried-stage-chain-for-every.md): 21. `try_compile` generated a curried stage chain for every registered combinator, whether or not anything ever dispatched through it -- found and pruned
- [22-kernel-rs-s-typing-context-was-cloned-wholesale-at-every.md](22-kernel-rs-s-typing-context-was-cloned-wholesale-at-every.md): 22. kernel.rs's typing context was cloned wholesale at every binder -- found and switched to a persistent structure
- [23-jit-rs-s-kernel-verify-recomputed-the-same-sample-battery.md](23-jit-rs-s-kernel-verify-recomputed-the-same-sample-battery.md): 23. jit.rs's kernel_verify recomputed the same sample battery three times, and invoke() paid a heap allocation on every call -- found and fixed
- [24-proof-rs-s-closures-section-doc-comment-still-described-the.md](24-proof-rs-s-closures-section-doc-comment-still-described-the.md): 24. proof.rs's closures-section doc comment still described the pre-migration opaque-Clo/apply_k design -- found and swept
- [25-two-smaller-stale-doc-comments-compile-rs-kernel-rs-found.md](25-two-smaller-stale-doc-comments-compile-rs-kernel-rs-found.md): 25. Two smaller stale doc comments (compile.rs, kernel.rs) -- found and fixed
- [26-term-rs-s-content-hash-under-sized-its-scratch-buffer-found.md](26-term-rs-s-content-hash-under-sized-its-scratch-buffer-found.md): 26. term.rs's content_hash under-sized its scratch buffer -- found and fixed
- [27-pap-ref-mistyped-a-partial-application-when-the-root-s-own.md](27-pap-ref-mistyped-a-partial-application-when-the-root-s-own.md): 27. pap_ref mistyped a partial application when the root's own saturated call itself returns a closure -- found and fixed
- [28-is-kernel-verified-reported-per-sample-certificates-as-if.md](28-is-kernel-verified-reported-per-sample-certificates-as-if.md): 28. `is_kernel_verified` reported per-sample certificates as if they covered every input -- found and fixed
- [29-the-installation-gate-now-requires-a-universal-theorem.md](29-the-installation-gate-now-requires-a-universal-theorem.md): 29. The installation gate now requires a universal theorem -- option 1 from §28, taken
- [30-cargo-bench-bench-execution-died-of-a-stack-overflow-found.md](30-cargo-bench-bench-execution-died-of-a-stack-overflow-found.md): 30. `cargo bench --bench execution` died of a stack overflow -- found and fixed
- [31-the-kernel-s-recursion-is-stack-safe-stacker-not-a-hand.md](31-the-kernel-s-recursion-is-stack-safe-stacker-not-a-hand.md): 31. The kernel's recursion is stack-safe -- `stacker`, not a hand conversion
- [32-eval-dyn-through-the-same-grow-three-budgets-become.md](32-eval-dyn-through-the-same-grow-three-budgets-become.md): 32. `eval_dyn` through the same `grow`; three budgets become one
- [33-one-classifier-for-the-compiler-and-every-proof.md](33-one-classifier-for-the-compiler-and-every-proof.md): 33. One classifier for the compiler and every proof walker
- [34-an-ir-between-term-analysis-and.md](34-an-ir-between-term-analysis-and.md): 34. An IR between term analysis and WAT
- [35-translation-validation-every-compilation-is-decompiled.md](35-translation-validation-every-compilation-is-decompiled.md): 35. Translation validation: every compilation is decompiled back
- [36-lambda-lifting-of-directly-called.md](36-lambda-lifting-of-directly-called.md): 36. Lambda lifting of directly called combinators
- [37-closure-specialisation-by-certificate-checked.md](37-closure-specialisation-by-certificate-checked.md): 37. Closure specialisation by certificate-checked βv
- [38-the-jit-installed-ill-typed-code-that-goes-wrong-only-off.md](38-the-jit-installed-ill-typed-code-that-goes-wrong-only-off.md): 38. The JIT installed ill-typed code that goes wrong only off the samples -- found and fixed
- [39-four-leftovers-from-37-s-review-found-and.md](39-four-leftovers-from-37-s-review-found-and.md): 39. Four leftovers from §37's review -- found and fixed
- [40-closures-of-the-wrong-arity-a-compiler-hole-the-proof-gate.md](40-closures-of-the-wrong-arity-a-compiler-hole-the-proof-gate.md): 40. Closures of the wrong arity: a compiler hole the proof gate closes
- [41-fuzzing-branches-that-go-wrong-off-the.md](41-fuzzing-branches-that-go-wrong-off-the.md): 41. Fuzzing branches that go wrong off the samples
- [42-proofs-about-closure-arguments-the-jit-never-passes-found.md](42-proofs-about-closure-arguments-the-jit-never-passes-found.md): 42. Proofs about closure arguments the JIT never passes -- found and fixed
- [43-how-other-compilers-call-a-closure-of-unknown.md](43-how-other-compilers-call-a-closure-of-unknown.md): 43. How other compilers call a closure of unknown arity (survey)
- [44-the-type-systems-tatic-has-the-one-it-would-ideally-have.md](44-the-type-systems-tatic-has-the-one-it-would-ideally-have.md): 44. The type systems tatic has, the one it would ideally have, and ways between
- [45-typing-shared-subterms-once-and-a-type-safety-fuzz-which.md](45-typing-shared-subterms-once-and-a-type-safety-fuzz-which.md): 45. Typing shared subterms once, and a type-safety fuzz -- which found a crash in the occurs check
- [46-g2-in-depth-where-the-type-notions-have-to-agree-and-how.md](46-g2-in-depth-where-the-type-notions-have-to-agree-and-how.md): 46. G2 in depth: where the type notions have to agree, and how other systems get one source
- [47-a-tree-size-gate-on-try.md](47-a-tree-size-gate-on-try.md): 47. A tree-size gate on `try_compile`
- [48-where-a-shared-term-s-jit-cost-goes-mostly-the-kernel-and-a.md](48-where-a-shared-term-s-jit-cost-goes-mostly-the-kernel-and-a.md): 48. Where a shared term's JIT cost goes: mostly the kernel, and a lost pointer cache
- [49-keeping-whnf-s-arguments-and-denoting-shared-subterms.md](49-keeping-whnf-s-arguments-and-denoting-shared-subterms.md): 49. Keeping `whnf`'s arguments, and denoting shared subterms once
- [50-design-note-making-the-kernel-s-infer-linear-in-the.md](50-design-note-making-the-kernel-s-infer-linear-in-the.md): 50. Design note: making the kernel's `infer` linear in the DAG
- [51-subst-top-skips-an-argument-its-body-doesn-t.md](51-subst-top-skips-an-argument-its-body-doesn-t.md): 51. `subst_top` skips an argument its body doesn't use
- [52-where-an-instance-proof-s-time-goes-eager-substitution-and.md](52-where-an-instance-proof-s-time-goes-eager-substitution-and.md): 52. Where an instance proof's time goes: eager substitution, and a shift cache that no longer pays
- [53-subst-top-substitutes-in-one.md](53-subst-top-substitutes-in-one.md): 53. `subst_top` substitutes in one pass
- [54-removing-the-shift.md](54-removing-the-shift.md): 54. Removing the shift cache
- [55-where-an-instance-proof-s-time-goes-after-53-and.md](55-where-an-instance-proof-s-time-goes-after-53-and.md): 55. Where an instance proof's time goes after §53 and §54
- [56-def-eq-answers-equal-sides-without.md](56-def-eq-answers-equal-sides-without.md): 56. `def_eq` answers equal sides without normalising
- [57-def-eq-compares-weak-head-normal-forms-not-full-normal.md](57-def-eq-compares-weak-head-normal-forms-not-full-normal.md): 57. `def_eq` compares weak head normal forms, not full normal forms
- [58-subst-top-drops-its-is-var-free.md](58-subst-top-drops-its-is-var-free.md): 58. `subst_top` drops its `is_var_free` guard
- [59-whnf-keeps-a-stuck-term-s-own.md](59-whnf-keeps-a-stuck-term-s-own.md): 59. `whnf` keeps a stuck term's own pointers
- [60-where-an-instance-proof-s-time-goes-after-56-to.md](60-where-an-instance-proof-s-time-goes-after-56-to.md): 60. Where an instance proof's time goes after §56 to §59
- [61-def-eq-remembers-the-pairs-found.md](61-def-eq-remembers-the-pairs-found.md): 61. `def_eq` remembers the pairs `==` found unequal
- [62-the-witness-is-built-at-one-context-depth-so-memo-hits.md](62-the-witness-is-built-at-one-context-depth-so-memo-hits.md): 62. The witness is built at one context depth, so memo hits share
- [63-infer-memoises-shared-nodes-by-node-context.md](63-infer-memoises-shared-nodes-by-node-context.md): 63. `infer` memoises shared nodes by (node, context id)
- [64-design-note-constants-free-parameters-and-cached-loose.md](64-design-note-constants-free-parameters-and-cached-loose.md): 64. Design note: constants, free parameters, and cached loose ranges
- [65-nodes-cache-their-loose-variable.md](65-nodes-cache-their-loose-variable.md): 65. Nodes cache their loose-variable range
- [66-an-idle-re-baseline-and.md](66-an-idle-re-baseline-and.md): 66. An idle re-baseline, and mimalloc
- [67-stage-2-constants-and-free-parameters-in-the.md](67-stage-2-constants-and-free-parameters-in-the.md): 67. Stage 2: constants and free parameters in the kernel
- [68-the-kernel-checks-its-claim-which-caught-an-ill-typed.md](68-the-kernel-checks-its-claim-which-caught-an-ill-typed.md): 68. The kernel checks its claim, which caught an ill-typed `Ev`
- [69-stage-3a-postulates-are.md](69-stage-3a-postulates-are.md): 69. Stage 3a: postulates are constants
- [70-stage-3b-a-scope-s-parameters-are-free.md](70-stage-3b-a-scope-s-parameters-are-free.md): 70. Stage 3b: a scope's parameters are free levels
- [71-where-a-cold-jit-call-s-time.md](71-where-a-cold-jit-call-s-time.md): 71. Where a cold JIT call's time goes
- [72-stage-4-what-stage-3-made.md](72-stage-4-what-stage-3-made.md): 72. Stage 4: what stage 3 made unnecessary
- [73-should-the-jit-prove-instances-of-a-theorem-it-already.md](73-should-the-jit-prove-instances-of-a-theorem-it-already.md): 73. Should the JIT prove instances of a theorem it already checked?
- [74-baseline-at-0c3c2fb-verify-samples-capped-at-12-stage-4.md](74-baseline-at-0c3c2fb-verify-samples-capped-at-12-stage-4.md): 74. Baseline at 0c3c2fb (verify samples capped at 12, stage 4, prelude cache, `prove_instances` off)
- [75-relational-compilation-rupicola-as-the-shape-of-found-to-be.md](75-relational-compilation-rupicola-as-the-shape-of-found-to-be.md): 75. Relational compilation (Rupicola) as the shape of "found to be equivalent" (survey)
- [76-search-guided-rewriting-what-prior-systems-verify-and-what.md](76-search-guided-rewriting-what-prior-systems-verify-and-what.md): 76. Search-guided rewriting: what prior systems verify, and what guides them (survey)
- [77-eager-versus-lazy-substitution-in.md](77-eager-versus-lazy-substitution-in.md): 77. Eager versus lazy substitution in kernels (survey)
- [78-can-normalization-be-eased-explicit-conversion-proof.md](78-can-normalization-be-eased-explicit-conversion-proof.md): 78. Can normalization be eased? Explicit conversion, proof irrelevance, observational, cubical, categorical views (survey)
- [79-stuck-spines-stayed-quadratic-after-59-the-spine-walks-2026.md](79-stuck-spines-stayed-quadratic-after-59-the-spine-walks-2026.md): 79. Stuck spines stayed quadratic after §59: the spine walks (2026-10-16)
- [80-the-infer-memo-s-key-was-quadratic-under-unused-binders.md](80-the-infer-memo-s-key-was-quadratic-under-unused-binders.md): 80. The infer memo's key was quadratic under unused binders (2026-10-16)
- [81-canonical-forms-for-bitwise-and-mixed-boolean-arithmetic.md](81-canonical-forms-for-bitwise-and-mixed-boolean-arithmetic.md): 81. Canonical forms for bitwise and mixed Boolean-arithmetic terms, and learning them (2026-10-22) (survey)
- [sources.md](sources.md): Sources
