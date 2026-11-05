## 68. The kernel checks its claim, which caught an ill-typed `Ev`

This closes §67's open item. `check_in` now infers `expected` to a `Sort`
before checking `e` against it, and `check`'s `Lam` rule infers the
annotation to one before comparing it with the Π's domain. That matches
Lean's `check_constant_val`/`infer_lambda` and Coq's `infer_definition`
(§67). Both are in the trusted kernel. `a_claim_that_isnt_a_type_is_rejected`
and `a_checked_lambdas_annotation_must_be_a_type` failed before the change,
and each fails again if its check is removed.

**What it caught.** Six closure-typed universal proofs failed the new
check (`a_closure_typed_loop_carried_parameter_gets_a_universal_proof`
and five others). Their statements were ill-typed, because `Ev`'s type
was:
- `build_universal` built `Ev : T_0 -> .. -> Int -> Sort(0)` by folding
  `arrow` over the domains, trusting `arrow`'s shift to keep the pieces
  consistent.
- The shift covers each new binder but not a push. `clo_ty(k)`'s first
  use pushes `ite_clo_ref(k)`, so every piece built before that call
  was one level stale.
- For parameters `(Int, Clo_1, Int)`, the result was `Π Int. Π Clo_1.
  Π #13. Π #14. Sort(0)` at depth 13. The last two domains named an
  arithmetic postulate instead of `Int`.
- Every proof still checked, since `check` compared each lambda's
  annotation with an equally malformed Π and never asked whether either
  was a type.
- The fix anchors each domain as it's resolved and re-resolves it once
  nothing more is left to push, as `env_ty` and `call_ref` already did.

**Why nothing noticed sooner.** A context entry is a postulate, and the
kernel never checks one. The ill-formed `Ev` sat in the context, and only
a claim that used it could expose it. Stage 3 removes this class of bug,
since a pushed `Const` shifts nothing. Its `push` is also the place to
infer each global's type to a `Sort`, once, which would have caught this
at the push.

**Cost.** A/B of fa6458d vs 8d24f07 (`scripts/quiet_ab`, clean pairs
only, Defender RTP off, 2026-09-26/27). `fib(16)`'s instance proof, 5
pairs: check best 133.6 → 147.3 ms (+10%), median 144.0 → 164.9 ms
(+14%); build unchanged. Proof benches (`target/ab/proofs2`, 6 base and 5
head clean runs; a first run with one clean base run agreed): universal
and instance proofs +11-30% on best (`universal_x1` 630 → 791 µs, the
loop-carried closure proof 954 → 1229 µs), the µs-scale ones +5-11% on
best and within noise on median. The claim checks cost what they check;
the universal proofs, with the most claims, pay the most.

