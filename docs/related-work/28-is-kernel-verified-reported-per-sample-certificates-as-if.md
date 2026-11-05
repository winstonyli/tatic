## 28. `is_kernel_verified` reported per-sample certificates as if they covered every input -- found and fixed

Following §27's own parting note, the first concrete piece of that
deeper issue turned out to be separable and small. `jit.rs`'s
`kernel_verify` returned a plain `bool`, but its five strategies fall
into two epistemically different classes:

- `prove_pure_expr`, `prove_closure_expr`, `prove_tail_recursive_universal`
  produce **one theorem covering every input**.
- `prove_tail_recursive_call` and `prove_closure_expr_instance` produce a
  certificate **per concrete call**, run once for each vector in
  `sample_arg_vectors` -- precisely the finite battery `verify()` already
  checked against the interpreter.

Collapsing both into `true` meant `is_kernel_verified` -- and the REPL
line printed after every evaluation -- claimed "kernel-checked
equivalence proof" for a call whose arguments no proof had ever seen.
The test suite contained a live instance of exactly that: a term in the
inconsistent-arity curried-dispatch family served compiled at `100` and
`-7`, neither of which is in `SAMPLE_ARGS` (`[0, 1, 2, 3, 5, -1, -3, 7,
20]`), with `assert!(jit.is_kernel_verified(top))` passing on the
strength of certificates at nine *other* points.

Fixed by replacing the bool with a three-way `ProofStrength`
(`Universal` / `Samples` / `None`), returned by `kernel_verify`, stored
on `CacheEntry::Compiled`, and exposed as `JitEngine::proof_strength`.
`is_kernel_verified` now means `Universal` specifically; the REPL prints
"only at the sampled inputs" for the weaker class rather than a flat
"true".

One subtlety worth recording: at arity 0 the sample battery *is* the
entire input space -- `sample_arg_vectors(0)` is a single empty vector
because there is exactly one possible call -- so a per-call certificate
there really does cover every input, and `kernel_verify` classifies it
`Universal`. Without that, the arity-0 members of the same
curried-dispatch family would have been under-reported, which is the
mirror-image error of the one being fixed. Three of the five tests that
initially failed the stricter classification were arity-0 and passed
again unchanged once this was added; the two that remained are the
genuine arity-1 cases described above, now asserting
`ProofStrength::Samples` explicitly with a comment naming why.

Nothing in `Stats` changed: `kernel_proofs_checked` still counts any
kernel proof regardless of strength, which is what it always meant.

Verify-teeth: temporarily made the per-sample classification return
`Universal` at every arity (collapsing the distinction back) and
confirmed the two arity-1 tests fail, then restored it and confirmed they
pass. Full validation green afterward: `cargo build --all-targets`,
`cargo clippy --all-targets`, `cargo test --lib --bins` (190/190), all
four fuzzers at release, and the release demo (all nine demo terms are in
the universal fragment, so every one still reports `true`).

### Terminology: these are not "translation validation"

Fixed alongside the above, since it was the same overstatement in prose
rather than in code. `proof.rs`'s module docs, `jit.rs`'s, `benches/
proofs.rs`'s and three places in `README.md` all described
`prove_tail_recursive_call` as *translation validation*. In the
literature that term means validating one **compilation**: the checker
runs once per compiled program, and when it succeeds the compiled
program is correct *for every input* (Pnueli et al.; Necula; Tristan &
Leroy's verified validators, POPL'08, whose register-allocation
descendant ships in mainline CompCert). What `prove_tail_recursive_call`
validates is one **execution** -- a single concrete `(term, args)` trace
-- which is a result-checking / certifying-computation regime instead.

The worst instance was README's "translation validation is inherently
per-call", which is false about the technique and made tatic's own
limitation look intrinsic rather than self-imposed. All six sites now
say "per-execution" and name the distinction; no function was renamed
(the blast radius isn't worth it, and the docs now carry the correction
at every entry point).

The practical consequence, and the reason this is worth more than a
wording nit: *per-compilation validation is a rung tatic does not
currently occupy at all*, and it sits exactly between "sample and hope"
and option 2's kernel work.

### Prior art worth knowing before either option is started

- **DDEC** (Sharma, Schkufza, Churchill, Aiken, OOPSLA'13) infers a
  simulation relation *from test-run data*, then discharges it with a
  solver -- sound because insufficient data makes the proof fail, never
  pass. That is tatic's two ingredients wired the other way round:
  sampling as heuristic, proof as gate. Adopting the structure does not
  require adopting the solver (which would trade a small kernel for an
  SMT TCB), but the discharge step still needs the kernel to be able to
  *state* the relation -- which is where §14's `Sigma` returns for the
  closure family specifically, and only for it.
- **TurboTV** (Heo et al., ICSE'24) is per-compilation translation
  validation for V8's TurboFan, via an SMT encoding of its IR with a
  staged decomposition. Evidence that per-compilation TV is tractable for
  a real JIT -- and it validates IR-to-IR, with the gap between its model
  and the real engine stated as a limitation, exactly as here.
- **CompCert's actual bug history** is the strongest argument about where
  to spend next. ~90% of its algorithms are proved; the unverified
  remainder is elaboration, pre-simplification, assembling and linking.
  Csmith (Yang et al., PLDI'11) found no middle-end wrong-code bugs in
  CompCert at all -- the wrong-code bugs it did find were in the code
  that expands and prints assembly instructions, attributed to operand-
  ordering tedium and absent printer unit tests. The analogue here is
  exact: `denote` vs `compile_node` is the modeling gap and WAT emission
  is the printer, and no kernel proof tatic can build reaches either.

  A first pass here proposed "extend `compile_fuzz` to differentially
  test `denote` against `compile_node`" as the cheap answer. It isn't
  available as stated, and the reason is worth recording so nobody
  re-proposes it: `compile_node` writes WAT into a `&mut String` while
  `denote` builds a kernel `Expr`, so there is no common form to diff;
  and `denote`'s output cannot be *evaluated* into one either, because
  `Int` and its operators are postulated rather than computing -- that
  is precisely why the proofs are `refl` on structure. The two
  derivations are hand-written twins that can only be compared by
  reading them. The tractable version is therefore structural
  unification, not testing: factor one traversal with two backends, so
  drift between them is impossible by construction rather than
  detectable after the fact.

  *Corrected by §33:* that overclaims. There is no single `denote` to
  pair with `compile_node` -- five denoters implement different proof
  methods -- and drift comes in two kinds. Which *case* a term falls
  into can be shared, and now is (`compile::classify`). What each case
  *means* -- Wasm instructions on one side, kernel terms on the other --
  is two meanings by nature; no refactor makes that drift impossible,
  and only something that reads the emitted WAT (a per-compilation
  validator) reaches it.
- **Verified-JIT calibration**: Myreen (POPL'10) verified a JIT to x86 in
  HOL4 including an instruction-cache model and self-modifying code;
  Barriere, Blazy, Fluckiger, Pichardie & Vitek (POPL'21) verified
  speculation and deoptimization in CoreJIT over a CompCert-RTL-like IR.
  Both verify a compiler *model*, with extraction closing model ->
  implementation. tatic has no extraction story -- `compile.rs` emits WAT
  by hand -- so that last step would be new work, not a port.
- **If the target semantics is ever wanted for real**: WasmCert-Coq and
  WasmCert-Isabelle (Watt et al., FM'21) mechanise Wasm 1.0/2.0 with
  verified executable interpreters, and found genuine spec bugs doing it.

**Still open at the time this was written.** The section above is an
honesty fix, not a soundness fix: execution was unchanged, and
`compile_verify_and_apply` still installed and served a compiled form on
`verify()`'s finite battery alone whatever `proof_strength` said. Option
1 below has since been taken -- see §29. Options 2 and 3 remain open, and
the closing paragraph about the modeling gap still stands in full.

1. **Gate on `Universal`.** Serve compiled code only for terms carrying a
   theorem covering every input; interpret everything else. Small diff,
   sound, but it withdraws the JIT from the entire `Samples` family --
   the inconsistent-arity curried-dispatch shapes `compile.rs` went to
   real trouble to support.
2. **Widen the universal fragment** to cover those shapes, so the
   `Samples` fallbacks stop being load-bearing. This was first written up
   as splitting into a cheap tail-recursive half and an expensive closure
   half; a measurement says otherwise. Instrumenting both per-sample
   returns in `kernel_verify` across the full lib suite: the
   `prove_tail_recursive_call` branch (step 4) fires **zero** times, and
   the `prove_closure_expr_instance` branch (step 5) fires **six** --
   `prove_tail_recursive_universal` already covers every tail-recursive
   shape the corpus contains. So there is no demonstrated cheap half:
   every `Samples` result comes from the closure / inconsistent-arity
   family, which is exactly the `Sigma` / dependent-sum discussion in §14
   and the arity-polymorphism findings in §9.

   That measurement left a separate question open -- is step 4
   *unreachable* or merely *untested*? -- and it has since been settled:
   **unreachable through the JIT**, for a specific and slightly
   surprising reason.

   Step 4 is genuinely more permissive than step 3 in exactly one place,
   the `If` condition. `classify_tree` requires a direct comparison
   (`Lt`/`Le`/`Eq`); `classify_step` imposes nothing, since it just
   evaluates whatever is there against the concrete arguments. But
   `compile::compile_cond` imposes *precisely* `classify_tree`'s
   restriction -- its `cmp_instr(op)?` fails for anything else -- so a
   term living in that gap never compiles, and `kernel_verify` never runs
   on it. Step 4's extra reach lies entirely outside the compilable
   fragment. Every other way `build_universal` can decline where step 4
   might not is closure-related (`infer_closure_arities`, `flatten_tree`'s
   leaf coverage, the `denote_closure_typed` stages), and step 4's own
   `denote` is arithmetic-only, so it declines those too.

   Pinned by `proof::tests::
   the_relational_steps_extra_reach_lies_entirely_outside_the_compilable_fragment`,
   which builds `rec f n = if (n - 1) then f(n - 1) else 42` -- tail
   recursive, terminating, non-comparison condition -- and asserts all
   three halves at once: `prove_tail_recursive_call` accepts it,
   `prove_tail_recursive_universal` declines it, and `try_compile`
   declines it. The two restrictions are load-bearing *as a pair*, and
   the test fails the moment either is relaxed without the other.

   Verify-teeth for that test also surfaced something worth noting on its
   own: relaxing `classify_tree` alone (adding `Sub` to the accepted
   condition ops) makes `prove_tail_recursive_universal` happily build a
   proof -- even though the `Ev` gating argument depends on a condition
   denoting only to `0` or `1`, which a `Sub` does not. So
   `classify_tree`'s comparison check is a soundness guard, not just a
   scope line, and nothing else was pinning it.

   Step 4 was **not** deleted. It costs nothing while unreached (tried
   only after step 3 declines), removing it would silently downgrade any
   future shape that does reach it from `Samples` to `None`, and the test
   above now announces the moment the situation changes. Deleting it is
   the right call only once the pair of restrictions is deliberately
   decoupled.
3. **Build a per-compilation validator** -- the rung the prior-art
   section above shows tatic doesn't occupy. Sampling infers the
   candidate relation, the kernel proof decides installation (DDEC's
   structure). This converts `verify()` from load-bearing to advisory
   without needing the universal fragment widened first, and is the
   option the literature supports best.

The `ProofStrength` split is a prerequisite for all three: option 1 is
now a one-line predicate change at the `CacheEntry::Compiled` insertion
site, and options 2 and 3 have a precise success criterion (the
`Samples` variant stops being reachable for the shapes in question).

None of the three touches the `denote`-vs-`compile_node` modeling gap or
WAT emission, which -- per CompCert's own bug history above -- is where
the empirically dangerous class lives. The cheapest genuinely
risk-reducing work available is orthogonal to all of them: extend
`compile_fuzz` to differentially check the two derivations structurally,
not just their outputs.

