## 72. Stage 4: what stage 3 made unnecessary

Plan: `docs/superpowers/plans/2026-09-27-stage-4-remove-what-no-longer-pays.md`.
Spec: `docs/superpowers/specs/2026-09-25-kernel-constants-and-loose-ranges-design.md`,
"Stage 4: remove what no longer pays" (untrusted, Tasks 1-4).

**What was removed.**
- §62's prepass, `push_ev_facts`: the call in `instance_from_scaffold` and
  the ~40-line function itself (Task 1, d434088).
- The closure priming (Task 2, 1614bdf/47d50fb): 3 functions
  (`prime_closure_postulates`, `prime_direct_call`,
  `prime_closure_if_tree_leaves`), 2 loops in `build_universal`, 3
  remaining call sites into them, and 8 discarded-result priming calls
  (`mk_env_ref`/`clo_ty`) across 5 other functions — counted from
  `git show 1614bdf -- src/proof.rs`. `Postulates::push`'s scope-open
  assertion (kernel.rs) went with it, so §70's JIT panic path is gone: no
  push can panic for being inside a scope any more. Kept: the literal
  pre-pass loop in `clo_eq_ref_if_tree` (and its twins in `call_eq_ref` and
  `build_universal`) — `denote`'s `lit_ref` still expects every literal
  pre-postulated, unrelated to the panic mechanism being removed.
- `Anchored` and `Params` (Task 3, e3087fc/9f4f25e/30b7fd0): both types and their
  impls deleted. `Anchored::at` was already the identity on a closed term
  (§70's finding). `src/proof.rs` was 11,277 lines at the plan's base
  commit (ff5e79b (unpublished)), 10,410 now.

**Decision's cost, stated plainly.** `push` still asserts a pushed type is
closed, but no longer that no scope is open. A closed-typed local pushed by
mistake inside a scope no longer panics — it becomes an extra global that
`close` leaves alone.

**Measured.**
- Task 1: fib(16) DAG 10466 → 10466 (unchanged); best build+check
  9.4373 → 9.7930 ms (×1.038, 10 interleaved rounds), measured under
  ~53-55% CPU load from another session's job, Defender RTP off.
- Tasks 2-3: DAG stayed 10466 throughout; all gates (338 lib tests, clippy
  `-D warnings`, `kernel_soundness_fuzz`, `compile_fuzz`, `golden_wat`,
  `ir_fuzz`) passed at every step — these changes were comment/dead-code
  and type-erasure only, no proof-size change; the order globals are
  pushed in, and so `Const` numbering, may differ. The deleted
  `prime_closure_if_tree_leaves` pushed while iterating a
  `hashbrown::HashMap` (per-process seeded), so push order now follows
  the deterministic proof traversal.
- The push-check prelude cost (§69, ~4 µs/proof) is handled separately, by
  `ArithPostulates::new`'s thread-local prelude (a8238e6, outside this
  plan); its A/B is in §69.

**Cost.** A/B of ff5e79b (unpublished) vs bf52ba4 (`target/ab4`, RTP off, 2026-09-28;
clean runs only). `fib(16)`, 20 pairs on a quiet machine (5% CPU): DAG
10,466 → 10,466, build 3.83 → 3.58 ms best (4.25 → 4.06 median), check
2.56 → 2.54 ms best (2.75 → 2.85 median). A first 10-pair run overnight,
with another session's job on the machine, had only 3 clean head samples
and read 12-16% slower on best-of; the quiet run did not reproduce it.
Proof benches, 5 pairs: three of the four closure-fragment proofs got
21-28% faster (non-capturing 6.56 → 4.70 µs, partial application
7.87 → 5.89 µs; capturing −3%), the
non-tail closure-recursion instance proofs 18-19%, the over-application
instance proofs 7-10%. The rest moved within ±4% (`universal_x1` 432 →
433 µs). The cold JIT (`jit_cold_compile_and_verify`, 5 pairs) moved
between −3.2% and +0.7% best-of on all six terms.

**What changed in behaviour.**
- A push may happen while a scope is open (kernel.rs `Postulates::push`);
  it still asserts the pushed type is closed and infers to a `Sort`.
- Lazy postulates (`mk_env_ref`, `ite_clo_ref`, ...) push on first use
  with no priming pass and no panic risk from being inside a scope.
- Every site that held a resolved `Expr` across further pushes now just
  holds the `Expr`: a `Const` doesn't shift (§69), so `Anchored` had
  nothing left to do.

