## 70. Stage 3b: a scope's parameters are free levels

Plan Tasks 5-8. A scope's parameters are `Expr::Free(level)`s from
`Postulates::bind`, and `close` abstracts them into binders. `Postulates`
now holds `globals` (only ever growing), the live parameters, the next
level and the open-scope count. Proof records carry `globals: Globals`.
The `Var`-local path, `close_pi`/`close_lam`, and every truncation are
gone.

**What was built.**
- `bind(ty)` checks `ty` against the globals and live parameters
  (`infer_open`) and returns a fresh level. Levels never go back, so a
  `Free` leaked from one scope can't be captured by a sibling's `close`;
  the kernel rejects it ("escaped its scope").
- `close` abstracts its scope's levels with `abstract_frees`, which skips
  any subterm whose cached `free` is below the scope's first level and
  memoises shared nodes by (pointer, depth). Without the memo, a
  30-deep doubling DAG was walked as its billion-leaf tree; with it the
  result keeps 93 nodes (`close_is_linear_in_the_dag_of_a_shared_body`).
- `check_open` checks a term mentioning live parameters by abstracting
  them into a kernel `Ctx`. Only `debug_assert_has_type` uses it; every
  final check passes an empty context, so a leaked parameter fails.
- Scopes must close innermost-first, and `push` panics while one is
  open: a missed `push`→`bind` conversion can't become a silent axiom.

**What the migration found.** 45 lib tests panicked at the new `push`
assertion before the conversion, and none after. No parameter escaped
its scope. `Anchored` never shifts anything any more (a probe showed
it), so stage 4 can delete it. `fib(16)`'s DAG is 10,466 nodes, 0.3%
fewer than 3a's, from `abstract_frees` keeping shared results shared.

**Failure mode.** `push`'s checks are `assert!`s, in release too. A lazy
postulate (`ite_clo_ref`, `clo_ty`, ...) first used inside a scope now
panics instead of going stale, and that panic reaches the JIT's
`kernel_verify`, which has no `catch_unwind`. The closure priming
(`prime_closure_postulates`) prevents it on every corpus and fuzz path;
stage 4 must relax the panic if it removes the priming.

**Cost.** None; 3b is faster. A/B of e273fcc vs d8dff3f (`target/ab3b`,
10 fib pairs and 5 proof-bench pairs, clean only, RTP off, 2026-09-27).
`fib(16)`: build 4.18 → 4.26 ms and check 2.74 → 2.76 ms best, within
noise. The µs-scale proofs got 20-29% faster (`straight_line_refl` 10.1 →
7.5 µs), the large ones 0-4%. So `bind`'s release `infer` stays: whatever
it costs is less than what 3b saved, likely 3a's split of the context into
globals and a local `Ctx` at every check (not profiled). Across stage 3
(576f5fe (unpublished) → d8dff3f), large proofs are 44-58% faster and the µs-scale ones
still 51-83% slower, from §69's push checks.

