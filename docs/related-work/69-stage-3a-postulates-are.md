## 69. Stage 3a: postulates are constants

The builder refers to postulates by `Expr::Const(level)`, as §64's spike
did, so a proof term's sharing survives every later push. Plan:
`docs/superpowers/plans/2026-09-26-stage-3-builder-constants-and-free-params.md`
(Tasks 1-4).

**What was built.**
- Scopes and checks go through `Postulates`: `open`/`close`/`abandon`
  with a `Binder`, and `check`/`infer`, which call `check_in`/`infer_in`.
  No builder code truncates the context or calls the kernel on it
  directly. Proof records are checked with `check_in(&globals, &Ctx::new())`.
- `get(pos)` is `Const(pos)` for a postulate. In 3a a scope's own entries
  were still `Var`s, and a check split the vector into globals and a
  local `Ctx`.
- `push` checks every entry: a postulate's type is closed (O(1) from the
  cached ranges) and infers to a `Sort` against the globals before it.
  That also rejects a reference to itself or a later postulate ("unknown
  constant"), so the plan's separate ordering walk was dropped: it
  repeated what `infer` checks, and walked the type as a tree, where
  `infer` is memoised on the DAG. This check is what §68's bug lacked.

**Decisions** (user-approved, 2026-09-26):
- 3a then 3b, measured apart, rather than one change: 3a carries the
  payoff in a small diff, and 3b's A/B then shows the safety change alone.
- `push` checks its type always, not in debug builds only, and is
  measured: a malformed global otherwise sits unchecked until a claim
  uses it (§68), as Lean's `add_decl` and Coq's `infer_definition` refuse.

**Result.** `fib(16)`'s instance proof: DAG 10,501 nodes, as the spike
had it (265k before); build 4-9 ms and check 3-6 ms on the release probe
under load, from about 0.8 s together before (§66). The fib DAG test now
compares fib(8) with fib(16) (`2*large < 5*small`), and
`fib16_instance_proof_builds_and_checks_quickly` guards it at 3 s (188 ms
in a debug build).

**Cost.** A/B of 576f5fe (unpublished) vs e273fcc (`target/ab3a`, 10 fib pairs and 5
proof-bench pairs, clean only, RTP off, 2026-09-27). `fib(16)`: DAG
227,157 → 10,501 nodes, build 136.9 → 4.2 ms best (174.5 → 4.9 median),
check 153.7 → 2.8 ms best (194.2 → 3.1 median). Universal and instance
proofs 43-57% faster (`universal_x1` 783 → 444 µs, the if-between-closures
instance proof 3685 → 1596 µs). The µs-scale proofs got 87-155% slower
(`straight_line_refl` 4.7 → 10.1 µs), a fixed ~5-10 µs a proof. A probe
at d8dff3f found the cause: `push`'s `infer`, run on every postulate.
`straight_line_refl` pushes 14 postulates, whose checks take 4.0 of its
8.2 µs; `ArithPostulates::new` alone (10 pushes) takes 4.8 µs, and every
proof builds one.

**Prelude cache.** `ArithPostulates::new` builds and checks its prelude
once per thread and clones it (a8238e6). A/B of ab4fc7d vs a8238e6
(`target/abA`, 5 pairs, RTP off, 2026-09-28; best-of):
`straight_line_refl` 8.80 → 3.67 µs (−58%), `gcd_relational_single_call`
10.8 → 5.3 µs (−51%), `relational_x1/x5/x10` −54%/−48%/−52%, the closure
fragment −31% to −53%, the non-tail closure-recursion instance proofs
−26% and −38%. The universal and over-application proofs (0.4-1.8 ms)
moved within ±9%. That removes the fixed cost above and lands under the
4.7 µs `straight_line_refl` took before this stage (above; a different
run, so indicative).

**What the flip broke.** Only a test: `kernel_soundness_fuzz`'s
globals-vs-context differential built both sides from the builder's
context, which is now `Const`s. It builds its `Var` side by hand
(`build_var_ctx`, `to_vars`), so the two kernel paths are compared again.

