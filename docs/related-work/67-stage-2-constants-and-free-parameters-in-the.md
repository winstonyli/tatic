## 67. Stage 2: constants and free parameters in the kernel

This builds stage 2 of §64: the kernel learns `Const` and `Free`, and
nothing produces either yet, so every answer is unchanged.

**What was built** (`src/kernel.rs`).
- `Expr::Const(l)`: global `l`, typed by `globals[l]` as is. A closed
  type has nothing to shift, so a `Const` means the same thing at every
  depth, and `shift` and `instantiate` leave it alone.
- `Expr::Free(l)`: a builder parameter by level. It is neutral in
  `whnf`, `nf` and `def_eq` (it matches only itself), so the structural
  helpers still work on open terms, and it never type-checks.
- `Node` gains `free`, one more than the largest `Free` level (0 if
  none), cached like `loose`. It fills the padding stage 1 left, so a
  heap node stays 72 bytes (`a_node_is_56_bytes` pins the 56-byte
  `Node<Expr>`).
- `pub type Globals = im::Vector<Expr>`, with `infer_in(globals, ctx, e)`
  and `check_in(globals, ctx, e, expected)`. `infer` and `check` keep
  their signatures and pass no globals, so `proof.rs` didn't change.

**Three decisions, and why.**
1. *`Globals` beside `Ctx`, not `Ctx { globals, locals }`.* The spec
   asked for a struct and also for unchanged callers, and those conflict:
   `proof.rs` uses `Ctx` as an `im::Vector` (`len`, `truncate`,
   `close_pi`'s iteration, `Postulates::push`). A separate vector gives
   the same guarantee, that a `Const` can never resolve to a binder the
   kernel pushed, and touches no caller. Stage 3 moves `Postulates` to
   `Globals` and its check sites to `check_in`.
2. *An explicit `g: &Globals` parameter* on the seven typing functions,
   not a field on `InferCache`. The cache is a memo; the rules read as
   "Σ; Γ ⊢ e" with Σ visible.
3. *`Free` is rejected at the door, not only at the leaf.* `infer` doesn't
   visit every subterm: `check`'s `Lam` rule compares the domain by
   `def_eq`, `WRec`'s `children_ty` is only compared, and nothing infers
   the expected type. A `Free` under a redex in any of them would reduce
   away unseen. So `infer_in` and `check_in` reject `e` (and `expected`)
   when `free_of` is nonzero, which is O(1); `ctx_lookup` rejects a
   context entry with a `Free`; and a global whose type has a `Free` or a
   loose `Var` is rejected when used.

The environment has the same trust as the context: nothing checks that
an entry is a type, and a constant is an axiom. The kernel checks only
that a global's type is closed. It doesn't check that the constants it
names are earlier ones: `globals = [Const(0)]` types `Const(0) :
Const(0)`. Stage 3's `Postulates::push` must enforce the ordering, as
§64 says.

**Mutations.** Each new test failed on the mutation its step named,
except two, each for a reason:
- `beta_leaves_const_and_free_alone` has no reachable mutation: stage
  1's fast path (`loose == 0`) returns before `shift` or `instantiate`
  reach a leaf's arm. It pins the behaviour for a future refactor.
- Storing `free` as a `u64` doesn't compile, rather than failing
  `a_node_is_56_bytes`; either way it can't land.

Removing `infer_in`'s door first broke no test only for want of one:
`infer` hands an `App`'s argument (and `Id`'s sides, `J`'s fields) to
`check`, whose `Lam` rule compares the domain by `def_eq` and never
infers it, so a `Free` hidden under a redex there reduced away and
`infer_in` returned `Ok`. The final review found it;
`a_free_is_rejected_everywhere` now covers it, and the door is
load-bearing in both entry points.

**The fuzzers** (`tests/kernel_fuzz.rs`, `tests/kernel_soundness_fuzz.rs`).
- `kernel_fuzz` generates `Const`s in and just past a four-entry
  environment whose last entry is deliberately open, and `Free`s; any
  term with a `Free` must come back `Err`.
- The soundness fuzzer's constant form: with the context's seven
  postulates as globals and candidates free to name any constant, nothing
  proves `Id(A, a, b)`; and mutants of valid proofs with a `Free`
  spliced in never check.
- A differential: 20,000 candidates, random or mutants of valid proofs,
  check against a claim in constant form exactly when they check in the
  original. 898 checked and 19,102 were rejected, with no disagreement.
- Kernel mutations the fuzzers catch: `const_type` resolving from the
  wrong end (the differential), a `Free` accepted with the doors removed
  (both `made_free` and the spliced-`Free` test), and `same_shape`
  ignoring a `Const`'s index (the differential, and the constant-form
  soundness test, which found `@5` accepted as a proof of
  `Id @0 @2 @3`).

**Measured.** Stage 2 claims no speedup: it adds one `max` per
`Rc::new`, one parameter per typing frame, and the O(1) doors. Base is
331a7bd (unpublished) (stage 1 with mimalloc), head is 8a13e5e; both built once and run
interleaved with `scripts/quiet_ab/` (§66), Defender real-time
protection off throughout.

`fib16_instance_proof_cost`, 10 clean pairs of 12 rounds, other
processes at 13 to 20%:

| | base best | base median | head best | head median | change, best | change, median |
|---|---|---|---|---|---|---|
| build | 128.7 ms | 140.7 ms | 130.4 ms | 143.1 ms | +1.3% | +1.7% |
| check | 131.6 ms | 139.3 ms | 122.7 ms | 143.6 ms | -6.8% | +3.0% |

Each side's slowest clean run was 16 to 32% above its best, so every
change is noise. The DAG is 227,157 nodes in every run, as in §66.

The proof benches, 5 clean pairs of 6 rounds, other processes at 4 to
15%: every bench's best within -1.3 to +1.0%, and every median within
-3.5 to +2.4%. Each is inside that bench's own spread (1.3 to 27%).

Stage 2 costs nothing measurable, so stage 3 starts from the same
baseline.

Two runner fixes came out of this: `pin.ps1` now resolves a relative
exe path, which `Process.Start` couldn't find, and `ab.sh` refuses a
directory that already has a `runs.log`, whose old rounds would count
toward the new run.

**Open (closed in §68): `check_in` trusts its claim.** `check_in` never infers
`expected`, and `check`'s `Lam` rule only compares the lambda's
annotation with the Π's domain, never inferring it to a `Sort`. So
`check_in(λx:a. x, Π(x:a). a)` returns `Ok` with `a` a term, and so does
`check_in(a, (λz:@99. @0) a)`, whose claim names a constant that doesn't
exist; `infer_in` rejects both claims. It isn't a way to prove a false
well-formed claim, but a builder bug that produced a malformed claim
would be "proved". Every kernel we checked establishes both facts
(2026-09-26):
- Lean 4 (`src/kernel/environment.cpp`): `check_constant_val` runs
  `checker.check` on the declared type and then `ensure_sort`, before
  `add_theorem` or `add_definition` look at the value. Lean has no
  check-against-a-type rule: `check` is `infer_type_core(e, false)`, and
  `infer_lambda` runs `ensure_sort_core` on every binder domain when not
  infer-only.
- Coq/Rocq (`kernel/constant_typing.ml`, `infer_definition`):
  `Typeops.infer_type` on the declared type (it must be a sort), then
  `check_cast` of the body against it.
- Lean4Lean (`Lean4Lean/Environment.lean`, `checkConstantValBody`:
  `checkType v.type`, then `ensureSort`; `TypeChecker.lean`, `inferLambda`:
  `ensureSortCore` on each domain unless `inferOnly`) and nanoda_lib
  (`src/tc.rs`, `check_declar_info`: `infer(info.ty, Check)`, then
  `ensure_sort`; `infer_lambda`: `infer_sort_of(binder_type)` under
  `Check`) do the same.
- They keep it cheap with an infer-only mode: once a term is known
  well-typed, re-inferring its type skips these checks (nanoda_lib's
  `InferFlag::InferOnly`, used in `is_def_eq`'s helpers; Lean4Lean's
  `inferType` defaults to `inferOnly := true` for internal uses).
- The fix: `check_in` infers `expected` to a `Sort`, and the `Lam` rule
  infers its annotation to one. Both are trusted-kernel changes that
  could turn a proof that checks today into an error, so they need
  measuring and a go-ahead. Lean's 2026 postmortem lists a bug of the
  same kind, #14807 ("is_prop check not requiring a sort").
  Also, nanoda_lib gives locals de Bruijn *levels*
  (`mk_dbj_level`) while checking a binder's body, as stage 3's `Free`s
  will.

