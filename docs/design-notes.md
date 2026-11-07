# Design notes

- **Why hash-consing, not just a tree**: two independently-built terms that
  are structurally identical hash to the same value, so the JIT cache and
  the kernel's proof cache are keyed by *content*, not by which piece of
  code happened to construct the term.
- **`kernel::Expr`'s recursive fields were `Rc`, not `Box`** (history: `Expr` is now a
  `Copy` handle to an interned node, `docs/tier-cycle/`, "Kernel scaling and the id arena"):
  `Expr` was built once and then threaded through many `.clone()` calls as it was composed into
  larger proof terms (`proof.rs`'s pre-stage-4 `Anchored` reshifting
  pattern especially, `docs/related-work/` §72, but also plain composition
  like `cong_n`'s per-argument accumulation) —
  with `Box`, every one of those clones was a full deep copy, cost scaling
  with however large the accumulated term had grown by that point, not with
  what actually changed. With `Rc`, `#[derive(Clone)]` clones each field by
  bumping a refcount, so cloning an `Expr` of any size was O(1) and its
  children were genuinely shared. This was deliberately *not* full
  hash-consing — there was no intern table, so two independently-built but
  equal subterms still got distinct allocations — but it removed the real
  cost this crate was paying, worth ~2x on `fib`'s cold-compile time (see
  Benchmarks). On its own it didn't fix branching-leaf instance proofs
  being slow — that cost turned out to live in `shift` (see the next
  entry), not cloning.
- **No `shift` cache**: `tatic-kernel` once had a thread-local cache scoped
  around instance proofs (`with_shift_cache`), engaged from a dry run of
  how many nodes an instance visits. It won ~2x on `fib(8)` by recovering
  reshifts that eager substitution caused. Once `subst_top` shifted its
  argument only where used (`docs/related-work/` §53), the cache cost more
  to fill and drop than it saved on every term measured, so it was
  removed (§54), along with its hidden state in the kernel.
- **Why a predicative kernel with exactly these five primitives**: see
  `tatic-kernel`'s module docs for the full argument, but briefly — `W`-types
  are load-bearing (not derivable from `Pi`/`Sort`/`Id` alone with
  definitional computation, which an interpreter's hot path needs).
  Base types like `Int` are postulated, the same approach real kernels
  take. An earlier version of this note called deriving them a wall (a
  "vacuous eliminator" needing a witness-extractor one universe up); that
  holds only for an eliminator built from `Pi`. `W` derives `Empty` with
  no postulate, and a tag that carries its own witness computes
  (`docs/tier-cycle/`, "The level wall is Church's"). `Sigma` is
  the fifth, added separately: `W`'s own children function maps back into
  `W` itself, so it can only stand in for a payload that's *another
  instance of the same inductive type*, not an arbitrary, independently-
  chosen one — a genuine dependent sum needs its own primitive, and a
  Church/impredicative encoding of one from `Pi` alone was rejected for
  the same computation-preserving reason `W` itself was chosen over that
  route.
- **Why sample verification never goes away**: it is the only check in
  the system that touches the WAT wasmtime actually executes. Every
  kernel proof is stated over `proof.rs`'s `denote`, which models
  the compiler (`build_node`, the `lower_wat` templates) rather than
  reading its output, so a theorem covering
  every input still says nothing about a mistake in WAT emission. Sample
  verification is simple, total, and always applicable, so it stays the
  first half of the installation gate regardless of how far proof
  coverage grows — the proof is what extends coverage beyond the
  battery, not what replaces it.
- **Why the per-execution fallback stays anyway**: `prove_closure_expr_instance`
  certifies one concrete execution, which the gate treats as no better than
  the battery itself, so it builds it only at arity 0, where one execution
  is every input. That per-execution limit is a property of *this* check, not of translation
  validation as the literature means it — a genuine per-compilation
  validator's success would cover every input, and building one is a
  route tatic hasn't taken (see §28).
- **Division by zero is outside the theorems' claim**: they treat `/` and
  `%` as opaque postulated operators with no computation rule, so a
  theorem holds for every total reading of `x / 0`, and a term that
  divides by zero can still be kernel-verified. There the Wasm traps and
  `eval` returns `DivByZero`, which `verify()` counts as agreement, so no
  wrong value is reachable. The per-instance prover picks branches with
  `eval` itself (`eval_concrete_dyn`) and declines an execution that
  divides by zero; until 2026-10-27 (cleanup plan CU1) a private evaluator
  of its own took `x / 0 = 0`.
- **`Anchored`, and a staleness bug it doesn't automatically prevent**
  (history; the type is gone as of stage 4, `docs/related-work/` §72): back
  when a postulate's `Expr` reference was a `Var` index, only valid
  relative to the postulate context's length *at the moment it's
  resolved*, `Anchored` reshifted one held across further pushes, but
  nothing stopped code from resolving a plain `Expr` and holding it
  unwrapped instead. That exact mistake caused two real bugs in this
  project (the `Ev`-witness builder, then `denote_closure`), each only
  surfacing as an opaque kernel type-mismatch far from the actual cause.
  Stage 3 made the whole class structurally impossible — `Postulates::get`
  now returns a `Const`, which no push shifts (§69) — so `Anchored` had
  nothing left to do and was deleted. `proof/denote.rs` still has
  `debug_assert_has_type`
  (debug-only, zero-cost in release), called at the return point of every
  function that composes an `Expr` from more than one recursive sub-call,
  to turn a future instance of this bug class into an immediate,
  precisely-located panic instead of a slow bisection.

