# tatic

An efficient implementation of an expressive higher-order language where,
once a high-level transformation is *found to be equivalent* to a low-level
sequence of operations on a formalized target machine, that low-level form
is used as a JIT-compiled implementation for future invocations of the same
transformation.

Concretely: terms are content-addressed (hash-consed), so structurally
identical transformations anywhere share one cache key. The first call for
a given term tries to compile it to WebAssembly and JIT it via `wasmtime`
(Cranelift); every later call for that same content hash skips straight to
the compiled, native-speed path. "Found to be equivalent" is not just
asserted — it's checked, with two complementary layers of assurance: sample
verification against a reference interpreter (always), and, where the term
falls in a covered fragment, an actual **kernel-checked proof** that the
compiled and interpreted readings agree.

## Quick start

```sh
cargo run --release   # runs the demo in src/main.rs
cargo test            # unit tests across all modules
cargo bench           # criterion benchmarks (benches/) -- see below
```

The demo builds a few example terms (factorial, gcd, a naive Fibonacci, a
genuinely higher-order term, a straight-line arithmetic function), runs
them through the JIT, and prints timing plus which ones got a kernel-checked
equivalence proof.

## Architecture

```
 term.rs -----> eval.rs (reference semantics)
    |               ^
    |               | compared against
    v               |
 compile.rs ---> jit.rs ---> wasmtime (Cranelift JIT)
    |               ^
    |               | additional evidence
    v               |
 proof.rs <----> kernel.rs (Pi/Sort/Id/W type theory)
```

| Module | Role |
|---|---|
| `term.rs` | Content-addressed term store. Hash-conses a small higher-order language (`Var`/`Lit`/`Prim`/`If`/`Abs`/`App`/`Rec`) by BLAKE3 content hash, so structurally identical terms — however independently constructed — always share one hash and one cache entry. |
| `eval.rs` | The reference interpreter (call-by-value). Defines correctness: everything else is judged against this. Supports the *full* language, including arbitrary higher-order closures. |
| `compile.rs` | Compiles a restricted "first-order arithmetic with self-recursion" fragment (no closures) to WebAssembly text. Tail self-calls become a `loop`/`br` (recursion → iteration, unbounded call-stack avoided); non-tail self-calls become an ordinary `call`. Anything outside the fragment is rejected — the compiler only needs to be sound, not complete. |
| `jit.rs` | The cache. On first use of a term, tries to compile it, then verifies the compiled code against the interpreter on a battery of sample inputs before trusting it; only then is the compiled form installed for future calls under that hash. A verification failure permanently blacklists that hash to the interpreter rather than risking a silently wrong optimization. |
| `kernel.rs` | A free-standing, minimal predicative dependent type theory: `Pi` + a stratified universe hierarchy (`Type₀:Type₁:...`) + `Id`/`Refl`/`J` (equality) + `W`/`Sup`/`WRec` (general inductive types) — four primitives, chosen because that's provably the minimum needed for *definitional* computation of user-defined recursive functions in a predicative system (see doc comments for why weaker combinations don't work). Has a real bidirectional typechecker and normalizer. |
| `proof.rs` | Connects `kernel.rs` to the JIT. For terms in scope, builds an actual `Id`-typed proof — checked by `kernel.rs`'s typechecker, not just asserted — that the compiled and interpreted readings of a term agree, and records it as additional evidence in `jit.rs`'s cache. |

## What's actually proven, and what isn't

This is stated precisely because it would be easy to overclaim here.

- **Straight-line (non-recursive) terms**: `proof.rs` builds one kernel
  proof covering *every* input. `compile.rs`'s instruction emission and
  `eval.rs`'s evaluation recurse over this fragment in exactly the same
  shape, so the proof is `refl` — an honest witness that a stack-based and
  a tree-walking evaluation of side-effect-free code compute the same
  value by construction, not a shortcut.
- **Tail-recursive terms** (the fragment compiled to a `loop`): proven two
  ways. `prove_tail_recursive_call` is *translation validation* — for one
  specific call, the proof follows the interpreter's actual execution
  trace, symbolically composing each iteration's new parameters, until it
  reaches the base case; a genuine per-call certificate, checked by the
  kernel, but not a universal theorem. `prove_tail_recursive_universal`
  goes further: it postulates an inductive "evaluates-to" trace family
  `Ev(params, v)` (the same "postulated inductive family" pattern `Int`
  itself uses) together with a recursor obeying the same universal-motive
  shape as `kernel::WRec`, and uses real induction on that recursor —
  built from `kernel::cong1`/`trans_proof` as its composition lemmas — to
  prove `loop_val(params, v, e) = v` once, for every `params` and `v`, not
  per call.
- **Non-tail recursion** (e.g. naive Fibonacci, compiled to a plain WASM
  `call`): not covered by a kernel proof at all yet. Sample verification
  is currently the only thing standing behind it.
- **Genuinely higher-order terms**: outside the compilable fragment
  entirely, so they're just interpreted — correctly, but there's no JIT
  path (and therefore no compiled-vs-interpreted question) to prove
  anything about.

In every case, `jit.rs`'s sample-based verification against the
interpreter is the actual trust gate for installing a compiled form. A
kernel proof, where one exists, is recorded as stronger evidence alongside
it (`Stats::kernel_proofs_checked`, `JitEngine::is_kernel_verified`), not a
replacement for it.

## Benchmarks

`benches/` has two [criterion](https://docs.rs/criterion) suites (`cargo
bench`, or `cargo bench --bench execution` / `--bench proofs` for one):

- `execution.rs` — interpreter vs. JIT, cold (compile + verify) vs. warm
  (cache hit), for a non-tail-recursive term (naive `fib`), a
  tail-recursive one (`gcd`, compiled to a loop), and straight-line
  `factorial`. Shows both the steady-state speedup and how much of it the
  one-time compile+verify cost eats into.
- `proofs.rs` — the cost of building each kind of kernel proof from
  `proof.rs`: one `refl` for a straight-line term, one relational
  (translation-validation) proof per call, and the one-time universal
  proof. Includes a direct N-relational-calls-vs.-one-universal-proof
  comparison, since that crossover is the actual argument for building the
  universal proof at all — on this machine it lands around 150-200 sample
  points (a universal proof ≈ 5ms once vs. ≈ 25µs per relational call), so
  which is cheaper depends entirely on how many sample points
  `jit.rs` would otherwise verify against.

## Design notes

- **Why hash-consing, not just a tree**: two independently-built terms that
  are structurally identical hash to the same value, so the JIT cache and
  the kernel's proof cache are keyed by *content*, not by which piece of
  code happened to construct the term.
- **Why a predicative kernel with exactly these four primitives**: see
  `kernel.rs`'s module docs for the full argument, but briefly — `W`-types
  are load-bearing (not derivable from `Pi`/`Sort`/`Id` alone with
  definitional computation, which an interpreter's hot path needs), and
  bootstrapping finite base types (`Bool`, `Nat`) from nothing hits a real,
  expected wall in a predicative system (a "vacuous eliminator" always
  needs a witness-extractor one universe above what it eliminates into).
  Base types like `Int` are postulated accordingly — the same approach
  real kernels take, not a shortcut specific to this project.
- **Why sample verification never goes away**: a kernel proof only exists
  for the fragment `proof.rs` currently covers, and translation validation
  is inherently per-call. Sample verification is simple, total, and always
  applicable, so it stays the baseline safety net regardless of how far
  the proof coverage grows.

## Future work

- Widening `prove_tail_recursive_universal` past its current shape (a
  single `If` with one base branch and one fully-saturated tail-call
  branch) to deeper branching.
- Proof coverage for non-tail recursion (a different argument — bounded
  term-structure induction rather than call-count induction).
- Widening the compilable fragment itself (e.g. closures, more primitives).
