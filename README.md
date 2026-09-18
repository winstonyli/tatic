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
cargo run --release             # runs the demo in src/main.rs
cargo run --release --bin repl  # an interactive REPL (src/bin/repl.rs)
cargo test                      # unit tests across all modules
cargo bench                     # criterion benchmarks (benches/) -- see below
```

The demo starts by parsing a real source string (`syntax.rs`) into a term,
then builds a few more example terms by hand (factorial, gcd, a naive
Fibonacci, a non-capturing higher-order term, a genuinely capturing
closure, a straight-line arithmetic function), runs them all through the
JIT, and prints timing plus which ones got a kernel-checked equivalence
proof.

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
| `syntax.rs` | A real, parseable surface syntax for that language, so a term doesn't have to be hand-built through `term.rs`'s De Bruijn-index builders. A small recursive-descent parser (no separate AST — each grammar production interns directly via `TermStore`) with ordinary named-variable scoping (`\x y. x + y`, `let`, `rec f x = ...`), translating names to De Bruijn indices as it parses; `print` is the reverse direction, a precedence-aware pretty-printer back to source text. |
| `eval.rs` | The reference interpreter (call-by-value). Defines correctness: everything else is judged against this. Supports the *full* language, including arbitrary higher-order closures. |
| `compile.rs` | Compiles a restricted "first-order arithmetic with self-recursion and non-capturing closures" fragment to WebAssembly text. Tail self-calls become a `loop`/`br` (recursion → iteration, unbounded call-stack avoided); non-tail self-calls become an ordinary `call`. A closure that doesn't capture anything from an enclosing scope ("known", in the compilers-literature sense) compiles to its own Wasm function, referenced by index into a shared function table — no heap, no environment struct; a literal lambda in function position becomes a direct `call`, one reached only through a parameter becomes `call_indirect`. A *named self-recursive* value (e.g. one bound by `let fact = rec f n = .. in ..`) goes through this same table-index machinery — it's just another combinator, self-recursive or not. Capturing closures, and partial application, are still outside the fragment. Anything outside the fragment is rejected — the compiler only needs to be sound, not complete. |
| `jit.rs` | The cache. On first use of a term, tries to compile it, then verifies the compiled code against the interpreter on a battery of sample inputs before trusting it; only then is the compiled form installed for future calls under that hash. A verification failure permanently blacklists that hash to the interpreter rather than risking a silently wrong optimization. |
| `kernel.rs` | A free-standing, minimal predicative dependent type theory: `Pi` + a stratified universe hierarchy (`Type₀:Type₁:...`) + `Id`/`Refl`/`J` (equality) + `W`/`Sup`/`WRec` (general inductive types) — four primitives, chosen because that's provably the minimum needed for *definitional* computation of user-defined recursive functions in a predicative system (see doc comments for why weaker combinations don't work). Has a real bidirectional typechecker and normalizer. |
| `proof.rs` | Connects `kernel.rs` to the JIT. For terms in scope, builds an actual `Id`-typed proof — checked by `kernel.rs`'s typechecker, not just asserted — that the compiled and interpreted readings of a term agree, and records it as additional evidence in `jit.rs`'s cache. |

## Surface syntax

```rust
use tatic::{syntax, term::TermStore};

let mut store = TermStore::new();
let fact = syntax::parse(&mut store, "rec f n = if n <= 1 then 1 else n * f (n - 1)")?;
```

`let`/`\`/`rec`/`if` all extend as far right as possible, so — as in most
ML-family languages — they need parentheses as a function argument or an
operand: `f (\x. x) (if c then 1 else 2)`, not `f \x. x if c then 1 else 2`.
`let x = e1 in e2` is pure sugar for `(\x. e2) e1` (the term language has no
separate `let` primitive); a named recursive function reads naturally as
one `let` binding a `rec` value:

```
let fact = rec f n = if n <= 1 then 1 else n * f (n - 1) in fact 10
```

One honest, non-obvious finding from building this: nesting two `let`s
where the inner one's body references the outer one's binding can
desugar into a term `compile.rs` correctly rejects as *capturing* — even
though nothing about the source looks like a capturing closure (see
`syntax.rs`'s own tests, `higher_order_let_chain_evaluates_like_the_hand_built_demo_term`).
It still evaluates correctly either way; it just falls back to the
interpreter instead of compiling, the same graceful degradation any other
out-of-scope term gets.

`syntax::print` is the reverse direction — a precedence-aware
pretty-printer back to source text `parse` accepts, assigning each binder
a fresh name by nesting depth (`v0`, `v1`, ...) since `Var`/`Abs` don't
carry names. It round-trips (`parse(print(t))` hashes identically to `t`,
a strictly stronger check than "looks plausible") for everything the
grammar can express, with one honest, documented exception: a literal
built directly as `Term::Lit(n)` for a negative `n` (never produced by
`parse` itself, which only reaches a negative value via unary-minus
desugaring) has no exact syntactic round trip, since this grammar has no
negative-literal syntax at all — only subtraction.

`src/bin/repl.rs` is a small interactive REPL built on `syntax::parse`/
`print`: each line is parsed, run through the JIT (falling back to the
interpreter automatically, same as ever), and reported with whether it
got a kernel-checked proof. `let NAME = EXPR` (no `in`) defines `NAME` for
later lines — since `syntax.rs`'s parser has no scope that persists
across separate calls, this works by re-parsing each new line with every
prior definition's `let .. in ` prefixed, not by threading parser state.
Building it is what surfaced two real `compile.rs` bugs (a crash on a
named recursive function used as a value, and a non-tail self-call that
hardcoded `call $f` instead of calling back into whichever function it
was actually compiled as) — see `compile.rs`'s own tests.

## What's actually proven, and what isn't

This is stated precisely because it would be easy to overclaim here.

- **Straight-line (non-recursive) terms**: `proof.rs` builds one kernel
  proof covering *every* input. `compile.rs`'s instruction emission and
  `eval.rs`'s evaluation recurse over this fragment in exactly the same
  shape, so the proof is `refl` — an honest witness that a stack-based and
  a tree-walking evaluation of side-effect-free code compute the same
  value by construction, not a shortcut.
- **Recursive terms, tail or not** (`gcd`'s `loop`, factorial's or naive
  Fibonacci's plain `call`): proven two ways. `prove_tail_recursive_call`
  is *translation validation* — for one specific call, the proof follows
  the interpreter's actual execution trace, symbolically composing each
  step's new parameters (recursing into non-tail self-calls too, wherever
  they sit), until it reaches a base case; a genuine per-call certificate,
  checked by the kernel, but not a universal theorem.
  `prove_tail_recursive_universal` goes further: it postulates an
  inductive "evaluates-to" trace family `Ev(params, v)` (the same
  "postulated inductive family" pattern `Int` itself uses) with one
  constructor per leaf of `body`'s decision tree — `body` can be an
  arbitrary tree of nested `If`s, and each leaf can itself contain any
  number of self-calls combined arithmetically (zero for a base case, one
  in tail position, or several — e.g. Fibonacci's `f(n-1) + f(n-2)`) —
  together with a recursor obeying the same universal-motive shape as
  `kernel::WRec`, and uses real induction on that recursor to prove
  `loop_val(params, v, e) = v` once, for every `params` and `v`, not per
  call. Each leaf's constructor is gated by the *conjunction* of
  hypotheses that `cond` denotes to whichever value selects that branch at
  every ancestor `If` on the way to it — without that, a leaf's
  constructor would make `Ev(params, v)` trivially inhabited for *any*
  `params` regardless of `cond`, which isn't what "the trace starting at
  `params`" is supposed to mean. Recombining a leaf's induction hypotheses
  (for leaves with more than one self-call) uses `kernel::cong_n`, an
  `n`-ary congruence lemma built from `cong1`/`trans_proof`; a leaf with
  zero or one (tail-position) self-calls is the special case where that
  reduces to the identity/no-op it always was. This is a *reusable lemma*,
  not itself a per-input guarantee: instantiating it at a concrete
  `params` needs an actual `Ev`-witness built by following `cond`'s real
  value at each step (`prove_tail_recursive_instance`, via
  `build_ev_witness`/`eval_and_prove`), grounded in one postulated axiom
  per distinct concrete primitive application the trace performs
  (`ArithPostulates::assume_prim_fact` — a postulated operator has no
  built-in computation rule, so a witness for one call has to assume each
  concrete fact it needs, the same pattern `Int` itself is postulated
  under). Restricted to leaves with at most one self-call — tail recursion
  and simple non-tail recursion (`gcd`, factorial) — since a witness for a
  genuinely branching leaf (e.g. Fibonacci's two self-calls) has a logical
  size that grows with the number of calls the interpreter itself makes for
  that shape, exponential in the input for two-way branching (sibling
  branches, like the `f(5)` reachable from both `f(7)` and `f(6)` inside
  `f(8)`, are built by unrelated recursive calls and share no structure with
  each other). `kernel::Expr`'s recursive fields are `Rc`, not `Box` (see
  Design notes below), which makes *building* a witness cheap — but
  confirmed empirically, that alone doesn't fix this: the dominant cost
  turns out to be `kernel::check`/`infer`'s `nf`, which beta-reduces a
  type's entire structure with no memoization on `Rc` identity, so it still
  re-normalizes a shared subterm once per place it's referenced. `fib(8)`
  (67 interpreter calls) is still single-digit seconds to build and
  re-typecheck. Fixing this for real needs a memoizing `whnf`/`nf`, not just
  sharing — future work. The theorem itself is unaffected either way; only
  per-call instantiation is out of scope for that shape.
- **Non-capturing ("known") closures**: `prove_closure_expr` gives a closed,
  non-recursive closures term one kernel proof covering every input, the
  same `refl`-on-a-shared-translation argument `prove_pure_expr` makes for
  straight-line arithmetic — nothing here evaluates anything concrete, so
  it needs no `assume_prim_fact`-style grounding either. A closure value is
  postulated opaque (`Clo : Sort(0)`, `Int`'s own "postulated type"
  pattern), one postulated constant per distinct combinator (referenced by
  identity only — a combinator's own *body* is never unfolded or denoted,
  so this doesn't need a fixpoint discovery pass the way `compile.rs`'s own
  codegen does), and postulated call functions mirroring `compile.rs`'s two
  call shapes exactly: `apply_k : Clo -> Int^k -> Int` for a
  parameter-typed closure (`call_indirect`, always `Int` arguments per
  `compile.rs`'s own typed dispatch), and, per combinator, a
  signature-specific `call_h : T_0 -> .. -> T_{k-1} -> Int` for a direct
  call (a static Wasm `call`, no `Clo` value involved at all) — needed
  because a combinator like `twice` takes a mix of closure- and `Int`-typed
  arguments, which the uniform `apply_k` can't express. Scope, honestly:
  closed and non-recursive only (combining with self-recursion is future
  work); every `If` branch must denote as `Int` (an `If` choosing between
  two closures is out of scope, though `compile.rs` would compile it); and
  it doesn't re-verify that each combinator it references is actually
  non-capturing the way `compile.rs` itself does — harmless in practice
  since `jit.rs` only calls into `proof.rs` after a term already compiled
  successfully. A genuinely *capturing* closure is still outside the
  compilable fragment entirely, so it's just interpreted — correctly, but
  there's no JIT path (and therefore no compiled-vs-interpreted question)
  to prove anything about.

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
  one-time compile+verify cost eats into — `fib`'s cold-compile cost
  includes building its (two-self-call) universal proof plus a few
  concrete-instance attempts `jit.rs` tries alongside it (see "Proof
  strategies" above), which together put that one case's cold time on this
  machine around ~95ms (versus ~15ms with no kernel proof involved at all;
  down from ~200ms before `kernel::Expr` switched to `Rc`-based structural
  sharing, see Design notes below); the warm (cached) case is unaffected
  either way, since none of this runs again for a hash already in the cache.
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
- **`kernel::Expr`'s recursive fields are `Rc`, not `Box`**: `Expr` is built
  once and then threaded through many `.clone()` calls as it's composed into
  larger proof terms (`proof.rs`'s `Anchored` reshifting pattern especially,
  but also plain composition like `cong_n`'s per-argument accumulation) —
  with `Box`, every one of those clones was a full deep copy, cost scaling
  with however large the accumulated term had grown by that point, not with
  what actually changed. With `Rc`, `#[derive(Clone)]` clones each field by
  bumping a refcount, so cloning an `Expr` of any size is O(1) and its
  children are genuinely shared. This is deliberately *not* full
  hash-consing — there's no intern table, so two independently-built but
  equal subterms still get distinct allocations — but it removes the real
  cost this crate was paying, worth ~2x on `fib`'s cold-compile time (see
  Benchmarks). It does *not* fix the branching-leaf witness limitation
  below — that cost lives in unmemoized normalization, not cloning.
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
- **`Anchored`, and a staleness bug it doesn't automatically prevent**: a
  postulate's `Expr` reference is only valid relative to the postulate
  context's length *at the moment it's resolved* (`kernel::Postulates::get`
  computes a fresh `Var` index each call); `Anchored` reshifts one held
  across further pushes, but nothing stops code from resolving a plain
  `Expr` and holding it unwrapped instead. That exact mistake caused two
  real bugs in this project (the `Ev`-witness builder, then
  `denote_closure`), each only surfacing as an opaque kernel type-mismatch
  far from the actual cause. `proof.rs` now has `debug_assert_has_type`/
  `debug_assert_well_typed` (debug-only, zero-cost in release), called at
  the return point of every function that composes an `Expr` from more
  than one recursive sub-call, to turn a future instance of this bug class
  into an immediate, precisely-located panic instead of a slow bisection.

## Future work

- Instantiating the universal theorem for genuinely branching leaves (e.g.
  naive Fibonacci's two self-calls) — `build_ev_witness` currently declines
  these outright (see "Proof strategies" above). Tried and confirmed
  insufficient: switching `kernel::Expr` to `Rc`-based structural sharing
  (see Design notes) — `fib(8)` (67 interpreter calls) is still single-digit
  seconds to build and re-typecheck, because the dominant cost is
  `kernel::check`/`infer`'s `nf`, which re-normalizes a shared subterm once
  per place a type references it rather than once. Fixing this for real
  needs a memoizing `whnf`/`nf` (or checking without fully normalizing), not
  just sharing.
- Allowing an `If` nested inside a leaf's own arithmetic expression (e.g.
  `n + (if c then 1 else 2)`), not just as the whole body of some branch —
  `find_self_calls`/`denote_with_placeholders` currently reject that shape
  outright.
- Combining closures with self-recursion in one proof (`prove_closure_expr`
  is closed/non-recursive-only, `prove_tail_recursive_universal` is
  closures-free) and allowing an `If` to choose between two closures, not
  just two `Int`s — both real, documented restrictions of
  `prove_closure_expr`, not fundamental limits. One concrete instance of
  the first: `compile.rs` now compiles a named self-recursive value called
  through the combinator table (`let fact = rec f n = .. in fact 10`,
  found via the REPL — see its own tests), but no proof strategy covers
  that shape yet, since it's neither `prove_closure_expr`'s fragment (which
  excludes `Rec`) nor `prove_tail_recursive_universal`'s (which needs the
  *top-level* term itself to be `Rec`-wrapped).
- Widening the compilable fragment further: capturing closures (would need
  real closure conversion — an environment representation, plus composing
  a separate correctness proof for that compilation stage, CompCert/CakeML
  style, rather than extending the existing one), partial application, more
  primitives.
