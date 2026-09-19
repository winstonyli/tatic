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
proof. (Two capturing-closure terms appear side by side: one that still
falls back to the interpreter for an unrelated, pre-existing reason, and
one that compiles via real closure conversion — see `compile.rs`'s module
docs and `main.rs`'s comments on each.)

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
| `compile.rs` | Compiles a restricted "first-order arithmetic with self-recursion and closures" fragment to WebAssembly text. Tail self-calls become a `loop`/`br` (recursion → iteration, unbounded call-stack avoided); non-tail self-calls become an ordinary `call`. Every closure value is a single packed `i64` (table index, plus a pointer into linear memory to its captured-values environment); a *non-capturing* ("known", in the compilers-literature sense) closure just has a `0` pointer half and reads nothing from it — one uniform representation either way, not two, so a `call_indirect` site never needs to know in advance whether its callee captures anything. A capturing closure's environment is allocated by a small bump allocator (`emit_allocator`, one page of linear memory grown via `memory.grow` on demand) at the point the closure is created, with the bump pointer (`"hp"`, exported whenever a fragment has any capturing closure) reset to `0` by `jit.rs` before every top-level call, not just the first — see `jit.rs`'s row below for why that reset has to happen from the host rather than inside the compiled function itself; `free_vars` finds what it captures by walking its body. A literal lambda in function position becomes a direct `call` (with a freshly created environment passed as its first argument), one reached through a *variable* — a parameter or a captured free variable, either resolves the same way — becomes `call_indirect` (unpacking the environment pointer and table index back out first). A *named self-recursive* value (e.g. one bound by `let fact = rec f n = .. in ..`) goes through this same table-index machinery — it's just another combinator, self-recursive or not, capturing or not. An *under*-applied literal lambda is real partial application, resolved at compile time rather than through a general runtime dispatch mechanism (every call site's argument count is already statically known, so there's no missing-argument count to resolve at runtime): `register_partial_app` synthesizes a wrapper combinator keyed by `(root, how-many-args-supplied)` alone, shared across every call site with the same shape, and `push_pap_env` creates a value of it (root's own environment plus the supplied arguments) exactly the way any other closure value gets created. An over-applied literal lambda and a variable called with inconsistent arities across call sites are still outside the fragment. Anything outside the fragment is rejected — the compiler only needs to be sound, not complete. |
| `jit.rs` | The cache. On first use of a term, tries to compile it, then verifies the compiled code against the interpreter on a battery of sample inputs before trusting it; only then is the compiled form installed for future calls under that hash. A verification failure permanently blacklists that hash to the interpreter rather than risking a silently wrong optimization. For a fragment with capturing closures, `invoke` also resets the bump allocator's pointer before *every* call (not just the first) — caught by benchmarking the closure-conversion path, not by any unit test: since this cache reuses *one* compiled instance across many separate calls, every capturing closure any call created was leaking its environment forever, growing that instance's linear memory unboundedly over its whole cached lifetime. The reset can't happen inside the compiled function itself (at `$f`'s own entry, say) — a non-tail self-recursive call is an ordinary `call $f`, re-entering the whole function from the top, which would reset mid-computation and corrupt a closure created earlier in the same call that's still needed after the recursive call returns. From the host, once per top-level call, there's no such hazard: nothing outside one call ever reads a closure value `$f` itself returned. |
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
desugar into a term that's genuinely *capturing* by the time `compile.rs`
peels its inner lambda standalone — even though nothing about the source
looks like a capturing closure (see `syntax.rs`'s own tests,
`higher_order_let_chain_evaluates_like_the_hand_built_demo_term`). Real
closure conversion (see `compile.rs`'s module docs) compiles this
correctly now rather than falling back to the interpreter; it still
doesn't get a *kernel-checked* proof, though, since `proof.rs`'s own
fragment doesn't cover higher-order terms at all yet (see below) —
independent of what `compile.rs` itself can compile.

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
  under). Covers any number of self-calls per leaf, including genuinely
  branching ones (Fibonacci's two self-calls) — `build_ev_witness` always
  derives *internally* in terms of the canonical literal params for a call
  (trivially self-consistent, `refl`-provable, and identical regardless of
  which call site reaches a given concrete argument tuple), memoized by
  concrete args (`memo`, a real DP table: without it a branching leaf
  re-derives every shared subproblem from scratch, exactly mirroring the
  interpreter's own unmemoized exponential call count — `f(5)` rebuilt once
  via `f(7)`→`f(6)`→`f(5)` and again via `f(7)`→`f(5)`, and so on
  recursively). The one place the canonical form doesn't already match what's
  needed is where a recursive call's result becomes an argument to *its*
  caller's own `Ev` constructor (which expects the *actual denoted call
  argument expression*, e.g. `n-1`, not just its value — postulated
  operators have no built-in reduction, so `Id`/`def_eq` can't equate
  `sub_ref(8,1)` with `lit_ref(7)` on their own): the caller recasts the
  canonical witness via `kernel::sym` + `kernel::cong_n` + `kernel::transport`
  (congruence for `Ev` over the params, then transport along the resulting
  type equality) — two new, general-purpose kernel primitives, not a
  special-cased hack, following the same pattern as `cong1`/`trans_proof`.
  Building this surfaced a real, previously-latent bug in `cong1`/`cong_n`
  themselves: they silently assumed the function being reasoned about had a
  codomain equal to its domain type (every existing caller happened to
  satisfy that), which broke the moment this needed `Int^arity -> Sort(0)`
  (`cong1` now takes an explicit `b_ty`). Per-call instantiation for a
  branching leaf is now also fast: profiling `fib(8)`'s instance proof
  found `shift` (via `Anchored::at`) dominating by three orders of
  magnitude over everything else, with the same subterm reshifted by the
  same amount repeatedly — not within any one caller, but *across* many
  (`Anchored::at`, `cong1`, `cong_n`, `trans_proof`, `sym`, `transport`,
  `arrow`). `kernel::with_shift_cache` scopes a cache across a whole call's
  construction via a thread-local slot (rather than threading a cache
  parameter through every function that might call `shift`), giving a
  measured ~2x on `fib(8)`'s instance proof. Deliberately opt-in, not
  automatic on every call `instance_from_scaffold` makes: wrapping it
  unconditionally regressed the common case (routine, small samples,
  confirmed via the `fib(30)` demo's cold-compile time going from ~120ms to
  ~220ms) — a real `HashMap`, grown across a construction and then dropped,
  costs more than it saves at that scale. A caller that specifically
  expects a large or branching construction wraps its own call in it (see
  Design notes below for the scoped-vs-standing-cache tradeoff).
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
  strategies" above, now all 3 of them succeeding since branching-leaf
  instances stopped being declined), which together put that one case's
  cold time on this machine around ~140ms (versus ~15ms with no kernel proof
  involved at all; ~95ms immediately after `kernel::Expr` switched to
  `Rc`-based structural sharing, before branching instances were attempted
  at all — see Design notes below); the warm (cached) case is unaffected
  either way, since none of this runs again for a hash already in the cache.
  Also `capturing_closure_loop` — a tail-recursive term that creates and
  immediately calls a fresh capturing closure every iteration, isolating
  the closure-conversion path's own cost (the bump allocator, not
  `call_indirect`'s unpacking). Building this benchmark surfaced a real
  bug, not just a number: warmed up, it ballooned to several GB and never
  finished within criterion's default sample window, because the bump
  allocator's pointer was never being reset between the many separate
  calls this cache makes to one compiled instance (see `jit.rs`'s table
  row above) — fixed, and now warm calls run at ~7.7µs each with memory
  staying bounded regardless of call count.
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
  Benchmarks). On its own it didn't fix branching-leaf instance proofs
  being slow — that cost turned out to live in `shift` (see the next
  entry), not cloning.
- **A scoped, opt-in `shift` cache, not a standing one**: `kernel::shift`
  is called constantly while composing a large proof term, and the same
  subterm gets reshifted by the same amount repeatedly — not within any
  one caller, but *across* several (`proof.rs`'s `Anchored::at`, plus
  `cong1`/`cong_n`/`trans_proof`/`sym`/`transport`/`arrow` internally).
  `kernel::with_shift_cache` runs a closure with a cache active in a
  thread-local slot for that closure's whole (dynamic) extent, rather than
  threading a cache parameter through every function that might call
  `shift` — a scope, not a bare `thread_local`, so it can't leak across
  unrelated calls the way one never cleared would. It's opt-in, not
  automatic: wrapping every call `instance_from_scaffold` makes regressed
  the common case (confirmed via the `fib(30)` demo's cold-compile time,
  ~120ms → ~220ms) — a real `HashMap`, grown across a construction and then
  dropped, costs more than it saves for routine small samples. The win
  (~2x, confirmed on `fib(8)`'s instance proof) is real but concentrated in
  large/branching constructions, so a caller opts in only when it expects
  one.
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
  far from the actual cause. `proof.rs` now has `debug_assert_has_type`
  (debug-only, zero-cost in release), called at the return point of every
  function that composes an `Expr` from more than one recursive sub-call,
  to turn a future instance of this bug class into an immediate,
  precisely-located panic instead of a slow bisection.

## Future work

- `kernel::with_shift_cache` is opt-in rather than automatic (see "Proof
  strategies" above) because wrapping every call regressed the common,
  small-sample case. A caller has to know in advance that its own
  construction will be large/branching to get the benefit; `jit.rs`'s
  automatic verification doesn't attempt that judgment call today (it just
  never opts in), so a branching-leaf function only gets a fast per-call
  instance proof when something explicitly asks for one at a large input,
  not from routine compilation. Making that automatic would need either a
  cheap way to predict "this one's going to be large" in advance, or a
  cache design whose overhead doesn't scale with size the way a `HashMap`
  grown-then-dropped does.
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
- Widening the compilable fragment further: an over-applied literal
  lambda, a variable called with inconsistent arities across sites, more
  primitives. (Capturing closures and partial application of a literal
  lambda — real closure conversion, an environment representation,
  calling a closure reached through a captured free variable, a
  compile-time-desugared synthesized wrapper for an under-applied literal
  — landed; see `compile.rs`'s own module docs.)
- Extending `prove_closure_expr` to cover *capturing* closures, not just
  non-capturing ones — `compile.rs` compiles them now, but the proof's
  own model (one postulated `Clo` constant per combinator, referenced by
  identity, never denoting its body) is only an honest reading of a
  non-capturing closure (always the same value, wherever it's
  referenced); a capturing one gets a different environment at every
  creation site, which that model doesn't represent at all yet (see
  `ClosureCombinators::register`'s own docs in `proof.rs`). The same gap
  applies to a partial application of a literal lambda now that
  `compile.rs` compiles those too — `denote_closure` already declines
  one outright (an arity mismatch against the callee's *own* arity), so
  no proof is silently over-claimed, just none is offered yet.
