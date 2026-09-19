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
proof. (Two capturing-closure terms appear side by side, compiled via
*different* dispatch paths: one reached by over-applying a literal
lambda's saturated-call result, the other by calling a closure-typed
*parameter* — see `compile.rs`'s module docs and `main.rs`'s comments on
each.)

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
| `eval.rs` | The reference interpreter (call-by-value). Defines correctness: everything else is judged against this. Supports the *full* language, including arbitrary higher-order closures. Trampolined for its own tail positions (an `If`'s chosen branch, and applying a value that resolves the current call), mirroring `compile.rs`'s own `loop`/`br` conversion at the interpreter level: a tail-recursive term runs at any depth without growing the native stack, while a genuinely non-tail-recursive one (naive `fib`, say) still grows it, exactly as it would grow a Wasm `call` chain in the compiled reading. |
| `compile.rs` | Compiles a restricted "first-order arithmetic with self-recursion and closures" fragment to WebAssembly text. Tail self-calls become a `loop`/`br` (recursion → iteration, unbounded call-stack avoided); non-tail self-calls become an ordinary `call`. Every closure value is a single packed `i64` (table index, plus a pointer into linear memory to its captured-values environment); a *non-capturing* ("known", in the compilers-literature sense) closure just has a `0` pointer half and reads nothing from it — one uniform representation either way, not two, so a `call_indirect` site never needs to know in advance whether its callee captures anything. A capturing closure's environment is allocated by a small bump allocator (`emit_allocator`, one page of linear memory grown via `memory.grow` on demand) at the point the closure is created, with the bump pointer (`"hp"`, exported whenever a fragment has any capturing closure) reset to `0` by `jit.rs` before every top-level call, not just the first — see `jit.rs`'s row below for why that reset has to happen from the host rather than inside the compiled function itself; `free_vars` finds what it captures by walking its body. A literal lambda in function position becomes a direct `call` (with a freshly created environment passed as its first argument), one reached through a *variable* — a parameter or a captured free variable, either resolves the same way — becomes `call_indirect` (unpacking the environment pointer and table index back out first). A *named self-recursive* value (e.g. one bound by `let fact = rec f n = .. in ..`) goes through this same table-index machinery — it's just another combinator, self-recursive or not, capturing or not. An *under*-applied literal lambda is real partial application, resolved at compile time rather than through a general runtime dispatch mechanism (every call site's argument count is already statically known, so there's no missing-argument count to resolve at runtime): `register_partial_app` synthesizes a wrapper combinator keyed by `(root, how-many-args-supplied)` alone, shared across every call site with the same shape, and `push_pap_env` creates a value of it (root's own environment plus the supplied arguments) exactly the way any other closure value gets created. An *over*-applied literal lambda dispatches the saturated call's own result through `call_indirect` too — the same mechanism a closure-typed variable already uses, just with the callee freshly computed rather than read from a local — since nothing here checks statically that the result genuinely is a closure, an over-application of a plain `Int`-returning function still compiles, into a `call_indirect` that traps or (astronomically unlikely) lands on some unrelated entry, caught either way by `jit.rs`'s sample verification disagreeing with the interpreter, which genuinely type-errors on such a term. A variable called with inconsistent arities across call sites is still outside the fragment (no fixed arity to desugar around at all). Anything outside the fragment is rejected — the compiler only needs to be sound, not complete. |
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
  in tail position, or several — e.g. Fibonacci's `f(n-1) + f(n-2)`), even
  when some of those self-calls sit inside a further `If` nested in the
  leaf itself, not just as the whole body of some branch — either purely
  arithmetic (e.g. `n + (if c then f(n-1) else f(n-2))`), or choosing
  between two `Clo`-typed values (e.g. a self-call argument
  `f(n-1, if c then g else h)`, via `ite_clo`, same as `prove_closure_expr`
  below) —
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
- **Closures combined with self-recursion, in `prove_tail_recursive_universal`**:
  covers a self-recursive function whose own parameters may be
  `Clo`-typed — threaded through the recursion unchanged, or called via
  `apply_k` within a leaf or a self-call argument — e.g. "iterate a closure
  `n` times": `rec f n g x = if n<=0 then x else f(n-1, g, g(x))`, a shape
  `compile.rs` already compiled (its own `infer_closure_arities`/
  `compile_node` machinery is generic over self-recursion vs. not) but that
  had no proof strategy at all before this. This part needs only `Clo`/
  `apply_k`, reused directly via `ClosurePostulates: Deref<Target =
  ArithPostulates>`, which lets the whole induction pipeline (`Ev`,
  `loop_val`, the congruence/transitivity chaining) keep calling every
  plain-arithmetic postulate method unchanged. `prove_tail_recursive_instance`/
  `_with_instances`'s own per-call specialization still declines whenever
  any parameter is `Clo`-typed (there's no way to represent a closure value
  as the concrete `i64` its model needs), but that's the weaker,
  sample-oriented proof — the *theorem* itself (what `jit.rs`'s
  `kernel_verified` actually depends on) covers every input regardless.
  Caught a real bug while building this: `ClosurePostulates::apply_ref`'s
  lazy-postulate memoization was designed for `prove_closure_expr`'s own
  usage, where the postulate context only ever grows; here, the induction
  machinery repeatedly pushes-then-rolls-back the same scratch space, and
  `apply_ref`'s *first* call for a given arity, triggered from inside one
  of those temporary scopes, memoized a position that then got rolled
  back while the memo entry stayed — silently going stale. `kernel::check`'s
  own final re-verification caught it immediately (a lambda-domain
  mismatch), not a silent acceptance; fixed by pre-pushing every needed
  arity once, before any temporary scope gets the chance, and confirmed
  via a dedicated regression test (mixed `Clo`/`Int` parameters, needed
  since the bug isn't observable when every parameter happens to be
  `Int`) that fails the same way when the fix is reverted.

  A self-call *argument* may also genuinely *create* a closure and call it
  right there, e.g. `f(n-1, (\y. acc+y)(n))` — exactly the shape
  `compile.rs`'s own `self_recursion_creating_a_fresh_capturing_closure_every_iteration_compiles`
  test and `capturing_closure_loop` benchmark already exercise, previously
  compiled but never proven. `denote_closure_typed` (the self-call-argument
  denotation `new_params_for` uses) mirrors `denote_closure`'s own
  `Term::Abs`/`Term::Rec` handling almost verbatim, now that the induction
  pipeline's own postulate-and-combinator bookkeeping is a full
  `ClosureCombinators` (not just `ClosurePostulates`) — registering a
  combinator, calling one directly, or partially applying one (still never
  a *recursive* root, matching `pap_ref`'s own restriction) all reuse the
  exact same methods `prove_closure_expr` does. A leaf's own *top-level*
  expression gets the identical treatment (`denote_with_placeholders`/
  `find_self_calls`, widened the same way) — e.g. `(\y. n+y)(5) + f(n-1)`,
  a closure-call's result combined arithmetically with the recursive call
  directly, not nested inside any self-call's own argument list. Caught
  the *same class* of staleness bug a second time, in a new place:
  `register`/`call_ref`/`pap_ref`, and transitively `mk_env_ref`/`env_ty`
  for a capturing one, are all lazily memoized exactly like `apply_ref`,
  and could just as easily be triggered for the first time from inside a
  temporary scope. Since these registrations depend only on a combinator's
  hash and a capture *count* — never the actual parameter values —
  `prime_closure_postulates` pre-triggers every one a self-call argument
  *or a leaf's own expression* will need via a lightweight structural walk
  (no parameter values needed at all), the same upfront-priming fix
  widened to cover closure creation, not just a call through a parameter.
  Also honestly scoped: the *instance* (per-call) specialization remains
  untouched and still rejects a self-call argument or leaf expression that
  creates a closure — `kernel_verified` doesn't depend on that, so this
  doesn't weaken what actually gets verified, only what gets additional,
  call-specific evidence.
- **Closures, non-capturing, capturing, and partially applied**: `prove_closure_expr` gives a
  closed, non-recursive closures term one kernel proof covering every
  input, the same `refl`-on-a-shared-translation argument `prove_pure_expr`
  makes for straight-line arithmetic — nothing here evaluates anything
  concrete, so it needs no `assume_prim_fact`-style grounding either. A
  closure value is postulated opaque (`Clo : Sort(0)`, `Int`'s own
  "postulated type" pattern). Calling one *through a parameter*
  (`call_indirect`) goes through `apply_k : Clo -> Int^k -> Int`, one per
  distinct arity actually used that way — unaffected by whether the
  underlying closure captures anything, the same way `compile.rs`'s own
  `call_indirect` dispatch doesn't need to know either. A combinator's own
  *body* is never unfolded or denoted (no fixpoint discovery pass the way
  `compile.rs`'s own codegen needs): a *non-capturing* one gets one fixed
  `Clo`-typed constant (`combinator_value`, referenced by identity) and one
  signature-specific `call_h : T_0 -> .. -> T_{k-1} -> Int` for a direct
  call — needed because a combinator like `twice` takes a mix of closure-
  and `Int`-typed arguments, which the uniform `apply_k` can't express. A
  *capturing* one can't use one fixed constant honestly — `compile.rs`
  builds a fresh environment at every creation site, so the same
  combinator denotes differently depending on where it's referenced — so
  instead `mk_clo_h : Env -> Clo` (a function of the environment) and
  `call_h : Env -> T_0 -> .. -> T_{k-1} -> Int` (environment prepended,
  mirroring `compile.rs`'s own `$env`-first calling convention), where
  `Env : Sort(0)` is postulated once *per capture signature* (`capture_sig`
  — which slots are `Clo`-typed, which are `Int`; shared across every
  combinator whose captures match that exact signature, the same way
  `apply_k` is shared by arity) with constructor `mk_env : T_0 -> .. ->
  T_{n-1} -> Env`; `build_env_expr` builds the actual environment argument
  fresh at each creation site, mirroring `compile.rs`'s own
  `push_closure_env` at the proof level — including a `Clo`-typed capture
  (e.g. capturing a closure-typed loop-carried parameter), not just `Int`.
  Scope, honestly: the *main*, top-level term must still
  be non-recursive (proving a self-recursive function's own body is
  `prove_tail_recursive_universal`'s job, not this one's — see its own
  row above); every `If` branch must denote as `Int`, or *both* as `Clo`
  (via `ite_clo : Int -> Clo -> Clo -> Clo`, postulated lazily since a
  term never choosing between two closures shouldn't pay for it) —
  reachable both when the `If`'s own result is used as a value (an
  argument to a closure-typed parameter, say) *and* when the `If` is a
  directly-called literal lambda's own top-level body: `call_ref`'s
  postulated return type is no longer a blanket `Int` assumption
  (`combinator_return_type` classifies it structurally, per `Hash`, once
  — see the "Future work" section below for how), so a combinator whose
  own body resolves to `Clo` gets an honest proof whether it's used as a
  bare *value* or *called* directly (including over-applied — see
  `compile.rs`'s own row above); and for a capturing
  combinator specifically, each captured value must resolve *directly* to
  one of the calling function's own parameters (not, transitively, to one
  of *that* function's own captures — one level of nesting only for now)
  and must be `Int`-typed, not `Clo` — `compile.rs` itself handles both
  more general cases fine, but extending this fragment's own `Int`/`Clo`
  discipline to a capture that might itself need *another* environment is
  meaningfully more machinery for comparatively little of what
  `compile.rs` actually exercises. Caught a real bug while building this:
  `ClosureCombinators::call_ref`'s own type construction read `int_ty`/
  `clo_ty` in a loop *before* possibly pushing a fresh `Env` postulate
  afterward, silently invalidating those earlier reads — the same
  staleness class `Anchored` exists to prevent, just inside one function's
  own type construction rather than across `denote_closure`'s recursive
  calls. Caught by the `#[cfg(debug_assertions)]` `debug_assert_has_type`
  checks on the very first test exercising a direct call to a capturing
  combinator, before it could reach anything outside this module. A
  literal lambda applied to *fewer* arguments than its own arity (a
  partial application, `compile.rs`'s own `register_partial_app`) also
  gets a value, `mk_pap_h_k : T_0 -> .. -> T_{k-1} -> Clo`, postulated once
  per `(h, k)` pair the same way `register_partial_app` itself dedups —
  the `k` supplied arguments are ordinary call-site subexpressions, denoted
  the normal recursive way rather than through any `Env`-style
  machinery, which makes this piece simpler than the capturing-closures
  one above. Now covers a *capturing* root too, mirroring `compile.rs`'s
  own `push_pap_env`: when the root captures, `mk_pap_h_k`'s postulated
  type takes the root's own `Env` as an extra leading parameter
  (`Env -> T_0 -> .. -> T_{k-1} -> Clo`, the same environment-first
  convention `call_h` uses), and every call site builds that environment
  via `build_env_expr` and prepends it to the supplied arguments. Caught
  the same class of indexing bug this fragment already had one
  example of: the postulate's own parameter types must be sliced from the
  *last* `k` entries of `h`'s `param_types` (the first-`k`-applied
  positions), not the first `k` — an initially-mis-drafted `param_types[..k]`
  slice, caught before being written by re-deriving `call_ref`'s existing
  wrap-order convention, and independently confirmed by a regression test
  built specifically to exercise it (mixed `Clo`/`Int` parameter types,
  where the two slices actually disagree — `add`'s own two `Int`
  parameters can't tell them apart). A combinator called or used as a bare
  value may itself be self-recursive (`Term::Rec`, not just `Term::Abs`
  — e.g. `let fact = rec f n = .. in fact 10`, or a direct `fact(10)`) —
  `register`/`call_ref`/`param_types_for` never look inside a combinator's
  own body regardless of whether it recurses (a call is always postulated
  opaque), so this needed only a wider match pattern, no new proof
  machinery; `compile::peel`/`compile::free_vars`/`compile::infer_closure_arities`
  were already generic over `is_rec` (`prove_tail_recursive_universal`'s own
  fragment already relied on that). `pap_ref` now covers a self-recursive
  root too, the same way: `compile.rs`'s own `register_partial_app`/
  `emit_pap_wrapper` never special-cased `is_rec` either (a PAP wrapper only
  ever forwards a static call to its root, indifferent to whether that
  root's own codegen happens to loop), so `pap_ref`'s own extra `is_rec`
  check was the only thing left rejecting it. Widening the capturing-PAP case
  surfaced a real bug in `prime_closure_postulates`'s own pre-priming pass:
  its partial-application branch primed `pap_ref` but not the transitive
  `mk_env_ref` a capturing root's `build_env_expr` call also needs, so
  that lazy push could still happen for the first time from inside a
  rolled-back `params_and_close_typed` scope — the exact staleness class
  this whole pre-priming mechanism exists to prevent, caught by
  `compile_fuzz`'s random-term fuzzing (not by any hand-written test) via
  a `debug_assert_has_type` panic in `denote_closure_typed`'s own partial
  application case.

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
  row above) — fixed, and now warm calls (20,000 iterations each) run at
  ~87µs total with memory staying bounded regardless of call count. Also
  `partial_application_loop`
  — the same idea for the compile-time partial-application desugaring
  (`register_partial_app`/`push_pap_env`): each iteration partially
  applies a literal lambda and completes it through a wrapper, so the
  synthesized wrapper combinator compiles once but its environment (the
  partially-applied function's own, empty, environment plus the
  newly-supplied argument) gets allocated fresh every time. Ran clean —
  no repeat of the capturing-closure bug, memory stays bounded across
  250k+ warm iterations — but noticeably slower than a plain capturing
  closure's warm call (~194µs vs. ~87µs, both 20,000 iterations), the expected cost of the
  extra indirection: creating the underlying function's own environment,
  then the wrapper's own, then a call through the wrapper on top of the
  real one. Also `closure_typed_loop_carried_parameter_loop` — the
  opposite shape from `capturing_closure_loop`: a closure-typed
  *parameter* (`inc`, non-capturing) threaded through every iteration and
  called via `call_indirect` each time, rather than a fresh closure
  created per iteration, isolating `call_indirect`'s own unpacking cost
  from closure-conversion's allocation cost. On this machine, warm calls
  (same 20,000 iterations) run at ~56µs, cheaper than either loop above (no
  environment to build at all, every iteration). The self-recursive function itself
  (`prove_tail_recursive_universal` covers a closure-typed loop-carried
  parameter, see "Proof strategies" above) gets the universal theorem,
  checked directly against it — but since a `Clo`-typed parameter can't be
  supplied through `jit.apply`'s plain-`i64` args from the outside, the
  benchmark itself bakes an initial closure in and calls through a
  wrapper, and `is_kernel_verified` on *that* wrapped term actually
  reflects `prove_closure_expr`'s own, separate "self-recursive combinator
  called directly" postulate (opaque either way) rather than the
  universal theorem — an honest distinction, not a weaker guarantee: the
  sample-based `verify()` against the interpreter is what actually gates
  trusting the compiled form regardless of which kernel proof accompanies
  it.
- `proofs.rs` — the cost of building each kind of kernel proof from
  `proof.rs`: one `refl` for a straight-line term, one relational
  (translation-validation) proof per call, and the one-time universal
  proof. Includes a direct N-relational-calls-vs.-one-universal-proof
  comparison, since that crossover is the actual argument for building the
  universal proof at all — on this machine it lands around 150-200 sample
  points (a universal proof ≈ 5ms once vs. ≈ 25µs per relational call), so
  which is cheaper depends entirely on how many sample points
  `jit.rs` would otherwise verify against. Also `closures_fragment_proof`
  — `prove_closure_expr`'s own cost across the closures fragment's shapes,
  none of which touch `build_universal`'s induction machinery at all (the
  top-level term must be non-recursive for this fragment): on this
  machine, `twice_inc_5` (non-capturing, the same term `main.rs`'s own
  demo uses) is the cheapest at ~10.3µs; a directly-called capturing
  closure costs ~14.4µs (the extra `Env` value); a non-capturing partial
  application ~11.8µs; a capturing one ~21.8µs (paying for both the PAP
  wrapper postulate and its own `Env`, on top of everything the
  non-capturing PAP case already does). Also
  `closure_typed_recursion_universal_proof` — `prove_tail_recursive_universal`'s
  own cost for a closure-typed loop-carried parameter (`iterate`'s
  shape, see the closures-fragment table row above), which unlike
  `closures_fragment_proof`'s own group *does* go through
  `build_universal`'s full induction pipeline
  (`denote_closure_typed`/`prime_closure_postulates`, not just
  `denote_closure`): at ~13.7ms, noticeably more than the same 2-leaf
  shape's plain-arithmetic counterpart (`gcd_2_leaves`, ~9.0ms above) —
  the closure-typed pipeline's extra bookkeeping costs something even on
  a term, like this one, that never actually creates a closure inside the
  loop.

## Fuzzing

**Differential**: `tests/compile_fuzz.rs` (`cargo test --test compile_fuzz`) generates
random terms — biased toward the closure/capture/self-recursion
interactions two real indexing bugs turned up in earlier, hand-derived
rather than found by any test failure — and checks that `jit::JitEngine`
(compiled, whenever `compile.rs` accepts the term) and `eval::apply_term`
(the reference interpreter) agree, across a battery of argument values
per term, not just the fixed small sample set `jit.rs`'s own internal
`verify()` checks before trusting a compile. Every generated term is
built to be well-typed on both readings (a generated closure sub-
expression always gets fully resolved back to an `Int` before it's used
anywhere an `Int` is expected), so a mismatch here means a genuine
divergence, not one side being fed a value it doesn't know how to
interpret. A tiny deterministic PRNG (splitmix64, no new dependency),
seed-scanned rather than relying on one lucky draw — a failure prints the
seed and argument trial that triggered it. Currently: 250 seeds × 12
argument trials each, ~99% of generated terms actually compile (the rest
fall outside the fragment by construction, e.g. curried-application
ambiguity), zero mismatches found so far.

One of the four program shapes it picks from, `gen_closure_typed_recursive`
(`rec f g n x = if n <= 0 then x else f(g, n-1, (g x) OP payload)`), is
also the only way this fuzzer's random bodies ever reach `proof.rs`'s
closure-typed-parameter pipeline directly: wrapping a fresh initial
closure in so the term is runnable through `jit.apply` (there's no way to
hand a real `Clo` value in through a plain-`i64` arg otherwise) means
`jit.rs`'s own `kernel_verify` cascade is satisfied by `prove_closure_expr`'s
opaque "self-recursive combinator called directly" postulate before it
ever reaches `prove_tail_recursive_universal` — so the test checks the
bare self-recursive combinator against `prove_tail_recursive_universal`
directly too, on every trial that generates this shape (~25% of seeds).
This generator's `payload` can itself be a `gen_closure_block`, so it
sometimes combines a loop-carried closure *parameter* with a second,
independently created-and-called closure in the same self-call argument —
a shape nothing else here produces. `gen_tail_recursive`'s own
`gen_closure_block` payload is what originally surfaced the
`prime_closure_postulates`/`mk_env_ref` staleness bug documented in "Proof
strategies" above, this fuzzer's first genuine catch (not by any
hand-written test) — `gen_closure_typed_recursive` widens the same kind of
coverage to a recursion shape that generator can't produce at all.

The same file's second test, `compile_rejects_out_of_scope_terms_cleanly`,
checks the complementary property: terms deliberately built *outside* the
fragment (a parameter called with inconsistent arities, a genuinely
unbound variable) must always come back `None` from `try_compile`, never
get silently accepted and miscompiled — a property the first test's
generator, which only ever produces in-fragment terms, has nothing to say
about. Verified these checks actually have teeth (not just vacuously
passing) by deliberately weakening the inconsistent-arity checks
(`scan_for_closure_calls`'s and `compile_node`'s own per-call-site check)
together, which immediately failed the test on the first seed, as
expected. A third generator in the same file, `gen_over_applied`, covers
a *different* property now that `try_compile` compiles an over-applied
literal lambda's *shape* unconditionally (see `compile.rs`'s own "Over-
application" docs): its own bodies are always plain arithmetic, never a
further closure, so every term it generates is genuinely ill-typed;
`over_applied_ill_typed_terms_still_agree_with_the_interpreter` confirms
`jit.rs`'s sample verification catches every one of these (a trap, or a
coincidentally-successful-but-wrong `call_indirect`) and falls back to
the interpreter, rather than `try_compile` rejecting the shape outright.

**Robustness**: `tests/kernel_fuzz.rs` fuzzes a different layer entirely: `kernel.rs`'s
own type-checker, directly, with no well-typedness discipline on the
generated terms at all (unlike `compile_fuzz.rs`, which only ever feeds
terms already known to be well-typed on both readings). Random `Expr`
trees — `Var`s sometimes genuinely in scope, sometimes deliberately just
past it, sometimes wildly unbound; `Sort`s occasionally at `u32::MAX` —
are checked only for one property: `infer`/`check`/`typecheck` never
panic, whatever nonsense they're asked to type-check; almost every
generated tree is simply rejected with an ordinary `Err`, which is the
expected, uninteresting outcome. A second test targets `check`'s own
top-level `Lam`-against-`Pi` special case directly (an independently
generated lambda checked against an independently generated `Pi`), since
nothing built on `typecheck` alone (a bare `infer` call at the root) ever
reaches it. This fuzzer's first run caught a real bug immediately: `infer`'s
`Sort(i) => Sort(i + 1)` case overflowed (a checked-in-debug-builds panic,
not a clean type error) for `Sort(u32::MAX)` — fixed with `checked_add`,
returning an honest `Err` ("universe overflow") instead. Verified test
teeth by reverting the fix: the fuzzer catches it again immediately (seed
16 out of 5,000, on the very first run at that seed count). Stress-tested
at 100,000 seeds (release) and 30,000 (debug, where the now-fixed overflow
check would have fired) with zero further failures before settling back
on the file's own 5,000-seed default.

**Round-trip**: `tests/syntax_fuzz.rs` fuzzes a third property, on a third
layer: `syntax.rs`'s own `parse(print(h)) == h` (exact content-hash
equality) for a random, well-scoped term across every constructor
(`Prim` with all eight operators, `If`, `Abs`, `App`, `Rec` of random
arity), with random right/left nesting — the same kind of shape
`syntax.rs`'s own hand-written tests cover with a handful of hand-picked
precedence traps (a right-nested subtraction a left-associative parser
would never itself produce, a nested comparison, an application argument
that's itself an application), generated far more broadly than anyone
would think to hand-pick. Deliberately stays inside `print`'s own
documented contract — every generated `Var` is genuinely bound (`print`
isn't written to handle an out-of-scope one; it isn't even a `Result`-
returning function) and every literal is non-negative (the one
documented, accepted round-trip gap, since this grammar has no negative-
literal syntax at all). Passed clean on its first run and stress-tested
at 200,000 seeds and, separately, depth 10 (up from the file's own
default of 6) with zero failures — confirmed real teeth anyway by
deliberately weakening `print_at`'s own right-hand-side strictness rule
for left-associative operators (`(p, p + 1)` → `(p, p)`, exactly the bug
class `round_trips_arithmetic_with_mixed_precedence_and_right_nesting`
guards against by hand): caught immediately, at seed 22.

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
- Combining closures with self-recursion more fully in one proof.
  `prove_tail_recursive_universal` now covers a closure-typed *parameter*
  threaded through recursion, *and* a closure genuinely created and
  called anywhere in the body — a self-call argument (`f(n-1, (\y.
  acc+y)(n))`, the `capturing_closure_loop` shape) or a leaf's own
  top-level expression (`(\y. n+y)(5) + f(n-1)`) alike — and
  `prove_closure_expr` now covers a self-recursive combinator called or
  used as a value from a non-recursive main term (see the table rows
  above). What's still open: a concrete *instance* proof for either
  closure-creation shape (`eval_and_prove`/`build_ev_witness` remain
  untouched, still reject `App`/`Abs`) — doesn't affect `kernel_verified`,
  only weaker, call-specific evidence.
- `prove_closure_expr` now covers an `If` choosing between two closures
  too (`ite_clo`, lazily postulated — see the table row above), when the
  `If`'s own result is used as a *value* — and, separately, `call_ref`'s
  own postulated return type is no longer a blanket `Int` assumption:
  `combinator_return_type` structurally classifies a literal lambda's own
  saturated-call return type (`Int` or `Clo`) once per `Hash`, without
  denoting its body in the usual (postulate-building) sense — well-founded
  since a self-call is always `Int` by this fragment's own convention and
  calling *any* closure value (a parameter, a capture, or another
  directly-called combinator's own result) is too, so the classifier only
  ever needs to look at each combinator's own declared parameters and its
  own `If`/literal-lambda-call shape, never a captured free variable's
  actual type. This closes two previously-open cases at once: a
  *directly-called* combinator whose own body is an `If` between two
  closures (see the table row above), and over-application of a literal
  lambda (`root`'s own saturated call, now denoted via the same
  `call_ref`, dispatched on the extra arguments through `apply_ref`
  exactly like calling a closure-typed variable — see `compile.rs`'s own
  "Over-application" docs for the compiled-code-level counterpart).
- Widening the compilable fragment further: a variable called with
  inconsistent arities across sites (a genuinely different, harder problem
  than over-application — there's no fixed arity to desugar around at
  all, only whatever the variable's consistently called with), more
  primitives. (Capturing closures and partial application of a literal
  lambda — real closure conversion, an environment representation,
  calling a closure reached through a captured free variable, a
  compile-time-desugared synthesized wrapper for an under-applied literal
  — landed, as has over-application of a literal lambda — dispatching a
  saturated call's own result through `call_indirect`, the same as
  calling a closure-typed variable; see `compile.rs`'s own module docs.)
- `prove_closure_expr` now covers *capturing* closures too (`mk_clo_h`/
  `Env`/`build_env_expr` — see the table row above and `proof.rs`'s own
  section docs), including a captured `Clo` value (e.g. capturing a
  closure-typed loop-carried parameter), not just `Int` — `Env`/`mk_env`
  are keyed by the whole capture signature (`capture_sig`), not a count,
  so a mixed-type environment gets its own honestly-typed postulate.
  Each captured index must still resolve directly to one of the calling
  scope's own parameters; a captured value that's itself a capture of
  that scope (`compile_var_read`'s own recursive case, for a function
  that's itself a capturing closure) has no proof-side counterpart, not
  because it's deferred, but because it can't arise here: `denote_closure`
  never enters a registered combinator's own body, and `compile::peel`
  always folds consecutive `Abs` layers into one combinator before it's
  ever registered, so there's no way for this fragment to encounter one
  combinator's own body containing another, separately registered one —
  every capture list is always relative to the one flat ambient scope
  currently being denoted.
- `prove_closure_expr` now covers partial application of a literal lambda
  too (`mk_pap_h_k`/`pap_ref` — see the table row above and `proof.rs`'s
  own section docs), including a *capturing* root: `pap_ref`'s postulated
  type takes the root's own `Env` as a leading parameter (mirroring
  `call_ref`'s own environment-first convention) when the root captures,
  and every call site builds that environment via `build_env_expr` and
  prepends it, mirroring `compile.rs`'s own `push_pap_env`, which composes
  a PAP wrapper's own environment with a copy of the root's. Also covers
  partial application of a *self-recursive* combinator, the same opaque-call
  reasoning `register`/`call_ref` already use for a direct call or bare
  value (`compile.rs`'s own `register_partial_app`/`emit_pap_wrapper` never
  special-cased `is_rec` either). Over-application (more arguments than
  arity) stays out of scope on both readings.
