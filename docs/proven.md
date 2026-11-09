# What is checked, and how

The routine run after every change, the exact reach of the proofs, and the fuzzers that test what the proofs do not cover.

## Validation

The full routine, run after every change:

```sh
cargo build --workspace --all-targets
cargo test --workspace --lib --bins
cargo clippy --workspace --all-targets
cargo test --release --test compile_fuzz --test syntax_fuzz
cargo test --release -p tatic-kernel --test kernel_fuzz --test kernel_soundness_fuzz
cargo test --release --lib ir_fuzz -- --ignored
cargo test --release -p tatic-wasm --lib a_large_check -- --ignored
cargo bench
cargo run --release
```

`cargo bench` is in that list deliberately. It used to be left out on the
reasoning that `--all-targets` already builds the benchmarks — which it
does, and which is exactly why a stack overflow sat unnoticed in
`crates/tatic/benches/execution.rs` until someone ran them (`docs/related-work/` §30).
Building a target proves nothing about running it.

A full `cargo bench` takes a while — `fib_30`'s interpreter bar alone is
over a second per iteration. When the point is "does it still run", not
"how fast", cut the sweep down per suite:

```sh
cargo bench --bench execution -- --warm-up-time 0.3 --measurement-time 0.5 --sample-size 10
cargo bench --bench proofs    -- --warm-up-time 0.3 --measurement-time 0.5 --sample-size 10
```

Those flags need `--bench <name>`; passing them to a bare `cargo bench`
fails, because that also runs the lib unittest target, which doesn't
understand criterion's arguments.

A note on what "clean" means here: `cargo bench` prints criterion's
`change:` percentages against whatever it last stored, which on a fresh
checkout is nothing. Treat a regression line as a prompt to look, not as
a failure.

To compare two versions, `scripts/gate/bench_ab.sh [REV] [cargo bench args]
[-- criterion args]` (default `HEAD`) benchmarks `REV` in a worktree
under `target/bench-ab`, then the working tree, then `REV` again, and
prints each bench's change next to the change the re-run of `REV` shows.
Re-running unchanged code on this laptop moves benches by up to
±100%, so only a change well beyond that noise column means anything.
For example, `scripts/gate/bench_ab.sh HEAD --bench proofs`.

The A/B gate on two builds is `scripts/gate/streams_ab.sh`. Its arms and
other timings of the church_bv sweeps go through `tools/runs` (its
`main.rs` header and `runs` with no arguments list the commands).
`runs time <dir> --rounds N -- <arm> -- <arm>` runs arms in
alternating rounds, each in a job object that counts every process it
starts; it waits for a quiet machine before each round and keeps only the
rounds no other process loaded (docs/related-work/ §66). `runs state` prints
Defender's real-time protection, the CPU load and the large-page privilege.

## What's actually proven, and what isn't

This is stated precisely because it would be easy to overclaim here.

- **Straight-line (non-recursive) terms**: `proof.rs` builds one kernel
  proof covering *every* input. `lower_wat.rs`'s instruction emission and
  `eval.rs`'s evaluation recurse over this fragment in exactly the same
  shape, so the proof is `refl` — an honest witness that a stack-based and
  a tree-walking evaluation of side-effect-free code compute the same
  value by construction, not a shortcut.
- **Recursive terms, tail or not** (`gcd`'s `loop`, factorial's or naive
  Fibonacci's plain `call`): proven two ways. `prove_closure_expr_instance`
  validates one *execution* — for one specific call, the proof follows
  the interpreter's actual execution trace, symbolically composing each
  step's new parameters (recursing into non-tail self-calls too, wherever
  they sit), until it reaches a base case; a genuine per-call certificate,
  checked by the kernel, but not a universal theorem. Deliberately *not*
  called translation validation: that term means validating one
  *compilation*, whose success covers every input — see `proof.rs`'s
  module docs for why the distinction is the whole point here.
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
  `build_ev_witness`/`eval_and_prove` -- **deleted 2026-10-26, "CU3"**: it was
  off the JIT path, whose per-call proofs come from
  `prove_closure_expr_instance`; the rest of this bullet is the record of
  what it did), grounded in one postulated axiom
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
  branching leaf is now also fast. Profiling `fib(8)`'s instance proof
  found `shift` dominating by three orders of magnitude, with the same
  subterm reshifted by the same amount repeatedly. A scoped shift cache
  (`with_shift_cache`, engaged from a dry run of the instance) won ~2x for
  a while. The reshifts turned out to come from `subst_top` substituting
  eagerly, shifting its argument at every binder crossed. It now
  substitutes in one pass (`docs/related-work/` §53), which made `fib(8)`'s
  instance about 18 times faster, and the cache, now a net loss, is gone
  (§54).
- **Closures combined with self-recursion, in `prove_tail_recursive_universal`**:
  covers a self-recursive function whose own parameters may be
  `Clo`-typed — threaded through the recursion unchanged, or called via
  `apply_k` within a leaf or a self-call argument — e.g. "iterate a closure
  `n` times": `rec f n g x = if n<=0 then x else f(n-1, g, g(x))`, a shape
  `compile.rs` already compiled (its own `infer_closure_arities`/
  `build_node` machinery is generic over self-recursion vs. not) but that
  had no proof strategy at all before this. This part needs only `Clo`/
  `apply_k`, reused directly via `ClosurePostulates: Deref<Target =
  ArithPostulates>`, which lets the whole induction pipeline (`Ev`,
  `loop_val`, the congruence/transitivity chaining) keep calling every
  plain-arithmetic postulate method unchanged. (Deleted 2026-10-26, "CU3":)
  `prove_tail_recursive_instance`/
  `_with_instances`'s own per-call specialization still declined whenever
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
  `Int`) that fails the same way when the fix is reverted (the pre-push
  and `apply_ref` itself are both removed in stage 4: a push inside a
  scope stopped panicking, and `clo_ty` no longer pushes, so there is no
  memo entry left to go stale, `docs/related-work/` §72).

  A self-call *argument* may also genuinely *create* a closure and call it
  right there, e.g. `f(n-1, (\y. acc+y)(n))` — exactly the shape
  `compile.rs`'s own `self_recursion_creating_a_fresh_capturing_closure_every_iteration_compiles`
  test and `capturing_closure_loop` benchmark already exercise, previously
  compiled but never proven. `denote_closure`'s `SelfCalls::Reject` reading
  (the self-call-argument denotation `new_params_for` uses) shares its
  `Term::Abs`/`Term::Rec` handling with the whole-body reading, now that the induction
  pipeline's own postulate-and-combinator bookkeeping is a full
  `ClosureCombinators` (not just `ClosurePostulates`) — registering a
  combinator, calling one directly, or partially applying one (still never
  a *recursive* root, matching `pap_ref`'s own restriction) all reuse the
  exact same methods `prove_closure_expr` does. A leaf's own *top-level*
  expression gets the identical treatment (the `SelfCalls::Placeholders`
  reading and `find_self_calls`, widened the same way) — e.g. `(\y. n+y)(5) + f(n-1)`,
  a closure-call's result combined arithmetically with the recursive call
  directly, not nested inside any self-call's own argument list. Caught
  the *same class* of staleness bug a second time, in a new place:
  `register`/`call_ref`/`pap_ref`, and transitively `mk_env_ref`/`env_ty`
  for a capturing one, are all lazily memoized exactly like `apply_ref`,
  and could just as easily be triggered for the first time from inside a
  temporary scope. Since these registrations depend only on a combinator's
  hash and a capture *count* — never the actual parameter values —
  `prime_closure_postulates` pre-triggered every one a self-call argument
  *or a leaf's own expression* would need via a lightweight structural walk
  (no parameter values needed at all), the same upfront-priming fix
  widened to cover closure creation, not just a call through a parameter —
  removed in stage 4, once a push inside a scope stopped panicking
  (`docs/related-work/` §72).
  Also honestly scoped: the *instance* (per-call) specialization remains
  untouched and still rejects a self-call argument or leaf expression that
  creates a closure — `kernel_verified` doesn't depend on that, so this
  doesn't weaken what actually gets verified, only what gets additional,
  call-specific evidence.
- **Closures, non-capturing, capturing, and partially applied**: `prove_closure_expr` gives a
  closed, non-recursive closures term one kernel proof covering every
  input, a `refl`-on-a-shared-translation argument, as for straight-line
  arithmetic — nothing here evaluates anything
  concrete, so it needs no `assume_prim_fact`-style grounding either. A
  closure value is postulated opaque (`Clo : Sort(0)`, `Int`'s own
  "postulated type" pattern). Calling one *through a parameter*
  (`call_indirect`) goes through `apply_k : Clo -> Int^k -> Int`, one per
  distinct arity actually used that way — unaffected by whether the
  underlying closure captures anything, the same way `lower_wat.rs`'s own
  `call_indirect` dispatch doesn't need to know either. A combinator's own
  *body* is never unfolded or denoted (no walk over every registered
  combinator the way `compile::build` needs): a *non-capturing* one gets one fixed
  `Clo`-typed constant (`combinator_value`, referenced by identity) and one
  signature-specific `call_h : T_0 -> .. -> T_{k-1} -> Int` for a direct
  call — needed because a combinator like `twice` takes a mix of closure-
  and `Int`-typed arguments, which the uniform `apply_k` can't express. A
  *capturing* one can't use one fixed constant honestly — `compile.rs`
  builds a fresh environment at every creation site, so the same
  combinator denotes differently depending on where it's referenced — so
  instead `mk_clo_h : Env -> Clo` (a function of the environment) and
  `call_h : Env -> T_0 -> .. -> T_{k-1} -> Int` (environment prepended,
  mirroring `lower_wat.rs`'s own `$env`-first calling convention; a
  lambda-lifted combinator gets the same values as separate parameters), where
  `Env : Sort(0)` is postulated once *per capture signature* (`capture_sig`
  — which slots are `Clo`-typed, which are `Int`; shared across every
  combinator whose captures match that exact signature, the same way
  `apply_k` is shared by arity) with constructor `mk_env : T_0 -> .. ->
  T_{n-1} -> Env`; `build_env_expr` builds the actual environment argument
  fresh at each creation site, mirroring `lower_wat.rs`'s
  `push_closure_env` at the proof level — including a `Clo`-typed capture
  (e.g. capturing a closure-typed loop-carried parameter), not just `Int`.
  Scope, honestly: the *main*, top-level term must still
  be non-recursive (proving a self-recursive function's own body is
  `prove_tail_recursive_universal`'s job, not this one's — see its own
  entry above); every `If` branch must denote as `Int`, or *both* as `Clo`
  (via `ite_clo : Int -> Clo -> Clo -> Clo`, postulated lazily since a
  term never choosing between two closures shouldn't pay for it) —
  reachable both when the `If`'s own result is used as a value (an
  argument to a closure-typed parameter, say) *and* when the `If` is a
  directly-called literal lambda's own top-level body: `call_ref`'s
  postulated return type is no longer a blanket `Int` assumption
  (`combinator_return_type` classifies it structurally, per `Hash`, once
  — see its docs in `crates/tatic/src/proof/closures.rs` for how), so a combinator whose
  own body resolves to `Clo` gets an honest proof whether it's used as a
  bare *value* or *called* directly (including over-applied — see
  `lower_wat.rs`'s row in `README.md` and its "Over-application" docs); and for a capturing
  combinator specifically, each captured value must resolve *directly* to
  one of the calling function's own parameters, freely `Int`- or
  `Clo`-typed (`Env`/`mk_env` keyed by the whole capture *signature*, not
  just a count, so a mixed-type environment gets its own honestly-typed
  postulate). A captured value that's itself a capture of the *calling*
  scope isn't a deferred restriction at all — it can't arise: a call is
  always postulated opaque (this fragment never enters a registered
  combinator's own body), and `shape::peel` always folds consecutive
  `Abs` layers into one combinator before it's ever registered, so there's
  no way to encounter one combinator's own body containing *another*,
  separately-registered one — every capture list is always relative to
  the one flat ambient scope currently being denoted. Caught a real bug while building this:
  `ClosureCombinators::call_ref`'s own type construction read `int_ty`/
  `clo_ty` in a loop *before* possibly pushing a fresh `Env` postulate
  afterward, silently invalidating those earlier reads — the same
  staleness class `Anchored` existed to prevent (removed in stage 4,
  `docs/related-work/` §72), just inside one function's own type construction
  rather than across `denote_closure`'s recursive calls. Caught by the `#[cfg(debug_assertions)]` `debug_assert_has_type`
  checks on the very first test exercising a direct call to a capturing
  combinator, before it could reach anything outside this module. A
  literal lambda applied to *fewer* arguments than its own arity (a
  partial application, `compile.rs`'s own `register_partial_app`) also
  gets a value, `mk_pap_h_k : T_0 -> .. -> T_{k-1} -> Clo`, postulated once
  per `(h, k)` pair the same way `register_partial_app` itself dedups —
  the `k` supplied arguments are ordinary call-site subexpressions, denoted
  the normal recursive way rather than through any `Env`-style
  machinery, which makes this piece simpler than the capturing-closures
  one above. Now covers a *capturing* root too, mirroring `lower_wat.rs`'s
  `Lowering::pap_env`: when the root captures, `mk_pap_h_k`'s postulated
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
  machinery; `shape::peel`/`shape::free_vars`/`shape::infer_closure_arities`
  were already generic over `is_rec` (`prove_tail_recursive_universal`'s own
  fragment already relied on that). `pap_ref` now covers a self-recursive
  root too, the same way: `compile.rs`'s `register_partial_app`/
  `lower_wat.rs`'s `emit_pap_wrapper` never special-cased `is_rec` either (a PAP wrapper only
  ever forwards a static call to its root, indifferent to whether that
  root's own codegen happens to loop), so `pap_ref`'s own extra `is_rec`
  check was the only thing left rejecting it. Widening the capturing-PAP case
  surfaced a real bug in `prime_closure_postulates`'s own pre-priming pass:
  its partial-application branch primed `pap_ref` but not the transitive
  `mk_env_ref` a capturing root's `build_env_expr` call also needs, so
  that lazy push could still happen for the first time from inside a
  rolled-back `params_and_close_typed` scope — the exact staleness class
  this whole pre-priming mechanism existed to prevent (both the priming
  pass and the scope-open panic it guarded against are gone as of stage 4,
  `docs/related-work/` §72), caught by
  `compile_fuzz`'s random-term fuzzing (not by any hand-written test) via
  a `debug_assert_has_type` panic in `denote_closure`'s own partial
  application case.

Installing a compiled form takes three checks. The term must be simply
typed (`typing::well_typed`; compiled code can't tell an `Int` from a
closure, docs/related-work/ §38). `jit.rs` runs the candidate against the
interpreter on a battery of sample inputs, *and* requires `proof.rs` to
have produced a kernel-checked theorem covering every input. A term that
passes the samples but has no such theorem is cached as
`NoUniversalProof` and served by the interpreter from then on
(`Stats::declined_no_universal_proof`).

The last two cover different things, which is why both are required.
The sample battery runs the WAT wasmtime actually runs. The kernel
theorem is the only check that says anything about inputs outside the
battery. For a straight-line fragment term it is about the emitted
instruction list itself (`proof/gate.rs`); for every other term it is
stated over `proof.rs`'s `denote`, which *models* the compiler
(`build_node` and the `lower_wat` templates) rather than reading its
output. There the pair is strictly stronger than either alone, and still
short of end-to-end soundness.

What counts as "a theorem covering every input" (`kernel_verify`,
reported by `JitEngine::is_kernel_verified`):

- For a term in the straight-line fragment (`proof/gate.rs#in_fragment`),
  the gate's theorem alone (`jit.rs#prove_install`): the emitted
  instruction list, run on `tatic_wasm`'s machine at n = 64, equals the
  source term for every input. This one is about the code that runs, not a
  model of the compiler.
- `prove_closure_expr` or
  `prove_tail_recursive_universal`: one theorem covering every input. This
  is genuinely stronger than the sample battery. Every input means every
  `Int`, which is all the JIT passes: a theorem that types a called
  parameter as a closure doesn't count (docs/related-work/ §42).
- At arity 0 only, `prove_closure_expr_instance`'s per-execution
  certificate: there the
  one possible call is the entire input space. Above arity 0 such a
  certificate covers only the vectors `verify()` already checked, so the
  gate doesn't build it; a term with nothing better would otherwise serve
  arbitrary `i64` arguments on the strength of nine sampled points, which
  is the whole reason the gate exists.

The price is real and worth stating plainly: the JIT is now withdrawn
from the inconsistent-arity curried-dispatch shapes the `Samples`
certificates exist for — the capability `compile.rs` went to genuine
trouble to support — whenever they take arguments. A closed (arity-0)
one still installs, since its one certificate covers its one input, but
only while its trace fits the 200-step budget. Measured against this
repo's own corpus: zero demo terms, two tests, and one benchmark, which
now runs its loop at 150 iterations instead of 20,000 to stay installed
(§30 of `docs/related-work/`). It is a capability regression, and the way to undo it is to widen the universal
fragment rather than to relax the gate. See §28 of `docs/related-work/` for
what that would take.

## Fuzzing

**Differential**: `crates/tatic/tests/compile_fuzz.rs` (`cargo test --test compile_fuzz`) generates
random terms — biased toward the closure/capture/self-recursion
interactions two real indexing bugs turned up in earlier, hand-derived
rather than found by any test failure — and checks that `jit::JitEngine`
(compiled, whenever `compile.rs` accepts the term) and `eval::apply_term`
(the reference interpreter) agree, across a battery of argument values
per term, not just the fixed small sample set `jit.rs`'s own internal
`verify()` checks before trusting a compile. Every `gen_program` term is
built to be well-typed on both readings (a generated closure sub-
expression always gets fully resolved back to an `Int` before it's used
anywhere an `Int` is expected), so a mismatch here means a genuine
divergence, not one side being fed a value it doesn't know how to
interpret. A tiny deterministic PRNG (splitmix64, no new dependency),
seed-scanned rather than relying on one lucky draw — a failure prints the
seed and argument trial that triggered it. Currently: 1000 seeds × 12
argument trials each, ~99% of generated terms actually compile (the rest
fall outside the fragment by construction, e.g. curried-application
ambiguity), zero mismatches found so far. A separate test wraps a term
that goes wrong (ill-typed, or a closure of the wrong arity) in a branch
taken only at an input no sample reaches, in plain functions, loops and
recursion, so only the JIT's static gates
(the type check and the universal-proof requirement) can keep it out;
disabling either one fails it (docs/related-work/ §41).

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
`prime_closure_postulates`/`mk_env_ref` staleness bug documented in "What's actually
proven, and what isn't" above, this fuzzer's first genuine catch (not by any
hand-written test) — `gen_closure_typed_recursive` widens the same kind of
coverage to a recursion shape that generator can't produce at all.

The same file's second test, `compile_rejects_out_of_scope_terms_cleanly`,
checks the complementary property: terms deliberately built *outside* the
fragment must always come back `None` from `try_compile`, never get
silently accepted and miscompiled — a property the first test's
generator, which only ever produces in-fragment terms, has nothing to
say about. Originally covered both a parameter called with inconsistent
arities and a genuinely unbound variable, verified to actually have teeth
(not just vacuously passing) by deliberately weakening the
inconsistent-arity checks (`scan_for_closure_calls`'s and
`compile_node`'s, now `build_node`'s, own per-call-site check) together, which immediately
failed the test on the first seed, as expected. The inconsistent-arity
case moved out once `try_compile` stopped rejecting that shape
altogether (see the curried-dispatch mechanism, "Generic closure
dispatch" in `lower_wat.rs`'s module docs) — its own soundness property (jit.rs's
verification/fallback still agrees with the interpreter for whatever
garbage value such a call site is actually fed) is checked instead by
`inconsistently_called_parameters_still_agree_with_the_interpreter`,
right next to `over_applied_ill_typed_terms_still_agree_with_the_interpreter`,
which already covered the analogous property for over-application; only
the unbound-variable check is left here now. A third generator in the
same file, `gen_over_applied`, covers
a *different* property now that `try_compile` compiles an over-applied
literal lambda's *shape* unconditionally (see `lower_wat.rs`'s "Over-
application" module docs): its own bodies are always plain arithmetic, never a
further closure, so every term it generates is genuinely ill-typed;
`over_applied_ill_typed_terms_still_agree_with_the_interpreter` confirms
`jit.rs` declines every one of these as ill-typed (`typing.rs`, §38 of
`docs/related-work/`) and falls back to the interpreter, rather than
`try_compile` rejecting the shape outright.

The same file's `specialisation_is_checked_and_preserves_meaning_on_random_terms`
extends this fuzzer's generators (adding `Div`/`Mod`) to check `specialise.rs`
and `spec_check.rs` (§37 of `docs/related-work/`): every one of 1000 random
terms is specialised and checked, `spec_check::check` must accept every
trace produced, and `eval` on the original and specialised term must agree
exactly on the sample arguments — including which error variant, not just
whether one occurred. One seed in five is an open term
(`gen_unbound_variable`, bare or under a redex): it must get the empty
trace, and the checker must reject it. Every term also goes through
`compile_specialised`, and its fragment is run directly (no `verify()` in
between) against `eval` on the same arguments, for every term
`typing::well_typed` accepts (compiled code assumes well-typedness, and
`gen_redex_rich` can use a closure as an `Int`). For those terms it also
checks type safety: `eval` must never give `TypeError`, `NotAFunction` or
`UnboundVariable`. And `JitEngine` must agree with `eval` on every term,
typed or not (§38 of `docs/related-work/`). 645 of the 1000 seeds specialise, 564 compile
(213 from `h'`), and 4400 compiled runs are compared. Verified test teeth by two planted bugs: a
specialiser bug that produces a wrong term is caught by `spec_check`
rejecting its trace; making both the checker and the specialiser agree on
an unsound step (treating a `Prim` expression as a value) passes the
certificate check but is still caught, by the `eval` comparison
disagreeing on a `Div` term.

**Robustness**: `crates/tatic-kernel/tests/kernel_fuzz.rs` fuzzes a different layer entirely: `tatic-kernel`'s
own type-checker, directly, with no well-typedness discipline on the
generated terms at all (unlike `compile_fuzz.rs`, whose terms are built
to be meaningful to both the interpreter and the compiler). Random `Expr`
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

**Soundness**: `crates/tatic-kernel/tests/kernel_soundness_fuzz.rs` fuzzes a different property
than `kernel_fuzz.rs`'s own crash-safety — the one every "kernel-checked
equivalence proof" this project produces actually rests on: given two
postulated constants of the same type with *nothing* in the context
relating them, `kernel::check` must never accept *any* term as a proof
that they're propositionally equal (`Id(A, a, b)`). This is deliberately
not "is `a` `def_eq` `b`" — a *postulated* equality is legitimately
`Id`-provable without being computationally equal at all (that's the
whole point of postulating axioms rather than deriving everything from
nothing) — the property under test is narrower and sharper: can the
kernel be talked into deriving a false proposition from an unrelated
pair? Two strategies, both checked against the same unrelated pair's
claim: pure random generation (as `kernel_fuzz.rs`'s own generator does),
and — the sharper one — random single-point mutation (a structural
subtree swap, or a wildly different `Var`/`Sort` substituted in) of a
proof that's genuinely valid for a *different*, actually-related pair,
since starting from a well-typed skeleton is far more likely to land
near a real checker bug than blind generation is. Verified test teeth by
deliberately injecting two different bugs and confirming each is caught:
an off-by-one in `ctx_lookup`'s own de Bruijn shift (too blunt — it broke
typechecking universally, caught only by this file's own "the seed pool
itself is valid" sanity check, not the soundness property specifically)
and, more precisely, weakening `check`'s final comparison to only compare
an `Id`-type's own domain when both sides are `Id`-typed, ignoring the
two endpoints entirely — caught immediately by both dedicated soundness
tests (seed 7 and seed 97 respectively, out of 20,000), while the sanity
check kept passing, confirming these tests actually discriminate a real,
narrow false-equality bug rather than merely reacting to wholesale
breakage.

**Round-trip**: `crates/tatic/tests/syntax_fuzz.rs` fuzzes a third property, on a third
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
returning function); literals of both signs are generated. Passed clean on its first run and stress-tested
at 200,000 seeds and, separately, depth 10 (up from the file's own
default of 6) with zero failures — confirmed real teeth anyway by
deliberately weakening `print_at`'s own right-hand-side strictness rule
for left-associative operators (`(p, p + 1)` → `(p, p)`, exactly the bug
class `round_trips_arithmetic_with_mixed_precedence_and_right_nesting`
guards against by hand): caught immediately, at seed 22.

