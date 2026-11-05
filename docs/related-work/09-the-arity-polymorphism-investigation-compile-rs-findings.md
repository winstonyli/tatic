## 9. The arity-polymorphism investigation (compile.rs) — findings worth keeping

While scoping "let a closure-typed variable be called with a different
number of arguments at different sites" (README's own long-standing
"still open" item), investigation found the real blocker is deeper than
a missing case:

- Every closure value is one packed `i64` (Wasm table index + a linear-
  memory environment pointer) with **zero spare bits for a runtime arity
  tag** (`src/compile.rs`, `push_closure_env`/the packing code near the
  closure-value call sites).
- Every combinator gets its **own exact Wasm function type**, sized to
  its own real arity — there is no fixed/padded max-arity ABI
  (`compile_function`, `emit_pap_wrapper`).
- Wasm's `call_indirect` requires the type at the call site to match the
  callee's real type or it traps, and this compiler declares one
  `call_indirect` type per distinct arity actually used, chosen at
  *compile* time per call site (`try_compile`'s `used_arities`
  deduplication, and the `Term::Var` arm of `compile_node`) — there is no
  single call site today that can dispatch to "whatever arity this table
  entry happens to have."

Real precedent for solving this exists and was confirmed directly, not
approximated: **GHC's STG machine** represents an under-applied closure
as a `PAP` object storing the underlying function's own arity, dispatched
through a small family of **generic apply** routines that check that
stored arity at runtime; **Lean 4's own compiler** (the most directly
relevant precedent, since it's also a dependently-typed proof assistant
compiling itself) represents a closure as a `lean_closure_object` holding
a function pointer, its arity, and its number of already-fixed arguments,
right in the object.

The conclusion this investigation reached: closing this gap for real
needs a **uniform calling convention** (either fully curried, one
argument at a time — the same "everything is unary" convention every
classical HOL/λ-calculus system uses, which is *why* those systems never
have an arity problem in the first place — or thin fixed-signature
trampoline adapters wrapping today's arity-specific functions), not an
incremental patch on the current representation. This is a genuine
multi-session backend rewrite, not a single-session feature; the
"pre-generate every `(root, k)` curry-chain wrapper eagerly" narrower
alternative was also considered and rejected as only covering the case
where a variable's closure value is statically traceable to a finite set
of literal lambdas — it does not cover a closure of genuinely unknown
runtime origin (an arbitrary parameter, or an `If` between differently-
shaped closures), so it would not actually deliver arity polymorphism as
a real capability.

**Since implemented.** This turned out to be exactly the "thin
fixed-signature trampoline adapters" alternative above, not the rejected
narrower one, and not full currying as the sole calling convention
either (a real perf regression on every existing saturated call, and not
what either cited precedent actually does). Concretely: `Combinators`'
own fully-discovered registered-combinator set (the same one the
existing fixpoint already builds for every literal lambda reachable
anywhere in a term) gets a curried "stage chain" per combinator
(`emit_curried_stages` — `stage_0..stage_{arity-1}`, one argument at a
time, sharing one `$ty1`-shaped `call_indirect` type) whenever *any*
variable anywhere in the compiled fragment is found called at
inconsistent arities; every closure-typed-variable call site in that
fragment then dispatches through it (`emit_dynamic_apply`) instead of
the ordinary fast path — not just the call sites that are themselves
inconsistent, since this compiler has no type system to locally rule out
a value flowing from one to the other. This is why it isn't the
rejected, narrower alternative: it acts on the whole registry, not on
traced call sites, so it covers a closure of genuinely unknown runtime
origin (an arbitrary parameter, an `If` between two different literal
lambdas) exactly as well as a directly-named one — confirmed by a test
built specifically to be the sharpest regression guard against silently
narrowing back to a traced mechanism
(`a_parameters_own_value_arriving_via_an_if_between_two_literals_still_agrees_once_dispatched_generically`,
`src/compile.rs`).
A genuinely fiddly correctness point surfaced while building the
call-site dispatch itself: chaining several single-argument
`call_indirect` steps needs each step's own env/table-index halves to
survive across the *next* argument's own (possibly reentrant, possibly
closure-creating) compilation — structurally the same hazard
`push_pap_env`'s own docs describe, but naively "just recompute the
previous step like over-application already does" is *exponential* here
(each step would need to recompute its own entire prefix twice), not the
bounded, one-off cost over-application accepts. The actual fix keeps
everything live across that one recursive call *on the operand stack*
(immune to reentrant reuse of the shared scratch locals by construction,
per Wasm's own stack-nesting guarantee) and only touches
`$envtmp`/`$papenv` in tight windows strictly before or after it, giving
linear-time dispatch with no new locals at all (`emit_dynamic_apply`,
`src/compile.rs`).

**Measured, not just reasoned about.** `benches/execution.rs`'s
`inconsistent_arity_loop_carried_parameter_loop` isolates exactly the
cost this section's own mechanism description flags: the same
20,000-iteration loop, calling a closure-typed parameter once per
iteration, as `closure_typed_loop_carried_parameter_loop`, except one
syntactically-present-but-never-reached extra call site elsewhere in
the same function makes that parameter `ArityUse::Inconsistent` — which
switches the *whole* fragment to curried dispatch, including the hot,
otherwise-fast-path-eligible call the dead branch has nothing to do
with. On this machine: **~43µs → ~67µs per warm call (~1.56×)**, and
~70ms → ~81ms one-time cold compile (the two-pass discovery/emit
restructuring's own fixed cost, paid once per fragment regardless of
how many calls it makes). A single dead, never-executed call site
elsewhere in a hot function is enough to pay this — a real, measured
argument for keeping this mechanism opt-in (triggered only by an
actual `Inconsistent` classification, never speculatively) rather than
a reason to reconsider the design: the alternative, full currying as
the *universal* convention (§ above), would have imposed a comparable
or larger cost on *every* closure call in the compiler, not just the
fragments that actually need it.

*Since §30:* the installation gate declined this benchmark at 20,000
iterations, so the pair now runs at 150, side by side in one group
(~1.37× on the whole warm call, ~1.55× on the loop once fixed per-call
overhead is removed). See §30.

This new capability shipped compile-time-only at first, with no
kernel-checked proof counterpart — `Γ`'s own "one arity per variable"
limitation is unchanged, and `denote_closure`'s purely structural
classification has no way to reason about a value whose identity is
only known by executing, not by term shape (see `docs/types.md` §3.1/§6.3).

**Since covered, per instance.** `proof::prove_closure_expr_instance`
(`src/proof.rs`) closes a real slice of that gap without touching `Γ` at
all: a new evaluator, `eval_dyn`, follows one concrete execution trace
through a term (resolving an `If`'s own condition concretely and
recursing into only the taken branch, the same discipline
`prove_tail_recursive_call`'s own `classify_step` already established
for tail recursion, transplanted to closures) and, when a literal-headed
call's own declared parameter type is dishonest for a concretely-`Clo`
argument (exactly the `Inconsistent` case), *inlines* that callee's own
body with the concrete argument substituted in, rather than trying to
type it opaquely. This needed one new piece of machinery beyond the
transplant: a closure value's own `ConcreteClo` carries not just which
literal lambda it concretely is but a *snapshot of the frame active when
it was created*, so its own captures resolve against the right scope
once it's read back after crossing a call boundary — the same two-frame
discipline `eval_and_prove_call_over`/`eval_and_prove_direct_call`
already established for the `Int`-only family (root's own captures
resolve against root's *own* frame, distinct from the calling frame),
applied to the closure-aware family for the first time. No new
postulate is introduced anywhere; every construction reuses
`call_ref`/`register`/`mk_clo_ref`/`mk_env_ref` unchanged, and the
resulting proof is a per-instance certificate (`jit.rs`'s
`kernel_verify` requires every sample in the battery to get one,
mirroring how tail recursion's own per-call fallback already works),
not a universal theorem — an honest reflection of the fact that a real
universal proof for this shape would need an honest single kernel type
for "either `Clo_1` or `Clo_2`", i.e. a real dependent sum, which
remains the separate, larger research question §9's own investigation
already concluded it is. As a side effect of inlining firing on
*any* dishonest `None`-vs-`Clo` mismatch (not only the arity-Inconsistent
one), it also picked up a second, previously out-of-scope shape for
free: a parameter passed along but never actually called as a closure
at all (`src/syntax.rs`'s own `higher_order_let_chain_evaluates_like_the_inlined_sample`
test, a let-desugaring artifact, is the regression guard for this).

**Since covered too: a recursive use, for tail recursion.** The
recursive (`Rec`-wrapped) case named above as deliberately not attempted
is now also closed, for *tail*-recursive shapes: `eval_dyn_direct_call`
no longer declines outright when the callee it would otherwise inline is
itself `Rec`-wrapped, instead handing off to `eval_dyn_tail_recursive`
(`src/proof.rs`), which follows the loop's own concrete tail self-calls
one iteration at a time — reusing `classify_step` (from tail recursion's
own relational proof) for branch/self-call dispatch, and `eval_dyn`
itself, once per iteration, to denote each fresh argument. No new
postulate or dependent sum was needed here either: unlike a *universal*
theorem for this shape (still the open research question above — the
loop-carried parameter still has no honest static type across
iterations), a per-instance certificate only ever needs the one concrete
closure identity each traced call actually has, which `eval_dyn` already
computes. This closes exactly the gap
`samples::inconsistent_arity_loop_carried_parameter_loop`
and `jit::tests::a_tail_recursive_loop_compiles_and_is_kernel_verified_once_its_own_closure_parameter_turns_inconsistent`
were written to document as open. One new piece of plumbing this needed:
`eval_concrete`'s own pure-arithmetic fragment (`Var`/`Lit`/`Prim`/`If`)
can't evaluate a fresh argument that's itself a call (e.g. a loop-carried
`g(x)`, needed so a later branch condition depending on it stays
evaluable) — rather than duplicate a second concrete evaluator that
understands closures, `eval_concrete_dyn` rebuilds an `eval::Env` from
the current frame and defers to the reference interpreter (`eval::eval`)
directly. (2026-10-27, cleanup plan CU1: `eval_concrete` is gone too;
branch conditions also go through `eval_concrete_dyn`, which declines on
a division by zero where `eval_concrete` took `x / 0 = 0`.)

**Since covered too: a *non*-tail recursive use, including branching.**
A self-call embedded inside a larger expression (`1 + f(n-1)`, or two
self-calls in one leaf as in naive Fibonacci, `f(n-1) + f(n-2)`) is now
also provable per instance. `classify_step`'s own tail-position check
only recognizes a self-call that *is* the entire remaining leaf, so a
non-tail self-call reaches `eval_dyn_tail_recursive`'s loop as an
ordinary `Base` leaf and gets handed to `eval_dyn` as before — the new
piece is that `eval_dyn` itself now recognizes an embedded self-call
inside that leaf (via a new parameter, `self_ctx`, carrying the
enclosing `Rec`'s own `(body, arity)` whenever one is in scope) and
recurses back into `eval_dyn_tail_recursive` for that self-call's own
body, mutually. Branching non-tail recursion falls out of this for
free — each self-call occurrence in a leaf is recognized and evaluated
independently — and is exponential in trace length like any naive
Fibonacci, which is fine since this whole per-instance methodology only
ever runs against `jit.rs`'s own small, fixed sample battery. `self_ctx`
is `None` once inlining crosses into a *different* combinator's own
body (which computes its own fresh self-context, never inherits the
caller's), matching `compile.rs`'s own structural restriction that a
bare, unapplied self-reference can't be captured as a plain value
either.

This needed a real stack-safety bound, not just a step-count one:
`eval_dyn`'s recursion for an embedded self-call genuinely recurses
through the *native* Rust call stack (unlike `eval_dyn_tail_recursive`'s
own loop, which never does), so `DynBudget` now carries two separate
counters — `tail_steps` (10,000, matching `prove_tail_recursive_call`'s
own bound, safe to keep large since the tail loop never grows the native
stack) and `recursion_depth` (bounding embedded non-tail self-calls,
kept much smaller since each one is a real stack frame). The safe value
here was found empirically, not assumed: 500 levels of this specific
recursion (each frame carrying `ClosureCombinators`, `Anchored` values,
and `DynVal` frame vectors — heavier than `eval.rs`'s own ~8,000-10,000
native-stack budget for plain interpreter recursion) already overflows
the smaller per-test-thread stack `cargo test` gives a debug build; 20
was confirmed safe up to `n = 1_000_000` in both debug and release
builds, and the shipped value, 50, was verified the same way with
margin to spare. A dedicated boundary test asserts the decline is a
clean `None`, not a crash, once the bound is exceeded.

**Since covered too: a closure argument arriving via a further call.**
The other named gap — a callee whose own saturated call itself returns a
further, not-statically-known `Clo` — is closed too, and turned out to
need no new mechanism at all: `eval_dyn_direct_call` already inlines a
callee whenever some argument's own concrete value is a `Clo` that the
callee's static classification didn't expect; widening the same
`needs_inline` condition to also fire whenever the callee's own return
type (`combinator_return_type`) is a `Clo` reuses that exact machinery
to identify *which* concrete literal a further call's own result is,
rather than trying (and failing) to treat it opaquely. This removed a
`return None` that used to fire whenever a proof attempt reached such a
call, replaced with a `debug_assert!` recording that the opaque path
below is now only ever reached once `return_ty` is already known to be
`None` — the assertion itself doubles as the regression guard for
silently narrowing this back (a test built to trigger it, with the
widening reverted, panics through that assertion rather than returning a
silently wrong proof).

Reordering note: `jit.rs`'s `kernel_verify` tries the universal and
relational tail-recursion strategies *before* `prove_closure_expr_instance`
now, not after — once `prove_closure_expr_instance` could also succeed on
plain arithmetic recursion (gcd, say) as a side effect of this widening,
trying it first would have silently downgraded those to weaker,
per-instance-only evidence instead of the stronger theorem they already
had.

On the same 20,000-iteration benchmark measured above, the added
per-instance proof attempt (which runs once, at compile time) raises
`jit_cold_compile_and_verify` further (roughly 70ms → 80ms → ~105ms on
this machine): `eval_dyn_tail_recursive`'s own bound (`MAX_STEPS =
10_000`, matching `prove_tail_recursive_call`'s existing bound) is
smaller than this benchmark's own 20,000 iterations, so the proof
attempt runs the full 10,000-iteration search, declines, and that work
is thrown away — a real but one-time, compile-only cost, and `jit_warm_cache_hit`
(the number that actually matters for a hot loop) is unaffected.

**Since found and fixed: most of that ~105ms was a redundant-call bug,
not the search itself.** This benchmark's term has arity 0 (it's a fully
saturated computation, not a function awaiting arguments), and
`jit.rs`'s `sample_arg_vectors` had no dedicated `0` arm — it fell
through to the higher-arity catch-all, which pushes `vec![a; arity]` once
per entry in a small fixed set of sample integers. For `arity == 0`,
`vec![a; 0]` is `[]` regardless of `a`, so this produced *six identical
empty-argument samples*, and `kernel_verify`'s `prove_closure_expr_instance`
fallback — the expensive one, ~25ms per call on this term, since it's the
one genuinely walking a concrete execution trace up to the step budget —
ran on all six, back to back, for zero new information each time.
Instrumented directly (`proof::prove_closure_expr_instance` called in
isolation): one call, 25.3ms; the actual six-call loop `kernel_verify`
was running, 128.7ms. Adding a dedicated `0 => out.push(vec![])` arm
(`src/jit.rs`) collapses this to the one meaningful sample, and
`jit_cold_compile_and_verify` on this exact benchmark drops from ~103ms
to ~38ms (a real run, not the estimate above) — the remaining cost is
the one genuine 10,000-step search plus ordinary compile/instantiate/
sample-verify overhead. The `1`- and `2`-arity arms don't have this bug
(`SAMPLE_ARGS` are pairwise distinct, so their generated vectors are
too); a cheaper, more general dedup was considered and rejected in favor
of this targeted fix, since arity 0 is the only shape where the existing
scheme can produce a genuine duplicate.

