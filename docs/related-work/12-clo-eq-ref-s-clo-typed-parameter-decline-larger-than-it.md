## 12. `clo_eq_ref`'s `Clo`-typed-parameter decline: larger than it looked, investigated not attempted

`clo_eq_ref` declines outright whenever `root`'s own declared parameters
include a `Clo`-typed one (`param_types.iter().any(Option::is_some)`),
with its own comment already flagging why: `clo_eq_ref_if_tree`/
`clo_eq_ref_call`/`clo_eq_ref_pap` each quantify `root`'s own params
`Int`-typed unconditionally (`quant_types = vec![None; n_captures +
arity]`). A prior survey estimated lifting this as "a larger refactor,
touching all three branch functions uniformly" — investigated properly
this time, the real scope turns out to be substantially bigger than that
framing suggests, for a reason the survey didn't surface: it isn't just
`quant_types`.

**`dummy_caller_param_types` isn't just for `root`'s own declared
params — it also forces every one of `root`'s own *captures*, and every
leaf's own captures inside an `IfTree`, to be treated as `Int`-typed,
structurally, regardless of what they actually are.** `capture_sig`
(`src/proof.rs`) looks up each capture's type by reading whatever
`caller_param_types[rel]` says — it never independently inspects the
captured value's real type. Every one of the thirteen-or-so
`dummy_caller_param_types`/leaf-level `dummy` constructions across
`clo_eq_ref_if_tree`/`clo_eq_ref_call`/`clo_eq_ref_pap`/
`prime_closure_if_tree_leaves`/`closure_leaf_value_expr`/
`closure_leaf_pap_value_expr` builds this array as `vec![None; ...]`
unconditionally. This isn't an oversight specific to any one of them: at
axiom-construction time (memoized once per `Hash`), there is no single
fixed "caller" to consult in the first place — a captured variable's real
type lives in whichever *enclosing* combinator's own signature declared
it, information the callee's own `Hash` alone can't recover, and nothing
currently threads it in from whoever calls `clo_eq_ref`.

**Widening `quant_types` alone would not actually lift the decline for
any term that uses the `Clo`-typed parameter for anything.** Every
`cond`/leaf-argument in `clo_eq_ref_if_tree`/`clo_eq_ref_call`/
`clo_eq_ref_pap`'s own axiom construction goes through plain `denote`/
`collect_literals` — by their own docs, these translate only `Var`/
`Lit`/`Prim`/`If` into a kernel `Int` expression and return `None` on
anything else, including a reference to a `Clo`-typed variable used as a
value (a bare `Var(i)` read still works structurally, but any *use* of
it — captured by a nested closure, called, passed as an argument — does
not, since `denote` has no `Clo`-typed case at all). This codebase
already has the fix for exactly this gap, built for a different context:
`denote_with_placeholders`/`denote_closure_typed`/
`collect_literals_closure` (used by `prove_closure_expr`'s own
self-recursive-body pipeline) are the closures-aware counterparts,
already handling a `Clo`-typed parameter call (`AppShape::ParamCall`) and
a captured `Clo`-typed value correctly. Lifting `clo_eq_ref`'s own
decline for real means swapping the closures-blind `denote`/
`collect_literals` for these closures-aware siblings throughout all three
branch functions' own axiom construction, *and* threading a real
`caller_param_types` into every `dummy_caller_param_types`/leaf-level
`dummy` site so `capture_sig` stops assuming `Int` — not a `quant_types`
widening plus a flag.

**Verdict: real, but large enough that it should be its own separately
scoped session, not folded into a batch alongside smaller items.** This
is comparable in size to the generic-dispatch rewrite (`docs/related-work/`
§9) or larger, touching the historically most staleness-bug-prone part of
this file (§4's own five-plus-bug count already came from this same
neighborhood) under exactly the conditions (deep proof-composition
changes, `Anchored` discipline threaded through new call sites) that have
produced real bugs here before. Attempting it under the same time budget
as this section's other, much smaller items risked exactly that outcome.
Investigating and scoping it honestly, rather than shipping a partial
`quant_types`-only change that would silently still decline (or worse,
silently mis-type a capture) on the first real term that exercises it,
matches this project's own standing discipline (see the two corrections
in section 11 above, both caught by reading the real construction rather
than trusting the first plausible-sounding claim).

**Correction, a session later: even the narrower, provably-safe slice
turns out to be dead code today, for a deeper reason than the above.**
A follow-up attempt scoped this down further, to just `root`'s own
*declared* parameters (leaving captures forced `Int`, which
`classify_app_node` was confirmed to decline cleanly rather than
mis-type if ever violated -- a real, safe increment, not the risky
partial fix warned against above). A new function,
`denote_param_calls`, mirroring `denote`'s exact `Var`/`Lit`/`Prim`/`If`
fragment plus one addition -- a saturated call to a `Clo`-typed
parameter denotes as a direct kernel application, needing no
`ClosureCombinators` access and so none of `denote_closure`'s own
lazy-postulate staleness risk -- was built and wired through
`clo_eq_ref`/`clo_eq_ref_if_tree`/`clo_eq_ref_call`/`clo_eq_ref_pap` and
their leaf helpers. It compiled clean and the full existing test suite
stayed green (widening `quant_types`'s arity slice from all-`Int` to
`root`'s own real `param_types`, and `Some(&param_types_full)` in place
of `None` for the `collect_literals` pre-pass, are both no-ops on every
term with no `Clo`-typed declared parameter, confirmed by the
unchanged 175-test result).

Then, writing the regression test the fix was supposedly for, surfaced
the real problem: **`clo_eq_ref` has exactly one call site in the whole
file** (`build_clo_call_bridge`), reached only through
`eval_and_prove_call_over` (directly, or via
`resolve_closure_shape_to_leaf`'s own recursion) -- and
`eval_and_prove_call_over` already declines independently, one level
up, on the *identical* condition (`callee_param_types.iter()
.any(Option::is_some)`), for a reason that has nothing to do with
`clo_eq_ref`'s own quantifier types: `eval_and_prove`'s own docs already
state it plainly -- "every caller of this function... only ever runs
where the *outer* frame is entirely `Int`-typed" -- and its return type
makes that structural, not incidental: `eval_and_prove` returns
`(i64, Expr, Expr)`, an `i64` *concrete value* alongside the denotation
and proof. A `Clo`-typed argument has no `i64` to put there in this
convention at all -- there is no way to instantiate `clo_eq_ref`'s own
newly-widened axiom at a concrete `Clo` value through this call graph,
no matter how correctly the axiom itself is built, because nothing on
the only path that reaches it can ever produce one. This makes the
`clo_eq_ref`-level fix, however correct and safe in isolation, genuinely
unreachable dead code as things stand -- confirmed, not merely
suspected, by trying to write the end-to-end test and finding no way to
drive a concrete `Clo` value into the one call site that would exercise
it. The change was reverted rather than merged half-exercised, matching
this project's own standing rule against unreachable code.

**What real reachability would need, and why it's the already-flagged
larger question.** The one methodology in this codebase that *does*
carry genuine concrete `Clo` values through a per-instance proof is
`eval_dyn`/`DynVal` (docs/related-work/ §9's "Since covered, per instance"),
built for a completely different call graph (inlining a callee's own
body at a concretely-resolved value, never touching `clo_eq_ref`'s
universal-axiom family at all). Making a `Clo`-typed *declared parameter
of `root` itself* reachable would mean either teaching `eval_and_prove`'s
own family a `Denoted`-typed return convention in place of its current
`i64`-only one (a signature change rippling through every caller in the
same neighborhood the "larger refactor" framing above already flagged),
or routing this specific shape through `eval_dyn`'s own machinery
instead of `clo_eq_ref`'s. Either is real additional scope beyond what
this section's own verdict already priced in, not a smaller follow-on --
so the verdict stands: still real, still large, still its own separately
scoped session, now with a materially more precise reason why.

**Final correction: the second path above is not a follow-on at all --
it's already built, already shipped, and already tested.** Set out to
build it and found, before writing a line of code, that
`eval_dyn_direct_call` already has the exact case needed: when a
callee's own declared parameter is *honestly* `Clo`-typed
(`root_param_types[pos] == Some(_)`) and the concrete argument really is
a `DynDenoted::Clo`, its "ordinary opaque call" path already matches
`(Some(_), DynDenoted::Clo(e, _)) => e` and denotes the call through
`call_ref`, the same opaque postulate `clo_eq_ref`'s own callee-side
construction would use -- no inlining, no new machinery, just the
already-existing per-instance methodology doing exactly what it was
built to do. An existing, already-passing test exercises precisely this
shape end to end:
`branching_non_tail_self_calls_carrying_an_inconsistently_classified_closure_parameter_get_a_per_instance_proof`
(`proof.rs`) builds `it = rec f n g x = if dead then .. else (if n<=0
then x else 1 + f(n-1, g, g(x)))`, a self-recursive combinator whose own
loop-carried parameter `g` is called honestly (`g(x)`, one call site,
one arity) every iteration, and gets a per-instance proof via
`prove_closure_expr_instance` for every `n` tried, despite
`prove_closure_expr`'s own purely-structural universal attempt declining
on the very same term. The identical shape is confirmed a second time,
through the *real* compiled pipeline, by
`jit::tests::a_tail_recursive_loop_compiles_and_is_kernel_verified_once_its_own_closure_parameter_turns_inconsistent`.

This resolves the whole question, not just the path to it. A `Clo`
value can only ever originate from a literal `Abs` written somewhere
inside the term being evaluated -- there is no surface syntax or
runtime mechanism for anything *outside* a term to hand it a closure --
so the only place a "`root`'s own declared parameter is genuinely
`Clo`-typed" scenario can ever concretely arise is exactly the shape
above: a nested (here, self-recursive) combinator's own parameter,
supplied a real closure literal from elsewhere in the *same* term. That
shape is what the existing tests confirm already works, today, via
`eval_dyn`. The one configuration that's still declined --
`clo_eq_ref`'s or `prove_closure_expr_instance`'s own *outermost* `h`,
the term whose own top-level arguments are supplied externally via
`args: &[i64]`/`jit.rs`'s own sample battery -- was shown structurally
unreachable in the correction above (there is no `i64` encoding of a
closure `jit.rs` could ever construct for such a sample), and that
unreachability is not a gap to close: it correctly reflects that nothing
external can ever supply a closure in the first place. There is nothing
left to build here. §12's original decline, in `clo_eq_ref` itself, is a
real and permanent property of that one methodology (a universal axiom
has no way to ask "which concrete value is this, at runtime" the way a
per-instance proof can) -- but it is not, and was never, an overall
capability gap once `eval_dyn` is counted as part of this file's answer
to "can a `Clo`-typed parameter be proven," which it always has been.

