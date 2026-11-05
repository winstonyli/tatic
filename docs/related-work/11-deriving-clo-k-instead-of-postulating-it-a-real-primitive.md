## 11. Deriving `Clo_k` instead of postulating it — a real primitive-count win, confirmed by a standalone prototype

A natural question once §9's arity-indexed `Clo_k` family existed at all
(one fresh opaque `Sort(0)` axiom per distinct arity a term uses, plus its
own `ite_clo_k` co-postulate — `proof.rs`'s `ClosurePostulates::clo_ty`/
`apply_ref`/`ite_clo_ref`): does this "minimize primitives," or could the
whole family be built from something already postulated, the way
`NatPostulates` replaced a raw `Nat : Sort(0)` postulate with `W(Bool,
ChildTy)`?

**The naive answer — curry `Clo_k` down to nested `Clo_1`s — doesn't
work.** `apply_ref(k)`'s own postulated type is *unconditionally* `Clo_k
-> Int -> .. -> Int` (every argument and the result flattened to `Int`,
deliberately, matching `compile.rs`'s own untyped `call_indirect` — see
`docs/types.md` §4.4). Currying that to `Clo_1`-of-`Clo_1` would need
`apply_1`'s own result to be "either `Int` or `Clo_{k-1}`, depending on
which real value is behind it" — exactly the "no honest single type for
`Clo_1`-or-`Clo_2`, needs a real dependent sum" gap §9 already names as a
separate, unsolved research question. Naive currying just walks back into
that same wall.

**What actually works: stop postulating `Clo_k` as opaque at all — build
it as the literal curried `Int -> .. -> Int` arrow type.** Every consumer
of the `Clo_k` family (`apply_ref`, `call_ref`, `pap_ref`,
`clo_eq_ref_*`) only ever uses `k`/`arity` two ways: as a `HashMap` key
selecting which memoized postulate to reuse, and as a fold/loop bound
("build `k` nested arrows," "apply `k` arguments one at a time" —
confirmed by a direct audit of every such call site, none of which
inspects `k` distinct argument *types*, since `apply_ref`'s own arguments
are uniformly `Int`). So `Clo(k) := Int -> Int -> .. -> Int` (`k`
copies), built with the exact same `for`-loop `apply_ref(k)`'s own type
construction already uses, is already exactly as expressive as today's
opaque `clo_ty(k)` — and, once `Clo(k)` genuinely *is* that Pi type
rather than an unrelated opaque tag, applying a `Clo(k)`-typed value to
`k` arguments is just ordinary `kernel::App` chaining (already what
`apply_n`/`app2`/`app3` reduce every "packed" application to underneath —
`kernel::Expr` has no n-ary `App` node at all, see §9's own confirmation
that `App(App(f,x),y)` is already, at the term level, two single
applications). This makes `apply_ref` itself unnecessary: nothing needs
an axiom stating "here is how to call a `Clo_k`-typed thing" once calling
one is just ordinary application (see the second correction below for
why this narrower claim — `apply_ref` alone, not the whole
`apply_clo_eq_ref`/`apply_pap_eq_ref` machinery built on top of it — is
the one that actually survives scrutiny).

**Correction, caught before any real migration work started on the
strength of this claim**: the paragraph below, as originally written,
overstated what the `bool_rec`-derived `ite` actually buys against *this
codebase's real* `ite_clo_k`. The standalone fact is still correct — a
`bool_rec` instantiated at a constant motive is a genuine, zero-postulate
`ite : Bool -> A -> A -> A` for any `A` — but `proof.rs`'s real
`ite_clo_ref(arity)` postulates `Int -> Clo_arity -> Clo_arity ->
Clo_arity`, condition on `Int` (matching the source `If`'s own condition
type), not `Bool`. `Int` has no recursor in this kernel (deliberately —
it's an open-ended arithmetic domain, grounded only per concrete value via
`assume_prim_fact`/`assume_ite_fact`, never given a case-elimination
principle the way `Bool` was), so there is no bridge from a symbolic `Int`
condition to `bool_rec`'s own `Bool` motive — the derivation below simply
doesn't apply to the postulate this codebase actually has. Worse, even
where it *would* apply, `ite_clo_ref`'s own value is used as an opaque
building block *inside* `clo_eq_ref_if_tree`'s single already-postulated
axiom (`build_closure_if_tree_rhs`'s `ite_clo_k(...)` calls become part of
one assumed `Id(..., lhs, rhs)` fact, never separately reduced or
related to anything) — so unlike `apply_ref` (whose entire *reason to
exist* was reconciling two independently-postulated things, and
disappears once application is native), `ite_clo_ref` was never trying to
be *proven* from anything in the first place. It stays exactly as it is:
one opaque, per-arity postulate, unchanged by this section's own
migration.

**A second correction, caught mid-Phase-2 implementation (see the
migration log below) rather than before starting this time**:
`apply_clo_eq_ref`/`apply_pap_eq_ref` are *not* deletable either, for a
reason structurally similar to `ite_clo_ref`'s: `register(h)`/
`mk_clo_ref(h, sig)` (a combinator's own `Clo_k`-typed *value*) and
`call_ref(h)` (the same combinator's own *callable*, useful,
further-reducible axiom) are two *independently postulated* opaque
constants — nothing about making `Clo_k` transparent relates them to each
other on its own; a `Clo_k`-typed constant still has no `Lam` body, so
`kernel::whnf` never discovers on its own that `register(h)` and
`call_ref(h)` denote "the same real closure." `apply_clo_eq_ref`'s entire
job was exactly this: postulating that equality once per combinator so
every later use gets it for free. Removing `apply_ref` removes one layer
of indirection from *that same postulated statement* (its LHS becomes
`register(h)(args)` directly instead of `apply_ref(k)(register(h),
args)`), but the statement itself — and the `p.push` that assumes it —
still has to exist. The real, confirmed win is narrower than first
claimed twice over now: only `clo_ty`'s own `Sort(0)` push (one of the
two postulates `clo_ty` currently pushes per distinct arity) and
`apply_ref` itself are eliminated. `ite_clo_ref` and
`apply_clo_eq_ref`/`apply_pap_eq_ref` both stay, the latter two
simplified (one fewer `apply_ref` hop in their own construction) but not
removed.

**Soundness is preserved, not weakened.** The original arity-blind-`Clo`
unsoundness (§6.2 in `docs/types.md`) came from a single universal `Clo`
giving the kernel *no* way to distinguish arities. Literal Pi types don't
reopen that: `Int -> Int` and `Int -> Int -> Int` are already
structurally distinct under `kernel::check`'s own Pi-formation and
`def_eq` rules, for free, with no reliance on remembering "which `k` was
already postulated." An opaque postulated *constant* of a literal Pi type
(e.g. `combinator_value(h)`) still has no `Lam` body to beta-reduce, so
`whnf` leaves any application of it neutral/stuck exactly as it does
today — nothing about making the type transparent lets the kernel
compute anything through the value itself.

**Confirmed with a standalone prototype**
(`proof::tests::a_curried_int_arrow_can_stand_in_for_clo_k_with_zero_new_postulates`,
not wired into `ClosurePostulates`), which builds two opaque `Clo(2)`-typed
constants, a `Bool`-conditioned `ite` derived from `bool_rec` (the
standalone fact from the corrected paragraph above — kept as a genuine,
independently-useful result, just not one that touches `ite_clo_ref`
itself, which stays `Int`-conditioned and opaque), checks that selecting
one via that `ite` and calling it with two `Int`s through ordinary
`kernel::App` (no `apply_ref` anywhere) typechecks as `Int`, checks that
`bool_rec_true_eq`'s own instantiation already proves the selection's
computation rule, and confirms a `Clo(3)`-shaped value is still rejected
where a `Clo(2)` is expected. All four hold. One real bug was hit and
fixed while building this prototype: an early version cached
`Clo(2)`'s `Expr` before pushing further postulates (the two closure
values, the two `Int`s, the `Clo(3)` value) — exactly the `Anchored`-class
staleness bug §4 documents at length, which this project has hit
repeatedly (a postulate's `Var`
index depends on how many postulates exist *right now*; caching an
`Expr` built from one and reusing it across a later `p.push` silently
points it at the wrong thing once the context has grown). Fixed by
pushing every postulate the test needs first, then resolving every
reference fresh in one final pass — the same discipline `proof.rs`'s own
`Anchored` type enforces mechanically everywhere else. A verify-teeth
check (swapping the `ite` condition from `true` to `false`) confirmed the
`bool_rec_true_eq` instantiation genuinely discriminates, not just
vacuously typechecks.

**Scope of what this does and doesn't unify.** This applies cleanly to
`Clo_k`'s own "value type" and its `ite`/`apply` machinery — not to
`Env_sig` (the per-capture-signature environment type
`ClosurePostulates::env_ty`/`mk_env_ref`), which is a genuinely
heterogeneous product (each captured slot may independently be `Int` or
some `Clo_j`), not a uniform `k`-fold repetition — unifying *that* would
need real dependent-sum/record types, the same open research question §9
already names, not the mechanism above. `call_ref`/`pap_ref` keep their
current per-combinator-`h`/per-`(h,supplied)` postulate count unchanged
(they're keyed by `h`, not by arity alone); what changes is only that
wherever they reference `clo_ty(k)` as a domain or codomain, that
reference becomes the literal Pi type instead of a fresh opaque tag.

**Migrating the real `ClosurePostulates` to this representation, staged
like §9's own rollout.** Phase 1 (landed): `clo_ty` itself no longer
pushes anything — `Clo_arity` is `curried_int_ty(arity)`, a pure function
of `arith.int_ty()`, with `ite_clo_ref` (still genuinely postulated, per
the correction above) factored out to build its own domain from the same
pure helper rather than calling back through `clo_ty`, which would
otherwise recurse forever on `ite_clo_ref`'s first call for a given
arity. Verify-teeth checked: temporarily dropping `clo_ty`'s own
`ite_clo_ref`-priming side effect broke 8 existing tests immediately (the
exact push-inside-a-temporary-rolled-back-scope staleness class this same
region's own comments already document), confirming the priming
contract every existing call site depends on is still load-bearing, not
vestigial. Phase 2 (landed): eliminated `apply_ref` itself and its dozen
call sites, each of which built `apply_n(apply_fn, [callee_or_sat_applied]
++ args)` and now builds `apply_n(callee_or_sat_applied, args)` directly,
since a `Clo_k`-typed value is itself the real curried arrow type and
needs no separate "how to call this" axiom. `apply_clo_eq_ref`/
`apply_pap_eq_ref` are kept (per the second correction above), simplified
to drop their own `apply_ref` hop from both their axiom construction and
the `cong1`-based congruence step `eval_and_prove_call_over`'s own
over-application dispatch builds around them. The trickiest part wasn't
the mechanical call sites (a uniform, low-risk rewrite once the pattern
was recognized) but `eval_and_prove_call_over`'s own `f_clo`/
`apply_at_denoted`/`apply_at_chosen_denoted_args` congruence-and-`trans_proof`
chain, which still referenced the removed `apply_fn` as the function
being congruence-lifted and as the head of the chain's own endpoints --
missing this broke 10 tests immediately with a `kernel::check` type
mismatch (an `Id` proposition's own type parameter coming out as a `Clo`
Pi type instead of `Int`, from composing a proof built against the new,
`apply_ref`-free axiom shape with congruence machinery still built
against the old one) until updated to congruence-lift the callee's own
direct application instead. `Clo_k`'s own `Sort(0)` push, `apply_ref`,
and its dozen call sites are now fully migrated;
`ite_clo_ref`/`apply_clo_eq_ref`/`apply_pap_eq_ref` remain, as
established above, genuinely necessary postulates.

