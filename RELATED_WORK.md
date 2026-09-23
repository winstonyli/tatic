# Related work

This document is not a design proposal — it's a record of the formal-logic
and compiler-runtime landscape surveyed while scoping possible future work
(see `README.md`'s own Future Work list, and `TYPES.md` for what this
project's own type system actually is), kept for whoever picks one of
those directions up next. Every connection below is drawn deliberately:
either "this is the established solution to a problem tatic currently has
no good answer for" or "this is a different point on the same tradeoff
tatic itself makes."

## 1. Where tatic's own kernel sits

`src/kernel.rs`'s own dependent-type kernel (`Sort`/`Pi`/`Id`/`W`, a
stratified predicative universe hierarchy, no impredicative encoding) is a
small fragment of the lambda cube's bottom-right corner — closer to
Martin-Löf Type Theory (MLTT) than to the Calculus of (Inductive)
Constructions (Coq's own core, which adds impredicative `Prop` and a
richer inductive-type mechanism) or to classical Church-style Higher-Order
Logic (HOL4/HOL Light/Isabelle/HOL, which stays simply-typed — no
dependent types at all, quantification over predicates/functions instead).

This placement is *why* `prove_tail_recursive_universal` (`src/proof.rs`)
can't induct on a bare inductive `Nat` the way a CIC-based system would —
predicativity forbids the impredicative encoding that would let one
generic recursion principle cover every case, so it postulates a bespoke
`Ev(params, v)` family with its own postulated recursor mirroring
`kernel::WRec`'s universal-motive shape, by hand, per proof strategy. See
§3 below (guarded recursion) for the type-theoretic tool that would
actually solve this generically rather than ad hoc.

## 2. The historical root: combinatory logic

Curry/Schönfinkel's combinatory logic (1920s-30s) predates λ-calculus:
no variables or binders at all, every term built from fixed-arity
combinators (`S`, `K`, `I`) composed purely by application. Illative
combinatory logic (Curry's later extension, folding logical connectives
in as combinators) ran straight into Curry's paradox — an early, hard
lesson that "just add application" needs real stratification discipline
to stay consistent, directly prefiguring why tatic's own kernel is
predicative rather than naively unrestricted.

Worth noting for vocabulary alone: tatic's own `Combinators`/`register`
naming (`src/compile.rs`, `src/proof.rs`) echoes this lineage — a
"combinator" here, as there, is a fixed-arity building block whose
identity and shape are pinned at construction time, composed by
application, never partially-evaluated into some more general closure
form.

## 3. Guarded recursion — the generic tool `Ev` reinvents ad hoc

Nakano's "later" modality (`▷A`, Nakano 2000) and its descendants (guarded
recursive type theory, guarded cubical type theory) let a type system
check that a self-referential/recursive definition is well-formed
*structurally*, via the modality guarding the recursive occurrence,
without a separate syntactic termination/positivity checker layered on
top. On closer inspection this is the right tool for *coinduction*
(productive corecursion over infinite/streaming structures) — a genuine
capability this project has no story for at all — but it does *not*
actually address `Ev`'s own duplication: `Ev` encodes a well-founded,
*finite* recursion relation, which needs ordinary induction, not guarding
a self-reference against premature use. Parked for whenever coinductive
reasoning becomes the actual goal, not as `Ev`'s own fix. Adopting it
would be a kernel-level (not `proof.rs`-level) change with real soundness
risk if the guard discipline isn't enforced correctly (real guarded type
theories generally need step-indexed semantics or a clock/tick context
discipline to stay consistent), well outside anything scoped so far.

**Since built instead: a real `Nat`, from existing primitives alone.**
`kernel::tests::nat_via_w_is_a_genuinely_computing_inductive_type`
(`src/kernel.rs`) builds a genuine `Nat` — `Zero`/`Succ` and a real
structural recursor — entirely from this kernel's own four existing
primitives (`Pi`/`Lam`/`App`, `Id`/`Refl`/`J`, `W`/`Sup`/`WRec`), no new
kernel-level machinery at all. The premise behind reaching for guarded
recursion (or `Ev`'s own ad hoc postulation) was that predicativity
blocks a generic recursion principle — but `WRec` already supports
eliminating into *any* `Sort(k)` unconditionally, unlike Coq's own
`Prop`, which restricts this specifically to avoid inconsistency; nothing
about predicativity here ever actually blocked a real, computing `Nat`,
it just hadn't been built. `Bool`/`Unit`/`Empty` are postulated once (the
standard, accepted way to seed a predicative kernel with no fifth
primitive — see `Postulates`' own docs), and `Nat := W(Bool, ChildTy)`;
the identity recursor (mirroring `w_recursor_computes_definitionally`'s
own shape) confirms `Zero`/`Succ(pred)` reduce back to themselves
*definitionally* via `WRec`'s free `Sup`-reduction alone.

A genuinely per-case recursor (`bool_rec`, Bool's own postulated
eliminator, dispatching differently per tag rather than ignoring it) is
also built and shown to produce a well-typed step function — but proving
a *concrete* result of such a recursor (e.g. `is_zero(Zero) = true`)
surfaced a real, deeper obstacle, corrected here after an initial
misdiagnosis: `WRec`'s own automatic reduction (`whnf_impl`) builds its
induction-hypothesis closure with an inert placeholder `Lam` domain
annotation (`sort(0)`, deliberately irrelevant to reduction, since beta
substitution never consults a `Lam`'s domain field at all) — this closure
turns out to be *unconditionally ill-typed on its own*, at any Pi-type
whatsoever, whenever the step function's `ih` parameter is genuinely used
rather than discarded: its own body applies a variable declared type
`Sort(0)` where the real children type is what the application inside
actually needs. This was first read as a function-extensionality gap
(two pointwise-equal functions needing a postulate to be equal outright)
— that diagnosis doesn't hold up: funext requires *both* sides to already
be well-typed inhabitants of the same Pi-type before it can relate them,
and one side here never is one at all, so no postulate fixes this. A real
fix would need `WRec`'s own reduction rule to thread enough type
information through its own induction-hypothesis construction to give it
an honest domain, which conflicts with this kernel's own deliberate
"reduction never needs a typing context" design (`kernel.rs`'s own
reduction-section docs: "always sound regardless of typing context,
since reduction never consults one").

**Since fixed.** The "conflicts with reduction never needing a typing
context" framing above turned out to be the wrong read of what a fix
would actually require: reduction still never consults a *typing
context* (`Ctx`, the ambient list of postulated types), it just needed
one more piece of the *term itself*. `Expr::WRec` now carries a fourth
field, `children_ty` -- `B` from the underlying `W(A,B)`, in the exact
representation `W`'s own second field already uses (written one binder
deeper) -- purely so `whnf_impl`, still fully untyped, can build its
induction-hypothesis closure's domain as `subst_top(children_ty, a)`
(`B(a)`, the real children type at the concrete tag `a` a `Sup` target
was just matched against) instead of the old inert `sort(0)`
placeholder. This is genuinely just redundant, purely syntactic
information riding along with the term -- not a typing judgment smuggled
into reduction -- but redundant data a caller could get *wrong* is a
soundness risk on its own: `infer`'s own `WRec` case independently
re-derives `B` from `target`'s own real inferred type (exactly as it
already did before this fix) and now rejects the term outright via
`def_eq` if the two disagree, so a term built with a mismatched
`children_ty` is caught at typechecking, never silently trusted by
`whnf_impl` later (`kernel::tests::wrec_with_a_mismatched_children_ty_is_rejected`
is the permanent regression guard for that gate specifically). The old
"unconditionally ill-typed standalone" assertion in
`kernel::tests::nat_via_w_is_a_genuinely_computing_inductive_type` is now
its own mirror image: the same induction-hypothesis closure shape,
hand-rebuilt with `children_ty` threaded through honestly, now
*typechecks* at its real domain -- and a deliberate revert of the fix
(back to the `sort(0)` placeholder) makes that same test fail again
immediately, confirming it actually exercises the mechanism, not just
its own hand-rebuilt mirror.

Reasoning propositionally about a concrete result of a recursor whose
step genuinely uses `ih` is unblocked as a result -- a hand-built proof
can now legitimately reference the induction-hypothesis closure as a
well-typed subterm of its own (e.g. as a `cong`-held-fixed argument when
bridging to a postulated recursor like `bool_rec`, which never
auto-reduces on its own regardless of this fix).

**Since finished: `is_zero(Zero) = true`, propositionally.** The same
test now carries the concrete proof through to the end, confirming the
fix's practical value rather than just its own isolated typechecking.
`bool_rec_false_eq` instantiated at `(is_zero_motive_c, case_true,
case_false)` relates `is_zero_step(false)` to `case_false`
propositionally (`bool_rec` itself is postulated and never reduces on
its own, unaffected by this fix); one `cong1` step lifts that through
`\h. h(f_zero)(rec_step)` -- the same `f_zero`/`rec_step` `whnf_impl`
itself builds one reduction step into `is_zero(Zero)`, confirmed
syntactically identical by direct `assert_eq!`, not just independently
well-typed -- to a `Bool`-typed equality; `case_false`'s own body
ignores both arguments and reduces to `true` outright, so `trans_proof`
closes the gap from `is_zero(Zero)` to `true` in one more step. Exactly
the "ordinary, unblocked proof-construction exercise" this section
predicted, once the closure itself was fixed.

The practical consequence for `proof.rs`'s own `Ev`/`ev_rec` methodology
-- postulate the recursor's existence *and* separately postulate each
leaf's own computation rule as an explicit axiom, never relying on any
underlying automatic reduction -- is unchanged: that shape remains
necessary for `Ev` regardless of this fix, since `Ev(params, v)` is an
*indexed* family (see below) that a plain structural recursor doesn't
eliminate for in the first place, `WRec`-fixed or not.

**Since done: extracted into a clean, reusable public API --
`kernel::NatPostulates` (`src/kernel.rs`).** `NatPostulates::new` pushes
every postulate the construction needs onto a `Postulates` in one call;
`nat_ty`/`zero`/`succ`/`zero_child_fn`/`bool_rec`/etc. resolve fresh
against the stored postulate *positions* every time they're called,
mirroring `Postulates::get`'s own "recompute, never cache" discipline
rather than returning a fixed `Expr` once. That discipline isn't just
style: the original, self-contained test needed one manual `shift` to
avoid a value (built before a later `p.push`) silently referencing the
wrong postulate once the context grew deeper; the extracted API doesn't
-- calling `nat.nat_ty(&p)`/`nat.zero(&p)` again *after* the later push
already reflects the deeper context, with nothing for a caller to get
wrong. The test this was extracted from now consumes the public API
(confirming the extraction changed nothing observable, verified with a
deliberately-broken `zero` caught immediately by the existing `Zero :
Nat` check) rather than duplicating the construction.

**Still not attempted: wiring `NatPostulates` into `proof.rs`'s own
`Ev`/`ev_rec` strategies.** This turns out to be more than "swap in the
shared type once it's trusted" -- `Ev(params, v)` is an *indexed* family
(its very type depends on `params`/`v`, which change per recursive
call), while this `Nat`'s own structural recursor (`WRec`, inherited from
`W`) eliminates over a plain, non-indexed carrier. A plain `Nat`
recursor doesn't directly hand you an indexed family's induction
principle either way -- `Ev` would still need to be built essentially as
it is now (one postulated family, gated per leaf, plus `ev_rec`), whether
or not a shared `Nat` exists elsewhere in the same kernel. So reusing
`NatPostulates` here would only save inventing a fresh `Bool`/`Unit`/
`Empty`/`ChildTy` postulate quartet each time `Ev` needed one as a
building block -- which it currently doesn't -- not any part of `Ev`'s
own indexed-family construction or its per-leaf axiom discipline. Left
as a real but narrower opportunity than it first sounds, not pursued
further without a concrete use for it.

**A sibling gap found and closed in `Sup`'s own typing rule, same bug
class as `children_ty` above.** `infer`'s `Sup(a, f)` case derives the
target `W(A,B)` by substituting the tag `a` into `f`'s inferred
codomain (`subst_top(cod, a)`) -- sound only if `cod` doesn't actually
depend on `f`'s own bound argument, exactly the invariant `Expr::Sup`'s
own doc already stated as required. Unlike `children_ty`, nothing
enforced it: a hostile or mistaken `f` whose codomain genuinely varied
per argument (built via any real per-argument case split, e.g. through
`WRec`/`SigRec` on that argument) could in principle have its `Sup`
formation validated only at the one concrete `a` in use, with no check
that every other point of `f`'s domain agrees on the same `W(A,B)` --
letting `WRec`'s own later reduction call `f y` at other domain points
under an assumption never actually verified. No end-to-end exploit was
built (constructing a genuinely dependent, well-typed `f` of this shape
takes real work), but the missing check was real and sat exactly at the
kernel's trust boundary. Closed the same way `children_ty` was: a new
`is_var_free` occurs-check, run on `cod`'s normal form (not raw syntax,
so a codomain that only syntactically mentions its argument but
beta-reduces free of it -- `kernel::tests::is_var_free_tracks_binder_depth_and_is_checked_against_normal_form_not_raw_syntax`
covers this) rather than a redundant carried field, since -- unlike
`WRec`'s `target`, whose real children-type `infer` can independently
re-derive -- `Sup`'s `f` doesn't come with a second, independently-
checkable source of truth to compare against; non-dependence is
directly checkable instead.

One nonobvious cost this surfaced: the fix's own two extra lines, added
directly in `infer`'s `Sup` arm, were enough on their own to overflow a
debug-build test thread's stack in
`proof::tests::a_non_tail_self_call_carrying_an_inconsistently_classified_closure_parameter_gets_a_per_instance_proof`
-- a test that deliberately drives `DynBudget::recursion_depth`'s bound
to confirm it declines cleanly rather than actually overflowing the
native stack (see `proof.rs`'s own docs on that budget). `infer` sits
exactly on that budget's tight margin, so *any* extra unconditional
per-frame locals in a hot arm can eat it, regardless of how small the
change; `#[inline(never)]` on a narrowly-scoped helper alone wasn't
enough to avoid this (the call's own argument/return-value footprint
still counted against `infer`'s frame) -- what actually restored margin
was extracting the *entire* `Sup` arm out of line into its own
`infer_sup` function, mirroring `infer_pair`'s already-established
precedent for exactly this problem (`kernel.rs`'s own `Sigma`-family
docs). Net effect: `infer`'s own frame is now *smaller* than before this
fix, not larger, since none of `Sup`'s locals (`ta`, `dom`, `cod`,
`w_candidate`, `wa`, `wb`) sit in it anymore either. Worth remembering
for any future `infer` arm that grows past a couple of lines: this
budget has essentially zero slack in debug builds, and the fix belongs
in the calling convention (out-of-line the whole arm), not in shrinking
the new logic itself.

## 4. Higher-order abstract syntax / logical frameworks — the fix for this session's own recurring bug class

Twelf and the Edinburgh Logical Framework (LF) represent an object
language's own binders using the *meta*-level's own binders, so the
framework's built-in substitution/α-equivalence machinery handles shifting
for you, by construction, instead of by hand.

This is the most concretely relevant item on this whole list. Tatic's own
`Anchored` type (`src/proof.rs`) and its documented discipline — resolve
a value once, hold it `Anchored`, re-resolve fresh via `.at()` only once
nothing more is left to push onto the postulate context — exists
*specifically* because postulates are pushed onto one flat, ever-growing
context, and a value computed before a later push needs manual
reshifting or it silently references the wrong postulate. Across the two
most recent proof.rs features landed (`call_eq_ref`'s own pass, and
`AppShape::LitLambdaOver`'s `clo_eq_ref`/`ite_clo_eq_ref`/
`apply_clo_eq_ref`), at least five real bugs of exactly this shape were
found — always by running tests, never by review:

- a `refl(call_fn)` built against the bare function instead of the
  fully-applied term, in the non-capturing branch
- a `register(inner)` value silently dropped in favor of a bare
  environment application (not itself a staleness bug, but found via the
  same debugging methodology)
- `clo_ty`/`int_ty` resolved once near the top of `eval_and_prove_call_over`
  and reused across several lazily-pushing boundaries the single-boundary
  `call_eq_ref` pass never had to cross
- an `Anchored::new` call ordered *after* the very push it needed to
  survive, silently computing a zero shift instead of the real one

A HOAS-style approach would make this whole class of bug structurally
impossible rather than something a discipline has to be followed
perfectly for, at the cost of a much heavier meta-theory than this
project's small, auditable, hand-rolled de Bruijn kernel currently needs.
Whether that trade is worth making here is exactly the kind of thing to
scope properly, not assumed.

**Investigated: an automatic staleness detector, short of the full HOAS
rewrite.** The concrete proposal was a monotonic generation counter on
`Postulates`, with `Postulates::get`-derived `Expr`s debug-tagged so any
use across an intervening push trips a `debug_assert` instead of
silently mis-shifting. It doesn't hold up on closer inspection, for two
independent reasons:

- **Nothing to tag the common case with.** The overwhelmingly common
  leak vector is a bare `Expr::Var(k)` (`Postulates::get`'s own return
  for the typical case) — a plain `u32`, no `Rc` at all, so there's no
  pointer identity a side table could key on the way
  `SHIFT_SCOPE`/`ReductionCache` already key their own caches on `Rc`
  pointers (see this module's own docs on why an address-only key would
  be wrong even there). Tagging would need to change `Expr`'s own
  representation, which means touching `kernel.rs` — deliberately kept
  free-standing and minimal (see its own module docs) — not `proof.rs`
  alone.
- **A generation counter adds nothing `Anchored`'s own `depth` field
  doesn't already give.** The dangerous case is `Postulates::ctx`
  growing and *staying* grown between a value's construction and its
  reuse; `params_and_close`/`params_and_close_typed`'s own push-then-
  `truncate` pattern (temporary pushes rolled back to `base_len`) looked
  like a case a length-based check might miss, but it isn't: truncation
  only ever removes entries *above* `base_len`, so anything an
  already-built value references (always `< base_len` for a value built
  before the round-trip) is untouched regardless, and `Anchored::at`'s
  existing `cur - self.depth` shift already handles net growth
  correctly. A counter that never decrements distinguishes nothing a
  `ctx.len()`-based depth doesn't already distinguish for this bug class.

The real gap is narrower and harder: not "can staleness be detected once
it happens" but "a caller forgot to wrap a value in `Anchored` at all" —
and a forgotten wrap leaves no trace to check against later. Closing
*that* automatically needs either the `Expr`-level change above, or
redesigning `ArithPostulates`/`ClosureCombinators`'s own common
accessors to return `Anchored` by default (an explicit escape hatch for
the rare case where immediate use is safe) — a real, large refactor
across `proof.rs`'s entire accessor surface, not a bounded follow-on.

What already works, and keeps working: `debug_assert_has_type` at a
composition's own final step, exactly the discipline this section's own
bug list came from. Every staleness bug found in this project so far —
the four listed above, plus two more found while landing `ClosureRhsShape
::Call`'s own recursion and the `WRec` `children_ty` fix (both fixes,
both committed) — was caught this same way: a real, immediate,
un-ignorable panic, never a silent wrong answer that shipped. The
recursive functions most exposed to this class (`eval_and_prove_call_over`
and its siblings, `resolve_closure_shape_to_leaf`, `build_ev_witness`,
`eval_dyn`/`eval_dyn_tail_recursive`/`eval_dyn_direct_call`) already carry
`debug_assert_has_type` at their own return points; extending that same
manual discipline to new proof.rs code as it's written remains the
practical mitigation, not a mechanism that can be built once and forgotten.

**A second, distinct bug class from the same root cause, found extending
`clo_eq_ref` to a PAP-producing `root`** (`clo_eq_ref_pap`/
`apply_pap_eq_ref`, `src/proof.rs`): not staleness, but an *argument-order
convention mismatch* between two independently-built term constructions
meant to be syntactically identical. `pap_ref`'s own calling convention
(established by `denote_closure`'s existing, tested `LitLambdaPartial`
handling) applies its `s` supplied arguments in plain, unreversed
application order; `call_ref`'s own convention (established by
`call_eq_ref`/`apply_clo_eq_ref` elsewhere) is "descending", applied via
`.iter().rev()` on both the axiom's own construction *and* its
instantiation at a call site, the two reversals deliberately canceling
out. The new axiom's `s`-supplied-argument group crosses *neither*
boundary uniformly — it feeds `pap_ref` (unreversed) on one side and
`call_ref` (needs the cancel-out `.rev()`, matching every existing
argument group) on the other — so copying the `.rev()` pattern
wholesale, by analogy, silently duplicated an assumption that only held
for the case it was copied from. A single-supplied-argument test passed
by construction (reversing one element is a no-op) and revealed nothing;
a second test with two supplied, asymmetric-coefficient arguments (5 and
7 at different weights, so a swap changes the answer, not just its
symmetry) failed loudly at `debug_assert_has_type`, and the fix was
using the unreversed convention for that one group specifically, with
the *why* recorded in `apply_pap_eq_ref`'s own doc comment. The general
lesson generalizes beyond staleness: any de Bruijn/argument-order
convention copied "by analogy" from a structurally similar but not
*identical* existing construction needs its own from-scratch check, and
a test built to catch it needs inputs asymmetric enough that a swap is
observable — a symmetric or single-element test proves nothing about
ordering at all.

**A third instance of the same staleness class, found extending
`eval_and_prove_call_over` to a further-nested-call-producing `root`**
(`clo_eq_ref_call`/`resolve_closure_shape_to_leaf`, `src/proof.rs`): this
generalization needed the resolver to *recurse* — `root`'s own body
calls a further literal lambda `g` whose own saturated call is itself
`Clo_k`-typed (not a bare `Pap`/`IfTree` leaf), so finding the ultimate
literal-lambda leaf means building `g`'s own analogous bridge and
resolving *its* own shape, which could itself be a further `Call`. The
new code held a `Postulates::get`-derived `clo_ty` reference across
exactly this recursive call — the same reference used both before and
after it, unchanged — even though the recursive call could (and, for
any `g`, generally does) push further postulates onto the shared
context, silently invalidating the earlier reference's implicit shift
level the same way an unanchored `Expr` would. The bug produced no
compiler warning and no `None` decline (the classic silent-wrongness
risk `Anchored`'s own docs warn about) — only a `debug_assert_has_type`
panic deep in `kernel::check`'s own type inference ("expected a Sort,
got a Pi type"), on the very first test exercising this shape at all.
Bisected by adding temporary `debug_assert_has_type` checks at each
composition step (confirming everything *before* the recursive call
type-checked, and only the *final* composition after it failed) rather
than by re-deriving the whole shift arithmetic by hand — the fix was
simply re-deriving `clo_ty` fresh after the recursive call, exactly the
discipline `build_clo_call_bridge`'s own doc comment already states as
the reason for its own analogous fresh re-derivations. The general
lesson: a genuinely *recursive* proof-construction function is a
stronger staleness trap than a linear sequence of pushes, precisely
because it's easy to reason "nothing local pushes between these two
uses" while missing that the recursive call itself is exactly the kind
of intervening push this whole `Anchored` discipline exists to guard
against — recursion is where "did anything push in between" stops being
answerable by reading the immediately-surrounding lines.

## 5. Self-types / Cedille — the same "postulate your way to power" tradeoff, one level down

Cedille (Stump et al.) gets inductive-datatype- and dependent-type-*like*
expressiveness on top of a base far weaker than full CIC (System Fω plus
one new "self type" former, `ιx:A. B`) rather than deriving it from a
maximal dependent kernel. This is the same tradeoff axis tatic itself
sits on — `assume_prim_fact`/`call_eq_ref`/every other computation-rule
axiom in `src/proof.rs` postulates exactly the behavior needed and no
more, rather than deriving it from first principles — just applied one
level up (type formers) instead of at the term/axiom level.

## 6. Observational Type Theory / Setoid Type Theory — equality without the heavy machinery

An alternative to HoTT/cubical for function extensionality and
well-behaved equality: define equality by recursion on type structure
("what would make two functions/pairs/etc. equal") rather than an
inductively-generated identity type with an axiom bolted on. Another
"honest, minimal postulate" design in the same spirit as tatic's own
`Id`-typed axioms — a useful reference point for anyone tempted to reach
for cubical machinery here later: it usually isn't necessary for what
this project actually needs from equality (compositional-structure
agreement between two readings of a term, not synthetic mathematics).

## 7. Homotopy Type Theory / Cubical Type Theory — the maximal end of the same axis

Equality as genuine structure (a path/identification), the univalence
axiom, cubical type theory (2015-on) giving it real computational content
via an interval type and Kan composition. Very active currently — 2024-25
work spans "higher observational type theory" (folding OTT ideas back
into HoTT), formalized synthetic-homotopy results in Cubical Agda, and
explicit unifications of cubical with guarded/multimodal type theory
(§3) into one framework. `Id` in `src/kernel.rs` is deliberately the
un-cubical, non-univalent Martin-Löf identity type — this tier represents
what tatic's kernel is *not* trying to be, on purpose: the goal here is
compositional-structure proofs about one specific compiler, not synthetic
homotopy theory.

## 8. Quantitative Type Theory — usage tracking, not arity tracking

QTT (Idris 2, Granule) extends dependent types with per-binder usage
multiplicities (0 = erased, 1 = linear, ω = unrestricted), checked as
part of typing. Tangential to tatic's own concerns (it tracks *how many
times* an argument is used, not *how many arguments* a function takes),
but flagged during the arity-polymorphism scoping pass as a reminder that
"track an extra dimension of a value's usage/shape in the type" is itself
an established, actively-used 2020s technique — relevant framing for
anyone re-approaching the arity-tracking problem in §9.

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

This new capability shipped compile-time-only at first, with no
kernel-checked proof counterpart — `Γ`'s own "one arity per variable"
limitation is unchanged, and `denote_closure`'s purely structural
classification has no way to reason about a value whose identity is
only known by executing, not by term shape (see `TYPES.md` §3.1/§6.3).

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
at all (`src/syntax.rs`'s own `higher_order_let_chain_evaluates_like_the_hand_built_demo_term`
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
`benches/common.rs`'s own `inconsistent_arity_loop_carried_parameter_loop`
and `jit::tests::a_tail_recursive_loop_compiles_and_is_kernel_verified_once_its_own_closure_parameter_turns_inconsistent`
were written to document as open. One new piece of plumbing this needed:
`eval_concrete`'s own pure-arithmetic fragment (`Var`/`Lit`/`Prim`/`If`)
can't evaluate a fresh argument that's itself a call (e.g. a loop-carried
`g(x)`, needed so a later branch condition depending on it stays
evaluable) — rather than duplicate a second concrete evaluator that
understands closures, `eval_concrete_dyn` rebuilds an `eval::Env` from
the current frame and defers to the reference interpreter (`eval::eval`)
directly.

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

## 10. Making `kernel::with_shift_cache` automatic — and why locally-nameless wasn't the fix

`with_shift_cache` (`src/kernel.rs`) was opt-in because wrapping every
`instance_from_scaffold` call regressed the common case: `fib(30)`'s
cold-compile time going from ~120ms to ~220ms, a real `HashMap` grown
across a construction and dropped, on top of routine small samples that
never needed it. Made automatic now, via `proof::instance_visit_count` —
a cheap, exact, `Expr`-free dry run of `build_ev_witness`'s own memoized
recursion (plain `i64` arithmetic, no term construction at all) that
counts how many distinct nodes *this concrete instance* actually visits,
engaging the cache only once that crosses a small threshold (`6`,
calibrated so `fib(8)`'s own proven ~2x win clears it while `jit.rs`'s
own routine samples, `0, 1, 2, 3, -1, -3, ...`, don't).

Considered first, and rejected: gating on the function's own *shape*
alone (does any leaf have more than one self-call), reusing data
`build_universal` already computes with no new analysis pass at all.
This looked like the ideal answer — free, structural, no prediction
needed — but measurably regressed the exact case it was meant to fix:
`sample_arg_vectors`'s own small samples still only visit a handful of
`build_ev_witness` nodes even for a branching-shaped function, so shape
alone re-triggered the original regression (confirmed: `fib(30)`'s
cold-compile time went to ~350ms), just now scoped to branching
functions instead of every function. The dry run fixes this by measuring
the actual concrete cost instead of only the syntactic possibility of
one.

**Also investigated, and deliberately not pursued: a locally-nameless
representation**, so postulate references never need reshifting at all.
Turns out to require two pieces working together, not one: (1) a
distinct `Free`-style constructor for postulate references, immune to
`shift`/`subst` — but `Var` is already a leaf, O(1) to shift regardless,
so this alone buys nothing, since the actual cost is recursively
*descending into* composite subtrees, not adjusting individual leaves;
and (2) a per-node cached "loose bound-variable range" letting `shift`
skip recursing into a subtree once `cutoff` already exceeds everything
adjustable inside it (the technique some kernels, e.g. Lean 4's, use this
exact metadata for) — but `proof.rs`'s own `Anchored::at`, the dominant
caller per the profiling above, always shifts at `cutoff = 0`, where
*every* ordinary `Var` needs touching, so this piece alone helps only
subtrees nested deep enough locally to matter, not top-level postulate
references. Only combined — postulate references as `Free`, plus the
range check able to see that a subtree built purely from `Free`s and
closed structure needs nothing touched *regardless* of cutoff — would
this plausibly hit the actual redundancy pattern. The blast radius is
smaller than it first looks (confined to `kernel.rs`'s `Expr`
representation and its constructors; `proof.rs`'s ~180 `Anchored`
call sites are untouched, since `shift` just gets cheaper underneath
them), but it's still a real change to `Expr` itself, and — the
disqualifying difference from the cache-based fix — a *correctness*-risk
one: a hand-derived range formula that's off by one binder would make
`shift` *silently* skip adjusting a variable that needed it, in the one
piece of machinery every proof in this kernel depends on, with no
sample-verification-style backstop the way the JIT has. Rejected in
favor of the dry-run heuristic above, which can only ever be *slow* when
wrong, never *wrong*.

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
`TYPES.md` §4.4). Currying that to `Clo_1`-of-`Clo_1` would need
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
unsoundness (§6.2 in `TYPES.md`) came from a single universal `Clo`
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
is comparable in size to the generic-dispatch rewrite (`RELATED_WORK.md`
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
`eval_dyn`/`DynVal` (RELATED_WORK.md §9's "Since covered, per instance"),
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

## 13. A `Call`-shaped `IfTree` leaf targeting a further `IfTree` — already worked, confirmed rather than built

Section 10 above added `Call`-shaped leaf support to
`clo_eq_ref_if_tree`/`resolve_closure_if_tree`, for a leaf whose own
target is itself resolved via a further, recursive `build_clo_call_bridge`/
`resolve_closure_shape_to_leaf` pass. That recursive pass dispatches
generically on `ClosureRhsShape` (`IfTree`/`Pap`/`Call`), so the natural
follow-up question is whether a `Call`-shaped leaf's *own target* can
itself be an `IfTree` (as opposed to a bare `Abs`/`Pap`) — i.e., whether
the two mechanisms compose two levels deep, not just one.

They do, with zero additional code. `resolve_closure_shape_to_leaf`'s
`IfTree` arm was already written to walk an arbitrary `DecisionTree` down
to whichever `Leaf` the concrete literals select, and `resolve_closure_if_tree`
already returns `IfTreeLeafResolution::Indirect` for a `Call`-shaped leaf,
carrying the fully-resolved concrete value up through the same recursion
used for a root-level `Call`. Nothing in that path assumes the *target*
of a `Call`-shaped leaf is any particular shape — it just recurses through
`resolve_closure_shape_to_leaf` again, which handles `IfTree` exactly as
it would at the root.

Confirmed empirically, not just by re-reading the dispatch: a term of the
shape `root = \a b. if 0<a then g(b) else (\c. b*2+c)`, where `g` is
itself `\b. if 0<b then (\c. b+c) else (\c. b-c)` (so the `Call`-shaped
leaf's own target `g` has a further `If`-shaped body, selecting between
two different concrete closures depending on `g`'s own argument) —
hand-verified against `eval::apply_term` across three literal cases
distinguishing every branch (`root`'s own `If`, `g`'s own `If`, and the
final called closure), then run through `eval_and_prove_call_over` and
kernel-checked — passed on the first attempt, added as
`a_call_shaped_if_tree_leaf_whose_own_target_is_itself_a_further_if_tree_gets_a_concrete_instance`
in `proof.rs`. Verify-teeth here took a different shape than usual:
since the new test exercises existing, already-verified machinery in a
new combination rather than new code, there's no production-code
mutation to make fail-then-revert. Instead, corrupting one of the test's
own hardcoded `expected` values and re-running confirmed the test's
assertions are genuinely live (not vacuously true) — same discipline,
applied to the test harness rather than to `proof.rs` itself.

**Takeaway:** `resolve_closure_shape_to_leaf`'s generic, shape-dispatched
design (built for section 10's single level of `Call`-leaf indirection)
already generalizes to arbitrary depth for free, because it recurses
through its own dispatch rather than hardcoding what a `Call` target's
own shape must be. No further work item follows from this — it's a
confirmation, not a capability gap.

## 14. Adding `Sigma` (dependent sums) as a fifth kernel primitive

A web survey of prior art on the open dependent-sum research question
(closing this document's own long-standing "an honest single kernel type
for 'either `Clo_1` or `Clo_2`'" gap) turned up two useful, opposed
precedents: typed closure conversion via existential/Sigma packaging
(Minamide/Morrisett/Harper; Bowman & Ahmed's PLDI'18 extension to the
Calculus of Constructions, which found the classical existential-package
trick breaks down for real dependent types — an unordered package can't
honestly hide an environment whose later entries' types depend on earlier
ones) versus defunctionalization (Huang & Yallop, PLDI'23), which
sidesteps that problem entirely by representing every closure in a
*closed, finite* program as one shared, tag-indexed type. This project's
own closed-world assumption (`combinator_return_type`'s own docs: the
"calls" relation over hash-consed literal lambdas is a strict partial
order over an already-fixed set) matches defunctionalization's own
precondition, not the open/first-class-module setting existential
packaging is built for — and this kernel already has a production
instance of the relevant recipe: `NatPostulates` builds `Nat := W(Bool,
ChildTy)`, tag = which constructor, payload shape varying by tag.

**Correction to that survey's own framing.** The survey's write-up
described a dependent sum as "a special case" of `W`, following how
general container/polynomial-functor treatments *define* `W` as the
fixed point of `X ↦ Σ(a:A). (B(a) → X)` — i.e. built *from* Sigma, not
the reverse. Attempting the encoding directly (rather than trusting that
framing) surfaces exactly why it doesn't run backwards here: `W(A,B)`'s
own `Sup` constructor requires its second argument to be a function
`B(a) -> W(A,B)`, mapping back into *the same* `W` type — it can only
stand in for a payload that's another instance of the same inductive
type, never an arbitrary, independently-chosen one. A general dependent
pair's second component is just a value of type `B(a)`, no such
self-reference required. There is no encoding of general `Sigma` from
this kernel's `Pi`/`Id`/`W` alone (short of a Church/impredicative
encoding from `Pi` alone, rejected for the same reason `W` was chosen
over Church-encoding inductive types in the first place: it wouldn't
reduce by `refl`, only propositionally) — `Sigma` needed to be added as
a genuine fifth primitive, not derived.

**The addition**, mirroring `W`/`Sup`/`WRec`'s own three-constructor
shape exactly: `Sigma(A,B)` (formation, `B` one binder deeper than `A`,
the same convention `Pi`/`W`'s own second field already use), `Pair(fam,
a, b)` (introduction — `fam` is `B` itself, carried explicitly because,
unlike `Sup`'s own second argument, whose `Pi`-type already reveals the
whole `W(A,B)` it targets, a pair's two components alone don't determine
which family was intended: many different families agree at one
concrete `a`, the same reason `Lam` carries its own domain annotation),
and `SigRec { motive, step, target }` (the recursor — genuinely simpler
than `WRec`'s: no induction-hypothesis closure to type, since a pair
isn't recursive, so no `children_ty`-style redundant field is needed).
Confirmed computing by `refl` alone, the same bar `w_recursor_computes_
definitionally` already set for `W` (`sigma_pairing_typechecks_and_
projects_by_refl`), and confirmed to genuinely need dependency, not just
tolerate it (`sigma_family_genuinely_varies_with_the_tag`, a family
`fam(x) := Id(A,x,a0)` that only typechecks because `subst_top`
correctly substitutes the tag into the payload type).

**A real regression, caught by the existing suite, not shipped
unnoticed.** Adding `Sigma`/`Pair`/`SigRec`'s own match arms directly
inline into `infer`/`shift`/`subst`/`whnf_impl`/`nf_impl` overflowed the
native stack on an existing, unrelated test
(`a_non_tail_self_call_carrying_an_inconsistently_classified_closure_
parameter_gets_a_per_instance_proof`) — confirmed via `RUST_MIN_STACK`
that it was a margin problem, not a genuine infinite recursion. This is
exactly the failure mode `wrec_children_ty_mismatch`'s own pre-existing
`#[cold] #[inline(never)]` extraction already documents: `eval_dyn`'s own
per-instance proof search runs close to its empirically-tuned
`DynBudget::recursion_depth` native-stack budget, and in a debug build,
every local variable appearing *anywhere* in a function's body — even in
a match arm no call in that recursive chain ever takes — inflates that
function's own per-call stack frame. Fixed the same way: every new arm
across all five functions extracted into its own `#[inline(never)]`
helper, so none of `Sigma`'s own locals cost the hot, pre-existing paths
anything. Worth remembering for any *future* kernel primitive: this
class of regression is invisible to `cargo build`/`clippy` and only
surfaces as a stack overflow in a deep-recursion test — extract new
`Expr`-match arms out of line from the start, don't wait to be bitten.

**Scope: the kernel primitive only, not yet wired to the motivating use
case.** This closes the *kernel-level* half of the dependent-sum
question — `Sigma` now exists, computes, and is tested in isolation.
`proof.rs`'s own arity-polymorphic closure question (the actual "either
`Clo_1` or `Clo_2`" problem this was motivated by) is *not* touched here
and would need its own separate design pass: a tag-indexed `W`-style
closure representation built on top of this primitive, threaded through
`ClosureCombinators`'s own postulate family. Not attempted in this pass
— deliberately scoped to "does the kernel primitive itself work," matching
this project's own standing discipline of landing one confirmed,
independently-tested layer at a time rather than a partially-wired one.

**Correction, a session later: that sketch doesn't actually reach the
motivating case, and the reason is load-bearing enough to write down
before attempting it for real.** Set out to build the tag-indexed `Clo`
representation the sketch above proposed, and prototyped it directly
(not just reasoned about it) before touching `ClosureCombinators`. The
design: `TaggedClo := Sigma(Int, fam)` where `fam(tag) := ite_sort_ref(tag,
Clo_1, Clo_2)` for a new postulate `ite_sort_ref : Int -> Sort(0) ->
Sort(0) -> Sort(0)`, mirroring `ite_clo_ref`'s own already-trusted shape
(`Int -> Clo_k -> Clo_k -> Clo_k`) one universe level up — selecting a
*type*, not a value. (A first attempt tried reusing `NatPostulates`'s own
`bool_rec` for this instead; it doesn't fit — confirmed by a direct
probe, not assumed — `bool_rec`'s own motive is hardcoded to `C : Bool ->
Sort(0)`, targeting ordinary *values* at level 0, but selecting between
two *types* needs a motive whose own codomain is `Sort(0)`-valued, i.e.
one level higher than what `NatPostulates` was ever built for. The
`ite_sort_ref` design above sidesteps this by not needing a dependent
motive or `Bool` at all, exactly the way `ite_clo_ref` itself doesn't.)

That part works — `fam` correctly infers as `Sort(0)` once `ite_sort_ref`
exists. But building the actual pair, `pair(fam, cond, f)` for a concrete
`f : Clo_1`, fails: `Pair`'s own kernel typing rule (`check(ctx, b,
subst_top(fam, a))`, see `Expr::Pair`'s own doc) requires the payload's
inferred type to be *definitionally* equal to `fam(a)` — and `fam(a) =
ite_sort_ref(a, Clo_1, Clo_2)` never reduces, because `ite_sort_ref`, like
every other case-discriminating mechanism available here (`bool_rec`,
`ite_clo_ref`, `ite_bool_ref`), is necessarily a *postulate* (`Int` has no
recursor in this kernel, deliberately — see `ite_clo_ref`'s own doc — and
a genuinely computing type-level `Bool` recursor hits the exact
"vacuous-eliminator, one universe up" wall this document's README
citation already names for bootstrapping `Bool`/`Nat` themselves).
Postulates never reduce by construction, so `def_eq` fails, confirmed
directly by `kernel::infer` rejecting the pair with a "type mismatch"
between `f`'s own `Clo_1` type and the stuck, unreduced `ite_sort_ref(a,
Clo_1, Clo_2)` application.

**This is not a narrower version of the same gap — it changes what the
achievable result even is.** The one available workaround, `transport`
across a *propositional* equality (`J`'s own infer rule doesn't require
the equality proof to reduce, only to be well-typed — confirmed this much
holds), only produces a well-typed pair once a *concrete* `Id`-proof
connecting `fam(a)` to `Clo_1` exists for that specific `a` — exactly
`ite_clo_eq_ref`'s own "memoized per exact literal" shape, needing `a`'s
concrete value known ahead of time. In `clo_eq_ref_if_tree`'s own
axiom-construction context, `a` (the condition) is an abstract quantified
variable, not a concrete literal, so no such proof can be built there —
meaning a Sigma-based `TaggedClo` can only ever be *instantiated* per
concrete instance, never quantified over universally. That's not actually
new capability: `eval_dyn`/`prove_closure_expr_instance` already handles
a per-instance closure of concretely-resolved identity, more directly and
without needing `Sigma` at all (§12, closed above). A tag-indexed `Sigma`
built this way would be strictly redundant with what already ships.

**Where this leaves the actual research question.** A genuinely
*universal* kernel proof for "the result is either a `Clo_1` or a
`Clo_2`, depending on an arbitrary runtime condition" needs the
type-level selector itself to compute — not just exist as a postulate —
for *any* symbolic condition, not only concrete ones. Nothing in this
kernel's current primitive set provides that (`Int` has deliberately no
recursor; the one type that does compute generically, `W`, has no way to
fold an *arbitrary arithmetic condition* into a `Sup`-shaped dispatch
without first deciding it, which is exactly the open question). This
isn't a gap `Sigma` closes by existing — it's the same "separate, larger
research question" this document already named before `Sigma` was added,
now with a concretely-ruled-out approach rather than an unexamined one.

**Reopened, a later session: the above overclaimed the wall's extent —
a symbolic-tag pairing genuinely typechecks, kernel-checked, once the
value is built the right way.** The failure above traced to how `f` (the
pair's payload) was built: independently, as an ordinary `Clo_1`-typed
closure, then relying on *reduction* (`fam(a)` normalizing all the way
down to `Clo_1`) to bridge its natural type to `Pair`'s own required
`subst_top(fam, a)`. That reduction only ever completes for a *concrete*
`a` (postulates and stuck `WRec`/`bool_rec` applications don't reduce for
a bound variable) — correctly diagnosed, but taken to mean no symbolic
construction could exist at all. It doesn't follow: `WRec`'s own typing
rule (`Expr::WRec`'s `infer` arm) hands back `app(motive, target)` as its
type *by construction*, not by reducing anything — so if the payload
itself is built as a second `WRec` application sharing `fam`'s own
`motive` (wrapped in a matching `Lam`), its inferred type and `fam`'s own
substituted form are literally the same expression up to one
*unconditional* beta step (`App(Lam, target) → target's body`, which
fires whether `target` itself reduces further or not) — `def_eq` (built
on full `nf`) closes the rest for free, regardless of whether the shared
tag is concrete or a bound variable.

Built and kernel-checked directly, not just reasoned about
(`kernel::tests::a_tagged_selector_built_via_wrec_typechecks_a_pair_for_a_symbolic_tag`):
a `Nat`-tagged (`NatPostulates`) selector `fam := wrec(motive, ChildTy,
step, Var(0))` with `motive := \_:Nat. Sort(0)` (constant — the family's
*own* type doesn't need to vary per branch; what varies is `step`'s
*value*) and `step` built via a new `sort_rec` postulate — `bool_rec`'s
own shape, but targeting `Bool -> Sort(1)` instead of the hardcoded
`Bool -> Sort(0)` `NatPostulates::bool_rec` carries (needed because
`step`'s own per-branch result is itself a *type*, e.g. `Unit` vs. `Nat`
standing in for `Clo_1`/`Clo_2` — a `Sort(0)`-valued term is itself
`Sort(1)`-typed; the payload-selecting `step` one level down, by
contrast, produces ordinary `Sort(0)`-typed *values* and reuses
`NatPostulates::bool_rec` unchanged, no new postulate needed there).
The payload `b := wrec(value_motive, ChildTy, value_step, a)` where
`value_motive := \x:Nat. fam` (literally reusing `fam` as the new
`Lam`'s own body) typechecks at `subst_top(fam, a)` for `a` a **freshly
pushed, unreduced postulate** — confirmed genuinely symbolic (`whnf(a)
== a`) and `fam(a)` confirmed to stay stuck, not secretly collapse to a
closed type — and `Pair(fam, a, b) : Sigma(Nat, fam)` typechecks as a
result. Verify-teeth: pairing `b` (built for tag `a`) against a
*different* concrete tag is correctly rejected by the kernel ("expected
a W type"), confirming the check isn't vacuous.

`value_step`'s own two branches (needed so `b` actually computes to the
*right* concrete payload once the tag becomes concrete, not merely
typechecks abstractly) needed one more piece: `value_motive(sup(tag,f))`
reduces to a *stuck* expression (`bool_rec`/`sort_rec` never
auto-reduce, concrete tag or not), so producing an inhabitant of it
needs `NatPostulates::bool_rec_true_eq`/`false_eq` (propositional) plus
`transport`, bridging a real, concrete witness (`nat.star`/`nat.zero`)
across — the same `cong1`/`f_cong` trick this document's own `is_zero`
proof (§3) already established, one level up.

**What this changes, and what it doesn't.** The earlier verdict —
"a Sigma-based `TaggedClo` can only ever be instantiated per concrete
instance, never quantified over universally" — is wrong as a general
claim about `Sigma`; a symbolic-tag pairing is achievable, kernel-checked,
today. What's still unresolved, and is the actually load-bearing gap
now: this construction needs the *tag itself* to already be a genuinely
`W`-typed value (here, `Nat`, riding on `NatPostulates`'s existing
`Bool`-indexed encoding) — `clo_eq_ref_if_tree`'s own `cond` is an
arbitrary `Int`-valued runtime condition (e.g. the result of `x < 5`),
not already a `Bool`/`Nat`-shaped tag, and `Int` deliberately has no
recursor in this kernel (`ite_clo_ref`'s own doc). Whether an arbitrary
`Int` condition can be bridged to a `W`-typed discriminant *universally*
(for every possible `Int` value, not case-by-case) is exactly the
"separate, larger research question" this document names above — now
narrowed from "can a computing type-level selector for a symbolic tag
exist at all" (settled: yes) to "can `clo_eq_ref_if_tree`'s specific
`Int`-typed `cond` be turned into one" (still open). Not attempted this
session — this correction is scoped to the kernel-primitive feasibility
question alone, matching this section's own standing discipline of
landing one confirmed layer before wiring it further.

## 15. Why over-application proofs cost ~1000x a plain arithmetic call — investigated to root cause

`benches/proofs.rs`'s own `over_application_instance_proof` doc comment
had flagged, since the benchmark was first written, that each
over-application instance (`eval_and_prove_call_over`'s own
`clo_eq_ref_if_between`/`clo_eq_ref_pap` shapes) costs roughly
20-30ms — three orders of magnitude past
`gcd_relational_proof_single_call`'s own ~24us per plain-arithmetic
call — "left as a discovered fact this benchmark documents, not
something fixed here." Investigated properly this session, with two
genuinely separate findings, one real and fixed, one real and inherent.

**Fixed, on the first attempt: real, but aimed at the wrong three of
five files.** `term::Hash` is a BLAKE3 digest — 32 bytes, already
uniformly random — and profiling `over_application_instance_proof`
under `callgrind` found `<DefaultHasher as Hasher>::write`/
`BuildHasher::hash_one` accounting for over 40% of all instructions
retired, re-hashing that already-good digest through Rust's default,
cryptographically-oriented SipHash for no benefit. The first fix applied
a small, self-contained rotate-xor-multiply hasher (`term::FxHasher`/
`FxBuildHasher`, the same reasoning `rustc-hash`/`FxHash` is built on)
across all 17 `HashMap<Hash, _>` sites in `term.rs`, `compile.rs`,
`jit.rs`, and `proof.rs`. It was correct (full test suite, fuzzers,
clippy, release demo all green) but helped only modestly (0% to -8.5%
wall-clock) — a sign something was off, since eliminating a 40%
instruction-count contributor should have moved the needle much more.

**Root cause, found via re-profiling and a direct question about
`hashbrown`'s own defaults: three of the five touched files were
already on a fast hasher, and the fix needed to go somewhere else
entirely.** Re-profiling after the first fix showed instruction count
barely moved (1.040B → 1.028B, ~1%) — the real win wasn't where the
first fix looked. `hashbrown` (already a direct dependency, and already
imported directly as `HashMap` in `term.rs`, `compile.rs`, and
`jit.rs`) ships its own `default-hasher = ["dep:foldhash"]` feature,
enabled by default: a bare `hashbrown::HashMap<K, V>` (no explicit
third type parameter) already uses `foldhash`, a modern, fast,
well-vetted non-cryptographic hasher — meaning those three files were
never the problem, and the custom `FxHasher` applied to them was a
lateral move, not a fix. The two files that *did* import
`std::collections::HashMap` (always SipHash, `hashbrown` or not) —
`proof.rs`'s `ClosurePostulates` memoization tables and `kernel.rs`'s
`ReductionCache`/`ShiftCacheMap` — were the real bottleneck, and hadn't
been switched to `hashbrown` at all (the first fix had only bolted a
custom `BuildHasher` onto their existing `std::collections::HashMap`,
which works but is strictly worse than the library's own vetted
default). Corrected by fully reverting the custom `FxHasher` everywhere
(deleted from `term.rs`; all 17 sites back to plain, unparameterized
`HashMap`) and instead changing exactly two import lines —
`proof.rs`'s and `kernel.rs`'s own `use std::collections::HashMap;` to
`use hashbrown::HashMap;` — no struct or constructor changes needed
anywhere, since every call site already used the simple `HashMap::new()`
API both types share.

**Confirmed properly this time: re-profiled, not just re-measured.**
Re-profiling `over_application_instance_proof` under `callgrind` after
the real fix found `DefaultHasher`/SipHash gone from the profile
entirely — not reduced, gone — with total instructions retired down
~44% (1.04B → 584M). Wall-clock (criterion) confirmed it independently:
-24% to -26% on both benchmark shapes, `p < 0.05`. This is also,
incidentally, the fix for this project's own previously-open lead on
`kernel.rs`'s `ReductionCache`/`ShiftCacheMap` sitting on the same
default SipHash — the same one-line-per-file import change covers both.

**Ruled out: `with_shift_cache` doesn't help here, confirmed by
measurement, not assumed.** Given ~938,812 `shift_rc` calls for 4
iterations, the natural next guess was that the existing
`with_shift_cache` mechanism (a proven ~2x win on large branching-leaf
instances, per its own docs) was simply not engaged for this shape.
Tried directly (wrapping the benchmark's own `prove_tail_recursive_instance`
call in `kernel::with_shift_cache`): it made both shapes measurably
*slower* (223ms vs 202ms; 139ms vs 127ms), not faster. This matches the
cache's own documented limitation: it wins when the *same* subterm gets
reshifted by the *same* amount across several callers, and loses
(HashMap overhead paid for nothing) when it doesn't. This workload's own
938K shift calls aren't that pattern — see below for what they are.

**The real, inherent answer: the cost is super-linear in iteration
count by construction, not a hidden bug.** A direct scaling check (the
same term, `prove_tail_recursive_instance` at 1, 2, 4, 8, 16, 32
iterations) measured 69.6ms / 102ms / 204ms / 441ms / 985ms / 2672ms
(measured before the hashbrown/foldhash fix above — the fix changes the
constant factor throughout, not this shape). Each doubling of the
iteration count costs progressively *more*, not a
constant multiple (1.47x, 2.00x, 2.16x, 2.24x, 2.71x) — consistent with,
and explained by, `trans_proof`'s own cumulative composition: each new
iteration's own step proof is built by transitivity against the *entire*
proof chain accumulated so far (`kernel::trans_proof`, chained once per
iteration), so total work across `n` iterations is a sum of growing
terms — the same reason repeatedly appending to a growing structure by
copy is inherently superlinear, not specific to closures or
`eval_and_prove_call_over` at all. `with_shift_cache`'s own inability to
help is the same fact from a different angle: there's no *repeated*
work to cache here, just a genuinely *growing* one.

**This also means the original comparison was apples to oranges.**
`gcd_relational_proof_single_call`'s ~24us proves one *relational* step
of a tail-recursive call (`prove_tail_recursive_call`) — it never
unrolls or accumulates a chain across iterations at all, by design (see
this project's own module docs on the relational-vs-universal-vs-instance
proof strategies). `over_application_instance_proof` measures a fully
*unrolled instance* proof's own amortized per-iteration cost instead — a
structurally different, inherently more expensive strategy, run here at
just 4 iterations specifically because that's what real usage
(`build_ev_witness`'s own per-self-call-argument handling) needs, not
because the underlying operation is 1000x more expensive at matched
strategies. The three-orders-of-magnitude framing measured a real
number correctly, but implied a comparison ("over-application closures
are inherently ~1000x slower than arithmetic") that doesn't hold once
the two benchmarks' own proof strategies are accounted for.

## 16. `Div`'s compiled and interpreted semantics silently disagreed at one input — found and fixed

`eval.rs`'s reference interpreter implements `PrimOp::Div` with
`wrapping_div`, the same non-trapping, silently-wraps-on-overflow
convention `Add`/`Sub`/`Mul` already use uniformly (`Mod` needs no such
treatment -- `wrapping_rem` and Wasm's `i64.rem_s` already agree at the
one input that matters here). `compile.rs`'s codegen, until now, emitted
a bare `i64.div_s` for `Div` -- and per the WebAssembly spec, `i64.div_s`
*traps* at exactly one input, `i64::MIN / -1` (the one case where the
mathematical quotient itself overflows `i64`), rather than wrapping.
Interpreted: `Ok(i64::MIN)`. Compiled: a trap, i.e. `Err`. A genuine,
if narrow, disagreement between the reference semantics and the
compiled fragment -- exactly the class of bug `jit.rs`'s own sample
verification exists to catch, and it does, whenever a term's structure
happens to divide by a sampled `-1` while the dividend is `i64::MIN`.
`SAMPLE_ARGS` (`jit.rs`) never includes `i64::MIN`, though, so a term
that instead *computes* `i64::MIN` at runtime (from small sampled
inputs, e.g. via repeated doubling or a shift) and then divides that by
`-1` would never trigger the mismatch during verification, and its
wrong compiled behavior on that one input would go undetected.

Fixed by special-casing that one combination in codegen
(`compile::emit_wrapping_div`) rather than changing `eval.rs`: two new
scratch locals (`$diva`/`$divb`, declared unconditionally in
`compile_function` alongside `$envtmp`/`$papenv`, the same "harmless if
unused" convention) hold the two operands, an `i32.and` of two `i64.eq`
checks decides whether this is the overflow case, and an `if (result
i64)` either yields `i64::MIN` directly or falls through to the ordinary
`i64.div_s`. `jit::tests::division_agrees_with_the_interpreter_at_i64_min_over_negative_one`
is the permanent regression guard -- reverting the fix makes it fail
immediately with a `Trap`, confirming it actually exercises the new
codegen path rather than passing vacuously.

## 17. A structural verification-coverage gap in `sample_arg_vectors` for arity >= 3 -- found and fixed

`jit.rs`'s `sample_arg_vectors` (the sample battery both `verify()` and
every per-sample `kernel_verify` fallback use to gate trust in a
compiled term) had a higher-arity (`_`, arity >= 3) branch whose own
comment promised two diagonals -- "the all-equal and all-small-distinct
diagonals" -- but only ever generated the first: `vec![a; arity]` for
each of a few sampled `a`s, every position the *same* value. No code
path produced a sample where different positions held different values.

The consequence is structural, not incidental: a compiled-code bug that
swaps or misindexes two argument positions (a codegen slot mixup between
parameters 1 and 2, say) is *invisible* to an all-equal sample -- swapping
two equal values changes nothing observable. Every arity->=3 term's
`verify()` call, and every per-sample kernel proof attempt built on the
same battery, was checking a battery that could never have caught that
bug class, for as long as this project has had a JIT. Confirmed nothing
in the fuzz suite exercised arity->=3 at all either (`compile_fuzz.rs`'s
generators all cap arity at 1 or 2), so this wasn't compensated for
elsewhere.

Fixed by actually generating the promised second diagonal: several
rotations of `SAMPLE_ARGS`, each assigning a different sampled value to
each argument position (`(0..arity).map(|i| SAMPLE_ARGS[(i + offset) %
SAMPLE_ARGS.len()])` for a handful of `offset`s). No bug was found by
adding this -- the compiler itself checked out clean -- but the coverage
gap itself was real, and closing it is what makes that a confirmed
absence of bugs rather than an unchecked one.
`jit::tests::sample_arg_vectors_for_higher_arity_includes_a_genuinely_distinct_sample`
is the permanent regression guard; reverting the fix makes it fail
immediately, confirming every sample it generates really was constant
across positions before.

## 18. A mismatched call arity could permanently poison the JIT cache -- found and fixed

`JitEngine::compile_verify_and_apply` cached `CacheEntry::NotCompilable`
whenever a call's `args.len()` didn't match `h`'s own structural arity
(`frag.arity`, from `compile::try_compile`) -- conflating "is `h`
compilable at all" (a real property of `h` alone) with "did *this one
call* happen to pass the right number of arguments" (a property of the
call, not the term). Since `eval::apply_term` is fully generic over arg
count (applies one at a time, so under- or over-applying a term is a
legitimate, well-defined shape, not an error condition in itself), a
single mismatched call permanently defeated compilation for that term:
every later call, even one with the correct arity, hit the cached
`NotCompilable` entry and was routed to the interpreter forever, with
compilation never retried.

A second, related gap in the same area: `apply`'s own dispatch for an
*already-compiled* cache entry never checked the incoming call's arity
against the arity it was actually compiled for before calling
`call_compiled` -- which carries a `debug_assert_eq!(arity, args.len())`
of its own. A mismatched call against an already-compiled term would
therefore panic in a debug build, or in release, hand the compiled
function's fixed Wasm signature the wrong number of `Val`s, surfacing as
a spurious `Trap` rather than the correct, ordinary interpreter fallback
every other "can't serve this shape from the cache" path already gets.

Fixed by (1) no longer caching `NotCompilable` on an arity mismatch --
just interpreting that one call and leaving the cache untouched so a
later, correctly-sized call gets a fresh attempt, and (2) checking a
`Compiled` entry's own stored `arity` against the call's `args.len()`
in `apply` itself before ever reaching `call_compiled`, falling back to
`eval::apply_term` on a mismatch exactly like every other "not servable
from the cache" case already does.
`jit::tests::a_mismatched_arg_count_does_not_poison_the_cache_and_is_served_by_the_interpreter`
covers both: a mismatched call followed by a correctly-sized one (which
must still compile), and a mismatched call against an already-compiled
entry (which must fall back cleanly, not panic or trap) -- reverting
either half of the fix makes it fail immediately.

## 19. `eval_dyn_direct_call`'s cross-combinator inlining could grow the native stack without bound -- found and fixed

`proof.rs`'s per-instance proof machinery bounds two distinct kinds of
native-stack recursion through `DynBudget`: `eval_dyn_tail_recursive`'s
own flat loop (`tail_steps`, generous, since the loop itself never
recurses through Rust's call stack) and `eval_dyn`'s recognition of an
*embedded* (non-tail) self-call (`recursion_depth`, deliberately much
smaller, since each one is a genuine Rust stack frame). A third path
through the same machinery had no bound at all:
`eval_dyn_direct_call`'s own `needs_inline` branch -- reached whenever a
call's callee concretely returns a further `Clo`, or some argument's
concrete value is a `Clo` that the callee's own static classification
declined to type as one -- inlines into a *different* combinator's body
(reached only through an ordinary captured closure value, `Rec`-wrapped
or not) by recursing straight back into `eval_dyn`/`eval_dyn_tail_recursive`,
with no check against either counter. Two or more combinators calling
each other only through captured closures (never a direct self-call
`eval_dyn`'s own recognition would catch) could therefore recurse the
native Rust stack without any bound at all -- a crash/DoS risk, not a
soundness one, since a term that got this far without declining could
still only ever be trusted once `kernel::check` verifies the resulting
proof term.

Fixed by checking and decrementing a budget counter on this path too,
before recursing -- but *not* by reusing `recursion_depth` directly.
Measured directly (a term built specifically to drive this path: `step =
\g n. if 1<0 then g(999) else (if n<=0 then n else g(g, n-1))`, called as
`step(step, n0)` -- a plain, non-`Rec` Y-combinator-style self-application
that reaches `step` again only via an ordinary captured `Clo` value, never
via `eval_dyn`'s own `self_ctx`-based recognition, since inlining always
hands the callee a *fresh* `None` self_ctx; the dead `g(999)` call site
forces `g` to classify as `Inconsistent`, so every level takes the
`needs_inline` branch), reusing `recursion_depth`'s existing bound of 50
reliably overflowed the native stack in an unoptimized debug-build test
thread at roughly the 43rd-45th level -- comfortably *inside* that bound.
`eval_dyn_direct_call` itself carries substantially more live state per
frame than the embedded-self-call case `recursion_depth` was tuned for
(`param_types_for`, `combinator_return_type`, and each argument's own
`eval_dyn` call, all evaluated before dispatch is even decided), so the
same numeric bound isn't safe for both paths.

The first fix attempted was out-of-lining the continuation into its own
`#[inline(never)]` function (`eval_dyn_inline_call`), mirroring `kernel.rs`'s
own `infer_sup` precedent (§3/inline note above) exactly. Unlike that
precedent, this alone did *not* resolve the overflow: `infer_sup` worked
because the *caller*'s own locals were what was marginal; here,
`eval_dyn_direct_call`'s own prologue stays live on the stack for the
whole nested call regardless of what's extracted out of its tail, since
it's still waiting on that call to return. The actual fix is `DynBudget`
gaining a third, dedicated counter -- `inline_call_depth`, set to 25,
comfortably below the measured (40 safe / 45 overflowing) boundary --
checked and decremented in `eval_dyn_direct_call`'s `needs_inline` branch
independently of `recursion_depth`, so `eval_dyn`'s own embedded-self-call
recognition keeps its existing, already-validated bound unchanged.
Verify-teeth: removing the `inline_call_depth` check reliably reproduces
the stack overflow on
`proof::tests::a_self_application_reached_only_through_a_captured_closure_is_bounded_by_recursion_depth`'s
own `n=1_000_000` case; restoring it declines cleanly (a graceful `None`)
instead, while `n` in `{0, 1, 3, 10}` still get correct, kernel-checked
per-instance proofs agreeing with the interpreter.

Worth remembering alongside the `infer_sup` episode: an out-of-line
extraction shrinks a *caller's* stack cost, not a callee's own prologue
that stays resident across the recursive call -- when the latter is what's
marginal, the fix is a smaller, honestly-scoped budget for that
specific path, not restructuring the code around the existing one.

## 20. `eval_dyn_direct_call` wastefully evaluated arguments before a cheap, args-independent scoping check -- found to be a crash risk, not just a performance one

`eval_dyn_direct_call` always evaluated every argument (`arg_vals`, each
its own, possibly expensive, recursive `eval_dyn` call building up a
kernel proof term) *before* deciding `needs_inline` and, inside
`eval_dyn_inline_call`, checking whether `root`'s own captures are
non-empty (out of this whole per-instance methodology's scope -- it only
ever inlines a non-capturing `root`). Whenever `return_ty.is_some()` --
a fact about `root`'s own static structure alone, entirely independent
of what the arguments evaluate to -- `needs_inline` is already
unconditionally about to be `true`, so if `root`'s captures also turn
out non-empty, every bit of work spent evaluating the arguments was for
nothing: the call was always going to decline.

Measured directly, not just reasoned about: `compile::free_vars` (the
captures check) is a pure, cheap function of `root`'s own body/arity/
`is_rec` alone, so it can just as well run *before* evaluating any
argument. Doing so isn't merely faster in the case it fires -- reverting
it and constructing a term specifically to hit this path (a capturing
closure that itself returns a further `Clo`, reached via a `let`-bound
call whose argument is a deliberately expensive, genuinely non-tail
300-deep `Prim` chain) reliably **overflowed the native stack** in an
unoptimized debug-build test thread, rather than just running slowly.
`eval_dyn`'s own non-tail `Prim` evaluation has no `DynBudget` counter
bounding it at all (unlike the self-call and inline-call paths, which
do) -- it's assumed to stay shallow in practice, an assumption this path
could silently violate by wastefully evaluating an argument that was
never going to matter.

Fixed by computing `captures` once, immediately after `root`'s arity/
body/`is_rec`/`param_types`/`return_ty`, and returning `None` right away
when `return_ty.is_some() && !captures.is_empty()` -- before the
argument-evaluation loop, not after. `captures` is then threaded through
to both `eval_dyn_inline_call` (which no longer needs to recompute
`free_vars` itself) and the opaque-call path below (which already needed
the same value as its own `captures` local) -- a genuine simplification
alongside the fix, not just a reordering. Since the whole `combinators`
context (including anything an argument's own evaluation might have
pushed into it) is discarded unconditionally whenever `eval_dyn_direct_call`
returns `None` -- `prove_closure_expr_instance`'s own `?`-propagation
never looks at partial state on failure -- skipping the wasted evaluation
changes no observable output, only whether it's paid for.
`proof::tests::a_capturing_clo_returning_root_declines_without_evaluating_its_own_argument`
covers it: reverting the hoisted check back to its original position
(checked only after every argument is evaluated) reproduces the stack
overflow on this exact term; restoring it declines cleanly instead.

## 21. `try_compile` generated a curried stage chain for every registered combinator, whether or not anything ever dispatched through it -- found and pruned

Once a fragment needed generic dispatch at all (`Combinators::needs_generic_dispatch`
-- some closure-typed variable is called with genuinely different arities
at different call sites), `try_compile` generated `emit_curried_stages`'s
full curried stage chain (one Wasm function per remaining argument, plus
a densely-allocated funcref table slot for each) for *every* registered
combinator in the fragment, unconditionally. But a `stage_0` index is
only ever packed into an `i64` value at two specific sites in
`compile_node` -- a literal lambda used as a plain value, and an
under-applied root's own PAP-wrapper creation -- so a combinator only
ever reached through a direct, exactly-saturated call site (`call
$c{idx}` straight from another combinator's own body, never packed as a
value at all) had a stage chain generated for it that nothing could ever
call through: dead Wasm functions and dead table slots, purely from
generic dispatch being on anywhere in the fragment rather than from this
specific combinator ever needing it.

Fixed by tracking, during the discovery pass, exactly which combinator
(or PAP wrapper) indices are ever reached as a bare value --
`Combinators::used_as_bare_value`, a `HashSet<usize>` populated
unconditionally (not gated on `emitting`/`needs_generic_dispatch`) at the
same two sites that read `stage0_index`. Since discovery already walks
every reachable combinator's own body once (the existing fixpoint over
`combinators.pending`), and neither of those two sites' own control flow
differs between the discovery and emit passes (both branches of every
`emitting`-gated choice compile the identical set of sub-terms, just with
different Wasm sequencing -- confirmed by reading through the surrounding
`Term::Var(i)`-callee and over-application dispatch code, neither of
which itself registers or creates a bare value), the set is already
complete by the time discovery finishes, and the emit pass can only ever
re-confirm membership, never discover a new entry. `try_compile`'s stage-
generation loop, the funcref-table-length computation, and the `elem`
section's own listing all now skip any index the set doesn't contain,
freeing up `stage_needs_alloc` to narrow the same way (a fragment that
needs generic dispatch for *calling* through a variable, but never itself
creates a bare value locally, now needs no allocator-driven stage
machinery at all).
`compile::tests::a_combinator_never_reached_as_a_bare_value_gets_no_stage_chain_even_when_the_fragment_needs_generic_dispatch`
covers it directly: a fragment with one inconsistent-arity parameter (so
`needs_generic_dispatch` is true) alongside a second, unrelated literal
combinator that's only ever called directly and saturated -- asserts the
first still gets a stage chain (dispatch isn't broken) while the second's
`$c{idx}` fast-entry function has no matching `$s{idx}_*` anywhere in the
output. Reverting the pruning filter back to unconditional makes this
assertion fail, confirming it's exercising the real mechanism.

## 22. kernel.rs's typing context was cloned wholesale at every binder -- found and switched to a persistent structure

`kernel.rs`'s `Ctx` (`infer`/`check`'s own typing context, threaded
through every recursive call) was a plain `Vec<Expr>`. Every binder --
`Pi`, `Lam`, `Sigma`, `Pair`, `W` -- entered its body one level deeper by
doing `let mut ctx2 = ctx.clone(); ctx2.push(...)` before recursing, at
five call sites (`infer_sigma`, `infer_pair`, and `infer`'s own `Pi`,
`Lam`, and `W` arms; `check`'s `Lam`-against-`Pi` special case makes it
six). Each `Expr` itself is cheap to clone (`Rc`-based), but the *`Vec`*
clone is O(current context length) regardless -- so a term with `k`
nested binders, checked under a context of length `L` at its deepest
point, pays O(k*L) total copying, not the O(k) the module's own
"one push per binder" design implies. Confirmed with a deliberately
deep, cheap-to-build stress term (`pi(sort(0), pi(sort(0), ... sort(0)))`
nested 800 deep, checked from an empty context via `typecheck`): 17.8ms
with the plain `Vec`, vs. 2.45ms after the fix below -- a ~7x difference
at a depth this project's own `eval_dyn`-adjacent proof search can
plausibly reach, and one that gets worse, not better, as terms grow.

Considered and rejected three alternatives before fixing this: manual
mutable push/pop (`&mut Ctx` instead of by-value clone-then-recurse) --
correctness-equivalent and allocation-free, but would have meant
threading pop-on-every-return-path through `infer`/`check`'s entire
call graph in both `kernel.rs` and `proof.rs`, in the single most
soundness-critical part of the codebase, for a purely-performance fix;
`Rc<Vec<Expr>>` plus `Rc::make_mut` -- doesn't actually help, since the
caller's own `ctx` reference stays alive across the recursive call at
every one of these sites, so the refcount is never 1 at the point
`make_mut` would need it to be, and it clones anyway; and a hand-rolled
persistent structure -- avoids a new dependency, but risks introducing a
genuinely new bug into the kernel to solve a problem an existing,
well-tested library already solves.

Fixed by switching `Ctx` to `im::Vector<Expr>` (the `im` crate, added as
a new dependency): a persistent, structurally-shared vector whose
`.clone()` and `.push_back()` are both O(log n) (amortized ~O(1) in
practice) instead of O(n). The fix is almost entirely mechanical --
`Ctx`'s definition, `Postulates::new`'s `Vec::new()` -> `Ctx::new()`,
the six `.push(...)` call sites -> `.push_back(...)`, and
`ctx_lookup`'s own `ctx[idx]` needs no change at all (`im::Vector`
implements `Index<usize>` the same way `Vec` does). The one non-trivial
spot: `close_pi`/`close_lam` (`kernel.rs`) used to take `ctx: &[Expr]`
and slice it (`ctx[base_len..]`) to find "everything pushed since
`base_len`" -- `im::Vector` has no contiguous backing store to slice, so
these now take `&Ctx` directly and use `ctx.iter().skip(base_len).rev()`
instead. Both call sites that pass `close_pi`/`close_lam` around as `fn`
pointers (`proof.rs`'s `params_and_close`/`params_and_close_typed`)
needed their pointer type updated to match (`fn(usize, &Ctx, Expr) ->
Expr`), but their own bodies -- and everywhere else that reads, clones,
or truncates `arith.p.ctx` -- needed no change: `im::Vector` already
supports `.len()`, `.clone()`, and `.truncate()` with the exact same
signatures `Vec` did.

Verified directly (not just by reasoning about complexity): reverted
`Ctx` back to `Vec<Expr>` via `git stash`, re-ran the same 800-deep
stress term, reproduced the 17.8ms baseline, then restored the fix and
confirmed the 2.45ms result again -- a real, measured improvement, not
just an asymptotic argument. Full existing suite (188 lib/bin tests, all
four fuzzers at release, `cargo clippy --all-targets`, the `cargo run
--release` demo) stayed green throughout, confirming the change is
observably behavior-preserving.

## 23. jit.rs's kernel_verify recomputed the same sample battery three times, and invoke() paid a heap allocation on every call -- found and fixed

Two small, independent inefficiencies in `jit.rs`'s hot verification/
invocation paths:

`kernel_verify` called `sample_arg_vectors(arity)` three separate times
(once truncated to the first 3 samples for
`prove_tail_recursive_universal_with_instances`, once in full for
`prove_tail_recursive_call`, once more in full -- identical output to
the second call -- for `prove_closure_expr_instance`), recomputing and
reallocating the same `Vec<Vec<i64>>` each time even though only the
first call's result is ever truncated. Fixed by computing the sample
battery once and reusing it for all three: the truncated slice
(`samples.iter().take(3).cloned()`) for the first strategy, and the full
`samples` (already alive, only ever borrowed by the second strategy's
own `.iter().all(...)`, never consumed) for the second and third.

`invoke` -- the function every real compiled-function call (and every
`verify()` sample call) goes through -- built a fresh `Vec<Val>` from
`args` on every single call, an unconditional heap allocation on what's
meant to be the JIT's fast path. Fixed with a small stack-allocated
buffer (`Val` is `Copy`, confirmed from wasmtime's own source) for the
common case: `STACK_ARGS = 8` covers every combinator arity this
project's own demo/bench/test corpus reaches, with a `Vec` fallback kept
for the rare case above that bound, so correctness at any arity is
unaffected.

Verified directly, not just by inspection: added
`invoke_agrees_with_the_interpreter_past_the_stack_buffer_threshold`
(a 10-ary summing term, deliberately past `STACK_ARGS`), asserting both
that the compiled result agrees with the interpreter *and* that the term
actually went through the compiled path (`jit.stats.compiled == 1`) --
the second assertion turned out to be load-bearing: a deliberately
truncated heap-fallback buffer (dropping the last two arguments) didn't
produce a wrong *value* here, since `verify()` itself calls `invoke` on
its own sample battery first and a corrupted fallback just makes that
verification disagree, safely blacklisting the term to the interpreter
(exactly the project's own "sound, not complete" architecture doing its
job) -- confirmed by watching `jit.stats.compiled` read back `0` instead
of the expected `1` under the deliberately broken version, then
restoring the fix and confirming `1` again.

## 24. proof.rs's closures-section doc comment still described the pre-migration opaque-Clo/apply_k design -- found and swept

The doc block opening `proof.rs`'s closures section (and roughly a dozen
smaller echoes scattered through the file) still described an earlier
design: a closure value postulated fully opaque (`Clo : Sort(0)`, the
same pattern `Int` itself uses) with a separate axiom, `apply_k : Clo ->
Int^k -> Int`, postulated once per arity to let a `call_indirect` site
apply one. That design was superseded in two steps this project's own
history already covers (`RELATED_WORK.md` section 11, and the
`apply_ref`-removal writeup later in `proof.rs` itself): `Clo` was first
made arity-aware (`apply_k` renamed/reworked into a per-arity
`apply_ref(k)`), then `apply_ref` itself was removed entirely once
`Clo_k` became a *literal* kernel Pi type (`Int -> .. -> Int`, `k`
copies, built from ordinary `Pi` nodes via `ClosurePostulates::clo_ty`)
rather than an opaque `Sort(0)` postulate -- calling one through a
closure-typed parameter is now just ordinary `App`, checked by
`kernel::infer`'s own Pi-application rule, no per-arity axiom needed at
all. The `apply_ref`-era writeup (`proof.rs`, the "Caught a real bug
while building this" section) was correctly kept as history when
`apply_ref` was swept in an earlier pass; the older `apply_k` mentions,
predating even that, were simply never touched at either migration and
were still describing the axiom-based design in the present tense as if
it were current.

Swept every present-tense `apply_k`/`Clo : Sort(0)` mention (the main
closures-section header block, `build_universal`'s own doc, `denote_closure`'s
doc, `combinator_return_type`'s doc, `return_type_of`'s inline comment,
`ClosureCombinators::env_ty`'s doc, `call_ref`'s doc, and a test's own
doc comment) to describe the actual, current mechanism: `Clo_k` as a
real Pi type, ordinary `App` for the generic closure-typed-parameter
case, and `ite_clo_ref` as the one genuine remaining axiom (needed only
for an `If` choosing between two same-arity closures, since `Int` has no
case-eliminator in this kernel). Left untouched the handful of `apply_k`/
`apply_ref` mentions that are explicitly narrating history ("used to
be", "was removed", a bug-fix writeup describing the mechanism as it
existed *at the time*) -- those are accurate as written and rewriting
them to the present tense would make the history they're recording
harder to follow, not easier.

No code changed (comment-only), so verification here is `cargo build
--all-targets`, `cargo clippy --all-targets`, and `cargo doc --no-deps`
(to confirm no new broken intra-doc links -- the 9 pre-existing warnings,
all an unrelated `Hash` type-alias/derive-macro ambiguity, are
unchanged) staying clean, plus the full existing test/fuzz suite and the
release demo confirming the change is what it claims to be: purely
textual.

## 25. Two smaller stale doc comments (compile.rs, kernel.rs) -- found and fixed

Two more small doc-staleness items, each caught by grepping for a claim
the code no longer supports:

`compile.rs`'s `emit_curried_stages` still said "Not yet reachable from
`try_compile`'s own codegen" -- true when originally written (Phase 1 of
the curried-dispatch rewrite, built and tested in isolation before being
wired in), stale since Phase 2 actually wired it into `try_compile`'s own
stage-generation loop. Fixed to describe the real, current gating: called
once per combinator that's both in a fragment needing generic dispatch
(`Combinators::needs_generic_dispatch`) *and* actually reached as a bare
value (`Combinators::used_as_bare_value`, section 21 above).

`kernel.rs`'s `infer_sigma` doc still said "nothing in this crate
constructs a `Sigma`/`Pair`/`SigRec` term yet (this primitive was just
added)" -- true when `Sigma` was first added as a postulate-free kernel
primitive, stale since the crate's own test module now builds and checks
several (`sigma`/`pair`/`sigrec` calls throughout `kernel.rs`'s tests).
Fixed to state the actual, permanent reason for the `#[inline(never)]`
extraction (keeping these arms' own locals off `infer`'s hot frame on
every *other* expression shape) without the now-false "nothing
constructs one yet" framing.

Comment-only changes; verified the same way as section 24: full build/
clippy/doc/test/fuzz/demo suite green, `cargo doc` showing no new
warnings.

## 26. term.rs's content_hash under-sized its scratch buffer -- found and fixed

`Term::content_hash` built its serialization scratch buffer with
`Vec::with_capacity(64)`, but `write_bytes`'s own worst case (`If`,
carrying three `Hash`es) needs `1 + 3*32 = 97` bytes -- past 64, forcing
`Vec` to grow (doubling to 128) partway through every single `If` node
interned. `Prim` (`1 + 1 + 2*32 = 66`) and even `App` (`1 + 2*32 = 65`)
both exceed 64 too, so in practice almost every non-leaf node hit this
same unnecessary reallocation. Fixed by starting at 128 directly, which
comfortably covers every variant with no growth needed at all.

This closes out the last item on the audit's punch list (`RELATED_WORK.md`
sections 16 through 26 above cover items #2-13: five soundness/
correctness fixes, three performance fixes, three doc-staleness sweeps,
and this one) -- worked one by one, each with its own implement/verify/
validate/document/commit/push cycle.

## 27. pap_ref mistyped a partial application when the root's own saturated call itself returns a closure -- found and fixed

A fresh, from-scratch audit (independent of the prior 26-section punch
list) surfaced a genuine soundness bug in how `proof.rs` types a partial
application. `pap_ref` builds the postulated Pi type for `mk_pap_h_k`,
the wrapper standing in for a combinator `h` (arity `arity`) called with
only `k` of its arguments supplied. Every call site computing this
wrapper's "remaining shape" -- `pap_ref` itself, `return_type_of`'s
`Ordering::Less` (partial-application) arm, three `debug_assert_has_type`
sites in the three parallel closure-denotation pipelines
(`denote_with_placeholders`, `denote_closure_typed`, `denote_closure`),
and the PAP-shape classifiers `clo_eq_ref_pap`/
`classify_closure_if_tree_leaf` -- hardcoded that remaining shape as
`Clo_{arity-k}`, silently assuming `h`'s own saturated call always
denotes `Int`.

That assumption is false whenever `h`'s body itself returns a further
closure. For example `root = \p a. if a == 0 then (\b. b) else (\b. a +
b)`: `root`'s saturated call (both `p` and `a` supplied) denotes `Clo_1`,
not `Int`. So `root x` -- a 1-of-2 partial application, `p` supplied, `a`
still missing -- has genuine remaining shape `Clo_2` (`a`, then `b`), not
the `Clo_1` every one of the sites above assumed. Since `Clo_k` is a
*literal* kernel Pi type (`ClosurePostulates::clo_ty`), not an opaque
postulate, the kernel has no way to catch this on its own: a wrong-but-
internally-consistent arity still typechecks. Concretely: put that PAP
value in one arm of an `If` whose other arm is a genuine, unrelated
`Clo_1`, then call the result with a single argument as if both arms
agreed on arity. `prove_closure_expr` built and the kernel happily
accepted a `refl`-based proof claiming this was *universally* valid; the
compiled form was marked `is_kernel_verified`; and at a concrete
adversarial input reaching the mismatched arm, the compiled code --
genuinely dispatching one argument short -- returned whatever raw bits
its own extra `call_indirect` produced (garbage, not a trap), silently
disagreeing with the interpreter.

Fixed with one new shared helper:

```rust
fn pap_extra_arity(store: &TermStore, root: Hash) -> usize {
    combinator_return_type(store, root).flatten().unwrap_or(0)
}
```

and folding it into every site above: the remaining shape is
`Clo_{(arity-k) + pap_extra_arity(h)}`, not `Clo_{arity-k}`. This fold is
*exact*, not approximate: `Clo_j`/`Clo_m` are both literal, associative
Pi-type chains, so `Int^(arity-k) -> Clo_m` is definitionally the same
term, arrow for arrow, as `Clo_{(arity-k)+m}` -- not merely isomorphic to
it -- whenever the remaining `arity-k` parameters are themselves plain
`Int` (every call site already independently restricts to that case, the
same restriction `combinator_return_type`'s own callers already default
to: "undetermined" conservatively means "assume no widening," consistent
with this classifier's use everywhere else in the file).

Verified with a permanent regression test,
`if_branches_with_different_pap_extra_arity_are_not_conflated_into_a_false_proof`,
built from exactly the `root`/`If`-between-mismatched-arities shape
above, asserting `prove_closure_expr` returns `None`. Verify-teeth:
temporarily made `pap_extra_arity` return `0` unconditionally (reproducing
the pre-fix behavior at its single defining site rather than reverting
seven call sites by hand) and confirmed the new test fails exactly as
expected (the false universal proof reappears), then restored the real
definition and confirmed it passes again. Full validation green
afterward: `cargo build --all-targets`, `cargo clippy --all-targets`,
`cargo test --lib --bins` (190/190, including the new test), all four
fuzzers at release, and the release demo.

A distinct, deeper issue surfaced while investigating this one and is
**not** fixed here: even after this fix declines the false universal
proof, `jit.rs`'s `compile_verify_and_apply` still gates whether a
compiled form is *cached and trusted* purely on `verify()` -- a fixed,
finite sample battery -- with `kernel_verify` running only afterward and
purely informationally (it never un-installs an already-cached form).
A term whose compiled behavior only diverges from the interpreter at an
adversarially-chosen input outside that sample set can still reach a
caller silently wrong, with or without a kernel proof ever being
attempted. This is a structurally separate concern from the arity-typing
bug above (it's about `verify()`'s completeness, not about any specific
postulate's type) and needs its own scope discussion before further work
proceeds into it.

## 28. `is_kernel_verified` reported per-sample certificates as if they covered every input -- found and fixed

Following §27's own parting note, the first concrete piece of that
deeper issue turned out to be separable and small. `jit.rs`'s
`kernel_verify` returned a plain `bool`, but its five strategies fall
into two epistemically different classes:

- `prove_pure_expr`, `prove_closure_expr`, `prove_tail_recursive_universal`
  produce **one theorem covering every input**.
- `prove_tail_recursive_call` and `prove_closure_expr_instance` produce a
  certificate **per concrete call**, run once for each vector in
  `sample_arg_vectors` -- precisely the finite battery `verify()` already
  checked against the interpreter.

Collapsing both into `true` meant `is_kernel_verified` -- and the REPL
line printed after every evaluation -- claimed "kernel-checked
equivalence proof" for a call whose arguments no proof had ever seen.
The test suite contained a live instance of exactly that: a term in the
inconsistent-arity curried-dispatch family served compiled at `100` and
`-7`, neither of which is in `SAMPLE_ARGS` (`[0, 1, 2, 3, 5, -1, -3, 7,
20]`), with `assert!(jit.is_kernel_verified(top))` passing on the
strength of certificates at nine *other* points.

Fixed by replacing the bool with a three-way `ProofStrength`
(`Universal` / `Samples` / `None`), returned by `kernel_verify`, stored
on `CacheEntry::Compiled`, and exposed as `JitEngine::proof_strength`.
`is_kernel_verified` now means `Universal` specifically; the REPL prints
"only at the sampled inputs" for the weaker class rather than a flat
"true".

One subtlety worth recording: at arity 0 the sample battery *is* the
entire input space -- `sample_arg_vectors(0)` is a single empty vector
because there is exactly one possible call -- so a per-call certificate
there really does cover every input, and `kernel_verify` classifies it
`Universal`. Without that, the arity-0 members of the same
curried-dispatch family would have been under-reported, which is the
mirror-image error of the one being fixed. Three of the five tests that
initially failed the stricter classification were arity-0 and passed
again unchanged once this was added; the two that remained are the
genuine arity-1 cases described above, now asserting
`ProofStrength::Samples` explicitly with a comment naming why.

Nothing in `Stats` changed: `kernel_proofs_checked` still counts any
kernel proof regardless of strength, which is what it always meant.

Verify-teeth: temporarily made the per-sample classification return
`Universal` at every arity (collapsing the distinction back) and
confirmed the two arity-1 tests fail, then restored it and confirmed they
pass. Full validation green afterward: `cargo build --all-targets`,
`cargo clippy --all-targets`, `cargo test --lib --bins` (190/190), all
four fuzzers at release, and the release demo (all nine demo terms are in
the universal fragment, so every one still reports `true`).

### Terminology: these are not "translation validation"

Fixed alongside the above, since it was the same overstatement in prose
rather than in code. `proof.rs`'s module docs, `jit.rs`'s, `benches/
proofs.rs`'s and three places in `README.md` all described
`prove_tail_recursive_call` as *translation validation*. In the
literature that term means validating one **compilation**: the checker
runs once per compiled program, and when it succeeds the compiled
program is correct *for every input* (Pnueli et al.; Necula; Tristan &
Leroy's verified validators, POPL'08, whose register-allocation
descendant ships in mainline CompCert). What `prove_tail_recursive_call`
validates is one **execution** -- a single concrete `(term, args)` trace
-- which is a result-checking / certifying-computation regime instead.

The worst instance was README's "translation validation is inherently
per-call", which is false about the technique and made tatic's own
limitation look intrinsic rather than self-imposed. All six sites now
say "per-execution" and name the distinction; no function was renamed
(the blast radius isn't worth it, and the docs now carry the correction
at every entry point).

The practical consequence, and the reason this is worth more than a
wording nit: *per-compilation validation is a rung tatic does not
currently occupy at all*, and it sits exactly between "sample and hope"
and option 2's kernel work.

### Prior art worth knowing before either option is started

- **DDEC** (Sharma, Schkufza, Churchill, Aiken, OOPSLA'13) infers a
  simulation relation *from test-run data*, then discharges it with a
  solver -- sound because insufficient data makes the proof fail, never
  pass. That is tatic's two ingredients wired the other way round:
  sampling as heuristic, proof as gate. Adopting the structure does not
  require adopting the solver (which would trade a small kernel for an
  SMT TCB), but the discharge step still needs the kernel to be able to
  *state* the relation -- which is where §14's `Sigma` returns for the
  closure family specifically, and only for it.
- **TurboTV** (Heo et al., ICSE'24) is per-compilation translation
  validation for V8's TurboFan, via an SMT encoding of its IR with a
  staged decomposition. Evidence that per-compilation TV is tractable for
  a real JIT -- and it validates IR-to-IR, with the gap between its model
  and the real engine stated as a limitation, exactly as here.
- **CompCert's actual bug history** is the strongest argument about where
  to spend next. ~90% of its algorithms are proved; the unverified
  remainder is elaboration, pre-simplification, assembling and linking.
  Csmith (Yang et al., PLDI'11) found no middle-end wrong-code bugs in
  CompCert at all -- the wrong-code bugs it did find were in the code
  that expands and prints assembly instructions, attributed to operand-
  ordering tedium and absent printer unit tests. The analogue here is
  exact: `denote` vs `compile_node` is the modeling gap and WAT emission
  is the printer, and no kernel proof tatic can build reaches either.

  A first pass here proposed "extend `compile_fuzz` to differentially
  test `denote` against `compile_node`" as the cheap answer. It isn't
  available as stated, and the reason is worth recording so nobody
  re-proposes it: `compile_node` writes WAT into a `&mut String` while
  `denote` builds a kernel `Expr`, so there is no common form to diff;
  and `denote`'s output cannot be *evaluated* into one either, because
  `Int` and its operators are postulated rather than computing -- that
  is precisely why the proofs are `refl` on structure. The two
  derivations are hand-written twins that can only be compared by
  reading them. The tractable version is therefore structural
  unification, not testing: factor one traversal with two backends, so
  drift between them is impossible by construction rather than
  detectable after the fact.
- **Verified-JIT calibration**: Myreen (POPL'10) verified a JIT to x86 in
  HOL4 including an instruction-cache model and self-modifying code;
  Barriere, Blazy, Fluckiger, Pichardie & Vitek (POPL'21) verified
  speculation and deoptimization in CoreJIT over a CompCert-RTL-like IR.
  Both verify a compiler *model*, with extraction closing model ->
  implementation. tatic has no extraction story -- `compile.rs` emits WAT
  by hand -- so that last step would be new work, not a port.
- **If the target semantics is ever wanted for real**: WasmCert-Coq and
  WasmCert-Isabelle (Watt et al., FM'21) mechanise Wasm 1.0/2.0 with
  verified executable interpreters, and found genuine spec bugs doing it.

**Still open.** This is an honesty fix, not a soundness fix. Execution is
unchanged: `compile_verify_and_apply` still installs and serves a
compiled form on `verify()`'s finite battery alone, whatever
`proof_strength` says. Closing that needs one of these decisions, none
taken here:

1. **Gate on `Universal`.** Serve compiled code only for terms carrying a
   theorem covering every input; interpret everything else. Small diff,
   sound, but it withdraws the JIT from the entire `Samples` family --
   the inconsistent-arity curried-dispatch shapes `compile.rs` went to
   real trouble to support.
2. **Widen the universal fragment** to cover those shapes, so the
   `Samples` fallbacks stop being load-bearing. This was first written up
   as splitting into a cheap tail-recursive half and an expensive closure
   half; a measurement says otherwise. Instrumenting both per-sample
   returns in `kernel_verify` across the full lib suite: the
   `prove_tail_recursive_call` branch (step 4) fires **zero** times, and
   the `prove_closure_expr_instance` branch (step 5) fires **six** --
   `prove_tail_recursive_universal` already covers every tail-recursive
   shape the corpus contains. So there is no demonstrated cheap half:
   every `Samples` result comes from the closure / inconsistent-arity
   family, which is exactly the `Sigma` / dependent-sum discussion in §14
   and the arity-polymorphism findings in §9.

   That measurement leaves a separate question open: is step 4
   *unreachable* (the universal proof subsumes it, making it dead weight
   in the cascade) or merely *untested* (a corpus gap)? One experiment
   settles it -- build a tail-recursive term whose body is not a
   `DecisionTree` (an `If` on a non-comparison condition), and check
   whether `prove_tail_recursive_universal` declines it while
   `prove_tail_recursive_call` accepts it. If it does, that's a coverage
   hole to fill with a test; if nothing can reach step 4, delete it.
3. **Build a per-compilation validator** -- the rung the prior-art
   section above shows tatic doesn't occupy. Sampling infers the
   candidate relation, the kernel proof decides installation (DDEC's
   structure). This converts `verify()` from load-bearing to advisory
   without needing the universal fragment widened first, and is the
   option the literature supports best.

The `ProofStrength` split is a prerequisite for all three: option 1 is
now a one-line predicate change at the `CacheEntry::Compiled` insertion
site, and options 2 and 3 have a precise success criterion (the
`Samples` variant stops being reachable for the shapes in question).

None of the three touches the `denote`-vs-`compile_node` modeling gap or
WAT emission, which -- per CompCert's own bug history above -- is where
the empirically dangerous class lives. The cheapest genuinely
risk-reducing work available is orthogonal to all of them: extend
`compile_fuzz` to differentially check the two derivations structurally,
not just their outputs.

## Sources

- [Partial application (Wikipedia)](https://en.wikipedia.org/wiki/Partial_application)
- [The Spineless Tagless G-Machine](https://www.arbertrary.dev/stgm-presentation/stgm-deck.html)
- [C&C — The Guts of a Spineless Machine](https://jozefg.bitbucket.io/posts/2014-10-28-stg.html)
- [Lean 4 `lean.h` (closure object layout)](https://github.com/leanprover/lean4/blob/master/src/include/lean/lean.h)
- [Lean 4 reference — Boxing](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Boxing/)
- [Lean.Compiler.LCNF.Closure](https://lean-lang.org/doc/api/Lean/Compiler/LCNF/Closure.html)
- [Idris 2: Quantitative Type Theory in Practice (Brady, ECOOP 2021)](https://arxiv.org/abs/2104.00480)
- [guarded recursion — nLab](https://ncatlab.org/nlab/show/guarded+recursion)
- [A Generalized Modality for Recursion](https://arxiv.org/abs/1805.11021)
- [Unifying cubical and multimodal type theory](https://arxiv.org/pdf/2203.13000)
- [Higher inductive types in cubical computational type theory](https://dl.acm.org/doi/10.1145/3290314)
- [Recent Work in Homotopy Type Theory: Modal, Algebraic, Synthetic, and Cubical](https://ncatlab.org/homotopytypetheory/files/awodeyMURI18.pdf)
