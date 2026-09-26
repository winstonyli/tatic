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

*Since §30:* the installation gate declined this benchmark at 20,000
iterations, so the pair now runs at 150, side by side in one group
(~1.37× on the whole warm call, ~1.55× on the loop once fixed per-call
overhead is removed). See §30.

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

*Superseded: the reshifts this cache recovered came from eager
substitution. §53 fixed that, and §54 removed the cache.*

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

  *Corrected by §33:* that overclaims. There is no single `denote` to
  pair with `compile_node` -- five denoters implement different proof
  methods -- and drift comes in two kinds. Which *case* a term falls
  into can be shared, and now is (`compile::classify`). What each case
  *means* -- Wasm instructions on one side, kernel terms on the other --
  is two meanings by nature; no refactor makes that drift impossible,
  and only something that reads the emitted WAT (a per-compilation
  validator) reaches it.
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

**Still open at the time this was written.** The section above is an
honesty fix, not a soundness fix: execution was unchanged, and
`compile_verify_and_apply` still installed and served a compiled form on
`verify()`'s finite battery alone whatever `proof_strength` said. Option
1 below has since been taken -- see §29. Options 2 and 3 remain open, and
the closing paragraph about the modeling gap still stands in full.

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

   That measurement left a separate question open -- is step 4
   *unreachable* or merely *untested*? -- and it has since been settled:
   **unreachable through the JIT**, for a specific and slightly
   surprising reason.

   Step 4 is genuinely more permissive than step 3 in exactly one place,
   the `If` condition. `classify_tree` requires a direct comparison
   (`Lt`/`Le`/`Eq`); `classify_step` imposes nothing, since it just
   evaluates whatever is there against the concrete arguments. But
   `compile::compile_cond` imposes *precisely* `classify_tree`'s
   restriction -- its `cmp_instr(op)?` fails for anything else -- so a
   term living in that gap never compiles, and `kernel_verify` never runs
   on it. Step 4's extra reach lies entirely outside the compilable
   fragment. Every other way `build_universal` can decline where step 4
   might not is closure-related (`infer_closure_arities`, `flatten_tree`'s
   leaf coverage, the `denote_closure_typed` stages), and step 4's own
   `denote` is arithmetic-only, so it declines those too.

   Pinned by `proof::tests::
   the_relational_steps_extra_reach_lies_entirely_outside_the_compilable_fragment`,
   which builds `rec f n = if (n - 1) then f(n - 1) else 42` -- tail
   recursive, terminating, non-comparison condition -- and asserts all
   three halves at once: `prove_tail_recursive_call` accepts it,
   `prove_tail_recursive_universal` declines it, and `try_compile`
   declines it. The two restrictions are load-bearing *as a pair*, and
   the test fails the moment either is relaxed without the other.

   Verify-teeth for that test also surfaced something worth noting on its
   own: relaxing `classify_tree` alone (adding `Sub` to the accepted
   condition ops) makes `prove_tail_recursive_universal` happily build a
   proof -- even though the `Ev` gating argument depends on a condition
   denoting only to `0` or `1`, which a `Sub` does not. So
   `classify_tree`'s comparison check is a soundness guard, not just a
   scope line, and nothing else was pinning it.

   Step 4 was **not** deleted. It costs nothing while unreached (tried
   only after step 3 declines), removing it would silently downgrade any
   future shape that does reach it from `Samples` to `None`, and the test
   above now announces the moment the situation changes. Deleting it is
   the right call only once the pair of restrictions is deliberately
   decoupled.
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

## 29. The installation gate now requires a universal theorem -- option 1 from §28, taken

`compile_verify_and_apply` installed a compiled form on `verify()` alone.
`ProofStrength` (§28) made the weakness reportable; this makes it
actionable. Installation now requires **both** halves:

```rust
if proof != ProofStrength::Universal {
    self.cache.insert(h, CacheEntry::NoUniversalProof(proof));
    self.stats.declined_no_universal_proof += 1;
    self.stats.interpreted += 1;
    return eval::apply_term(terms, h, args);
}
```

The new `CacheEntry::NoUniversalProof(ProofStrength)` carries the
strength purely so `proof_strength` can still report what evidence did
exist; nothing reads it to make a decision. A declined term is served by
the interpreter from then on, exactly like `NotCompilable`, and shows up
in the new `Stats::declined_no_universal_proof`.

**Why both halves, and why neither is redundant.** The sample battery is
the only check in the system that touches the WAT wasmtime actually
runs. The kernel theorem is the only one that says anything about inputs
outside the battery -- but it is stated over `proof.rs`'s `denote`,
which models `compile_node` rather than reading its output (`proof.rs`
contains zero references to `wat`, `wasm` or `CompiledFragment`). So the
pair is strictly stronger than either alone, and still short of
end-to-end soundness. *(Later: the pair also said nothing about types, so
ill-typed code that goes wrong only off the samples got installed. §38
adds a third check.)* Anyone tempted to drop `verify()` now that a proof
is required should re-read that sentence: the proof does not cover
emitted code, and CompCert's own bug history (§28's prior-art notes) says
the printer is where wrong-code bugs actually live.

**The price.** This withdraws the JIT from the inconsistent-arity
curried-dispatch family -- the capability `compile.rs` went to real
trouble to support. Against this repo's corpus that costs nothing today:
the release demo still compiles all nine terms with
`declined_no_universal_proof: 0`, and exactly two tests changed behavior
(the arity-1 members of the `Samples` family measured in §28; the
arity-0 members classify `Universal` and still install). It is
nonetheless a capability regression, and the way to undo it is option 2
-- widen the universal fragment -- not relaxing the gate.

*(An earlier draft of this paragraph also claimed "every benchmark is
unaffected". That was asserted rather than measured. Running them
afterwards confirmed the gate changes no benchmark's behavior -- every
`jit_warm_cache_hit` bar still beats its `interpreter` bar by the same
orders of magnitude -- but also turned up a pre-existing crash in
`benches/execution.rs` that has nothing to do with the gate. See §30.)*

**A consequence worth flagging rather than fixing.** With the gate in
place, `kernel_verify`'s steps 4 and 5 can no longer change any
installation decision; they run purely to populate `proof_strength`.
`prove_closure_expr_instance` is expensive (it walks a full concrete
execution trace, exponential in trace size for the branching case,
bounded only by `DynBudget`), so a declined term now pays a real cost for
a diagnostic string. Left as-is deliberately -- it is once per term, and
the reporting is what makes the decline legible -- but skipping steps
4-5 unless someone asks for the diagnostic is an obvious cheap win if
that cost ever shows up in a profile.

Two tests renamed to match what they now assert
(`..._is_kernel_verified` -> `..._is_declined_for_want_of_a_universal_
proof`) and extended to pin `declined_no_universal_proof == 1`,
`compiled == 0`, `interpreted == 2`. Verify-teeth: relaxed the gate to
`if proof == ProofStrength::None` (letting `Samples` install again) and
confirmed exactly those two tests fail, then restored it. Full
validation green: `cargo build --all-targets`, `cargo test --lib --bins`
(191/191), all four fuzzers at release, and the release demo.

Note on `cargo clippy --all-targets`: on a 1.100-era nightly it now
reports four warnings from `cranelift-entity`'s `entity_impl!` macro
expanding the deprecated `std::u32::MAX` path at `term.rs:18`. Not
tatic's code, and deliberately not suppressed with an `#[allow]` that
would mask a future real deprecation in that file -- but "clippy clean"
is no longer a valid pass criterion on that toolchain. (Later fixed at
the root: `TermStore` was the crate's only user, and it needed no more
than a `Vec` and a hash-to-index map, so the dependency is gone and
clippy is clean again. Newer `cranelift-entity` releases, up to 0.135,
still expand the deprecated path.)

## 30. `cargo bench --bench execution` died of a stack overflow -- found and fixed

Found while checking (belatedly) whether §29's installation gate changed
any benchmark. It didn't. But the benchmark suite did not complete:

```
Benchmarking inconsistent_arity_loop_carried_parameter_loop/jit_cold_compile_and_verify
thread 'main' has overflowed its stack
error: bench failed  (exit code 0xc00000fd, STATUS_STACK_OVERFLOW)
```

**Pre-existing, not caused by the gate.** Confirmed by checking out
`src/jit.rs` from the commit before §29's change and re-running: it
overflows identically.

**Why nothing caught it.** Benchmarks were not in the standing validation
routine. `--all-targets` *builds* them, which is presumably why this
looked covered. Building a target proves nothing about running it. The
routine is now written down in `README.md`'s own "Validation" section,
with `cargo bench` in it.

### Isolation

A throwaway harness ran each stage of a cold compile separately on the
same term, at varying loop counts and thread stack sizes:

- `eval::apply_term` -- fine at 20,000 iterations. Not the interpreter.
- `compile::try_compile` -- fine. Not the compiler.
- `proof::prove_closure_expr_instance` -- overflows.
- The same call on a 1 GB thread **returns `None`**, correctly, at
  n=20,000 (its budget is exhausted). So the logic was right all along;
  it simply needed more stack than it had to reach the decline.
- Instrumenting the expression handed to `kernel::check`: depth 101 at
  n=50, 201 at n=100, 401 at n=200. Depth grows at ~2 levels per trace
  step, exactly as the per-*execution* proof design implies.
- `prove_tail_recursive_call` -- the purely arithmetic sibling, no
  closures anywhere -- overflows too, at an even lower loop count. So
  this was never closure-specific; it is a property of both per-execution
  strategies.

### Two distinct overflow sites

1. **`kernel::check`.** `infer`, `whnf`, `def_eq` and `nf` are mutually
   recursive over `Expr` structure. Release build: depth ~400 survives,
   ~500 takes the process down. Debug is far worse -- a `refl` tower
   overflows a debug main thread somewhere between depth 50 and 100.
2. **Recursive `Drop`.** When the step budget runs out, the accumulated
   `Rc<Expr>` chain is discarded unproved, and dropping it recurses one
   frame per level. Measured: depth ~8,000 survives, ~12,000 does not.
   This is the one that actually killed the benchmark -- with
   `tail_steps: 10_000` a 20,000-iteration loop built a ~20,000-level
   expression, never reached `check` at all, and died on the way out.
   (`Clone` is unaffected: `#[derive(Clone)]` over `Rc` fields is
   shallow.)

### Fix

Both step budgets drop from 10,000 to **200** --
`prove_tail_recursive_call`'s `MAX_STEPS` and `DynBudget::tail_steps` --
sized to sit between the two ceilings rather than at whatever number
looked generous. Above them, nothing past ~100 steps could ever produce
an acceptable proof anyway; below them, 200 steps cannot build anything
within two orders of magnitude of the drop cliff.

Second, `kernel::depth_within` (iterative, explicit stack, early-exit)
plus `kernel::MAX_CHECK_DEPTH = 128`, checked once in `proof::finish` --
the single point where every strategy that can build an unbounded
expression hands it to the kernel. Over-deep means `None`, the same
graceful failure an exhausted budget already produces.

**Why the guard is not inside `kernel::check`, where it belongs.** That
was tried first, and measured: a 50-160% slowdown across every single
proof benchmark. The lib test suite makes **184,785** `check` calls, and
`depth_within` must visit every node to answer "no". `check` is too hot
to afford it. `typecheck` -- cold, and the other public entry that
accepts or rejects a term -- is guarded.

**The constant, measured rather than guessed.** Instrumenting all 184,785
`check` calls, the deepest expression any real proof passes is **64**
levels (57 on the `expected` side). 128 is double the observed maximum
and far below the release cliff.

**Known gap, recorded rather than papered over.** `kernel::check` stays
unguarded, and a debug build overflows at depths inside
`MAX_CHECK_DEPTH`. Lowering the constant to fit debug would start
rejecting proofs the project actually builds; the real fix is making the
kernel's traversals iterative, which is its own project. What stops the
crash today is the step budgets -- the guard is a backstop for anything
that gets past them.

*Since closed by §31*, with `stacker` rather than a hand conversion, and
the guard removed.

### A benchmark consequence worth stating

`inconsistent_arity_loop_carried_parameter_loop` runs 20,000 iterations,
so its trace now exhausts the 200-step budget, `prove_closure_expr_
instance` declines, and §29's gate therefore refuses to install it. Its
`jit_warm_cache_hit` bar now measures the interpreter (~18 ms against the
interpreter's ~23 ms), not curried dispatch. That bar was the whole point
of the group -- its own docs say so -- so the benchmark needs either a
loop short enough to stay provable or an explicit note that it is
measuring the declined path. Not done here.

This also corrects §29 a second time. The gate *did* change this
benchmark: before, the term compiled and was served fast; now it is
interpreted. That was invisible earlier only because the benchmark
crashed before reaching the point where you could see it.

**Since resolved.** Two changes to `benches/execution.rs`:

- *The pair now runs at 150 iterations, side by side in one group.* The
  inconsistent term's only proof is `prove_closure_expr_instance`'s
  trace, one step per iteration against the 200-step budget. Measured
  ceiling: 199 iterations install, 200 are declined -- the budget binds,
  not `MAX_CHECK_DEPTH`. Shortening only the inconsistent term would
  have broken the comparison, and the companion group's 20,000 feeds its
  own README comparison with `capturing_closure_loop`. So both builders
  now take an iteration count, and the inconsistent group benches a
  `consistent_baseline_jit_warm_cache_hit` bar at the same 150. I
  initially wrote that no provable length would work, because fixed
  per-call overhead would dominate. Measurement says otherwise. A
  1-iteration loop costs ~220 ns warm, so at 150 the loop is most of the
  call. Result: **~1.01 µs curried vs ~0.73 µs baseline (~1.37×)**.
  Subtract the fixed overhead and the loop itself is ~1.55× slower,
  consistent with the ~1.56× §9 recorded at 20,000 before the gate.
  Criterion's spread on the baseline was wide this run (523-898 ns), so
  the ratio is approximate.
- *Every warm bar now asserts the path it measures.* A shared `warm`
  helper replaces each group's warm-up call and fails the run unless
  `stats.compiled` matches the group's stated expectation (all seven
  expect compiled). The class of bug here was a bar that silently
  changed meaning; now a change to the gate or a budget that uninstalls
  any benchmarked term stops `cargo bench` instead. Verify-teeth:
  expecting compiled at 20,000 iterations, and running the pair at
  200, both panic in `warm` naming the declined stats.

### Tests and verification

- `proof::tests::a_long_running_trace_declines_instead_of_overflowing_the_stack`
  -- a 20,000-step arithmetic loop must return `None`, and a 10-step one
  must still prove. Verify-teeth: restoring `MAX_STEPS` to 10,000 makes
  it overflow the test process exactly as described.
- `kernel::tests::an_over_deep_expression_is_measurable_and_refused_by_typecheck`
  -- `depth_within` measures, `typecheck` refuses, and a shallow term of
  the same shape still typechecks. It deliberately never calls `check` on
  the deep term, since `check` is unguarded and doing so *is* the crash.
  Verify-teeth: raising `MAX_CHECK_DEPTH` to 10,000,000 makes the test
  overflow.

Full validation green afterwards: build, 193/193 lib tests, all four
fuzzers at release, `cargo bench` (both suites, to completion), and the
release demo. The proof benchmarks are back within noise of their
pre-guard numbers.

## 31. The kernel's recursion is stack-safe -- `stacker`, not a hand conversion

§30 left one gap open: `kernel::check` had no guard, and its traversals
recurse over `Expr` (and `whnf`/`nf` once per reduction step too), so a
deep enough term took the process down instead of returning a verdict.

**Measured first, and narrower than §30 said.** Survivable depth of two
shapes (a `refl` tower, and `(\x:Type0. x)` applied n-fold), bisected per
build and thread size:

| build | 1 MB (Windows main thread) | 2 MB (test threads) |
|---|---|---|
| debug | ~90-100 | ~185-205 |
| release | ~450-570 | ~900-1,120 |

So "a debug build overflows inside `MAX_CHECK_DEPTH` (128)" was only true
on a 1 MB thread -- `cargo run` and the REPL in debug, not the test
suite.

**The choice.** Hand-converting every traversal into an explicit worklist
would turn `infer`/`check` into a defunctionalized continuation machine
of about 20 states: hundreds of new lines inside the trusted kernel, no
longer reading like the typing rules they implement, where a de Bruijn
off-by-one is a soundness bug rather than a crash. `stacker` instead
spills onto a heap-allocated stack segment when the current one runs
low. It is what rustc does (`ensure_sufficient_stack`, whose constants
this copies: 100 KB red zone, 1 MB segments). The cost is `unsafe`
platform assembly in `psm` added to what must be trusted not to crash --
though not to what must be trusted for soundness. Chosen: `stacker`.

**What had to be covered.** Every recursive function body in
`kernel.rs` (`infer`, `check`, `whnf_impl`, `nf_impl`, `shift`, `subst`,
`is_var_free`) runs through `kernel::grow`, and so do `PartialEq` (now
written out rather than derived, since `def_eq` compares two full normal
forms with it) and `Debug` (error messages print whole terms). The
surprise was `Drop`. With every traversal wrapped, a 1,000-deep check
still crashed, because the compiler-generated drop glue is recursive and
`whnf` discards a full intermediate term at every beta step -- on
whatever segment is current, with only the red zone guaranteed. `Drop
for Expr` now checks the stack at each level, and only when it runs low
moves the children it would free onto a fresh segment. Implementing
`Drop` forbids moving fields out of an `Expr` by value (E0509), which
touched ~20 match sites; they now bind by reference and clone the `Rc`.

**The cost, and a fix to it.** The first version used
`stacker::maybe_grow` directly and made every proof benchmark 80-100%
slower. One `stacker::remaining_stack` call measured **8.9 ns** on
Windows -- a lazily-initialized thread-local plus a non-inlined assembly
call -- against ~1 ns for reading a local's address, and the kernel
checks at every `shift`/`==`/`Drop` node. So `grow` now compares a
local's address against a const thread-local floor (`FLOOR`) and calls
stacker only when genuinely low, or to learn the floor once per thread.
The floor tracks whichever segment is current, restored by a guard on
the way out, so unwinding restores it too. The first draft of that got
the "unknown" sentinel wrong (`0`, which every check *passes*, so
nothing was ever protected); it is `usize::MAX`, which every check
fails.

This machine was at 100% CPU from unrelated work throughout, so
one-shot criterion comparisons swung ±25% run to run, and the same
binary ranged 12.9-44 ms on `gcd_2_leaves` across rounds. The numbers
that count are from an interleaved A/B -- the pre-change commit built in
a separate worktree, both binaries alternated, minimum and median over
ten rounds: **+4-7%** on the two slowest-affected benches
(`gcd_2_leaves`, `relational_x10`), and within about ±5% on the other
four sampled. Against the 50-160% the depth guard cost inside `check`
(§30), that is the price of safety at every depth.

**What it removed.** `MAX_CHECK_DEPTH`, `depth_within`, and their guards
in `typecheck` and `proof::finish`: their only stated purpose was
surviving the native stack. `DynBudget::tail_steps` and `MAX_STEPS` stay
at 200, but both ceilings they were sized against are gone -- they are
now cost bounds that nobody has re-measured.

**Corrections to §30's record, found while doing this.** `DynBudget`'s
docs gave `MAX_CHECK_DEPTH` as 200 (it was 128), and said a trace past
roughly a hundred steps "cannot produce a provable result". The
inconsistent-arity benchmark measured otherwise just before this: 199
steps install.

### Tests and verification

- `kernel::tests::check_survives_a_term_far_deeper_than_the_native_stack_allows`
  replaces the old guard test. It runs `check` on 1,000-deep terms of
  both shapes on a 1 MB thread in a debug build, through beta reduction,
  a two-tree `==` and a `Debug`-formatted error. Written first, and it
  overflowed. Verify-teeth: making `Drop`'s check always pass crashes it
  with an access violation (an overflow on a stacker segment), and making
  every check pass overflows the native stack.
- Outside the suite: depth 20,000 checks and drops cleanly on a 1 MB
  thread in release, and 5,000 in debug.

Full validation green: build, 193/193 lib tests, clippy (only the four
upstream `entity_impl!` warnings), all four fuzzers at release, and the
release demo (`compiled: 9, declined_no_universal_proof: 0`).

### Open

- **Re-measure the step budgets as cost bounds.** Raising `tail_steps`
  could bring `inconsistent_arity_loop_carried_parameter_loop` back to
  20,000 iterations. Its per-step cost grows with the expression, so
  measure before choosing.
- **`eval_dyn` is still native-recursive.** `DynBudget::recursion_depth`
  (50) and `inline_call_depth` (25) were tuned against a debug thread's
  stack, and the `#[inline(never)]` extractions throughout `kernel.rs`
  exist to shrink frames for that budget. Routing `eval_dyn` through the
  same `grow` would make both limits purely cost bounds, and the
  extractions removable.
  *Since done:* §32.

## 32. `eval_dyn` through the same `grow`; three budgets become one

§31's second open item. `eval_dyn`'s per-instance proof search recurses
through the native stack in two ways: an embedded (non-tail) self-call
re-enters `eval_dyn_tail_recursive`, and a closure call can be inlined
into another combinator's body (`eval_dyn_direct_call` →
`eval_dyn_inline_call`). Each path had its own depth counter,
`recursion_depth` (50) and `inline_call_depth` (25), tuned against a
debug test thread's stack. The second was measured to overflow at the
43rd-45th level, so it got a smaller bound than the first.

**The change.** Every cycle in that mutual recursion passes back through
`eval_dyn`, so one `kernel::grow` there bounds the whole family's depth
by heap (`grow` is now `pub(crate)`). What was left of the two counters
was a *termination* bound, not a stack one, and it turned out not to
need separate counters. A self-application reached only through a
captured closure (a plain `\g n. .. g(g, n-1)`, not `Rec`-wrapped)
consumes no step of the tail loop, so without `inline_call_depth` it
would never stop. So `DynBudget` is now one `steps` counter (200, the
old `tail_steps`), charged once per descent into a body:
- each iteration of the tail loop, which an embedded self-call also
  enters, so `recursion_depth` was redundant;
- plus `eval_dyn_inline_call` inlining a non-`Rec` body, the one
  descent the loop never sees.

**Behaviour change.** Per-instance proofs can now follow up to ~200
levels of embedded or inlined recursion instead of 50 / 25. Both
existing depth tests now also require n=100 to prove, past both old
bounds and the measured debug crash at ~45. That extension was written
first and failed, declined by the old bounds. Verify-teeth: with the
`grow` removed, the tests overflow the stack. The `n = 1,000,000` halves
of both tests still decline cleanly, now on `steps`.

**The frame-size extractions are kept.** The `#[inline(never)]` helpers
in `kernel.rs` (`infer_sigma`/`infer_pair`/`infer_sigrec`/`infer_sup`,
the `*_sigma_family` arms, `whnf_sigrec`) and `eval_dyn_inline_call`
existed to fit that debug-thread budget. Nothing depends on them now --
frame size only decides how soon a deep walk moves to a new segment --
but they cost nothing, and removing them is a codegen change I could not
measure reliably on a machine running at 100% CPU from unrelated work.
Their docs no longer claim a stack budget that no longer exists
(`infer_sigma` carries the one full explanation).

## 33. One classifier for the compiler and every proof walker

§28 proposed unifying `denote` and `compile_node` as "one traversal
with two backends". Reading the code showed that shape doesn't exist.
There are five denoters -- `denote`, `denote_with_placeholders`,
`denote_closure_typed`, `denote_closure`, and the `eval_dyn` family --
and they are different proof methods (symbolic, induction with
placeholders, per-execution trace), each covering a different slice of
what `compile_node` accepts. They are not one walk that could share a
backend. What they, `compile_node`, and the scope-gating walkers
(`collect_literals*`, `find_self_calls`, `return_type_of`,
`prime_closure_postulates`, `classify_step`, `scan_for_closure_calls`,
...) do share is a case analysis. Each did it by hand, some from
`compile.rs`'s `match_self_call`/`unwind_app_spine`, some through
`proof.rs`'s own `classify_app_node`.

**The change.** `compile::classify` returns a `Shape` -- `If`,
`SelfCall`, `VarCall`, `CombinatorCall` (a literal callee that peels to
`arity > 0`), `OtherCall`, `Var`, `Lit`, `Prim`, `Combinator { is_rec }`
-- and all 16 of those functions now dispatch on it. `compile_node` and
every denoter start with the same `match`. `classify_app_node` became
`app_shape`, which only *refines* an application-shaped `Shape` with the
closures fragment's parameter types. The rules it fixes in one place:
- a saturated self-call is recognised before any other application,
  and only when saturated -- under- or over-applied, it is a `VarCall`;
- a callee counts as a combinator only if it peels to a function;
- `If` conditions: `compile::is_comparison` is defined by `cmp_instr`
  itself, and `classify_tree`'s soundness check (a condition must only
  ever denote `0` or `1`, §28) now uses it instead of a hand-copied
  `Lt | Le | Eq`.

Each consumer still decides which shapes it supports and what they
mean. Behaviour-preserving with one deliberate exception:
`scan_for_closure_calls` used to accept any `Abs`/`Rec` callee and rely
on `register` rejecting a non-function `Rec` at codegen. It now declines
at the scan. Both paths end in the same decline.

**Verify-teeth.** Making `classify` treat over-application as
`OtherCall` -- a one-line change in one function -- fails 16 tests
across `compile::tests` (1), `jit::tests` (2) and `proof::tests` (13).
Both sides really do read the same classification. A new
`compile::tests::classify_recognizes_only_a_saturated_self_call_and_only_a_peelable_callee`
pins the two non-obvious rules above.

**What this does not do.** It makes *classification* drift impossible.
It does nothing about *meaning* drift: `compile_node`'s `i64.div_s` and
`proof.rs`'s postulated `op_ref(Div)` are still hand-kept twins, as is
every other per-case translation. §28's correction says why no refactor
reaches that.

## 34. An IR between term analysis and WAT

§33 made the *classification* shared; this separates the *meaning* from the
*representation*, the precondition for checking meaning per compilation.
`compile.rs` now builds a closure-converted, representation-neutral IR
(`ir.rs`): which function, which local, which environment slot, which kind of
call. `lower_wat.rs` turns it into WAT, one template per node. Closure packing,
the bump allocator, scratch locals, the wrapping-division sequence and the
curried stage chains all live in the templates. Design, alternatives and
research: `docs/superpowers/specs/2026-09-23-jit-ir-design.md`.

**Why this level.** The mid-level IR of every system surveyed (GHC STG,
CakeML BVL, CertiCoq-Wasm's λANF input, Lean IR, Flambda 2, Hoot's CPS after
closure conversion, MLton SSA) sits at this level or above it, and each makes
the layout concrete in exactly one pass downstream. The lowest levels (GHC
Cmm, Gibbon L4) are the least checked. An IR with explicit memory operations
would have made the step-2 decompiler a symbolic evaluator of memory traffic.
An annotated term would have left closure conversion, where past bugs were,
entirely trusted. Flat closures were kept rather than Lean-style lambda
lifting. Hash-exact decompilation needs to know which leading arguments are
captures either way, so lifting would not have made the decompiler simpler;
and keeping the representation let step 1 require byte-identical WAT.

**How it was checked.** For the whole transition, `try_compile` ran both
the old direct emitter and build → check → lower, and asserted identical
WAT, `needs_hp_reset` and `arity` on every call. That covered every unit
test, all four fuzzers in release, the demo and both bench suites. Golden
snapshots (`tests/golden/`) were then recorded, and the old path deleted.
Verify-teeth: swapping `If` branches in the builder, or skipping
`local_index`, made the gate panic across the suite (15 and 16 failing
`compile::tests`). After the deletion, a one-byte template change
(`i64.const 32` → `33` in `MakeClosure`'s packing) failed the golden test
for all 7 of the 20 terms that build a closure value, and 3 closure tests.
Five `rejects_*` terms in the same corpus pin rejections, recorded as
`REJECTED`.

**Field parity.** So that the step-2 decompile check cannot be vacuous,
every IR field is in one of three classes:
1. read by both the lowering and the decompiler (`Lit`, `Read`, ops, every
   `args`/`env`/`root_env`, `f`, `wrapper`, `Pap.root`, `callee`, `arity`);
2. read only by the decompiler and unable to change runtime meaning
   (`is_rec`; `SelfCall.tail`, whose two lowerings are both correct);
3. read only by the lowering, a representation choice that `ir::check`
   validates (`dispatch`, `env_len`, `Pap.supplied`).

`ir::check` is a complete precondition for lowering: besides ranges, arities
and environment lengths, it requires every lambda and every recursive
function to have `arity >= 1` and every `CallUnknown` to have arguments, so
nothing it admits makes `lower` panic, loop or disagree with the decompiler.
A check failure is a builder bug; release builds reject the term and count
it in `compile::ir_check_failures()`, which `compile_fuzz` asserts is 0.

**What changed besides the split.** The discovery pass is gone. The dispatch
mode is a field of the module, known before any WAT is written. Renames:
`compile_node` → `build_node` (term shape) plus `lower_wat` templates (emitted
code); `compile_var_read` → `build_read`; `emit_dynamic_apply` →
`Lowering::dynamic_apply`; `push_pap_env` → `Lowering::pap_env`. Cold-compile
timings (`jit_cold_compile_and_verify` medians, the step's base `deb8ec7` →
after, median of three interleaved runs of each build) are fib_30 227 → 227
ms, gcd 78.9 → 73.5 ms, capturing_closure_loop 67.8 → 65.6 ms,
partial_application_loop 67.2 → 64.6 ms,
closure_typed_loop_carried_parameter_loop 18.4 → 20.1 ms and
inconsistent_arity_loop_carried_parameter_loop 4.9 → 5.6 ms, all within
this machine's run-to-run spread of up to about 15% (three longer
interleaved reruns of the last two gave 16.7 → 15.9 ms and 4.0 → 4.1 ms),
so the change is not measurable either way.

**Not yet, at the time.** Nothing checked the IR against the source yet.
That was step 2 (a decompiler that rebuilds the term and compares content
hashes), then step 3 (a differential test for each template) -- both now
done; see §35.

## 35. Translation validation: every compilation is decompiled back

Step 2 and 3 of the IR design (§34; `docs/superpowers/specs/2026-09-23-jit-ir-design.md`).

**The gate.** `try_compile` now accepts a module only if
`decompile::decompile` rebuilds, from the IR alone, a term with the
source's content hash -- meaning it exactly, up to a `Dispatch::Fast`
arity trap (a `call_indirect` type mismatch), a runtime distinction the
term semantics doesn't model and which `jit.rs`'s sample verification
still catches on real inputs. Hashes are store-independent, so the rebuild
goes into a scratch store and never reads the source. The decompiler
shares nothing with the compiler but the IR and term types (enforced by a
test -- an allowlist on every `crate::` path, not just a denylist on
`compile`/`lower_wat`), so a bug in `classify`/`peel`/`local_index`/
`free_vars` cannot be mirrored by it and cancel out -- the pitfall the Œuf
and CompCert-validator work warns about. A mismatch is loud in debug and
counted (`compile::ir_validation_failures`) and rejected in release; the
whole suite and the release fuzzers run with zero failures, i.e. no false
alarms on anything the fragment compiles. `ir::check` also gained a rule
the decompiler needed: the combinator reference graph (`CallKnown.f`,
`MakeClosure.f`, `MakePap.wrapper` resolved through its `Pap.root`) must be
acyclic, because a cyclic one made `decompile` recurse forever instead of
being rejected cleanly.

**Not vacuous.** Mutation tests apply every single-point change -- swapped
arguments, environment slots or branches, shifted reads, changed
operators, retargeted combinators (both a call/closure site's own target
and, separately, a `Pap` wrapper's `root`) -- to every built corpus
module; every well-formed mutant (214 of them) fails validation. Flipping
a self-call's `tail` flag, which is meaning-preserving (field-parity class
2), passes. The two bugs injected directly into the decompiler while
building it (a wrong Wasm-local-to-de-Bruijn mapping, and a dropped
self-binder offset on recursive captures) were caught not by the mutation
test but by round-trip tests: the corpus and fixture checks, and for the
offset a dedicated recursive-capture test, since no corpus term exercises
that path; the mutation test's own evidence is its 214 rejections.
Injected builder bugs (swapped `If` branches, a reversed
environment-capture order, a mis-split over-application argument list) are
caught across the suite.

**What the decompiler cannot see -- and step 3.** It reads the IR, not the
WAT, so a wrong template is invisible to it. `ir_fuzz.rs` closes that gap
differentially: each template, and random well-typed IR under both
dispatch modes, runs through `lower`+wasmtime and through
`decompile`+`eval`, and must agree, a division by zero matching a trap.
The per-template tests cover closure arity 1 through 4 -- the spec's whole
range, including the top of `Dispatch::Curried`'s stage chain -- and the
random generator reaches the same ceiling. Injected template bugs (the
`MIN / -1` sequence, dynamic-apply operand order, PAP slot order) are
caught. A ceiling assert on the fraction of runs where both sides merely
agree by both erroring (measured 5.8% at 150 seeds, 9.8% at 5000 seeds;
asserted below 20%) guards against the fuzzer quietly degenerating into
mostly-trapping, mostly-uninformative runs. What remains trusted: the
templates on inputs no test reached, wasmtime, and -- since the random
generator builds only non-recursive IR (self-calls are covered separately
by the fixed per-template test) -- any interaction between the generator's
shapes and recursion.

**Cost.** Cold-compile medians (`jit_cold_compile_and_verify`, `ecd8c9d`
-- no gate -- vs this branch, median of five interleaved runs per build
after the machine proved noisy): fib_30 314 → 302 ms, gcd 165 → 127 ms,
capturing_closure_loop 86.6 → 102 ms, partial_application_loop 103 → 103
ms, closure_typed_loop_carried_parameter_loop 28.4 → 26.1 ms,
inconsistent_arity_loop_carried_parameter_loop 7.41 → 6.19 ms. This
machine was shared with unrelated heavy processes throughout measurement
(individual runs for the same build swung by up to 5x); three of the six
fixtures land within about 10% and the other three move in both
directions with no consistent regression, so
the decompile-and-compare pass adds no cost distinguishable from this
machine's run-to-run spread.

**Deviations from the spec.** The decompiler lives in its own file and
takes the target `TermStore` (so step 3 can evaluate what it builds); the
failure count is a process-wide counter like `ir_check_failures`, not a
`jit::Stats` field -- every caller of `try_compile`, not only the JIT, is
covered that way.

## 36. Lambda lifting of directly called combinators

Step 4 of the IR design (`docs/superpowers/specs/2026-09-23-jit-ir-design.md`).

**What was wrong.** §34 kept flat closures and noted lambda lifting as later
work, and a first reading of the builder suggested it had nothing left to
do: a lambda literal in function position already becomes a statically
known `CallKnown`. But the lowering still allocated that callee's
environment in linear memory on every call (`push_closure_env`), even
though nothing else could ever see it. `capturing_closure_loop` paid one
bump allocation per iteration for a closure that never escapes.

**The spike first.** Before designing, hand-written equivalents of the
three closure benches were timed against today's code (20,000 iterations,
warm JIT, best of 15 interleaved, machine shared): lifting the capturing
closure 3.1-3.4x; specialising `caller (add acc) n` to `add acc n`
7.0-7.6x; substituting the loop-invariant closure parameter `g` 1.2-1.6x.
Only the first leaves the term unchanged, so only it fits the hash-exact
gate of §35; the other two need a validator beyond hash equality and are
recorded as future work in the spec.

**What changed.** A capturing combinator that nothing reaches through the
table -- never packed by `MakeClosure`, never a partial application's root
(`lower_wat::direct_only`) -- takes its captures as leading `i64`
parameters. Its `Env(k)` reads are locals, a call pushes the captured
values, and a non-tail self-call forwards them. Everything reachable
through the table keeps the uniform `$env` convention, so no indirect call
pays anything. It is a lowering choice derived from the module (field
parity class 3): the IR, `ir::check`, the decompiler and the gate are
untouched. The rejected alternatives -- a dual entry for every capturing
combinator (each indirect call pays an extra Wasm call through a stub), or
a hybrid for combinators both called directly and escaping -- are in the
spec; the hybrid stays open.

**How it was checked.** Golden WAT changed for exactly the two direct-only
capturing terms (`capturing_closure_loop`, `a_capturing_closure_call`):
the allocator, `hp` and memory exports disappear. New differential cases in
`ir_fuzz.rs` cover two captures in order, tail and non-tail recursion that
forwards a capture, a direct call made from inside a direct-only one, and
an escaping closure built from one's capture, under both dispatch modes.
Verify-teeth, each caught: reading `$e0` for every slot, forwarding zeros
on a non-tail self-call, and pushing a call's captures in reverse. The
memory-bound test that relied on the capturing loop allocating now uses an
escaping closure.

**Cost.** Criterion `capturing_closure_loop/jit_warm_cache_hit`, `main` vs
this change, three interleaved rounds on a shared machine: best-of-three
medians 301.6 µs -> 94.6 µs (3.2x). The unchanged controls moved 7-14% in
the same runs (`partial_application_loop` 628.7 -> 541.7 µs,
`closure_typed_loop_carried_parameter_loop` 161.3 -> 149.4 µs), so the
3.2x is well above noise and matches the spike. `capturing_closure_loop`'s
bench now also goes through the JIT and measures §37's specialisation on
top of this step's lambda lifting; lambda lifting itself stays covered
separately by its own `try_compile`-level golden-WAT test, not by the
bench number alone.

## 37. Closure specialisation by certificate-checked βv

Design: `docs/superpowers/specs/2026-09-24-closure-specialisation-design.md`.

**What was slow.** §36's spike measured `partial_application_loop`'s
hand-specialised form (`caller (add acc) n` rewritten to `add acc n`) at
7.0-7.6x today's code. Nothing in the pipeline did that rewrite: the term
that reaches `try_compile` is exactly the term `syntax.rs` or a benchmark
built, closure literals and all, so every iteration paid a partial
application's wrapper call and a fresh environment allocation for a
closure whose shape never changes.

**The trust-model survey.** Four ways to let a rewriter change the term
before compilation, and trust the result:

- **A, a single trusted normaliser.** One piece of code decides the
  rewrite is correct and nothing checks it afterwards. CompCert and CakeML
  both go this way for their optimisation passes -- but as *proven*
  transformations, checked once and for all at the meta level (Rideau &
  Leroy's validated register allocator is itself an exception inside
  CompCert, discussed under D below). Trusting an unproven rewriter the
  same way is too much weight on one piece of code with no independent
  check per run.
- **B, an NbE-based normal-form checker.** Normalise both sides by
  evaluation and compare. This project's own strict semantics make this
  the wrong tool: NbE has to track which subterms are values under the
  evaluation order in force, and a checker built that way rejects correct
  rewrites it can't itself see are stuck-free, the same shape of false
  rejection Tristan, Govereau & Morrisett's normalising validation (PLDI'11)
  built machinery to avoid for a *different* language.
- **C, a kernel-proved `h ≡ h'`.** CertiCoq ("Shrink fast correctly!") and
  Œuf (denote the source and target ASTs into Coq and finish with
  `reflexivity`) both certify a transformation this way, inside a proof
  assistant's own kernel. `kernel.rs` already plays that role here for
  compiled-vs-interpreted equivalence (`proof.rs`, §33), so it is the
  natural upgrade -- see the probe finding below for why it isn't the first
  cut.
- **D, certificate-carrying rewriting.** The rewriter (untrusted) emits the
  result plus a trace of steps; an independent checker (trusted) replays
  the trace from the original and must land on exactly that result.
  Crellvm (PLDI'18) is the closest precedent: an LLVM optimisation pass
  emits hints alongside its output, and a separate validator checks each
  hint locally rather than re-deriving the whole optimisation or trusting
  the pass. Alive2 checks individual peephole rewrites against a
  precise semantics but is intraprocedural -- it doesn't fit a rewrite that
  must chase every occurrence of a redex through a whole term. GHC takes a
  looser version of D in production: a trusted simplifier plus Core Lint,
  a well-formedness sanity check on the output, not a proof it denotes the
  same thing.

  D is what shipped: `specialise.rs` (untrusted) emits `h'` and a
  `Vec<Step>`; `spec_check.rs` (trusted, independent, allowed to import
  only `crate::term` and `std`) replays every step from `h` and accepts
  only if it reaches exactly `h'`. It beats A because nothing about the
  rewriter itself needs to be trusted, and it beats B because replaying a
  named step is exact where NbE-style comparison is approximate. It is a
  deliberately smaller commitment than C.

**The probe finding behind "D now, C later".** A throwaway test (recorded
in the design spec) ran `proof.rs`'s entry points on both loops and on
their specialised or hoisted forms: all six terms got universal-strength
proofs, so `denote` already covers `h` and `h'` individually. But each
theorem is stated per term -- `∀p v (e : Ev_h(p,v)). loop_val_h(p,e) = v`,
with `Ev_h` and its closure-call constants postulated fresh for that one
term -- so a kernel proof of `h ≡ h'` needs a new builder that doesn't
exist yet: `Ev_h(p,v) → Ev_h'(p,v)`, by induction on `ev_rec_h` with each
step's next parameters equal by congruence plus `call_eq` rewriting. That
builder is sized like the core of `build_universal` and is real work, so C
is future work (open questions, below) and D ships now. The trace D
produces is deliberately shaped to be that builder's proof outline: one
`BetaV { redex }` per congruence step it will need.

**Why βv, not full β.** `eval.rs` is strict and can fail
(`DivByZero`/`TypeError`/`NotAFunction`/`UnboundVariable`) or diverge
(`Rec` has no fuel), so full β is unsound here: `(\x. 0) (1/0)` fails under
call-by-value evaluation, but its β-contraction `0` does not. The rewrite
used is βv, `App(Abs(M), V) → M[0 := V]` restricted to a value argument
`V` (a bound `Var`, `Lit`, `Abs` or `Rec`) -- every binder under strict
evaluation is bound to exactly such a value, so this covers every redex
evaluation would itself contract. Plotkin (1975) shows βv is an observational
equivalence in the call-by-value λ-calculus and, unlike full β, is closed
under every context: a value evaluates in no steps with no effect, so
substituting it can neither introduce nor remove an error or divergence.
That is what licenses rewriting under binders, inside `If` branches and
inside a `Rec` body without re-checking anything about the surrounding
term.

**The source must be closed.** Found in final review, after the JIT had
started installing specialised fragments. βv's value set includes only
*bound* variables: `eval` starts in an empty environment, so an unbound
`Var` evaluates to `Err(UnboundVariable)` and is not a value. The checker
accepted any `Var` as a value, so for
`\n. if n == 777 then (\x. 0) v5 else 1` it accepted contracting
`(\x. 0) v5` to `0`. `try_compile` had rejected the original, for its
unbound variable, but it compiled `h'`. No sample hit 777, and `h'` got a
universal proof, so the JIT installed it and returned `Ok(0)` where `eval`
fails. `check` now rejects a source with a free variable before replaying
anything, using its own free-variable walk. In a closed source every `Var`
in every occurrence is bound by an enclosing binder, and βv keeps a term
closed, so every `Var` a step meets is a value. The specialiser returns
the empty trace for an open source, and for one over `MAX_NODES`, since
the checker rejects both whatever the trace. The probe is now a JIT
regression test (`an_open_redex_is_not_contracted_away_by_the_jit`), and
the fuzz includes open terms.

**Hash-addressed steps and optimal reduction.** A `Step` names its redex
by content hash and is applied to every occurrence in one pass, not by a
path into one specific occurrence. Because `term.rs` hash-conses (§1),
two occurrences of the same redex are already one node, so this is sound
by construction -- rewriting a subterm is rewriting it in every context
that shares it, and there is nothing further to justify. It also happens
to resemble a *weak* form of Lévy's family reduction (Lévy 1978): same
syntax, sharing by content identity, not the same dynamic origin -- a
genuine optimal-reduction implementation tracks *families* of redexes
descended from one another through reduction (Lamping 1990's sharing
graphs; Asperti's overview of what "efficient" reduction actually costs;
the weak/full-laziness distinctions in Balabonski's ICFP'13 and POPL'12
papers; Barenbaum & Bonelli's FSCD'17 linear substitution calculus). This
project's hash-addressed steps never need that machinery, because they
only ever claim to share syntactically identical terms, never terms that
happen to originate from the same redex. **Optimal reduction does not apply
here**, for three independent reasons: it minimises the *number of
normalisation steps* under full β, not the run-time cost of the residual
program, which is what this project actually wants; full β is unsound in
this strict semantics, as above; and its sharing-graph bookkeeping cost is
provably not bounded by any elementary function (Asperti & Mairson 1998),
which would dwarf anything it saved on a loop this small. The policy's
own "OnceInLam" restriction -- don't duplicate work that would turn into
extra closure allocations under a binder -- is GHC's occurrence-analysis
heuristic (Peyton Jones & Marlow 2002), not a step toward optimality; it
exists only to avoid code that gets slower.

**Placement: a separate driver.** Specialisation is not folded into
`try_compile`. `try_compile`'s existing tests deliberately build literal-
lambda redexes to exercise closure machinery directly (`MakeClosure`,
partial applications, allocation); specialising inside `try_compile` would
silently reduce those redexes away and weaken what those tests cover.
Instead `compile::compile_specialised` composes two untouched passes:
`specialise::specialise` (untrusted), `spec_check::check` (trusted), and
then the unchanged `try_compile`. `try_compile`'s own contract -- every
accepted module decompiles to the term it was given (§35) -- still holds
of whichever term it is handed, `h` or `h'`.

**How it was checked.** `spec_check.rs` has 15 tests: 13 unit tests (one
value kind per accepted step -- bound `Var`, `Lit`, closed `Abs`,
capturing `Abs`, `Rec` -- plus rejections for an open source, a non-value
argument, `Rec` in head position, an absent redex, a wrong claimed hash,
and over-limit traces/terms), the mutation test below, and an
independence test that scans its imports and admits only `crate::term`
and `std`, reusing `decompile.rs`'s existing import-scanner as a shared
`#[cfg(test)]` helper. The scanner covers `crate::`, `super::` and
`tatic::` paths; the last because `lib.rs` has `extern crate self as
tatic` in test builds, so a `use tatic::eval` slipped past it until final
review. `specialise.rs` has 10 tests, including the shapes
the design predicted: `partial_application_loop` specialises in 4 βv
steps to a plain loop computing `acc + n` (no `call_indirect`, no
`$alloc` in its WAT); `capturing_closure_loop` in 1 step;
`capturing_closure_loop`'s own closed-closure variant takes 2 steps
because the first substitution exposes a new redex, `(\y. y+1) n`; and a
capturing closure whose parameter is used inside a loop body is correctly
left alone (the OnceInLam policy rule). The other two, from final
review, give an open source and an oversized one the empty trace. The
oversized probe, `\n. (\x. n) BIG`, used to get a one-step trace that
shrinks it below `MAX_NODES`, which the checker then rejected for the
source's size: a debug panic in `compile_specialised`. A planted mis-shift
in the specialiser's `lift` is caught by the checker, as designed.

A corpus-and-fuzzer mutation test attacked valid `(h, trace, h')` triples
with five mutations -- drop a step, swap adjacent steps, retarget a step
to another subterm's hash, change a `Var`/`Lit` in the claimed `h'`,
truncate the trace -- at [26, 15, 206, 11, 26] attempts respectively. Every
mutant was rejected except one retarget, in
`over_application_pap_producing_root`, which turned out to still replay to
the same claimed term; the test confirms this against an independent
oracle (`specialise::replay`, `cfg(test)`, the specialiser's own
substitution, not the checker's) rather than trusting the checker's own
"accepted" verdict, and a planted change to that oracle makes the
assertion fail, so the check has teeth.

The differential fuzzer (`specialisation_is_checked_and_preserves_meaning_on_random_terms`,
extending `compile_fuzz.rs`'s existing generators with `Div`/`Mod`) ran
1000 seeds; the checker accepted every trace produced, and `eval` on `h`
and `h'` agreed exactly on the sample arguments, including which error
each raised. Two planted bugs confirm the fuzz has teeth: a specialiser
bug is caught via the checker rejecting its trace, and making the checker
and specialiser agree on an unsound step (accepting a `Prim` argument as a
value, in both places at once) is still caught, via the `eval` comparison
diverging on a `Div` term. Since final review, one seed in five is an open
term (`gen_unbound_variable`, bare or under a redex), which must get the
empty trace and be rejected by the checker. Every term also goes through
`compile_specialised`, and its fragment is run directly, with no
`verify()` in between, against `eval`, on every term `typing::well_typed`
accepts (§38; before, wherever `eval` was not a `TypeError`). Compiled
code assumes well-typedness, for `h` as much as `h'`: at seed 95
`try_compile(h)` itself returns 310 where `eval` raises a `TypeError`,
because `gen_redex_rich` can use a closure as an `Int`. `verify()` catches
that only when a sample reaches the ill-typed code, which is the bug §38
fixes. The latest run
specialised 645 seeds, compiled 564 (213 from `h'`) and compared 4400
compiled runs. Before, the fuzz asserted `spec_check_failures() == 0`
without ever calling `compile_specialised`, so the assertion was vacuous.
A planted rejection in `compile_candidate` now fails it (645 failures),
and a planted `i64.add` -> `i64.sub` in `h'`'s WAT fails the compiled
comparison.

`compile.rs` covers the driver's two fallbacks. A trace the checker
rejects panics in debug and, in release, falls back to `h` and increments
`spec_check_failures`. A checked `h'` that doesn't compile also falls back
to `h`: `over_application_if_between_closures` specialises to
`(if 0 < 10 then \c. .. else \c. ..) 100`, an application headed by an
`If`, which `build` doesn't cover.

`kernel_verify` running on `h'` rather than on `h` now has a test that
tells them apart. `\n. (\g. g) (\x. x + 1) n` gets no universal proof,
but its specialisation `\n. n + 1` does, so the JIT installs it only
because the proof is about `h'`. One limit is worth stating plainly
rather than papering over: `find_spine`'s `!in_fn_pos` guard is untested,
since removing it changed no observed result on the current corpus. It
is recorded as open rather than quietly left out. *(Later: closed by
`a_spine_is_reduced_whole_or_not_at_all`, §39.)*

**Cost.** Criterion `capturing_closure_loop/jit_warm_cache_hit` and
`partial_application_loop/jit_warm_cache_hit`, `main` vs this branch,
three interleaved rounds, `BelowNormal` priority, on a machine shared with
a training run (a `selfplay-burn` process was active throughout, and a
second one started partway through the third round, which is visible in
that round's much wider variance): best-of-three medians,
`capturing_closure_loop/jit_warm_cache_hit` 47.908 µs -> 11.773 µs (4.1x),
`partial_application_loop/jit_warm_cache_hit` 163.87 µs -> 6.8832 µs
(23.8x, well past the spike's 7.0-7.6x estimate for the same rewrite --
the full pipeline also removes the wrapper call and the per-iteration
environment allocation the hand-specialised spike term still needed
compiled around it). The untouched control,
`closure_typed_loop_carried_parameter_loop/jit_warm_cache_hit` (unchanged
because it calls through `Rec` in head position, never a candidate spine),
moved from 37.980 µs to 40.488 µs across the same runs -- a ~7% difference
in the noisy direction, consistent with no real change on a shared
machine, not a regression. `cargo run --release`'s own JIT stats:
compiled 9, specialised 3, `declined_no_universal_proof` 0, unchanged from
before this work except for the new `specialised` count.

The inlined-bump-allocation idea probed alongside the original spike is
not part of this change; see
`docs/superpowers/specs/2026-09-23-jit-ir-design.md`'s "Future work" for
its numbers.

## 38. The JIT installed ill-typed code that goes wrong only off the samples -- found and fixed

**The bug.** `\n. (\g. if n == 777 then g 1 + g else n) (\x. x + n)`
adds a closure to an `Int` when `n == 777`. `eval` gives `TypeError` there;
the JIT installed the compiled form and returned `Ok(779)`. The specialiser
isn't involved (`g` is used twice and captures `n`).

**Root cause.** Compiled code is untyped: an `Int` and a closure are both a
raw `i64` (`lower_wat.rs`'s packed table-index/env-pointer), with no tag to
test. So compiled code is correct only if nothing uses a closure as an
`Int` or calls an `Int`, and nothing established that. Neither half of the
installation gate (§28, §29) sees it: `verify()` compares only on
`sample_arg_vectors`, which never reach `n == 777`, and the universal
theorem is stated over postulated symbols (`call_ref` always returns an
`Int`), so it has no notion of type. Several docs claimed `verify()`
catches ill-typed code (`lower_wat.rs`'s over-application notes,
`compile_fuzz.rs`, §37, the README). It does only when a sample reaches the
ill-typed code.

**Options considered.** More samples only hide the symptom. Runtime guards
are impossible without tags, and tagging values (63-bit ints, as V8,
LuaJIT and Chez do, or boxing) costs every operation and changes integer
semantics. A flow analysis of which sites can receive a closure is more
precise than typing and harder to trust, with no corpus term needing the
precision. Making the kernel theorem model types is very large. Taken:
the other standard answer, the one ML-family compilers rely on when they
erase tags (typed closure conversion, Morrisett et al.). Only a term with
a simple type `Int -> ... -> Int` is installed, so by the usual type-safety
argument (Wright and Felleisen) it can't reach `TypeError`, `NotAFunction`
or `UnboundVariable` on `Int` arguments.

**The fix.** `src/typing.rs`, `well_typed(store, h, arity)`: monomorphic
unification over `Int | a -> b | variable`, with an occurs check (Milner's
algorithm without generalisation). Two rules go beyond the textbook:
- `Rec` must wrap an `Abs`, which is also all `compile.rs` compiles. `eval`
  treats a `Rec` value as a function, so `Rec(Lit 5) + 1` would otherwise
  type as `Int` and fail at runtime.
- An `If` whose condition is closed arithmetic over literals only types the
  branch `eval` would take. Without this, the dead `if 1 < 0 then g(x, 999)`
  in `inconsistent_arity_loop_carried_parameter_loop`, and five `jit.rs`
  tests built the same way, would be declined.

`jit.rs` runs it on `h` after compilation and before instantiation. A
declined term is cached as `CacheEntry::IllTyped`, counted in
`Stats::declined_ill_typed` and served by the interpreter. The check is on
`h` rather than on a specialised `h'`: βv preserves types, and `h` is what
the caller wrote. `typing.rs` is trusted, so the independence scan pins it
to `eval` and `term`. `try_compile` is unchanged: the `compile.rs` tests
that exercise curried dispatch through ill-typed dead branches still
compile.

**Cost, measured before choosing** with a throwaway probe of the same
inference:
- Corpus: 21 of 23 terms are typed. The other two, `iterate` and
  `fixture_twice`, take closure parameters, which the JIT can't pass (its
  arguments are `i64`), so the JIT never installed them anyway.
- `gen_program`: 1000 of 1000.
- `gen_redex_rich`: 366 of the 408 that compile.
- `gen_over_applied`, `gen_inconsistent_arity`: 0 of 1000, as designed.
  They are ill-typed by construction and passed before only because the
  samples caught them.
- `cargo run --release`: compiled 9, specialised 3, `declined_ill_typed` 0,
  so the demo is unchanged.

The monomorphism is a real limit: a closure used at two different types
is declined, where let-polymorphism would accept it. No corpus term needs
it.

**Tests.**
- `jit.rs`'s `an_ill_typed_branch_off_the_samples_is_not_miscompiled` is
  the regression test for the bug, and pins `declined_ill_typed == 1`.
- `typing.rs` has seven unit tests: acceptance and arity, closure as
  `Int`, constant and non-constant conditions (and a constant one that
  fails), `Rec`, the occurs check, open terms and closure parameters, and
  the independence scan.
- `specialisation_is_checked_and_preserves_meaning_on_random_terms` now
  checks type safety directly: if `well_typed` accepts a term, `eval` must
  never give `TypeError`, `NotAFunction` or `UnboundVariable` on it. It
  also compares the JIT with `eval` on every term, and compares compiled
  fragments exactly on every typed term, where before it skipped only
  `TypeError` results. Latest run: 4376 compiled runs compared, 17 terms
  compiled but ill-typed.
- The over-applied and inconsistent-arity fuzz tests now pin
  `declined_ill_typed == 1`.

**Teeth**, each broken, seen to fail, then restored:
- Not forcing a `Prim`'s left operand to `Int` fails the type-safety fuzz
  (seed 25).
- Disabling the JIT gate fails the regression test.
- Dropping the `Rec` rule fails `rec_must_wrap_an_abs`.
- Dropping the pruning fails the five inconsistent-arity `jit.rs` tests.

Disabling the gate does *not* fail the random fuzz: its 17 ill-typed
compiled terms happen to be caught by the samples. §41 adds a fuzz of
off-sample ill-typed terms, which does fail.

## 39. Four leftovers from §37's review -- found and fixed

- **A debug panic in the proof walkers.** `kernel_verify` on
  `\n. (\g. g 1) (\x. \y. x + y) n` panicked in `debug_assert_has_type`.
  `\g. g 1` gives `g : Clo_1`, but the argument is a `Clo_2`:
  `Denoted::Clo` carries no arity, and the three `denote_*` walkers passed
  any `Clo` argument through. The kernel rejects the composed term, so a
  release build was sound, just noisy in debug. `arg_denotation` now
  compares the argument's `return_type_of` with the parameter's arity at
  all six argument sites. The JIT still compiles the term, from its
  specialisation `\n. 1 + n`. Test:
  `a_closure_argument_of_the_wrong_arity_gets_no_proof`.
- **An overflow in the specialiser.** `occurrences` counted tree
  occurrences through a shared DAG as a `usize`. `t + t` nested 70 times is
  71 nodes and 2^70 occurrences: a debug overflow panic, and in release a
  wrap to 0 that the OnceInLam policy reads as "unused". Only 0, 1 and
  "more" matter, so the count is capped at 2.
- **An independence-scanner bypass.** `use crate as x` (or `extern crate
  self as x`, and the same for `super` and `tatic`) let `x::eval` past the
  allowlist, since no `crate::` follows. The scanner now rejects any of
  those roots followed by `as`. `independence.rs` had no tests of its own;
  it has two now, one of which failed before the fix.
- **`find_spine`'s `!in_fn_pos` guard** (§37) now has a test. Without the
  guard, `(\x. \g. g x + g x) 5 (\y. y + z)` has its inner spine
  `(\x. ..) 5` reduced on its own, although the whole spine is declined
  because the capturing closure bound to `g` is used twice.

Each test was seen to fail with its fix removed.

## 40. Closures of the wrong arity: a compiler hole the proof gate closes

§38's type check doesn't see arity. `\x. \y. x + y` and `\x. (\y. x + y)`
have the same simple type, but in compiled code one is a two-argument
table entry and the other a one-argument one. Under `Dispatch::Fast`,
a variable called with one argument everywhere is called through a
one-argument `call_indirect`, whatever closure it holds. So a well-typed
term can reach a mismatched `call_indirect`:

```
\n. (\g. if n == 777 then (\k. k n) (g 1) + (\k. k n) (g 2) else n)
    (\x. \y. x + y + n)
```

`typing::well_typed` accepts it, the specialiser leaves it alone (`g` is
used twice and captures `n`), and the compiled fragment traps at
`n = 777`, where `eval` gives 3111. No sample reaches 777.

The JIT still gets it right, because the fragment gets no universal
proof. That is by construction, not by luck, but the construction is the
provers', not the kernel's. `Clo_k` is a curried chain of `k` arrows
ending in `Int`, so the kernel can't tell `\x. \y. e` from
`\x. (\y. e)`. Both are `Clo_2`, and `g` above, used as
`Int -> (Int -> Int)`, has that type too. What declines the term is that
the prover types each closure parameter as `Clo_k` for the number of
arguments at its call sites (`g 1`: `Clo_1`), and then refuses an
argument whose root has another arity (§44 has more on this). The proof
walkers do that up front: `denote_*` through §39's `arg_denotation`, and
`eval_dyn`, whose closure values carry their concrete root, by comparing
that root's arity with the parameter's. §39 had missed `eval_dyn`, and
this test hit its debug panic there; a release build was sound either
way.

So this hole is closed by §29's universal-proof gate, not by the sample
battery the comments in `compile.rs` credited. The test
`a_closure_of_the_wrong_arity_off_the_samples_is_not_installed` runs the
fragment directly to show it traps, and requires the JIT to agree with
`eval` and to decline the term for want of a proof. With the gate relaxed
to install proof-less terms, it fails at `n = 777`.

A static check in the compile path would make this independent of the
proof gate: simple types extended with arity, where an arrow records how
many arguments it takes at once, as in "Kinds are calling conventions"
(Downen et al., ICFP 2020). That isn't done here. It is the natural next
step if the proof gate is ever relaxed (§29's "widen the universal
fragment"). §43 surveys what other compilers do instead.

## 41. Fuzzing branches that go wrong off the samples

§38 and §40 each pinned their hole with one hand-built term. The random
fuzz couldn't: its ill-typed compiled terms went wrong on the samples, so
`verify()` caught them first, and the gates were never the last line.
`compile_fuzz`'s `a_branch_that_goes_wrong_off_the_samples_is_never_installed`
generates

```
if x == 777 then <goes wrong> else <gen_expr>
```

where 777 is outside `jit.rs`'s sample battery. `<goes wrong>` is one of
a closure used as an `Int`, an `Int` (always a parameter) called, an
over-applied lambda (all ill-typed), or §40's well-typed closure of the
wrong arity. The branch sits in one of four hosts:

- the body of a plain function;
- the per-iteration payload of a tail loop or a non-tail recursion, with
  `x` the counter, so the branch runs when the counter reaches 777;
- `\x1. \x2. if x2 == 777 then x1 a else e`, where `x1` is only ever
  called (below).

Each term is run at every combination of `[0, 1, -1, 7, 777]`, and the JIT
must agree with `eval`. The test tallies each host and kind by outcome,
and requires each ill-typed kind to reach the typing gate, and the wrong
arity the proof gate, in every host.

Latest run, 600 seeds: every term compiled and passed the samples, and
every one was declined, 467 as ill-typed and 133 for want of a proof.
Early versions lost about half of the "Int called" terms before any gate:
`compile.rs` compiles only a variable or a lambda as a call head
(`Shape::OtherCall`), so calling a literal or an arithmetic expression
was declined earlier and tested nothing.

**Teeth.** Disabling the proof gate fails it (seed 3, a tail loop: `eval`
gives `Ok(682316)`, the JIT `Trap`). Disabling the typing gate fails it
(seed 7: `eval` gives `NotAFunction`, the JIT `Ok(10)`), but only because
of the fourth host, and since §42 only together with the check that
section adds. In the first three, the proof gate declined every
ill-typed term too. The first version's typing-gate failure (its seed 190)
was a noisier instance of the fourth host: `v1` called, and otherwise
only passed to lambdas.

**What the fourth host found.** `\v0. \v1. if v0 == 777 then v1 5 else v0`
gets a universal proof from `prove_closure_expr`. `v1` is only called, so
the prover types it `Clo_1` and proves the theorem for every closure
argument. The JIT's entry point is only ever passed `Int`s, so the theorem
covers none of the calls the fragment is installed for. This is the case
§38 anticipated ("the kernel theorem is over postulated symbols with no
types"), now pinned down: the typing gate is currently the only thing
standing between such a term and installation. Fixed in §42.

## 42. Proofs about closure arguments the JIT never passes -- found and fixed

§41's fourth host found a term the proof gate installed although it goes
wrong:

```
\a. \f. if a == 777 then f 5 else a
```

`prove_closure_expr` sees `f` called with one argument, gives it the
kernel type `Clo_1`, and proves that the compiled function equals its
denotation for every `Int` `a` and every one-argument closure `f`. The
theorem is true. But the JIT's entry point is only ever passed `Int`s, so
`f` is always an `Int`, and the theorem covers none of the calls the
fragment is installed for. At `a = 777` the compiled code calls through
whatever table entry the `Int` names (`Ok(10)` in §41's seed 7, with the
typing gate disabled), where
`eval` gives `NotAFunction`. The tail-recursive prover does the same for a
loop-carried closure parameter at the top level:
`rec go g n x = if n <= 0 then x else go g (n - 1) (g x)` got a universal
proof with `g : Clo_1`.

The typing gate (§38) already declined both, since calling an `Int` is a
type error, so nothing wrong was installed. But the proof gate's claim,
that the theorem covers every input the fragment will see, was false for
them. That was the case §38 warned of: the kernel's parameters are typed
by how the term uses them, not by how the JIT calls it.

**Fix.** `kernel_verify` returns `ProofStrength::None` for a term that
calls one of its own parameters (`calls_a_parameter`, from
`compile::infer_closure_arities`), before trying any prover. That's the
one place every prover's theorem meets the JIT's calling convention.

The provers are unchanged. A theorem over closure-typed parameters is
still a theorem, and the benches and `compile_fuzz` prove such terms (the
bare `it` of `gen_closure_typed_recursive`) directly. What changed is
which theorems the JIT counts. Where the fix belongs was a choice:

- **In `kernel_verify` (chosen).** One check covers every prover. It is
  syntactic: it asks whether a parameter is called, not what the
  theorem's context says, so it relies on every prover typing a called
  parameter as a closure. They must, since the kernel can't apply an
  `Int`.
- **In each prover.** This needs an "entry point" flag on
  `prove_closure_expr` and the tail provers, which also serve callers
  that want the closure-typed theorem.
- **Record parameter types on each proof and check them.** This is the
  most exact: the gate would read the theorem's own context. It means
  changing `EquivalenceProof` and `UniversalTailProof`, for no case the
  syntactic check misses.

**Tests.** `jit.rs`'s `a_parameter_that_is_only_called_gets_no_universal_proof`
checks both terms above, and each was seen to get `Universal` with the
check removed. In §41's fuzz, each static defence now keeps out every
ill-typed term on its own. With the typing gate disabled, there are no
mismatches. With the typing gate and this check both disabled, there are
91, all "Int called", 89 of them in the called-parameter host.

## 43. How other compilers call a closure of unknown arity

§40's hole comes from `Dispatch::Fast` assuming a call site's argument
count is the callee's arity, unchecked. No compiler surveyed here does
that. Each one either checks at runtime at a call to an unknown function,
or shows statically that there is no such call.

**Checking at runtime (eval/apply).**
- **GHC** (Marlow and Peyton Jones, "Making a fast curry"): a call to a
  known function with enough arguments is direct. A call to an unknown
  one goes through generic apply routines that read the closure's arity.
  If it matches, they jump in. If there are fewer arguments, they build a
  PAP. If there are more, they call with that many and apply the result
  to the rest.
- **OCaml:** a closure records its arity. An unknown call with `n`
  arguments goes through `caml_applyN`, which takes the full-application
  entry point when the arity is `n` and otherwise applies one argument at
  a time. Flambda 2 names the cases (`call_kind.mli`: direct, indirect of
  known arity, indirect of unknown arity). wasm_of_ocaml does the same on
  WASM, with an arity field in the closure.
- **Lean 4:** the IR separates `fap` (a full call of a known constant),
  `pap` and `ap`. `ap` goes through `lean_apply_n`, which checks the
  closure's stored arity (Ullrich and de Moura).

**Showing it statically.**
- **MLton:** closure conversion is directed by whole-program flow
  analysis (0CFA). A function value becomes a variant of a sum type
  naming which function it is, so every call is to a known function, and
  coercions are inserted between representations (Cejtin et al.). This
  needs the whole program, which a JIT compiling one term at a time
  doesn't have for a parameter.
- **GHC, again:** its Core optimiser eta-expands functions to the arity
  their uses need, so more calls take the fast path. Call Arity
  (Breitner) does this from how a function is used, not how it is
  defined. Downen et al. make it type-directed: extensional function
  types make eta-expansion always valid ("Making a faster curry with
  extensional types"), and arity in kinds makes the calling convention
  part of the type ("Kinds are calling conventions").

**What that means for tatic.** Three responses were surveyed after §42:
1. **A runtime check** (1a). Keep `Fast`, but check the stored arity at
   each unknown call and fall back to the curried path on a mismatch.
   This is the mainstream answer, and what §9 concluded a closure of
   genuinely unknown origin needs: a uniform calling convention or
   adapters. It makes the compiled code correct but earns no universal
   proof, since the kernel's `Clo_k` is arity-exact and curried dispatch
   gets only per-sample proofs. So such terms would still be declined.
2. **An eta rewrite** (1b), GHC's Core-level answer. Rewrite the term
   before compiling so that arities agree, e.g. pass `\x. (\y. clo x y)`
   where a one-argument function is expected, with a certificate that the
   rewrite preserves meaning (as `spec_check` does for the specialiser).
   Eta on a lambda value is sound under call-by-value. It is the only
   option that turns declines into installs, since the existing provers
   apply to the rewritten term.
3. **A static arity check** (1c), the Kinds paper without the rewrite.
   It is cheap and independent of the proof gate, but gains nothing while
   the proof gate already declines these terms.

None is done. The main run declines no term for want of a proof, so
nothing in the corpus needs them yet. If one is, 1b fits the proof-gated
design best, and 1a remains the eventual fix for closures of unknown
origin.

## 44. The type systems tatic has, the one it would ideally have, and ways between

§38 to §43 each patched one place where a type was assumed and not
checked. This section steps back and looks at all of them together.

**What exists.** Five separate notions of type decide whether a term runs
compiled:

1. **`typing.rs`**: `Int | Fun | Var`, simple types with unification. It
   is monomorphic and can't see arity. It has two non-standard rules:
   `Rec` must wrap an `Abs`, and a closed condition types only the branch
   it picks. It is trusted, and the `independent_of_the_compiler` test
   checks that it shares no code with the compiler.
2. **`compile.rs`'s `infer_closure_arities`**: for each variable, an
   `ArityUse`, `Consistent(k)` or `Inconsistent`. It decides module-wide
   between `Dispatch::Fast` and `Curried`, and it knows nothing about
   `Int` versus closure.
3. **`proof.rs`'s `Denoted::Int | Clo(Expr)`**: `Clo` records no arity.
   Parameter types come from `ArityUse`, and `return_type_of` has to be
   kept in step with it by hand. Arity is checked at six `arg_denotation`
   sites and in `eval_dyn`.
4. **The kernel's `Clo_k`** (`curried_int_ty(k)`, `Int -> ... -> Int`):
   it is curried, so `Int -> (Int -> Int)` and `Clo_2` are the same type.
   Arity is exact only because the prover picks `Clo_k` from the number
   of arguments at a call site (§40, corrected below).
5. **`jit.rs`'s `calls_a_parameter`** (§42): a syntactic check that stands
   in for "the theorem's parameters are all `Int`".

**What would be ideal.** One type system, over the term language, that:

- (a) is arity-aware, so that `\x. \y. e` and `\x. (\y. e)` differ exactly
  as they do in compiled code, and a `Fast` call is well-typed only when
  the callee has that arity (Bolingbroke and Peyton Jones's "Types are
  calling conventions"; Downen et al.'s "Kinds are calling conventions");
- (b) is the one source for all four consumers: the typing gate, the
  choice of dispatch, prover parameter types and kernel types;
- (c) has a proved type-safety theorem: on `Int` arguments, a well-typed
  term never reaches `TypeError`, `NotAFunction` or `UnboundVariable`;
- (d) is linear in the hash-consed DAG, not in the tree it unfolds to;
- (e) is at least as permissive as the corpus needs, in which case
  let-polymorphism is optional.

**Gaps, by consequence.**

- **G1: arity blindness** (1 vs 2, 4). The §40 hole is closed only by the
  proof gate, and the protection comes from how the prover models calls,
  not from kernel types.
- **G2: four places to keep in agreement.** Every hole §38 to §42 found
  was one notion assuming another had checked something. §42's
  `calls_a_parameter` exists because the kernel's parameter types come
  from use (3), while the JIT's come from the entry point (all `Int`).
- **G3: exponential on DAGs.** `infer` walks the tree and has no memo. A
  term that nests `t + t`, `d` deep, takes 22 ms to type at `d = 18`,
  395 ms at 22, and 3.4 s at 25. `try_compile` is worse: 417 ms, 8 s and
  73 s. This breaks the ideal (d), and it is also a denial-of-service
  risk for anything that feeds terms in. (Typing is fixed in §45.
  `try_compile`'s cost turns out to be the size of its output, not the
  walk.)
- **G4: soundness is argued, not proved.** "By the usual type-safety
  argument" (`typing.rs`'s doc) covers the textbook rules. The two
  non-standard rules are covered only by argument plus §41's fuzz.
- **G5: the pruning rule exists for tests.** It keeps dead, ill-typed
  branches compilable, "used in tests and benches to exercise curried
  dispatch". It makes the checker depend on `eval`.
- **G6: monomorphism.** A closure used at two types is declined, e.g.
  `(\id. id (\x. x) (id 1))`. The corpus has no such term. Since every
  value is a uniform `i64`, polymorphism costs nothing at runtime.

**Options.**

*G1, arity in the types.*

- **A1: multi-arity arrows in `typing.rs`.** Replace `Fun(a, b)` with
  `Fun([a1..ak], b)`. The arity of an `Abs` chain comes from how it is
  peeled, the arity of a call from its spine, and unification requires
  equal arity. This is §40's proposal.
  - Pros: it makes the §40 hole a type error independent of the proof
    gate. It is small: one constructor and one unify case.
  - Cons: it is more restrictive than `eval`. A term that partially
    applies a two-argument lambda, or over-applies a lambda that returns
    one, is declined unless there are coercion rules. Those rules
    (subsumption from `Fun([a], Fun([b], c))` to `Fun([a, b], c)`) are
    exactly what Downen et al. need extensional types for. It also
    doesn't touch G2, so it becomes a sixth notion that must agree.
- **A2: infer arity by use, with eta coercions.** Generalise A1 by
  letting a closure used at arity `k` but defined at `j` get an eta
  adapter (§43's 1b), recorded as a coercion in the typing derivation.
  - Pros: it declines nothing that `eval` accepts, and the adapters can
    be certified as `spec_check` does.
  - Cons: it is an elaboration, not a check, which puts rewriting inside
    the trusted base. Of the options here it has the most code, for no
    term the corpus has.

*G2, one source or many.* This is the central tension: the typing gate is
trusted *because* it is independent (§38). Four ways out:

- **B1: N-version.** Keep the independent checkers and add a test that
  they agree (typing's arity per variable equals `infer_closure_arities`'
  on every fuzzed term).
  - Pros: no trusted code changes, and disagreement is caught in testing.
  - Cons: agreement is tested, not enforced, and each new notion adds a
    pair to check.
- **B2: an untrusted elaborator and a small trusted checker.** One
  inference, anywhere and as clever as needed, emits a typed term (each
  binder and call annotated with its type and arity). A small trusted
  checker re-checks the annotations. Compile, the provers and the gate
  all read the same annotations. This is how GHC treats Core (Core Lint
  re-checks the typed IR between passes), and how typed assembly and
  proof-carrying code (Morrisett et al.; Necula) and translation
  validation (§35) work.
  - Pros: one source for (b). The trusted part is smaller than
    `typing.rs` today (checking is simpler than inferring: no
    unification, one linear pass, and G3 disappears for the checker), and
    independence still holds, since the checker needn't share code with
    the elaborator.
  - Cons: the largest change here. Every consumer switches from its own
    walk to the annotations. The annotated form has to survive the
    specialiser (§37) and lifting (§36), or be re-inferred after them.
- **B3: share `typing.rs` with compile and the provers.**
  - Pros: least code.
  - Cons: it gives up §38's independence. A bug in the shared inference
    then misleads the gate and the compiler the same way, which is the
    failure independence exists to catch.
- **B4: kernel types as the source.** Put the arity-exact type into the
  theorem (§42's third option: record parameter types on each proof),
  and have the gate read them.
  - Pros: the gate then reads the theorem's own statement, which is the
    most direct form of "what was proved covers what runs".
  - Cons: it needs arity-exact kernel types first. Today `Clo_k` is
    curried (4), so the kernel itself can't tell the two lambdas apart.
    It also doesn't help the typing gate.

*G3, the DAG blowup.* Monotyping a DAG is not the same as monotyping the
tree it unfolds to. If shared occurrences share one type node, a lambda
used at two types in two places is declined where the tree typing
accepted it. Three repairs, from most to least exact:

- **C1: memo ground results.** Memoise on (subterm hash, the resolved
  types of its free variables) only when inference fixes every type
  inside the subterm. Reuse is then exactly what re-typing would do.
  - Pros: it changes nothing that is accepted. It covers the measured
    case, which is first-order arithmetic.
  - Cons: a shared subterm with lambdas of unresolved type is still
    re-walked, so the worst case is still exponential.
- **C2: generalise closed subterms.** Type each closed shared subterm
  once, generalise, and instantiate fresh at each use. That is
  let-polymorphism for closed subterms (Milner), and it is sound here
  because there are no effects, so no value restriction is needed.
  - Pros: linear for closed sharing, and it removes part of G6 as a side
    effect.
  - Cons: the gate would then pass terms the provers can't type (F1's
    con, below). The blowup term is open, so this doesn't help it.
- **C3: share type nodes per (hash, environment).**
  - Pros: linear always.
  - Cons: incomplete relative to tree typing, as above.

  Whichever is chosen, `try_compile` still costs as much as the tree:
  its IR has no `let`, so what it emits is as big as the tree (§45). ML
  typing is DEXPTIME-complete because of `let` sharing
  (Mairson), so full sharing-aware polymorphic inference can't be linear
  in general. A monomorphic system that gives up the lambda-at-two-types
  case (C3) can be.

*G4, soundness.*

- **D1: prove progress and preservation in the kernel.** Wright and
  Felleisen style, for the checker's rules including the two
  non-standard ones.
  - Pros: the only way to meet (c).
  - Cons: large. The kernel reasons about compiled code, not about the
    term language's typing, so this needs a deep embedding of `Term` and
    `eval`'s rules.
- **D2: a type-safety fuzz.** For random well-typed terms and random
  `Int` arguments, `eval` never returns `TypeError`, `NotAFunction` or
  `UnboundVariable`.
  - Pros: cheap, and it states the property directly. §41's fuzz tests
    the gates, not this.
  - Cons: evidence, not proof.

*G5, the pruning rule.*

- **E1: a dead-branch pass before typing and compile.**
  - Pros: typing gets simpler.
  - Cons: the pass's trust moves into the pipeline.
- **E2: make the tests' dead branches well-typed.**
  - Pros: typing loses the rule and its `eval` dependency.
  - Cons: those tests exercise curried dispatch *because* the branch is
    ill-typed at `Fast` arity. This should be checked per test before
    committing to it.

*G6, polymorphism.*

- **F1: Hindley-Milner at `(\x. b) e` redexes** (`let` in all but name).
  - Pros: no runtime cost.
  - Cons: no gain unless the provers and `infer_closure_arities`
    follow. They type a closure by one arity and one `Clo_k`, so a
    polymorphic term would pass the gate and then get no proof.

**Recommendation.**

1. **C1, then the same memo for `try_compile`.** G3 is the one gap with a
   concrete cost today, and C1 changes nothing that is accepted. (Done in
   §45. The second half was a wrong premise: see there.)
2. **D2.** Done in §45. Cheap. It turns G4's "by the usual argument" into something
   tested.
3. **B2**, if the proof gate is ever relaxed (§29's "widen the universal
   fragment"). Only with a single annotated source do A1 and B4 become
   one change rather than two more notions to keep in step.

A1 alone fails G2, and F1 alone gains nothing. E is housekeeping.

## 45. Typing shared subterms once, and a type-safety fuzz -- which found a crash in the occurs check

This does §44's first two recommendations.

**C1: the memo.** `typing::infer` now memoises a result that is ground
(it has no type variables), keyed by the subterm's hash and its
environment. An environment is numbered by (enclosing environment, the
binder's type node), so the key is O(1) to build. Reuse is exact.
Re-inferring the same subterm in the same environment unifies a fresh
copy of the same constraints. Those succeed again and fix the copy to the
same ground type, so the memo changes no answer. A result that still has
variables isn't memoised. A copy's variables are fresh, and that is what
lets one shared `\x. x` node be used at two types.
`a_shared_lambda_can_still_be_used_at_two_types` pins this: with every
result memoised, it fails.

`\n. t_25`, with `t_{i+1} = t_i + t_i`, now types in about 30 µs, down
from 3.4 s. `a_shared_subterm_is_typed_once` bounds the calls to `infer`
at depth 12 (under 100, where the tree has 8191 nodes) and fails without
the memo. `the_memo_changes_no_answer` runs 4000 random terms with and
without the memo, and requires the two answers to agree on every one.

**D2: the fuzz.** `a_well_typed_term_never_goes_wrong` generates 4000
random terms. They cover every constructor, with subterms reused, dead
branches under constant conditions (including ones that divide by zero),
`Rec` without an `Abs`, and loops. Each is read at arity 0, 1 or 2. For
every term `well_typed` accepts, `eval` at every combination of
`[0, 1, -2, 7, 25]` must give `Ok` or `DivByZero`, never `TypeError`,
`NotAFunction` or `UnboundVariable`. Every generated term terminates, so
`eval` can run on any of them. That is strong normalisation for the
simply typed part, and each `Rec` either can't name itself or is a loop
whose counter goes down by one per self-call from at most 20. Latest
run: 1264 terms well typed, 13984 runs, 189 of them dividing by zero.

Teeth: each of three one-line mutations of the checker fails the fuzz
within the first 200 seeds:
- not unifying `Prim`'s second operand with `Int` (seed 177);
- dropping the rule that `Rec` wraps an `Abs` (seed 20);
- pruning to the wrong branch (seed 86).

**What the fuzz found.** Seed 931 overflowed the stack, with or without
the memo. Reduced:

```
\n. \f. (if n then f else \x. x) (\y. f)
```

The `if` gives `f` the type `a -> a`. The call then needs
`a -> a = (b -> F) -> r`, with `F` the type of `f` itself, so `a` would
have to contain itself. `unify` ran the occurs check only when binding a
variable. Linking one arrow node into another skipped it, which left the
type graph cyclic, and the next `occurs` followed the cycle until the
stack overflowed. So an ill-typed term crashed the process instead of
being declined. The JIT calls `well_typed` on every term it compiles, so
any caller could do that.

The fix runs the occurs check before every link. `occurs` and `ground`
now share one iterative walk with a visited set, so a shared type costs
one visit and no walk recurses. `find` is iterative too. The graph now
stays acyclic, which every later walk relies on.
`an_infinite_type_through_two_arrows_is_declined` is the reduced term;
it overflowed before the fix.

**Why `try_compile` isn't memoised too.** §44 assumed its 73 s came from
an unmemoised walk, as typing's did. Timing each stage at depths 14, 16
and 18 (build, `ir::check`, decompile, lower) shows each one growing
about 4× per two levels, in step with the output: 0.56, 2.2 and 8.9 MB
of WAT. `ir::Node` is a tree with no `let`, so a shared subterm is
emitted once per use. The compiled code is exponential, and no memo on a
walk changes that. The options:

- **Sharing in the IR.** A `Let` node, or a scratch local per shared pure
  subterm, emitted once and read at each use.
  - Pros: compiled code linear in the DAG.
  - Cons: it changes `ir.rs`, `check`, `lower_wat.rs` and `decompile.rs`
    (which would rebuild the shared term through the store's hash
    consing), and the proof walkers are tree walks too. A subterm can be
    bound once only where its first evaluation comes before every use. A
    subterm shared across `If` branches, or under a lambda, can't just be
    hoisted, since that could evaluate a division by zero or a loop the
    term never reaches.
- **A size gate.** Decline to compile a term whose tree size, computed
  with a memo over the DAG, exceeds a bound, and interpret it instead.
  - Pros: a few lines, and compile cost becomes linear in the bound.
  - Cons: `eval` walks the tree too, so such a term stays slow; the gate
    only stops the compiler costing more than the term.
- **Leave it.** No term in the corpus comes near.

The size gate is done in §47.

## 46. G2 in depth: where the type notions have to agree, and how other systems get one source

§44's G2 said the notions of type "must agree". This section says
exactly where, who checks each agreement today, and what other compilers
and checkers do instead.

**The agreements, one by one.**

| Pair | Must agree on | Checked by |
|---|---|---|
| `typing.rs` ↔ compiled code | `Int` vs closure at every value | `typing.rs`, which is independent (§38). Arity isn't covered. |
| `ArityUse` ↔ the closures that reach a variable | arity, under `Dispatch::Fast` | Nothing statically. `ir::check` checks that each variable is called at one arity, and its doc (`ir.rs`) says nothing proves the *values* reaching it have that arity. The proof gate covers it (§40). |
| `ArityUse` ↔ `proof.rs`'s parameter types | arity of each closure parameter | Shared code (`proof.rs` reads `ArityUse`), plus `return_type_of`, kept in step by hand. Not checked. |
| `proof.rs`'s `Denoted` ↔ the kernel | the type of each denoted `Expr` | The kernel. But `Clo_k` is curried (§11), so it can't tell `\x. \y. e` from `\x. (\y. e)` (§40, corrected). |
| The provers' parameter types ↔ the JIT's entry point | every parameter is an `Int` | `calls_a_parameter` (§42), a syntactic stand-in. |

`TYPES.md` already wrote the third and fourth rows down as one judgment,
and its §6.2 records a version of the fourth row's gap. It was closed by
opaque per-arity `Clo_k` postulates, then partly reopened when §11
replaced them with the curried arrow to save primitives.

**How others do it.**

- **A typed IR, re-checked between passes.** GHC's Core is typed, and
  Core Lint re-checks it after each pass when asked. Arity is a second
  notion there too: an `Id`'s arity lives in its `IdInfo`, apart from
  its type, and a lint invariant (GHC #10181) requires the arity not to
  exceed the type's. So GHC has tatic's "two notions that must agree",
  and handles it by checking one against the other. Lint is a debugging
  aid, not part of the trusted base.
- **An IR checker that knows calling conventions.** Lean 4's IR separates
  `fap`, `pap` and `ap` (§43), and `Lean.Compiler.IR.Checker` rejects a
  `fap` with the wrong number of arguments and a `pap` that supplies too
  many. That is `ir::check`'s `CallKnown` rule. Lean's `ap` then goes
  through `lean_apply_n`, which checks at runtime (§43, 1a).
- **A second checker on a lower IR.** rustc validates MIR at least once,
  and after every pass under `-Zvalidate-mir`. Borrow checking re-types
  MIR independently of the type checker that ran on HIR.
- **Type-preserving compilation.** TIL (Tarditi et al., PLDI 1996) and
  FLINT (Shao, ICFP 1998) keep types through every IR down to code
  generation, and TIL introduced the certifying compiler that TAL and
  proof-carrying code grew from. The types are the single source, and
  each pass must produce well-typed output.
- **One source by proof.** CakeML's type inferencer is proved sound and
  complete against a declarative type system (Tan, Owens and Kumar,
  IFL 2015), and type soundness is proved for that system. There is then
  nothing to keep in agreement: every consumer relies on the one
  declarative system.
- **The de Bruijn criterion.** A proof assistant is trusted if its proof
  objects can be checked by a small independent program (Barendregt's
  name for de Bruijn's design). The elaborator can be as large as it
  likes. Lean4Lean is such an external checker for Lean 4. §44's B2 is
  this criterion applied to types.
- **A typed target.** WebAssembly's typed function references add
  `call_ref`, which is statically typed, so the validator rejects a call
  at the wrong function type. `call_indirect`, which tatic uses, checks
  the type at runtime and traps on a mismatch (§40). wasmtime implements
  the proposal (`Config::wasm_function_references`; GC and exceptions are
  on by default from wasmtime 47, and tatic is on 42).

**Options for tatic.** §44 listed B1–B4. The survey adds two.

- **B5: a typed IR and a stronger `ir::check`.** Give each `Func`'s
  parameters and environment slots a type (`Int` or `Clo_k`, nested), and
  have `ir::check` check every node against them: `Arith` operands are
  `Int`, a `CallUnknown` under `Fast` calls a `Clo_k` with `k` arguments,
  a `MakeClosure` has the arity its type claims, and the entry point's
  parameters are `Int`. This is B2 at the IR, and it is Lean's checker
  extended from known calls to closures.
  - Pros: the IR is where every consumer meets. The builder emits it,
    `lower_wat.rs` reads it, and `decompile.rs` proves it means the
    term. Translation validation plus a type-checked IR means the
    compiled code is the term and can't go wrong, whatever
    `ArityUse` says, and §40's hole becomes a check failure independent
    of the proof gate. The checker is local and linear, with no
    unification. It would replace `calls_a_parameter` (the entry
    point's parameters are `Int` by type) and the Int-vs-closure part of
    the typing gate for compiled code.
  - Cons: the builder has to produce the types, which needs arity-aware
    inference (A1). `ArityUse` only knows about called variables, not
    which environment slots hold `Int`s. So a second, untrusted inference
    joins the code, the thing G2 counts against, though now it is checked
    rather than trusted. `ir::check` is in the same crate as the builder,
    so its independence would need the same `independence` test
    `typing.rs` has. The provers don't read the IR, so rows 3 and 4 of
    the table stay as they are.
- **B6: a typed Wasm target.** Lower to `call_ref` on typed function
  references, with `Int`s as `i64` and closures as typed references, so
  wasmtime's validator checks what B5's checker does.
  - Pros: the checker is external and already trusted, and was written
    by others to a public spec. That is as independent as a checker gets.
  - Cons: it replaces the uniform `i64` representation, the table and
    `call_indirect`, the linear-memory environments and the bump
    allocator (§9's design). It needs the same annotations as B5 to emit
    the types. It needs the GC proposal or a typed table, and wasmtime's
    GC is newer than the rest of the engine. It is the largest change
    here.

**How the options compare.**

| Option | Rows it closes | Trusted code | Size |
|---|---|---|---|
| B1: agreement tests | none (tests them) | unchanged | small |
| B2: annotated term + checker | 1, 2, 5, and 3 if the provers read the annotations | a small checker | large |
| B3: share `typing.rs` | 1, 2 | loses independence | small |
| B4: arity-exact kernel types | 4 | kernel postulates return | medium |
| B5: typed IR check | 1, 2, 5 for compiled code | the IR checker | medium |
| B6: typed Wasm | 1, 2, 5 for compiled code | wasmtime's validator | large |

**Recommendation.** Nothing in the corpus needs any of these yet. The
proof gate and `calls_a_parameter` keep out every term that would go
wrong (§41's fuzz). If the proof gate is ever relaxed:

1. **B5.** It closes the rows that matter for installed code, at the one
   place all of the compiler's consumers share, with a checker in the
   same style as `ir::check` and `spec_check`.
2. **B4**, if the provers are to stand on their own. Opaque per-arity
   `Clo_k` postulates come back, undoing §11's derivation, so the kernel
   sees the currying distinction the compiled code has. The cost is
   §11's saving in primitives.
3. **B6** as the end state, if typed references become the default in
   the wasmtime tatic uses.

## 47. A tree-size gate on `try_compile`

§45 left three options for `try_compile`'s blowup on shared subterms.
This takes the size gate.

**Why not sharing in the IR.** Compilation is a small part of what a
compiled term costs. Timing the whole JIT path on `\x. t_d`, with
`t_{i+1} = t_i + t_i`:

| `d` | `compile_specialised` | whole JIT call |
|---|---|---|
| 10 | 0.9 ms | 19.6 ms |
| 12 | 2.8 ms | 75 ms |
| 14 | 13 ms | 365 ms |

The rest is wasmtime compiling the module, the sample battery (`eval`)
and the provers, and each of those walks the tree too. A `let` in the IR
would make `try_compile` linear and leave about 96% of the cost, so it
would have to be followed by sharing in `lower_wat.rs`'s output and in
every prover walk. That is a large change for terms the corpus doesn't
have.

**The gate.** `try_compile` now starts by counting the term as a tree
(`tree_size`: one post-order pass over the DAG with a memo, saturating
just past the bound) and declines anything over `MAX_TREE_NODES` =
16384. The interpreter runs it. Every caller goes through `try_compile`,
including `compile_specialised` on the specialised term, and
`specialise.rs` is already bounded in distinct nodes (§37). The bound is
about 20 times the largest term the corpus compiles (838 nodes), and the
whole JIT path costs about 0.4 s there.

`a_term_is_compiled_only_up_to_a_tree_size` pins the boundary: `\x.
t_13` is exactly 16384 nodes and compiles, and `\x. t_14` doesn't.
`t_200` is counted without overflow. `a_term_too_big_as_a_tree_is_interpreted`
calls the JIT on `\x. t_16`: it is interpreted and agrees with `eval`,
in 0.06 s. Without the gate it compiles, in 5.3 s (debug build), and
both tests fail.

**What it doesn't fix.** `eval` walks the tree too, so such a term is
still exponential to run. The gate only stops the compiler costing
far more than the run. §48 times each stage: the kernel, not the IR, is
most of the cost.

## 48. Where a shared term's JIT cost goes: mostly the kernel, and a lost pointer cache

§47 put a tree-size gate on `try_compile` rather than sharing in the IR,
on the grounds that compilation was a small part of the cost. This
section times each stage separately, to see what sharing everywhere
would take. The term is again `\x. t_d` with `t_{i+1} = t_i + t_i`
(release build, one run each):

| `d` | WAT | compile | typing | wasmtime | `eval` battery | prove |
|---|---|---|---|---|---|---|
| 7 | 4 KB | 0.3 ms | 0.02 ms | 2.7 ms | 0.1 ms | 1.2 ms |
| 9 | 17 KB | 0.5 ms | 0.01 ms | 0.7 ms | 0.2 ms | 4.5 ms |
| 11 | 68 KB | 2.0 ms | 0.01 ms | 2.1 ms | 0.9 ms | 24.5 ms |
| 13 | 272 KB | 6.4 ms | 0.02 ms | 5.6 ms | 3.5 ms | 217 ms |

At `d = 13` the proof (`prove_pure_expr`) is 93% of the total, and it
grows faster than the tree: 8.8 times per two levels, where the tree
grows 4 times. Sharing in the IR would remove about 5% of the cost.

**Inside the proof.** `denote` builds the denotation in 3 ms. The kernel
does the rest: `infer` on the denotation takes 74 to 79 ms and
`check(refl d : Id(Int, d, d))` 221 to 258 ms (two runs). `check` infers
`d` and then runs `def_eq`, which normalises both sides of the `Id` in
full.

**A pointer cache that never hits.** `whnf` and `nf` already cache by
pointer (`ReductionCache`, keyed by `Rc` identity), so on a denotation
built with sharing they should be linear. They aren't. Built with each
level shared, `nf` still took 26 ms at `d = 13`, and `def_eq(e, e)` took
57 ms. The cause is `whnf_impl`'s stuck-application case:

```
other => app(other, (**a).clone()),
```

`app` wraps its argument in a new `Rc`, so the result's argument is a
new allocation. `nf` then recurses into it, misses the cache, and
normalises the whole subtree again, at every application. Reusing the
`Rc` (`Expr::App(Rc::new(other), a.clone())`) is the same term. As an
experiment, with that one line changed:

| | before | after |
|---|---|---|
| shared denotation, `nf` | 26 ms | 0.03 ms |
| shared denotation, `def_eq(e, e)` | 57 ms | 0.02 ms |
| today's unshared denotation, `check` | 221 ms | 60 ms |

The change was reverted at first, because it is in the trusted
kernel. It affects every proof, not just this term: any `nf` over an
application spine re-normalises its arguments. It landed in §49.

**What sharing end to end would take**, in order of payoff:

1. **The `whnf` fix above.** One line. It speeds up every proof, and
   makes `nf` and `def_eq` linear on a shared denotation.
2. **Memoise `denote` by term hash.** The pure fragment has no binders
   (parameters are postulates in the context), so a subterm's
   denotation depends only on its hash. This is outside the kernel, and
   untrusted.
3. **Memoise `infer`.** With 1 and 2, `infer` is the remaining tree walk
   (36 ms at `d = 13` on a shared denotation). Keyed by pointer and
   context, like `ReductionCache`, but inside `infer`, so it enlarges
   the trusted code. Soundness needs the same care as `ReductionCache`
   (the key keeps its `Rc` alive, so an address can't be reused).
4. **Sharing in the IR and the WAT** (§45's first option): compile and
   wasmtime, 12 ms at `d = 13`.
5. **Memoise `eval`** on pure subterms, as typing does (§45). This also
   speeds up the terms §47's gate hands to the interpreter.

Only 1 is small and pays off on every proof; 2 and 3 matter only for
terms with heavy sharing, which the corpus doesn't have. Until 2 to 5
are all done, some stage is still linear in the tree, so §47's gate
stays.

## 49. Keeping `whnf`'s arguments, and denoting shared subterms once

This does §48's first two steps.

**`whnf`.** Four places rebuilt an application from an argument they
already held as an `Rc`, copying it into a new one: the stuck case,
and the `J`, `WRec` and `SigRec` reductions. Each now reuses the `Rc`,
which gives the same term. §48 found the stuck case; the other three
are the same mistake, and the reduction results feed `whnf` again, so
they lose the cache the same way. `whnf_keeps_the_arguments_it_was_given`
checks pointer identity for all four, and each one-site reversion fails
it.

**`denote`.** It now memoises by term hash within one call. That is
exact, since the fragment has no binders: `classify` reads only the hash
and the parameter count, and the postulate lookups (`lit_ref`, `op_ref`,
`ite_ref`) are pure. `a_shared_subterm_is_denoted_once` checks that the
two operands of `a + a` share their children, and fails without the
memo.

**Effect.** `prove_pure_expr` on §48's `\x. t_13` went from 217 ms to
56 ms. It still doubles per level (0.7 s at `d = 16`, 11.5 s at 20),
because `infer` walks the tree, which is §48's step 3. On the benches,
an A/B against a saved baseline gave `straight_line_refl_proof` 29%
faster. Everything else was within noise. Re-running unchanged `HEAD`
against the same baseline moved benches by -13% to +34%, on a laptop
that slows over a run, so single percentages from one `cargo bench` on
this machine don't mean much. The full run's proof benches moved 5% to
50% faster, and the ones that moved slower include paths the change
doesn't touch, such as the interpreter.

§47's gate stays. `infer` is still a tree walk.

## 50. Design note: making the kernel's `infer` linear in the DAG

§48 and §49 left `infer` as the last tree walk on the proof path. This
note says what it would take, before any trusted code changes. Two
throwaway spikes (reverted) measured the options. Both use `\x. t_d`
from §48, with `denote`'s shared denotation.

**The spikes.**
- *Memo.* `infer` memoised on (address of the `Expr`, context length).
  That key is unsound in general, since the same node can be inferred
  under two contexts of the same length. It is exact for this term,
  which has one context.
- *Lazy substitution.* `subst_top(body, s)` returns `shift(body, 0, -1)`
  directly when `Var(0)` isn't free in `body`.

| `d` | neither | memo only | lazy `subst_top` only | both |
|---|---|---|---|---|
| 12 | not run | 3.5 to 4.7 ms | 3.0 ms | 0.13 ms |
| 16 | 0.7 s | 121 ms | 34 ms | 0.06 ms |
| 20 | 11.5 s | 2.25 s | 0.64 s | 0.08 ms |

Each cell is `infer` on the denotation, except the "neither" column,
which is §49's whole `prove_pure_expr`. Most of that is `infer`.

**Finding: the memo alone isn't enough.** With the memo on, `infer` made
only 67 calls at `d = 16` (32 hits), and still took 121 ms. The cost was
inside each call. `infer`'s `App` rule returns `subst_top(cod, a)`, and

```
fn subst_top(body: &Expr, s: &Expr) -> Expr {
    shift(&subst(body, 0, &shift(s, 0, 1)), 0, -1)
}
```

shifts the argument `s` in full before looking at `body`. For an
arithmetic operator `cod` is `Int`, which never mentions `Var(0)`, so
every application walks its whole argument, and `shift` has no cache
outside `with_shift_cache`. `subst`'s `Pi` and `Lam` cases do the same
once per binder they cross.

**Two changes, in order.**

*A. Lazy substitution in `subst_top`.* It has 22 callers in the kernel,
so fixing the shared function fixes all of them.
- A1, a guard: when `!is_var_free(body, 0)`, return
  `shift(body, 0, -1)`. That is equal to the old result, since `subst`
  is the identity when the variable is absent. It costs one extra walk
  of `body`, which is a type and usually small.
  - Pros: three lines, and obviously equal.
  - Cons: a dependent `body` still shifts `s` eagerly.
- A2, a fused `instantiate(body, s, depth)`: one pass over `body`.
  `Var(depth)` becomes `shift(s, 0, depth)`, higher indices drop by
  one, and `s` is shifted only where it is used. At depth 0 the shift is
  the identity.
  - Pros: never walks `s` unless it's substituted, including under
    binders.
  - Cons: a new traversal over every `Expr` variant, with the same
    binder bookkeeping as `shift` and `subst` (about 60 lines of trusted
    code).

A alone makes `infer` linear in the tree, and applies to every proof
with a large argument, not only shared ones. **Recommendation: A1,**
checked against the old `subst_top` on random `Expr`s (differential
test) and by `kernel_fuzz` and `kernel_soundness_fuzz`. A2 only if a
dependent-`body` case shows up in a profile.

*B. Memoise `infer` by (node, context).* Only this makes `infer` linear
in the DAG, which matters only for terms with heavy sharing, and the
corpus has none.
- Key: `(PtrKey, context id)`. A `PtrKey` holds its `Rc`, so an address
  can't be reused within the call, as with `ReductionCache`. `infer` gets
  an `Rc` form for children (`infer_rc`), and the top-level `&Expr` isn't
  memoised.
- Context ids: interned per top-level call, as `typing.rs` does (§45).
  Id 0 is the caller's context. Entering a binder whose type is the
  `Rc` `a` gives `intern(parent id, PtrKey(a))`. Equal ids then mean the
  same sequence of binder types, which is what `infer`'s result depends
  on. Keying on context length would be wrong: the same `body` under
  `Lam(A, _)` and `Lam(B, _)` has two types.
- Scope: one cache per public `infer`/`check` call, passed explicitly
  through private `infer_in`/`check_in` (and `infer_sigma`, `infer_pair`,
  `infer_sigrec`, `infer_sup`). This follows `def_eq`'s `ReductionCache`,
  not `with_shift_cache`'s thread-local, because hidden state is worse in
  trusted code than a wider signature.
- What's stored: only `Ok` results (an error ends the check), and only
  for nodes with `Rc::strong_count > 1`. A node reached twice has either
  that or a shared ancestor, which is memoised instead, so this keeps
  every walk linear. It also skips the hash-map cost on unshared terms,
  the common case, where `with_shift_cache` measured a regression when
  engaged unconditionally (see `with_shift_cache`'s doc).
- Optional: share one `ReductionCache` across the call's `def_eq`s.
  Reduction doesn't read the context, so this is sound.
- Why it's exact: `infer` is a pure function of the node's content and
  the context's content. Both are immutable behind the keys, which keep
  them alive.
- Tests:
  - a shared body under two different binder types (a length-keyed memo
    fails this);
  - on and off agree on every `kernel_fuzz` and `kernel_soundness_fuzz`
    term and every corpus proof, as `typing.rs`'s
    `the_memo_changes_no_answer` does;
  - a call-count bound on a shared term.
- Cost: about 60 lines of trusted code, and a signature change across
  `infer`'s helpers.

**Alternatives considered.**
- *Thread-local scope*, like `with_shift_cache`.
  - Pros: no signature changes.
  - Cons: hidden state in the kernel, and its nesting rules become part
    of what has to be trusted.
- *Hash-consing kernel `Expr`s.*
  - Pros: sharing everywhere, and `==` in O(1).
  - Cons: every constructor changes. By far the largest option.
- *Sharing in the proof term, not the kernel.* `denote` emits a
  beta-redex, `(\y: Int. y + y) a`, for a shared `a`. With A, the kernel
  checks `a` once and the body once, with no memo.
  - Pros: no trusted change beyond A.
  - Cons: the theorem's statement changes from `d` to a
    beta-equivalent `d'`. `denote` must choose where to bind. And `nf`
    would need A2, since beta-reduction substitutes `a` under the
    redex's own binder.

**Order.** A1 first: small, exact, and useful beyond sharing. Then B only
if sharing-heavy terms matter, and then together with sharing in the IR
and `eval` (§48's steps 4 and 5). Until all of those land, §47's gate is
what bounds a shared term's cost.

A1 landed in §51.

## 51. `subst_top` skips an argument its body doesn't use

This is §50's A1. `subst_top(body, s)` now returns `shift(body, 0, -1)`
when `Var(0)` isn't free in `body`, and only otherwise shifts `s` and
substitutes. The two agree, since `subst` is the identity on a body
without the variable. All 22 callers in the kernel get the change.

**Tests.**
- `subst_top_is_substituting_then_shifting` compares the new function
  with the old formula on 20000 random pairs of `Expr`s, covering every
  variant, with more than 2000 cases each where the body uses `Var(0)`
  and where it doesn't. It fails if the guard returns `body` unshifted,
  or if `shift` or `subst` is mutated in the `Pair` or `W` case.
- `subst_top_leaves_an_unused_argument_alone` substitutes a 20-level
  doubling tree into `Pi(Var(3), Var(4))`. That took 972 ms before
  and must now take under 50 ms.

**Effect.** `prove_pure_expr` on `\x. t_d` from §48 (release, one run
each):

| `d` | §49 | §51 |
|---|---|---|
| 13 | 56 ms | 9.4 ms |
| 16 | 0.7 s | 66.5 ms |
| 20 | 11.5 s | 1.07 s |

It still doubles per level, because `infer` walks the tree (§50's B).
On the benches, against a saved baseline of the parent commit:

| bench | before | after | noise re-run |
|---|---|---|---|
| `gcd_2_leaves` | 12.7 ms | 4.1 ms | 10.4 ms |
| `gcd_3_leaves` | 32.3 ms | 7.5 ms | 25.5 ms |
| `universal_x1` | 8.8 ms | 4.1 ms | 19.1 ms |
| `closure_typed_loop_carried_parameter_universal_proof` | 17.2 ms | 7.0 ms | 31.1 ms |

The last column re-runs the unchanged parent afterwards. The universal
proofs, which apply operators to large arguments, got 2 to 4 times
faster, well outside the noise. The microsecond benches moved by -43%
to +23%, while the noise run moved them by -25% to +73%, so they're
unchanged within what this laptop can resolve.

## 52. Where an instance proof's time goes: eager substitution, and a shift cache that no longer pays

`over_application_instance_proof` is the slowest proof bench after §51
(90 to 135 ms at `n = 4`). Timers around each stage of
`prove_tail_recursive_instance`, and counters inside the kernel, both
throwaway and reverted, give this for `n = 4` on the `If`-between-closures
term. The machine was shared with another session's build, so the
figures are rough, but the proportions held across runs.

| stage | time |
|---|---|
| `build_universal` (includes its own `check`) | 3 to 6 ms |
| `build_ev_witness` | 1 to 4 ms |
| `infer` on the applied instance proof | 65 to 80 ms |
| `whnf` of the inferred type | 44 to 51 ms |
| leaving `with_shift_cache` (dropping the cache) | 53 ms |

**The term isn't shared.** The applied proof has 9172 nodes as a tree and
8900 as a DAG, so §50's memo B wouldn't help. The kernel spends about
4 µs per node.

**`subst_top` on a dependent body is the cost.** With the shift cache
off, `subst_top` took 5.9 ms of `infer`'s 9 ms at `n = 1`, and did 80k of
its 87k `shift` node visits. The `whnf` of the type was three
`subst_top` calls with 43k shift visits between them. §51's guard
doesn't apply, since these bodies do use `Var(0)`. The eager path shifts
`s` once, again at every binder `subst` crosses, and then shifts the
whole result back by -1. `ctx_lookup` was small: 1205 lookups and 4.6k
shift visits.

**The shift cache is engaged here by mistake.** `instance_visit_count`
decides whether to use it. It returns "expensive" when it can't evaluate
a self-call argument concretely, and a closure application like these
self-call arguments can't be. So the cache is on even at `n = 1`, where
it doubles the time (44 ms against 20).

**Spike: A2, a fused `instantiate`.** A single pass over `body`:
`Var(d)` becomes `shift(s, 0, d)`, higher indices drop by one, and `s`
is shifted only where it's used. It passes
`subst_top_is_substituting_then_shifting`. `prove_tail_recursive_instance`
end to end:

| term, `n` | today (eager, cache on) | A2, cache off | A2, cache on |
|---|---|---|---|
| `If` between closures, 1 | 49 ms | 7.3 ms | 14 to 16 ms |
| `If` between closures, 4 | 191 to 195 ms | 15 to 20 ms | 29 to 33 ms |
| `If` between closures, 8 | 274 to 283 ms | 33 to 36 ms | 52 to 59 ms |
| PAP root, 4 | 109 to 122 ms | 16 to 17 ms | 20 to 22 ms |
| `fib`, 8 | 1.8 s | 90 to 98 ms | 214 ms |

The eager `fib(8)` with the cache off took 3.5 s, which is the 2x win
`with_shift_cache` was added for. It was recovering reshifts that the
eager substitution caused. With A2 those reshifts don't happen, and the
cache costs more to fill and drop than it saves on every term measured.

**Proposal (not landed, since it changes the trusted kernel).**
1. A2: replace `subst_top`'s eager path with `instantiate`, about 30
   lines mirroring `shift`. Checked by the existing differential test,
   `kernel_fuzz` and `kernel_soundness_fuzz`.
2. Then delete `with_shift_cache`, its thread-locals, `shift_rc`'s cache
   path, and `proof.rs`'s `instance_visit_count` and `VISIT_THRESHOLD`.
   That removes hidden state from the kernel. It needs the same
   measurements redone on the benches and `fib(30)`'s cold compile
   before it lands.

`subst` has no caller besides `subst_top` and the differential test's
reference formula, so it would move into the test module.

The first proposal landed in §53, the second in §54.

## 53. `subst_top` substitutes in one pass

This lands §52's first proposal (§50's A2). When `body` uses `Var(0)`,
`subst_top` now calls `instantiate(body, s, 0)`. Under `d` of `body`'s
binders, `Var(d)` becomes `shift(s, 0, d)`, higher indices drop by one,
and nothing else changes. So `s` is shifted once per use, not again at
every binder crossed and then in the result. `subst` had no other
caller, and moved into the test module as the reference formula.

**Tests.**
- `subst_top_is_substituting_then_shifting` (§51) now checks
  `instantiate` against the old formula on 20000 random pairs.
- `subst_top_shifts_a_used_argument_once` puts a 14-level doubling
  argument under 30 binders. It must take under 4 times one shift of the
  argument, plus 5 ms. Before the change it took 266 ms against 3 ms.
- Each of these mutations fails a test: `Var(d)` becoming `s` unshifted,
  higher indices not dropping, and a missing `d + 1` under `Pair`'s
  family, `WRec`'s children type or `Sigma`'s family.

**Effect.** fib(30)'s cold compile in `cargo run --release` took 40.6 ms,
where the README had about 140 ms. The full bench A/B ran while another
session's job held about 18 cores. Benches this change can't affect,
such as the interpreter and warm cache hits, came out 2 to 7 times
slower in the candidate run, so only large effects mean anything:

| bench | before | after |
|---|---|---|
| `over_application_instance_proof/if_between_closures_self_call_arg` | 230 ms | 27 ms |
| `over_application_instance_proof/pap_producing_root_self_call_arg` | 220 ms | 34 ms |
| `closure_typed_loop_carried_parameter_universal_proof` | 19.3 ms | 5.7 ms |
| `universal_proof_one_time_by_leaf_count/gcd_3_leaves` | 7.6 ms | 4.8 ms |

These agree with §52's spike. The shift cache is still in place; §54
removes it.

## 54. Removing the shift cache

This lands §52's second proposal. `kernel.rs` loses `with_shift_cache`,
its two thread-locals and `shift_rc`, so `shift` recurses directly.
`proof.rs` loses `instance_visit_count`, `VISIT_THRESHOLD` and the
closure `instance_from_scaffold` wrapped in the cache, and the tests
that exercised them. That is 325 lines deleted and 61 added, and the
kernel no longer has hidden state.

§10's cache was worth 2x on `fib(8)` because eager substitution
reshifted the same arguments. After §53, §52's spike measured the cache
as a net loss on every term tried (`fib(8)`: 214 ms with it, 90 to 98 ms
without), and it had been engaged by mistake on closure self-call
arguments.

**Measured against §53** (the full bench A/B, while another session's
job held most cores). The base run was the most contended of the three,
so each change is read against the noise column, the base's own re-run:

| bench | candidate | noise re-run |
|---|---|---|
| `over_application_instance_proof/if_between_closures_self_call_arg` | -46% | -31% |
| `over_application_instance_proof/pap_producing_root_self_call_arg` | -54% | -22% |
| `fib_30_non_tail_recursion/jit_cold_compile_and_verify` | -9% | -5% |
| `gcd_tail_recursion_to_loop/jit_cold_compile_and_verify` | -57% | +13% |

Nothing regressed beyond the noise. `closures_fragment_proof/
partial_application_non_capturing` read +295% once. Re-run alone, it
read -2%, while the base's own re-run jumped +213%. That bench never
engaged the cache. `fib(30)`'s cold compile in `cargo run --release` read
104 ms in this run and 40.6 ms in §53's, both single runs under load.
The bench's 79 ms against a base of 88 ms is the better number.

## 55. Where an instance proof's time goes after §53 and §54

A re-profile of the same two terms as §52, with throwaway counters and
timers in `kernel.rs` and `proof.rs` (reverted). These are the `fib(8)`
branching instance and the `if`-between-closures over-application at
`n = 4`. Another session's job held most cores, so treat the times as
rough. The call and node counts are exact.

| phase | `fib(8)` | `if`-between-closures |
|---|---|---|
| whole proof | 166 to 260 ms | 43 to 48 ms |
| `build_universal` | 13 to 21 ms | 4 to 5 ms |
| evaluating the witness | 32 to 40 ms | 4 to 18 ms |
| kernel `infer` | 110 to 193 ms | 16 to 36 ms |

Inside `fib(8)`'s `infer` (47.6k `infer` calls, context depth 48):
- **`def_eq`: 18,864 calls, 59 to 118 ms, about half of `infer`.** Each
  call builds a fresh `ReductionCache` and normalises both sides in full.
  - 17,951 of the calls (95%) get two syntactically equal sides. They
    still cost 11 to 12 ms of normalisation. The `==` pre-check that
    would skip it costs 2 to 3 ms over all calls.
  - The other 913 calls, where a real conversion is needed, take the
    rest: about 45 ms, or 50 us each.
  - Comparing the normal forms costs only about 1 ms in total.
- `subst_top`: 26k calls, 31 to 40 ms. `is_var_free` visits 235k nodes
  and `instantiate` 231k, so the guard's pre-pass doubles the walk of
  each body.
- `ctx_lookup`: 25k lookups shifting 48k nodes. `whnf` itself is
  negligible.

The `if`-between-closures term has the same shape at a smaller scale:
3,164 `def_eq` calls (3,013 equal, 151 not) take 7 to 8 ms of its
16 to 22 ms `infer`, and `subst_top` takes 3.5 ms.

**Where to go next** (each is a trusted-kernel change):
- *Equal sides first.* `def_eq` returns `true` when `a == b` before
  normalising. It's exact, since `nf` is a function, and saves the
  equal calls' normalisation: about 10 ms, or 15% of `def_eq`, here.
  A pointer check first would make most of the `==` free too.
- *The 913 real conversions.* These dominate, and each normalises both
  sides in full. Options are one `ReductionCache` shared across a
  top-level `infer`'s `def_eq`s (§50 B notes it's sound, since reduction
  doesn't read the context), or a lazy check that compares weak head
  normal forms and recurses only into arguments that differ. Neither has
  been measured.
- *Fuse `is_var_free` into `instantiate`.* One walk instead of two, by
  returning whether the variable was seen, and reusing the original
  node when it wasn't. At most about a third of `subst_top`'s time.

## 56. `def_eq` answers equal sides without normalising

This lands §55's first proposal: `def_eq` returns `true` when its sides
are the same pointer or syntactically equal (`==`), before building a
`ReductionCache` and normalising either side.

**Survey.** Every mature kernel does this first.
- Lean 4's `is_def_eq_core` starts with `quick_is_def_eq`: pointer
  equality (`is_eqp`), then a union-find cache of pairs already proved
  equal. Hash-consing makes its structural `==` cheap too.
- Coq's `gen_conv` tries `eq_constr_univs` (syntactic, up to universes)
  before calling the lazy conversion machine.
- Agda's `compareTerm` runs `checkSyntacticEquality` first.

**Why it's exact.** `nf` is a function, so `a == b` implies
`nf(a) == nf(b)`. The only behaviour change is that `def_eq(t, t)` now
answers for a `t` with no normal form, where it used to loop. That is
reflexivity of definitional equality, which all three kernels above rely
on too.

**Options considered.**
- *Pointer check only.* Free, but `infer` passes freshly built types
  (from `subst_top` and `ctx_lookup`), so it almost never hits.
- *Structural `==`* (chosen, with the pointer check in front). `Expr`'s
  `==` already short-circuits on `Rc::ptr_eq` at every child, and stops
  at the first difference. §55 measured it at 2 to 3 ms over all 18.9k
  calls of `fib(8)`, against 11 to 12 ms of normalisation saved.

**Test.** `def_eq_answers_equal_sides_without_normalising`: two
separately built copies of `d (d (... (d x)))`, 14 deep, with
`d = \x. x x`. The normal form is 2^14 nodes as a tree. The test must
finish in 5 ms. It took 0.26 s with only the pointer check (the
mutation) and 6 s at 18 deep before the change.

**Measured against §55** (bench A/B, while another session's job held
most cores). A full `proofs` run was too noisy to read, so the benches
it flagged were run again on their own:

| bench | candidate | noise re-run |
|---|---|---|
| `over_application_instance_proof/if_between_closures_self_call_arg` | -49% | +31% |
| `over_application_instance_proof/pap_producing_root_self_call_arg` | -66% | -13% |
| `gcd_relational_scaling_vs_universal/universal_x1` | -18% | +21% |
| `universal_proof_one_time_by_leaf_count/gcd_2_leaves` (full run) | -65% | +9% |

The full run's +276% on `universal_x1` and +115 to +166% on the closure
fragments didn't reproduce. The closure fragments are too noisy under
this load to read either way.

## 57. `def_eq` compares weak head normal forms, not full normal forms

This lands §55's second proposal. `def_eq(a, b)` used to decide
`nf(a) == nf(b)` by building both normal forms. Now `conv` reduces each
side to weak head normal form, compares the outermost constructors, and
recurses into the children, trying §56's `==` shortcut at every level.
So a part both sides share is never normalised.

**Survey.** No mature kernel normalises both sides in full.
- Lean 4's `is_def_eq_core` takes `whnf_core` of both sides, unfolds
  definitions lazily (`lazy_delta_reduction`), and compares applications
  argument by argument (`is_def_eq_app`).
- Coq's kernel conversion is a lazy machine that compares head
  constructors and their stacks, reducing only as needed.
- Agda's `compareTerm` works on weak head normal forms and compares
  eliminations one at a time.
- In the literature this is Coquand's algorithm ("An algorithm for
  type-checking dependent types", 1996), later refined by Abel and
  Coquand for eta. Every variant compares heads and recurses.

**Why it's exact.** `nf_impl(e)` is `whnf(e)`'s outermost constructor
over the `nf` of each child. So `nf(a) == nf(b)` holds exactly when the
two weak head normal forms have the same constructor (and the same index,
for `Var` and `Sort`) and each pair of children has equal normal forms,
which is what `conv` checks recursively. It answers `false` early at the
first mismatch, and never reduces anything `nf` wouldn't. tatic has no
eta rule, so there's nothing beyond this to compare.

**Options measured** (throwaway spike, reverted). `kernel::check` of the
`fib` instance proofs, best of 5, under load:

| `def_eq` | `fib(8)` | reductions (`whnf` + `nf` calls) | `fib(12)` |
|---|---|---|---|
| §56 (full `nf`) | 173 ms | 118.6k + 41.6k | 1.73 s |
| `conv` | 75 ms | 39.5k + 0 | 0.81 s |
| full `nf`, one `ReductionCache` per `check` | 146 ms | 113.4k + 40.0k | 1.52 s |
| `conv`, one cache per `check` | 66 ms | 39.4k + 0 | 0.52 s |

A shared cache barely changes the work once `conv` is in (39.4k against
39.5k reductions), and it would need either a thread-local or a cache
threaded through every `infer` signature (§50's objection). So only
`conv` landed.

**Tests.**
- `def_eq_normalises_only_where_the_sides_differ`: two `Pi`s whose
  domains are separately built copies of §56's doubling term, and whose
  codomains differ by one redex. It must finish in 5 ms. It took 415 ms
  before.
- `def_eq_agrees_with_comparing_normal_forms`: 20,000 random pairs, half
  of them the same term with different redexes inserted (`with_redexes`),
  must agree with `nf(a) == nf(b)`.
- Mutations caught: `Var`s all equal, `Sigma`'s second child skipped,
  and children compared without reducing them.

**Measured.** The bench A/B was too noisy to read. The same bench swung
from -50% to +48% between two runs. So `kernel::check` was timed on the
two over-application instance proofs, alternating the old and new
`def_eq` in one process (best of 15): 14.8 to 10.0 ms and 10.9 to 7.4 ms.

**A cost `conv` shares with `nf`.** Trying `==` at every level walks a
term once per ancestor when the first difference is deep, so conversion
is quadratic in depth in the worst case. `nf` already was, for a
different reason. On a neutral application spine, `whnf` returns
`App(Rc::new(whnf(f)), a)`, a fresh `Rc` that the pointer-keyed
`ReductionCache` misses, so each level re-reduces the spine below it.
Two spines 1,000 deep that differ only at the head take 0.81 s with `nf`
and 0.95 s with `conv`. At 4,000 deep they take 28 s and 26 s. The
corpus's terms are nowhere near that deep, but a proof with a long
neutral spine would be.

## 58. `subst_top` drops its `is_var_free` guard

This is §55's third proposal. It turned out smaller than proposed: the
guard wasn't worth fusing, only deleting.

§51 added the guard to skip the old eager `subst_top`, which shifted
the argument in full before looking at the body. Since §53,
`instantiate` walks the body once and touches `s` only at a `Var(d)`.
With `Var(0)` absent, it gives exactly `shift(body, 0, -1)`, in one walk.
So the guard added a second walk, all of the body when the variable was
unused and a prefix when it was used, and saved nothing.
`subst_top_leaves_an_unused_argument_alone` still holds without it.

**Survey.** Kernels that avoid this walk cost differently:
- Lean 4 stores each node's loose-bound-variable range in the node, so
  `instantiate` skips any subterm with no loose variables in O(1). That
  changes every `Expr` constructor.
- Coq's `Constr.map` returns the original pointer when no child changed,
  so substitution keeps unchanged subterms shared. For tatic that would
  also help the pointer-keyed `ReductionCache` and `==`'s pointer
  shortcut.

**Measured** (throwaway spike, reverted). `kernel::check`, best of 9,
with the three versions alternating in one process:

| proof | guard | no guard | no guard, sharing kept |
|---|---|---|---|
| `fib(8)` instance | 56 ms | 55 ms | 54 ms |
| `fib(12)` instance | 406 ms | 428 ms | 403 ms |
| `if`-between-closures instance | 8.3 ms | 7.8 ms | 6.8 ms |

All within noise. After §57, substitution is no longer where these
proofs spend their time. Keeping sharing would cost about 40 lines of
trusted code for at most 10% on one proof, so only the deletion landed.
The bench A/B against §57 showed nothing beyond its noise column either.

## 59. `whnf` keeps a stuck term's own pointers

This fixes the quadratic cost §57 found. On a stuck application
`whnf_impl` returned `App(Rc::new(whnf(f)), a)`, with a fresh `Rc` for
the function part even when `f` was already stuck and unchanged. `nf`
and `conv` then asked for that fresh `Rc`'s weak head normal form, missed
the pointer-keyed `ReductionCache`, and walked the spine below it again,
once per level. `J`, `WRec` and `SigRec` on a stuck target did the same.

Measured in a debug build before the fix (the test build):

| depth | `nf` of a stuck left spine | `def_eq` on two left spines, differing at the head | `def_eq` on two right-nested chains, differing at the bottom |
|---|---|---|---|
| 500 | 0.40 s | 0.86 s | 50 ms |
| 1,000 | 2.4 s | 4.0 s | 109 ms |
| 2,000 | 11.0 s | 22.0 s | 398 ms |

**Survey.** Other kernels keep a term's pointer when reduction leaves it
alone.
- Lean 4's `update_app`, `update_binding` and friends return the
  original expression when every new child is pointer-equal to the old
  one, and `whnf_core` caches its results.
- Coq's `Constr.map` returns the original term when no child changed.
- Hash-consing makes the question moot, since equal terms share one
  allocation, but it changes every constructor (§50).

**The change.** A new `whnf_step` returns `None` when its argument is
already in weak head normal form. `whnf_rc` then returns the argument's
own `Rc`, and the stuck cases rebuild a node only when a child actually
changed. `ReductionCache.whnf` stores `Rc<Expr>`, and `nf_rc` gets the
weak head normal form through `whnf_rc`, so it's cached too. Reducing a
result again then returns the same pointer and hits the cache after the
first visit. A spike also cached each fresh result as its own weak head
normal form, which turned out to be redundant: no test or mutation could
tell it apart, so it was dropped.

**Tests.**
- `whnf_keeps_the_stuck_part_it_was_given`: for `App`, `J`, `WRec` and
  `SigRec`, the stuck head or target in the result is the same `Rc` it
  was given.
- `nf_and_def_eq_are_linear_on_a_stuck_spine`: `nf` of two 2,000-deep
  spines, one with a redex for its head, and `def_eq` between them, in
  under 500 ms in a debug build. It took 36 s before.
- Mutation caught: `whnf_rc` returning a copy of an unchanged term fails
  both tests (32 s). Copying only a newly reduced head costs O(1) per
  level, and no test catches it, rightly.

**Measured.** The proof benches didn't move beyond their noise column:
§57's inputs never had a deep stuck spine. The fix only matters for
terms that do.

**Left alone: `conv`'s `==` on right-nested chains.** The third column
above is a separate, smaller quadratic. `conv` tries `==` at every
level, and on `f (f (... x))` against `f (f (... y))` each level's `==`
walks down to the bottom again. It's 50 times cheaper than the `whnf`
one, and far outside the corpus's term depths.
- Lean 4 avoids it with a structural hash cached in every node, so `==`
  fails fast. That's a representation change.
- A smaller fix would remember, within one `def_eq` call, the pointer
  pairs `==` already found unequal. That's about 30 lines of trusted
  code.

Neither was built without a term that needs it. §61 later built a
third option: noting the pairs a failing `==` found unequal.

## 60. Where an instance proof's time goes after §56 to §59

A re-profile after §56 to §59, again with throwaway counters and timers
(reverted). The machine was idle this time, so the times are best of
three and fairly stable. The call and node counts are exact.

| phase | `fib(8)` | `fib(12)` | `if`-between-closures | partial-application root |
|---|---|---|---|---|
| whole proof | 51 to 53 ms | 378 to 423 ms | 8 ms | 6 ms |
| `build_universal` | 3 ms | 3 ms | 1.5 ms | 1.3 ms |
| evaluating the witness | 10 ms | 96 to 120 ms | 1.1 ms | 0.6 ms |
| kernel `infer` | 34 ms | 235 to 246 ms | 5 ms | 3.6 ms |
| dropping the witness memo | 5 to 7 ms | 52 ms | 0 | 0 |

The last two terms are the `if`-between-closures over-application and a
partial application at the root, both at `n = 4`.

Inside `fib(8)`'s `infer` (48.8k calls):
- `def_eq`: 19.6k calls, 7.6 ms. It was about half of `infer` in §55,
  and is now under a quarter.
- `subst_top`: 18.3k calls, 9 ms. `instantiate` visits about 14 nodes
  per call.
- `whnf`: 23k calls, 5 ms. `ctx_lookup`: 26k calls, 2 ms.
- The rest is `infer`'s own per-node work.

**Findings.**
- *No quadratic is left on these terms.* Every cost is a per-node
  constant times the proof's size. `fib(8)`'s proof has 53.5k nodes,
  about 800 for each of `fib`'s 67 calls. `fib(12)`'s is about 8 times
  larger, close to its 7 times as many calls, although the memo means
  only 13 distinct witnesses are built.
- *Spines are short.* The longest application spine `infer` meets has 6
  arguments, so batching `instantiate` across a spine wouldn't help.
- *The proof has almost no sharing.* Its tree has 53,524 nodes and its
  DAG 52,380, so an `infer` memo keyed by node (§50 B) would find almost
  nothing to reuse. The cause is in `build_ev_witness`, not the kernel.
  Its memo stores each sub-call's witness as an `Anchored`, and a memo
  hit returns `Anchored::at`, a `kernel::shift` copy at the current
  context depth. Each reuse is a fresh tree.
- *The same copies explain the unaccounted time.* Dropping the memo
  frees an unshifted second copy of every sub-witness. It's 11 to 14% of
  the whole proof for both `fib` terms.

**Where to go next.**
- *Keep the witness's sharing.* `Anchored::at` copies only because the
  context grows while the witness is built (`combinators.lit` adds
  literals). If every literal and combinator the witness needs were
  added before `build_ev_witness` starts, each memo entry would already
  be at the final depth, and a hit could return its `Rc` unchanged. That
  would remove the memo's copies and their drop, and give §50 B's memo
  real sharing to reuse. It's untrusted code, in `proof.rs`.
- *Per-node constants in `infer`.* These are now the bulk. There is no
  single hot spot, so any gain would come from many small ones.

## 61. `def_eq` remembers the pairs `==` found unequal

§59 left one quadratic in `conv`. It tries syntactic `==` before reducing
at every level, which is what lets it skip equal subterms (§56, §57).
On two right-nested chains `f (f (... x))` that differ only at the
bottom, every level's `==` fails, and each one walks down to the bottom
again. Two 8,000-deep chains took 23 s in a debug build.

**How other checkers avoid it.**
- *Lean 4* caches a structural hash in every `Expr` node, so `==` on
  unequal terms usually fails at the first hash. Its kernel also keeps a
  union-find of terms already proven equal, and a cache of pairs whose
  definitional equality failed.
- *Coq*'s conversion tests only physical (pointer) equality on
  subterms, not structural `==`, and compares reduced terms lazily on
  stacks. There is no repeated `==` walk, but also no skipping of equal
  subterms that aren't shared.
- *Agda* runs a syntactic check before conversion, but not at every
  level.

**Options.**
- *A. A structural hash in every node* (Lean).
  - Pros: `==` fails fast everywhere, not only in `def_eq`.
  - Cons: every constructor and pattern in the kernel changes. By far
    the largest option.
- *B. A hash per pointer, cached in `ReductionCache`.*
  - Pros: no representation change.
  - Cons: every node `def_eq` compares gets hashed and inserted, even
    when the sides are equal, which is 95% of calls from `infer` (§55).
- *C. Pointer equality only below the top* (Coq).
  - Pros: removes code.
  - Cons: equal subterms that aren't shared get reduced again, which
    undoes §57.
- *D. Note the pairs a failing `==` found unequal,* for the rest of one
  `def_eq` call.
  - Pros: no cost when the sides are equal. A failing `==` notes one
    pair per level on its failing path, and exactly those pairs are the
    ones `conv` recurses into next.
  - Cons: a set of pointer pairs in `ReductionCache`.

**Built: D.** `eq_noting` is `==` that inserts each unequal child pair
into `ReductionCache::unequal` on its way back up. `conv` uses it for
the top-level `==`. `conv_rc` skips `==` for a noted pair and otherwise
uses `eq_noting` too. Keys are `PtrKey`s, which hold their `Rc`s, so an
address can't be reused within the call. A noted pair is exactly one
that `==` would reject, so skipping it changes no answer.

The constructor match that `PartialEq`, `conv_whnf` and `eq_noting` all
need is now one function, `same_shape(x, y, c)`: same constructor and
index, then `c` on each pair of children. Each of the three passes its
own `c`.

**Tests.**
- `def_eq_is_linear_on_a_chain_that_differs_at_the_bottom`: the
  8,000-deep chains, under 500 ms in a debug build. It fails under
  either mutation: dropping `conv_rc`'s check of the set (36 s), or
  dropping the insert (30 s).
- `def_eq_agrees_with_comparing_normal_forms` (§57) still holds on its
  20k random pairs, and the kernel fuzzers pass.

**Measured.** Another session's job held the machine, and criterion's
noise column ran from -63% to several hundred percent, so the proof
benches' A/B says nothing either way. An interleaved spike (reverted)
toggled between the old and new `conv` in one binary and took the best
of 20 to 40 alternating rounds. The two non-tail instance proofs and
the `if`-between-closures instance proof were within 3% of the old
`conv`, in both directions across two runs. The fix costs nothing
measurable on the corpus, which has no deep chains.

## 62. The witness is built at one context depth, so memo hits share

§60 found that an instance proof has almost no sharing. `fib(8)`'s
proof had 53,524 nodes as a tree and 52,380 as a DAG, although
`build_ev_witness` memoises each call's witness. Postulates are
de Bruijn variables of the context, so a term built at one depth has to
be shifted wherever the context has grown since. The witness pushes its
postulates lazily: each concrete arithmetic fact is postulated the first
time `eval_and_prove` needs it. By the time a memo entry is reused, the
context has grown, so `Anchored::at` returned a shifted copy, and every
reuse was a fresh tree.

**How other checkers avoid it.** Lean and Coq refer to global constants
by name, so adding to the environment never shifts an existing term.
Here the postulates live in the local context, so any push does.

**Options.**
- *A. Postulates by name or by de Bruijn level.*
  - Pros: no push ever shifts anything, anywhere.
  - Cons: a new `Expr` variant, with rules in `infer`, `shift`,
    `instantiate` and `ctx_lookup`. A large change to the trusted kernel.
- *B. Build the witness twice*, keeping the second. The first build
  pushes every postulate, and the pushes are memoised (`fact_pos` and
  its siblings), so the second grows nothing.
  - Pros: a few lines, and exact.
  - Cons: the first build is the old, copying one, so the witness costs
    more than it does today.
- *C. A prepass over the call trace.* Walk the calls
  `build_ev_witness` will make, and run `eval_and_prove` on each
  condition and self-call argument, discarding the results.
  - Pros: it pushes through the same function that the build uses, so
    nothing about which facts are needed is duplicated. It costs one
    `eval_and_prove` per condition and argument of each distinct call,
    not a witness. A push it misses only costs sharing: `Anchored` still
    shifts correctly, and the kernel checks the result either way.
  - Cons: a second walk of the trace, which has to stay in step with
    `build_ev_witness`'s.

**Built: C.** `push_ev_facts` runs before `build_ev_witness` in
`instance_from_scaffold`. It is bounded by `WITNESS_NODE_BUDGET` like
the build. The leaf lookup and canonical params it shares with the
build are now `trace_leaf` and `canonical_params`. It's untrusted code:
the kernel checks the proof exactly as before.

**Result.** During the build, the context no longer grows, and memo hits
return the stored term unshifted, so they share. Two kinds of shift are
left: the scaffold's small `combines` terms, and `v` under
`params_and_close`'s binder (next paragraph).

| | before | after |
|---|---|---|
| `fib(8)` proof, DAG nodes | 52,380 | 13,942 |
| `fib(12)` proof, DAG nodes | 424,656 | 48,154 |
| `fib(8)` instance proof | 49.8 ms | 30.8 ms |
| `fib(12)` instance proof | 384 ms | 192 ms |
| `if`-between-closures instance proof, `n = 4` | 7.9 ms | 7.1 ms |

The times are best of 16 interleaved rounds of an in-process toggle
(reverted), on an idle machine. A criterion A/B was attempted too, but
another session's job started during it, and benches this change doesn't
touch moved by up to +749%. `kernel::infer` still walks the proof as
a tree, so what's saved is the shifting while the witness is built and
freeing those copies afterwards.

**What still copies.** Recasting each child's witness to the caller's
arguments builds `λ params. Ev(params, v)` with `params_and_close`, so
`v` is shifted under the binders. `v` is a shared DAG whose tree is
exponential (`v(n)` combines `v(n-1)` and `v(n-2)`), and `kernel::shift`
has no memo, so it returns a tree. That's why `fib(12)`'s DAG is still
3.4 times `fib(8)`'s rather than about 1.4 times. The kernel's
`instantiate` does the same when it substitutes a shared argument. A
shift that preserves sharing is the prerequisite for §50 B's `infer`
memo to make these proofs linear, and it belongs with that design.

**Test.** `a_fibonacci_instance_proof_shares_its_repeated_witnesses`
counts the proof's DAG nodes. It requires `fib(12)`'s to be under 4
times `fib(8)`'s. Without the prepass the ratio is 8.1, and the test
fails.

## 63. `infer` memoises shared nodes by (node, context id)

This builds §50's option B. §50 held it back because the corpus had no
sharing. §62 created some: `fib(12)`'s instance proof now has 48k DAG
nodes, but `infer` still walked it as a tree.

**How other checkers do it.** Lean 4's kernel caches inferred types by
expression. Its bound variables become named free variables when it
goes under a binder, so the context isn't part of the key. With
de Bruijn indices here, the same node under two different binders can
have two types, so the key needs the context too.

**Design** (as §50 set out):
- *Key:* `(PtrKey, context id)`. `PtrKey` holds the `Rc`, so an address
  isn't reused within the call.
- *Context ids:* 0 is the caller's context. Entering a binder whose type
  is the `Rc` `a` from context `cid` gives the id interned for
  `(cid, a)`, and the context pushed is `a`'s content. So equal ids mean
  equal binder sequences. `infer_pair` pushes an inferred type, not an
  `Rc` of the term, and takes a fresh id, which is always sound.
- *Scope:* one `InferCache` per public `infer` or `check` call, passed
  explicitly. The private `infer_rc`, `infer_node`, `check_rc` and the
  four out-of-line arms take `(ic, ctx, cid, e: &Rc<Expr>)`. The public
  functions wrap their `&Expr` in a new `Rc`, a shallow copy.
- *What's stored:* only successes, and only for nodes with
  `strong_count > 1`. A node referenced once is reached twice only
  through a shared ancestor, which is memoised instead. So unshared
  terms pay no hashing.
- *Not memoised:* `check`'s `Lam` rule, which checks a body against the
  expected codomain rather than inferring it. `def_eq` still runs at
  every occurrence, but its equal-sides fast path (§56) makes a repeat
  cheap.

**Why it's exact.** `infer` is a pure function of the node's content and
the context's content. Both are immutable behind the keys, which keep
them alive.

**Tests.**
- `infer_is_linear_in_the_dag_of_a_shared_term`: `d(k+1) = f d(k) d(k)`
  at depth 20, a million leaves as a tree, under 500 ms in a debug
  build. It took 4.8 s before, and 4.1 s with the memo disabled.
- `infer_memo_keeps_same_length_contexts_apart`: one `Pi` shared under
  binders `Type0` and `Type0 -> Type0`. The first is well typed and the
  second isn't. Keying on context length accepts the pair; the test
  catches that mutation.
- `infer_memo_changes_no_answer`: 20,000 random terms, 1,508 of them
  well typed, built from a pool of shared nodes. Each gets the same
  result, `Ok` or `Err` with the same message, as a copy with no sharing
  (`shift` by 1 and back), which the memo never engages on. It also
  fails under the length-keyed mutation.

**Measured.** An interleaved in-process toggle (reverted), best of 16
rounds, on an idle machine (CPU 3 to 6%):

| instance proof | memo off | memo on | change |
|---|---|---|---|
| `fib(8)` | 41.6 ms | 19.8 ms | -52% |
| `fib(12)` | 282 ms | 76 ms | -73% |
| `fib(16)` | 2.66 s | 0.55 s | -79% |
| `if`-between-closures, `n = 4` | 9.8 ms | 9.8 ms | 0% |
| partial-application root, `n = 4` | 8.0 ms | 7.6 ms | -5% |
| non-tail branching | 17 us | 18 us | +4% |

The unshared proofs don't move, as the `strong_count` filter intends.
With §62, `fib(12)`'s instance proof went from 384 ms to 76 ms.

**What's left.** `fib(16)` is still well over 7 times `fib(12)`. `v` is
still copied as a tree wherever it's shifted under a binder, both in
`params_and_close` (§62) and in the kernel's `instantiate`, since
`shift` has no memo. A `shift` that preserves sharing, memoised by
pointer within one call, is the next step.

## 64. Design note: constants, free parameters, and cached loose ranges

§50 to §63 each memoised one thing (`infer`, `def_eq`'s unequal pairs,
the witness) or worked around one copy (`Anchored`, `Params`, §62's
prepass). This note asks whether one change covers them all. It
measures two candidates with a throwaway spike, before any trusted code
changes. The design is in
`docs/superpowers/specs/2026-09-25-kernel-constants-and-loose-ranges-design.md`.

**The root cause.** Postulates are de Bruijn variables at the end of
the context, so every proof term has free variables. Whenever the
context grows under a term, the term is shifted, and `shift` and
`instantiate` rebuild every node they visit. So a DAG comes back as a
tree. Every memo so far has been a way to shift less often.

**How other checkers avoid it.**
- *Lean 4.* Globals are `Expr.const name levels`, looked up in the
  environment, so adding one shifts nothing. Every node caches an
  `Expr.Data` word holding its hash, its loose bound-variable range and
  some flags. `instantiate`, `liftLooseBVars` and `lowerLooseBVars`
  return a subterm unchanged, by pointer, when its range shows there is
  nothing to do. The kernel's type checker keeps its caches (`infer`,
  `whnf`, failures, an equivalence union-find) in one state for a whole
  declaration. Hash-consing (`ShareCommon`) is an opt-in pass, not part
  of the kernel.
- *Coq.* Globals are `Const` and `Ind` by kernel name, locals are `Rel`
  (de Bruijn). Nodes cache nothing. `Constr.map` returns the original
  term when no child changed, so a lift keeps sharing where it does
  nothing, but it still walks the term. It hash-conses each constant's
  body once, when it's added to the environment, since the environment
  keeps it. Nothing here keeps a proof
  term (the JIT stores only a `ProofStrength` per `Hash`), so that has
  no counterpart yet.
- *Agda and Idris 2.* Globals are `Def` or `Ref` by name, locals
  de Bruijn. None of them uses a variable for a global.

**The candidates.**
1. *Constants plus cached loose ranges* (Lean's pair). Postulates become
   `Expr::Const(level)`. Each heap node caches one more than its largest
   free `Var`, so `shift` and `instantiate` keep closed children by
   pointer.
2. *Hash-consing.* One global table, so equal terms are one node, and
   `==` is a pointer compare.
   - Pros: sharing everywhere, and `def_eq`'s equal-sides test in O(1).
   - Cons: a shift still copies, since the shifted term is a different
     term. Postulates still shift, so `Anchored` and the prepass stay. It
     needs a table every constructor goes through.
3. *One checker state for a whole check.* One `ReductionCache` shared
   by every `def_eq` and `whnf` inside a top-level `check`, alongside
   §63's `InferCache`.

**The spike** (a throwaway worktree).
- A kernel-local `Rc<T>` wrapping `std::rc::Rc<Node<T>>`, where
  `Node { loose: u32, val: T }`. It keeps every pattern and
  `Rc::new`/`ptr_eq`/`strong_count` compiling unchanged, so only four
  match arms outside the traversals needed a `Const` case.
- `shift` and `instantiate` return a child by pointer when
  `loose <= cutoff`.
- `Expr::Const(l)`, typed by `ctx[l]`, which must be closed.
  `Postulates::get` returns it for positions below the current binder
  scope's start, and `params_and_close` and the other two scopes record
  that start.
- Candidate 3 as a toggle: `InferCache` owns a `ReductionCache`, which
  its `def_eq` and `whnf` calls use.
- A cached structural hash, under a feature flag, to measure its size
  and cost.
- Scope parameters as levels too, as a toggle: `get` returns a `Const`
  for every position, each node also caches its largest level, and
  `close_pi`/`close_lam` turn the scope's levels into `Var`s, keeping
  children below the scope by pointer. This shares one level sequence
  between postulates and parameters, which the spec doesn't keep (below).

All 301 lib tests passed with loose ranges on. With constants on too, the
two that failed build contexts by hand with `Var` postulates, which the
spike's `Const` rule doesn't cover. Every proof test passed.

**Payoff.** `fib(n)`'s instance proof, proved and then re-checked by
`kernel::check`. Best of 3 interleaved in-process rounds. Another
session's job held 7 to 8.5 cores throughout, but the effects are 100×,
not percent.

| `fib(n)` | as today | loose ranges | constants | both |
|---|---|---|---|---|
| 8, prove + re-check | 55 ms | 50 ms | 52 ms | 14.0 ms |
| 12 | 226 ms | 194 ms | 253 ms | 15.6 ms |
| 16 | 1.90 s | 1.49 s | 1.78 s | 18.5 ms |
| 8, DAG nodes | 13,942 | 12,641 | 13,942 | 5,445 |
| 12 | 48,154 | 42,124 | 48,154 | 7,973 |
| 16 | 265,366 | 227,157 | 265,366 | 10,501 |

With both on, the DAG grows by 632 nodes per level of `n`, so it's
linear: 18,085 nodes at `fib(28)`, proved and re-checked in about
35 ms. Each half alone does little. Constants alone still leave `shift`
rebuilding what it walks. Loose ranges alone find almost nothing
closed, since every term mentions a postulate. A second run added the
one checker state (candidate 3). Alone it was slower at every size: +45%,
+26% and +6% at `fib(8)`, `fib(12)` and `fib(16)`. On top of both it was
14.3, 17.0 and 24.7 ms, against 14.0, 16.2 and 21.2 ms without it in the
same run.

**Overhead.**

`cargo bench --bench proofs`, best of 2 rounds, times in µs. *Wrapper*
is the kernel `Rc` with every fast path off, so it measures the cost of
the bigger node alone; *both* is loose ranges plus constants; *+ hash*
adds the cached structural hash. Another session's job loaded the CPU
through part of round 1 (up to 100% after `base` and `wrapper`), so
round 2 carries most of the weight, and differences under about 25% on
the sub-50 µs benches are noise.

| bench | today | wrapper | both | both + hash |
|---|---|---|---|---|
| `gcd_2_leaves` | 1,688 | 1,799 | 505 | 747 |
| `gcd_3_leaves` | 2,999 | 3,256 | 809 | 1,053 |
| `universal_x1` | 1,613 | 1,671 | 569 | 941 |
| `closure_typed_loop_carried_parameter_universal_proof` | 2,653 | 2,548 | 1,199 | 830 |
| `if_between_closures_self_call_arg` | 8,147 | 8,568 | 4,750 | 3,336 |
| `pap_producing_root_self_call_arg` | 6,940 | 9,026 | 5,187 | 2,613 |
| `relational_x10` | 118 | 111 | 99 | 206 |
| `straight_line_refl_proof` | 9.7 | 9.3 | 6.3 | 9.0 |

- The wrapper alone ranged from 10% faster to 42% slower across benches
  and rounds, median about +4%: within noise, so the 8 extra bytes per
  node don't show.
- Both together were 42% to 73% faster on the five proofs over 1 ms, in
  both rounds, and 19% to 25% faster on `pap_producing_root`. No proof
  got slower.
- The hash was mixed: faster than without it on the closure proofs,
  slower on the `gcd` ones and 2× slower on `relational_x10`. With no
  consumer, that's cost and noise, not payoff.

**Parameters as levels too.** With constants alone, the parameters of
`params_and_close` and the other builder scopes are still `Var`s, so
`Params` and `Anchored` stay. The spike's toggle asked whether they can be
levels as well. That is Isabelle's `Const`/`Free`/`Bound` split and Lean's
`const`/`fvar`/`bvar`: McBride and McKinna's free variables by name and
bound ones by index, the locally nameless representation of Charguéraud
and of Aydemir et al., and Kovács's levels for contexts and indices for
syntax.
- No kernel `check` or `infer` ran while a builder scope was open, across
  every `proof::` test, including the debug-only `debug_assert_has_type`
  calls. Every push inside a scope was a local (parameters, the `v`, `e`,
  motive and ih binders, and `push_path`'s premises), never a lazy
  global. So the kernel only ever has to type globals.
- Closing a scope rebuilt 791 to 911 nodes per `fib` proof and kept 334
  to 414 children by pointer, nearly flat in `n`. The builder's own shift
  work fell from 625, 833 and 1,145 nodes to 204, 412 and 724 at
  `fib(8, 16, 28)`. The kernel's stays at 2.6k to 4k, since its binders
  are unchanged.
- 300 of 301 lib tests passed; the other builds `Var` postulates by hand.
- On `fib(8, 16, 28)`, proving and re-checking took the same time as with
  constants alone, within noise.

On the universal proofs it cost nothing measurable either. The table
shows `cargo bench --bench proofs` in µs, as the best of 3 interleaved
rounds on a mostly idle machine (CPU at 1% to 17% around almost every run).
The same config still varied up to 3× between rounds, so best-of is the
only fair summary. An earlier, noisier run seemed to show parameters as
levels 7% to 85% slower, but that didn't reproduce.

| bench | constants | + parameters as levels |
|---|---|---|
| `gcd_2_leaves` | 482 | 489 |
| `gcd_3_leaves` | 811 | 802 |
| `universal_x1` | 495 | 498 |
| `closure_typed_loop_carried_parameter_universal_proof` | 685 | 699 |
| `if_between_closures_self_call_arg` | 2,918 | 2,825 |
| `pap_producing_root_self_call_arg` | 2,176 | 2,176 |

Counting explains why. Closing scopes rebuilt 615 nodes for `gcd`'s
universal proof and 839 for `fib(16)`. The kernel's `instantiate`
rebuilt 3,547 and 34,804 in the same runs. Meanwhile the builder's own
shifting fell from 274 nodes to 4, and from 833 to 412.

The same runs tried Lean's traversal memo. `replace_rec_fn`, which every
`instantiate`, `lift_loose_bvars` and `abstract` in Lean's kernel goes
through, maps (node, binder offset) to its result for nodes with a
refcount above 1, so a shared subterm that mentions the variables being
replaced is rebuilt once and stays shared. Here it was idle. With
constants alone it found 0 hits in 375 lookups (`gcd`) and 5,605
(`fib(16)`); with parameters as levels, 10 in 402 and 59 in 5,760. A
shared node is almost never reached twice in one traversal, and its
timings matched the runs without it.

One shared level sequence works for the corpus, but only because of the
two facts in the first bullet, which nothing enforces: a leaked
parameter would be one more context entry, so an unproven axiom. The
spec keeps two spaces instead. `Free(l)` levels come from a counter that
never reuses one, and the kernel rejects `Free` in `infer` and `check`,
so a leaked parameter is a failed check. Globals are then never
truncated, so a lazy global inside a scope is safe, and the priming that
prevents one can go.

**Allocation.** The spike keeps `Rc`. The alternatives, for a workload
whose proofs are built, checked once and dropped, on one thread, with
memos keyed by node identity:
- *`Rc` with no weak count.* Lean's object header is 8 bytes (a 32-bit
  count plus tag fields), against `std::rc::Rc`'s 16, and nothing here
  uses weak references. That would bring a node back to today's 64
  bytes with both ranges. The cost is hand-written `unsafe` refcounting
  in the trusted kernel, or a dependency (`triomphe` does this for
  `Arc`).
- *`Arc`.* Only for parallel checking. Otherwise it's atomic updates on
  every clone and drop for nothing.
- *A per-check arena of 32-bit ids, hash-consed.* This is nanoda_lib, a
  Lean 4 checker in Rust. Expressions live in an `IndexSet`, so
  allocating one interns it. A pointer's top bit says whether it
  indexes the persistent export-file arena or the arena of the
  declaration being checked, which is dropped once the declaration
  passes. `alloc_expr` looks in the persistent arena first. Each node
  caches `num_loose_bvars` and `has_fvars`, instantiation and
  abstraction keep `(expr, offset)` caches, and unique free variables
  come from a counter that never goes back. Here it would halve `Expr`
  (4-byte children), drop refcounting and the deep-drop machinery, and
  make `==` an id compare and ids free memo keys. The costs:
  - every constructor and pattern goes through a context, across the
    kernel and all of `proof.rs`;
  - garbage stays until the arena is dropped;
  - every allocation is hashed, which the spike's cached hash measured
    as mixed;
  - an id used with the wrong arena silently names a different term.
- *A bump arena with `&'a Expr<'a>` children,* as rustc's `TyCtxt`
  interns types. Lifetimes would reach every proof record and the JIT.
- *A tracing GC,* as Rocq, Agda and Isabelle get from OCaml, GHC and
  Poly/ML. In Rust it's slower than `Rc` and buys nothing, since terms
  have no cycles.
- *A faster global allocator* (mimalloc). It's one line and independent
  of all of the above, but it also changes the allocator under wasmtime.
  Measured in §66: it halves every proof bench.

The kernel `Rc` wrapper puts every allocation behind one type, so the
first and last of these stay local changes later. The arena is the
principled long-term alternative: it gives hash-consing, stable ids for
a proof cache, and free-all together. It isn't needed for linearity.

**Recommendation.** Build the two-space design, in the four stages the
spec sets out: loose ranges, then `Const` and `Free` in the kernel, then
the builder using them, then removing what no longer pays (§62's
prepass, `Anchored`, the priming). Don't build candidate 3, the cached
hash or the traversal memo: none has a measured payoff yet, and the hash
costs 8 bytes on every node. Candidate 2 isn't needed for linearity. What it would still add is O(1)
equality between separately built equal terms, and nothing in the
current profile asks for that.

## 65. Nodes cache their loose-variable range

This builds stage 1 of §64: cached loose ranges, without constants.

**What changed** (`src/kernel.rs`).
- Every child of an `Expr` is a kernel `Rc`: `std::rc::Rc<Node<T>>`,
  where `Node { loose: u32, val: T }`. `Rc::new`, `ptr_eq`,
  `strong_count`, `as_ptr` and every pattern keep compiling, so only
  `proof.rs`'s two test uses of `Rc` on kernel nodes changed.
- `loose` is `loose_of(e)`: one more than the largest loose `Var` index,
  0 when closed, computed from the children's cached ranges when the node
  is built. It saturates, so it's exact only below `u32::MAX`, which no
  real term reaches.
- `shift`, `instantiate` and `is_var_free` return early when
  `loose_of(e)` is at or below the cutoff or depth. `shift` and
  `instantiate` also keep each such child by pointer (`shift_child`, and
  `instantiate`'s `go`), rather than rebuilding it.
- A heap node grows from 64 to 72 bytes: the `u32` plus padding.
- `shift_sigma_family` stayed. The spec said it goes once `shift`'s arms
  are one line each. But its reason, at `infer_sigma`, is only that
  smaller hot frames cost nothing, and that still holds.

**Measured.** `scripts/bench_ab.sh 417e2fd --bench proofs`, 3 rounds,
CPU 4 to 9% around every run. Each round runs base, candidate, then base
again; *noise* is that rerun against base. Round 1's noise was -7 to -63%,
so it's unreliable. Round 2's noise was within ±8% except `relational_x1`
(+13%). Round 3's was wider, up to +36%. Times are best of 3, in µs.

| bench | base | stage 1 | change | noise, rounds 2 / 3 |
|---|---|---|---|---|
| `gcd_2_leaves` | 1,730 | 1,350 | -22% | -7% / -5% |
| `gcd_3_leaves` | 3,210 | 2,530 | -21% | +1% / -5% |
| `universal_x1` | 1,640 | 1,370 | -16% | +8% / -4% |
| `closure_typed_loop_carried_parameter_universal_proof` | 2,430 | 2,480 | +2% | -2% / +16% |
| `if_between_closures_self_call_arg` | 8,020 | 8,190 | +2% | -3% / +10% |
| `pap_producing_root_self_call_arg` | 5,980 | 5,720 | -4% | -6% / +6% |
| `relational_x10` | 111 | 116 | +4% | +7% / +22% |
| `relational_x5` | 60.1 | 57.5 | -4% | +6% / +1% |
| `non_tail_embedded_call` | 18.1 | 18.0 | -1% | -4% / +27% |
| `branching` | 18.0 | 18.4 | +2% | -8% / +15% |
| `partial_application_capturing` | 15.3 | 15.5 | +1% | -4% / +18% |
| `partial_application_non_capturing` | 13.1 | 13.7 | +5% | +1% / +36% |
| `gcd_relational_proof_single_call` | 11.9 | 10.9 | -8% | +1% / -4% |
| `non_capturing` | 10.9 | 10.3 | -6% | +1% / +1% |
| `relational_x1` | 9.9 | 9.1 | -8% | +13% / +1% |
| `capturing` | 9.7 | 9.9 | +2% | -2% / +8% |
| `straight_line_refl_proof` | 9.6 | 8.0 | -17% | +2% / -14% |

The three universal proofs are 16 to 22% faster, well past the noise.
Every other bench but one moved 8% or less, and none got measurably
slower. The exception, `straight_line_refl_proof`'s -17%, is noise: its
per-round change was +10%, +10% and -20%.

**`fib(16)`.** `fib16_instance_proof_cost`, 3 interleaved rounds against
the base worktree, best of 3:

| | base | stage 1 | change |
|---|---|---|---|
| build | 510 ms | 454 ms | -11% |
| check | 448 ms | 401 ms | -11% |
| DAG nodes | 265,366 | 227,157 | -14.4% |

The spec expected `check` to be about 20% faster; it's 11%. The plan
expected the DAG unchanged, but it shrank, the same in every round, to
exactly the spike's loose-ranges figure (§64). The builder in `proof.rs`
shifts through the kernel: `Anchored::at`, `kernel::arrow`, and direct
`kernel::shift` calls. Those used to rebuild every node. Now closed
subterms come back as the same allocation, and the probe's `dag_size`
counts allocations, so the built proof shares more.

**Where the spec's 20% went.** It never existed on an idle machine. The
spec took it from §64's payoff table (1.90 s to 1.49 s), measured while
another session held 7 to 8.5 cores (a lower bound: until the 25H2
upgrade on 2026-09-25, Windows undercounted per-process CPU time, so
every "held N cores" figure in this file is at least that). Rerun idle from the spike patch
(`docs/superpowers/spikes/2026-09-25-constants-and-loose-ranges.patch`,
applied to 9f250e5; `SPIKE=... cargo test --release --lib spike_fib -- --ignored`; best of 5, in-process), `fib(16)` goes from 785 ms to
690 ms prove plus re-check, 12%. Stage 1's probe in the same idle window,
best of 3, goes from 800 ms to 686 ms, 14% (build 417 to 365 ms, check
383 to 321 ms). So stage 1 matches the spike, and the load inflated the
spike's gain. The spike's node-visit counter shows why the gain is small:
`shift` still visits 1.84 million nodes, against 2.22 million, 17% fewer.
Nearly every term mentions a postulate as a `Var`, so almost nothing is
closed. Constants (stage 2) are what make terms closed; with both, §64
measured the DAG at 10,501 nodes.

**Tests.** Each was checked against a mutation, then reverted.
- `loose_matches_a_walk`: 20,000 random terms; the cached range equals a
  walk. It caught `loose_of` without the `-1` under `Pi`/`Lam`/`W`/`Sigma`,
  and with `l` for `u` on `Pair`'s `fam` and on `WRec`'s `children_ty`.
- `shift_and_instantiate_match_a_reference`: 20,000 random terms. `shift`
  (by 1, 2 and -1), `instantiate` and `is_var_free` agree with the pre-§64
  versions, kept in the test module. It caught `<= cutoff + 1` in
  `shift_child` and in `shift`'s early return, `<= d + 1` in
  `instantiate`, `<= idx + 1` in `is_var_free`, and `shift_sigma_family`'s
  `Pair` arm shifting `fam` at `cutoff`. The -1 cases, added after review,
  also catch, on their own, a `shift` that returns early for any negative
  amount (the shift-up-and-back round trip already caught it).
- `shift_keeps_closed_children_by_pointer`: caught `shift_child` always
  rebuilding.
- `dropping_a_deep_term_does_not_overflow_the_stack`: drops a 100,000-deep
  `refl` chain on a 1 MB thread. It aborts when the wrapper's
  `strong_count` is one too high, since `Drop for Expr` then never frees a
  child on a fresh segment. `check_survives_a_term_far_deeper_than_the_native_stack_allows`
  passed under that mutation: its 1,000-deep terms drop fine by plain
  recursion.
- `infer_memo_changes_no_answer` built its unshared copy by shifting up
  and back, which now keeps closed subterms. It copies with the reference
  `shift` instead, asserts that the copy shares nothing, and still catches
  §63's length-keyed mutation.

**What's left.** Stages 2 to 4 of §64: `Const` and `Free` in the kernel,
the builder using them, then removing what no longer pays.

## 66. An idle re-baseline, and mimalloc

Both measured 2026-09-25, 18:04 to 19:21, with Defender's real-time
protection off (it had been on through §65's runs; the log shows it
turned off at 17:20 and has no record of when it turned on) and, from
re-baseline round 2 on, total CPU sampled every 10 s. Each is 3 rounds of `scripts/bench_ab.sh
--bench proofs`, best of the rounds per bench, then 3 interleaved rounds
of `fib16_instance_proof_cost`. The machine wasn't idle throughout: a
game and other sessions' jobs held the CPU at 14 to 90% through
re-baseline round 3 and mimalloc round 1 (round 1 of the re-baseline ran
before sampling began), and those rounds' noise
columns (base rerun against base) reach -63%. Mimalloc rounds 2 and 3
were quiet, with noise within -19% to +11%, and only they are used
below.

**Stage 1 against 417e2fd, again.** Best of 3, candidate against base:
`gcd_2_leaves` and `gcd_3_leaves` -28% and -29%,
`closure_typed_loop_carried_parameter_universal_proof` -24%,
`pap_producing_root` -21%, the closure fragment and non-tail proofs -11%
to -18%, and the rest within ±5% except `relational_x10`, +21%. That
one was +4% in §65 and its per-round changes swing from -37% to +31%, so
it's unresolved, not a regression shown. The `fib(16)` probe ran
contended (16 to 34% CPU): build +4%, check -6%, against -12% and -16%
in §65's idle rerun. The same unchanged code's `fib(16)` build ranged
from 297 to 414 ms across the evening, so these single-probe numbers
move by 30% with the machine's state.

**mimalloc.** The `mimalloc` crate (0.1.52) as `#[global_allocator]` in
`benches/proofs.rs` and, under `cfg(test)`, in `src/lib.rs`, against
HEAD (bdacb39) with the system allocator. The shipped binary was left
alone. Best of rounds 2 and 3:

| bench | system | mimalloc | change |
|---|---|---|---|
| `straight_line_refl_proof` | 7.8 µs | 4.3 µs | -45% |
| `gcd_relational_proof_single_call` | 10.7 µs | 5.7 µs | -47% |
| `gcd_2_leaves` | 1.24 ms | 0.63 ms | -49% |
| `gcd_3_leaves` | 2.36 ms | 1.16 ms | -51% |
| `relational_x10` | 101.7 µs | 55.0 µs | -46% |
| `universal_x1` | 1.38 ms | 0.67 ms | -52% |
| closure fragment proofs (4) | 8.2 to 13.9 µs | 4.1 to 7.9 µs | -43 to -50% |
| `closure_typed_loop_carried_parameter_universal_proof` | 1.79 ms | 1.07 ms | -40% |
| `if_between_closures_self_call_arg` | 5.82 ms | 3.59 ms | -38% |
| `pap_producing_root_self_call_arg` | 4.47 ms | 2.62 ms | -41% |
| non-tail proofs (2) | 14.9 to 15.2 µs | 8.4 to 8.5 µs | -44% |

`fib(16)`, 3 quiet rounds (CPU 1 to 3% before each): build 297 to
150 ms (-49%), check 256 to 144 ms (-44%), best of 3.

Every proof bench roughly halves, far past the noise, and the effect is
uniform across them, as an allocator's should be: the kernel's cost is
dominated by allocating and freeing nodes. That's three to four times what
stage 1 bought, from one dependency. It says nothing yet about the rest
of the program: the JIT (Cranelift, which also allocates heavily) and
wasmtime would run on it too once it's set in `main.rs`, and neither
was measured. `libmimalloc-sys` compiles C through `cc`, which the
build already uses.

**Measuring through contention (2026-09-26).** Another session's
selfplay jobs run back to back, about 40 s each with 15 s gaps, so a
quiet check before a run passes in a gap and the run lands in the next
job; the first attempt at the runs below ran at a median 88% CPU. The
runner used here (`scripts/quiet_ab/`) samples total CPU every 2 s alongside the runs,
alternates A and B in ABBA order, and keeps a pair only if both runs saw
no selfplay process and averaged under 20% CPU from other processes.
Defender's real-time protection was off throughout. "Other processes" is
the total minus the run's own CPU: for the benches, which run for
minutes, from sampling the bench process; for the demo and probes, which
run for about a second, from the process's exact CPU time at exit. The
first cut of the runner looked only at samples wholly inside a run,
found none for a 1 s run, and so kept no demo runs at all. Per-process
counters can't stand in for the subtraction: a non-elevated
`Get-Process` reads no CPU time for 129 of 348 processes (services), and
the `\Process(*)` counters, which do read them, still accounted for only
86% of the machine. The rest is processes that start and exit between
samples, such as other sessions' shell commands and our own short runs.

**`relational_x10`, settled.** 5 clean pairs of the proofs bench, 417e2fd
against HEAD (stage 1), other processes at 5 to 17%:

| bench | best | median |
|---|---|---|
| `relational_x1` | +0.8% | +0.5% |
| `relational_x5` | -2.1% | +1.4% |
| `relational_x10` | -0.4% | +7.1% |
| `universal_x1` | -9.9% | -10.4% |

`relational_x10`'s median comes from one +17% pair; its best is
unchanged, and the base alone spread 13 to 24% across its own rounds.
Stage 1 costs nothing on the small proofs, and the +21% above was
contention.

**mimalloc for the whole program.** The allocator is now set in
`src/main.rs`, `benches/execution.rs` and `benches/proofs.rs`; library
tests keep the system allocator. The execution bench, 3 clean pairs,
best of, mimalloc against system:
- the interpreter, -13 to -28% (`fib(30)` -13%, gcd -18%, factorial
  -15%, the closure benches -17 to -28%);
- `jit_cold_compile_and_verify` (Cranelift, wasmtime and the kernel
  check), -19 to -35%;
- `jit_warm_cache_hit`, within ±1%: compiled code barely allocates.

The demo binary (`cargo run --release`), 12 clean pairs, other
processes at 10 to 20%, best of: interpreted `fib(30)` 737 to 641 ms
(-13%), cold JIT 19.7 to 15.7 ms (-21%), warm JIT 4.37 to 4.38 ms. The
system allocator's own runs spread 10 to 19%. Peak memory was 17 MB with the system allocator and 19 MB with
mimalloc. Nothing measured got slower, so it's adopted.

**`fib(16)` baseline for stage 2.** Library tests now use mimalloc too
(`#[cfg(test)]` in `src/lib.rs`), so `fib16_instance_proof_cost`
measures the shipped allocator. At HEAD (stage 1), 10 clean pairs of the
same binary against itself (22 clean runs, other processes at 11 to
20%): build 128 ms best, 134 ms median; check 127 ms best, 139 ms median;
DAG 227,157 nodes every run. The slowest clean run was 24% (build) and
28% (check) above the best, so single `fib(16)` runs differing by less
than that say nothing; compare bests over many runs.

## 67. Stage 2: constants and free parameters in the kernel

This builds stage 2 of §64: the kernel learns `Const` and `Free`, and
nothing produces either yet, so every answer is unchanged.

**What was built** (`src/kernel.rs`).
- `Expr::Const(l)`: global `l`, typed by `globals[l]` as is. A closed
  type has nothing to shift, so a `Const` means the same thing at every
  depth, and `shift` and `instantiate` leave it alone.
- `Expr::Free(l)`: a builder parameter by level. It is neutral in
  `whnf`, `nf` and `def_eq` (it matches only itself), so the structural
  helpers still work on open terms, and it never type-checks.
- `Node` gains `free`, one more than the largest `Free` level (0 if
  none), cached like `loose`. It fills the padding stage 1 left, so a
  heap node stays 72 bytes (`a_node_is_56_bytes` pins the 56-byte
  `Node<Expr>`).
- `pub type Globals = im::Vector<Expr>`, with `infer_in(globals, ctx, e)`
  and `check_in(globals, ctx, e, expected)`. `infer` and `check` keep
  their signatures and pass no globals, so `proof.rs` didn't change.

**Three decisions, and why.**
1. *`Globals` beside `Ctx`, not `Ctx { globals, locals }`.* The spec
   asked for a struct and also for unchanged callers, and those conflict:
   `proof.rs` uses `Ctx` as an `im::Vector` (`len`, `truncate`,
   `close_pi`'s iteration, `Postulates::push`). A separate vector gives
   the same guarantee, that a `Const` can never resolve to a binder the
   kernel pushed, and touches no caller. Stage 3 moves `Postulates` to
   `Globals` and its check sites to `check_in`.
2. *An explicit `g: &Globals` parameter* on the seven typing functions,
   not a field on `InferCache`. The cache is a memo; the rules read as
   "Σ; Γ ⊢ e" with Σ visible.
3. *`Free` is rejected at the door, not only at the leaf.* `infer` doesn't
   visit every subterm: `check`'s `Lam` rule compares the domain by
   `def_eq`, `WRec`'s `children_ty` is only compared, and nothing infers
   the expected type. A `Free` under a redex in any of them would reduce
   away unseen. So `infer_in` and `check_in` reject `e` (and `expected`)
   when `free_of` is nonzero, which is O(1); `ctx_lookup` rejects a
   context entry with a `Free`; and a global whose type has a `Free` or a
   loose `Var` is rejected when used.

The environment has the same trust as the context: nothing checks that
an entry is a type, and a constant is an axiom. The kernel checks only
that a global's type is closed. It doesn't check that the constants it
names are earlier ones: `globals = [Const(0)]` types `Const(0) :
Const(0)`. Stage 3's `Postulates::push` must enforce the ordering, as
§64 says.

**Mutations.** Each new test failed on the mutation its step named,
except two, each for a reason:
- `beta_leaves_const_and_free_alone` has no reachable mutation: stage
  1's fast path (`loose == 0`) returns before `shift` or `instantiate`
  reach a leaf's arm. It pins the behaviour for a future refactor.
- Storing `free` as a `u64` doesn't compile, rather than failing
  `a_node_is_56_bytes`; either way it can't land.

Removing `infer_in`'s door first broke no test only for want of one:
`infer` hands an `App`'s argument (and `Id`'s sides, `J`'s fields) to
`check`, whose `Lam` rule compares the domain by `def_eq` and never
infers it, so a `Free` hidden under a redex there reduced away and
`infer_in` returned `Ok`. The final review found it;
`a_free_is_rejected_everywhere` now covers it, and the door is
load-bearing in both entry points.

**The fuzzers** (`tests/kernel_fuzz.rs`, `tests/kernel_soundness_fuzz.rs`).
- `kernel_fuzz` generates `Const`s in and just past a four-entry
  environment whose last entry is deliberately open, and `Free`s; any
  term with a `Free` must come back `Err`.
- The soundness fuzzer's constant form: with the context's seven
  postulates as globals and candidates free to name any constant, nothing
  proves `Id(A, a, b)`; and mutants of valid proofs with a `Free`
  spliced in never check.
- A differential: 20,000 candidates, random or mutants of valid proofs,
  check against a claim in constant form exactly when they check in the
  original. 898 checked and 19,102 were rejected, with no disagreement.
- Kernel mutations the fuzzers catch: `const_type` resolving from the
  wrong end (the differential), a `Free` accepted with the doors removed
  (both `made_free` and the spliced-`Free` test), and `same_shape`
  ignoring a `Const`'s index (the differential, and the constant-form
  soundness test, which found `@5` accepted as a proof of
  `Id @0 @2 @3`).

**Measured.** Stage 2 claims no speedup: it adds one `max` per
`Rc::new`, one parameter per typing frame, and the O(1) doors. Base is
331a7bd (stage 1 with mimalloc), head is 98b0e3e; both built once and run
interleaved with `scripts/quiet_ab/` (§66), Defender real-time
protection off throughout.

`fib16_instance_proof_cost`, 10 clean pairs of 12 rounds, other
processes at 13 to 20%:

| | base best | base median | head best | head median | change, best | change, median |
|---|---|---|---|---|---|---|
| build | 128.7 ms | 140.7 ms | 130.4 ms | 143.1 ms | +1.3% | +1.7% |
| check | 131.6 ms | 139.3 ms | 122.7 ms | 143.6 ms | -6.8% | +3.0% |

Each side's slowest clean run was 16 to 32% above its best, so every
change is noise. The DAG is 227,157 nodes in every run, as in §66.

The proof benches, 5 clean pairs of 6 rounds, other processes at 4 to
15%: every bench's best within -1.3 to +1.0%, and every median within
-3.5 to +2.4%. Each is inside that bench's own spread (1.3 to 27%).

Stage 2 costs nothing measurable, so stage 3 starts from the same
baseline.

Two runner fixes came out of this: `pin.ps1` now resolves a relative
exe path, which `Process.Start` couldn't find, and `ab.sh` refuses a
directory that already has a `runs.log`, whose old rounds would count
toward the new run.

**Open: `check_in` trusts its claim.** `check_in` never infers
`expected`, and `check`'s `Lam` rule only compares the lambda's
annotation with the Π's domain, never inferring it to a `Sort`. So
`check_in(λx:a. x, Π(x:a). a)` returns `Ok` with `a` a term, and so does
`check_in(a, (λz:@99. @0) a)`, whose claim names a constant that doesn't
exist; `infer_in` rejects both claims. It isn't a way to prove a false
well-formed claim, but a builder bug that produced a malformed claim
would be "proved". Every kernel we checked establishes both facts
(2026-09-26):
- Lean 4 (`src/kernel/environment.cpp`): `check_constant_val` runs
  `checker.check` on the declared type and then `ensure_sort`, before
  `add_theorem` or `add_definition` look at the value. Lean has no
  check-against-a-type rule: `check` is `infer_type_core(e, false)`, and
  `infer_lambda` runs `ensure_sort_core` on every binder domain when not
  infer-only.
- Coq/Rocq (`kernel/constant_typing.ml`, `infer_definition`):
  `Typeops.infer_type` on the declared type (it must be a sort), then
  `check_cast` of the body against it.
- Lean4Lean (`Lean4Lean/Environment.lean`, `checkConstantValBody`:
  `checkType v.type`, then `ensureSort`; `TypeChecker.lean`, `inferLambda`:
  `ensureSortCore` on each domain unless `inferOnly`) and nanoda_lib
  (`src/tc.rs`, `check_declar_info`: `infer(info.ty, Check)`, then
  `ensure_sort`; `infer_lambda`: `infer_sort_of(binder_type)` under
  `Check`) do the same.
- They keep it cheap with an infer-only mode: once a term is known
  well-typed, re-inferring its type skips these checks (nanoda_lib's
  `InferFlag::InferOnly`, used in `is_def_eq`'s helpers; Lean4Lean's
  `inferType` defaults to `inferOnly := true` for internal uses).
- The fix: `check_in` infers `expected` to a `Sort`, and the `Lam` rule
  infers its annotation to one. Both are trusted-kernel changes that
  could turn a proof that checks today into an error, so they need
  measuring and a go-ahead. Lean's 2026 postmortem lists a bug of the
  same kind, #14807 ("is_prop check not requiring a sort").
  Also, nanoda_lib gives locals de Bruijn *levels*
  (`mk_dbj_level`) while checking a binder's body, as stage 3's `Free`s
  will.

## Sources

- [I am not a number: I am a free variable (McBride and McKinna, Haskell Workshop 2004)](https://doi.org/10.1145/1017472.1017477)
- [The locally nameless representation (Charguéraud, JAR 2012)](https://doi.org/10.1007/s10817-011-9225-2)
- [Engineering formal metatheory (Aydemir et al., POPL 2008)](https://doi.org/10.1145/1328438.1328443)
- [Isabelle Pure `term.ML` (`Const`/`Free`/`Bound`, `loose_bnos`)](https://isabelle.in.tum.de/repos/isabelle/file/tip/src/Pure/term.ML)
- [Lean 4 `Expr.lean` (`Expr.Data`, `looseBVarRange`)](https://github.com/leanprover/lean4/blob/master/src/Lean/Expr.lean)
- [elaboration-zoo (Kovács)](https://github.com/AndrasKovacs/elaboration-zoo)
- [smalltt (Kovács)](https://github.com/AndrasKovacs/smalltt)
- [Lean 4 `replace_fn.cpp` (per-traversal cache on shared nodes)](https://github.com/leanprover/lean4/blob/master/src/kernel/replace_fn.cpp)
- [Rocq `safe_typing.ml` (hash-consing constant bodies)](https://github.com/rocq-prover/rocq/blob/master/kernel/safe_typing.ml)
- [nanoda_lib (a Lean 4 type checker in Rust; `src/util.rs`)](https://github.com/ammkrn/nanoda_lib)
- [mimalloc (Leijen, Zorn and de Moura; free-list sharding)](https://github.com/microsoft/mimalloc)
- [Kinds are calling conventions (Downen et al., ICFP 2020)](https://doi.org/10.1145/3408986)
- [Lean 4 IR checker (`Lean/Compiler/IR/Checker.lean`)](https://github.com/leanprover/lean4/blob/master/src/Lean/Compiler/IR/Checker.lean)
- [GHC #10181: Lint check for the arity invariant](https://gitlab.haskell.org/ghc/ghc/-/issues/10181)
- [rustc dev guide: MIR passes and validation](https://github.com/rust-lang/rustc-dev-guide/blob/main/src/mir/optimizations.md)
- [TIL: a type-directed optimizing compiler for ML (Tarditi et al., PLDI 1996)](https://dl.acm.org/doi/10.1145/249069.231414)
- [Implementing typed intermediate languages (Shao et al., ICFP 1998)](https://dl.acm.org/doi/10.1145/289423.289460)
- [A verified type system for CakeML (Tan, Owens and Kumar, IFL 2015)](https://dl.acm.org/doi/10.1145/2897336.2897344)
- [The de Bruijn criterion vs the LCF architecture (Paulson)](https://lawrencecpaulson.github.io/2022/01/05/LCF.html)
- [Lean4Lean: an external type checker for Lean 4 (Carneiro)](https://arxiv.org/abs/2403.14064)
- [Typed function references for WebAssembly](https://github.com/WebAssembly/function-references/blob/master/proposals/function-references/Overview.md)
- [wasmtime `Config`](https://docs.wasmtime.dev/api/wasmtime/struct.Config.html)
- [GC and exceptions in Wasmtime (Bytecode Alliance)](https://bytecodealliance.org/articles/wasmtime-gc)
- [Types are calling conventions (Bolingbroke and Peyton Jones, Haskell 2009)](https://dl.acm.org/doi/10.1145/1596638.1596640)
- [GHC Core Lint (compiler notes)](https://ghc-compiler-notes.readthedocs.io/en/latest/notes/compiler/coreSyn/CoreLint.hs.html)
- [The Glasgow Haskell Compiler (AOSA vol. 2, on Core and Lint)](https://aosabook.org/en/v2/ghc.html)
- [Deciding ML typability is complete for deterministic exponential time (Mairson, POPL 1990)](https://dl.acm.org/doi/10.1145/96709.96748)
- [Necula, Translation validation for an optimizing compiler (PLDI 2000, ACM)](https://dl.acm.org/doi/10.1145/349299.349314)
- [Making a faster curry with extensional types (Downen et al., Haskell 2019)](https://pauldownen.com/publications/eta.pdf)
- [Call Arity (Breitner, TFP 2014)](https://link.springer.com/chapter/10.1007/978-3-319-14675-1_3)
- [Flow-directed closure conversion for typed languages (Cejtin et al., ESOP 2000)](https://link.springer.com/chapter/10.1007/3-540-46425-5_4)
- [MLton ClosureConvert](http://www.mlton.org/guide/20201002/ClosureConvert)
- [A theory of type polymorphism in programming (Milner, JCSS 1978)](https://doi.org/10.1016/0022-0000(78)90014-4)
- [A syntactic approach to type soundness (Wright and Felleisen, Inf. Comput. 1994)](https://doi.org/10.1006/inco.1994.1093)
- [From System F to typed assembly language (Morrisett et al., TOPLAS 1999)](https://doi.org/10.1145/319301.319345)
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
- [stacker (crates.io)](https://crates.io/crates/stacker)
- [rustc `ensure_sufficient_stack`](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_data_structures/stack/fn.ensure_sufficient_stack.html)
- [Marlow & Peyton Jones, Making a fast curry: push/enter vs. eval/apply](https://simonmar.github.io/bib/papers/eval-apply.pdf)
- [GHC STG syntax (`GHC/Stg/Syntax.hs`)](https://github.com/ghc/ghc/blob/master/compiler/GHC/Stg/Syntax.hs)
- [Podlovics et al. 2020, GRIN](https://cyber.bibl.u-szeged.hu/index.php/actcybern/article/download/4101/4018)
- [Gibbon compiler pipeline (`Gibbon/Compiler.hs`)](https://github.com/iu-parfunc/gibbon/blob/main/gibbon-compiler/src/Gibbon/Compiler.hs)
- [Rideau & Leroy, Validating register allocation and spilling](https://xavierleroy.org/publi/validation-regalloc.pdf)
- [Tristan & Leroy, Verified validation of lazy code motion](https://jtristan.github.io/papers/pldi09.pdf)
- [The verified CakeML compiler backend](https://kar.kent.ac.uk/71304/1/paper.pdf)
- [CertiCoq-Wasm (CPP'25)](https://womeier.de/files/certicoqwasm-cpp25-paper.pdf)
- [Œuf: minimizing the Coq extraction TCB](https://homes.cs.washington.edu/~djg/papers/oeuf2018.pdf)
- [Necula, Translation validation for an optimizing compiler](https://people.eecs.berkeley.edu/~necula/Papers/tv_pldi00.pdf)
- [Myreen, decompilation into logic](https://www.cl.cam.ac.uk/~mom22/extensible-compilation.pdf)
- [Ullrich & de Moura, Counting immutable beans (Lean 4 IR, `fap`/`pap`/`ap`)](https://arxiv.org/abs/1908.05647)
- [Flambda 2 call kinds (`call_kind.mli`)](https://github.com/oxcaml/oxcaml/blob/main/middle_end/flambda2/terms/call_kind.mli)
- [wasm_of_ocaml closures (`gc_target.ml`)](https://github.com/ocsigen/js_of_ocaml/blob/master/compiler/lib-wasm/gc_target.ml)
- [CPS in Guile](https://www.gnu.org/software/guile/manual/html_node/CPS-in-Guile.html)
- [CPS in Hoot](https://wingolog.org/archives/2024/05/27/cps-in-hoot)
- [Crocus / VeriISLE: verified lowering rules](https://dl.acm.org/doi/10.1145/3617232.3624862)
- [Reduction strategy (Wikipedia)](https://en.wikipedia.org/wiki/Reduction_strategy)
- [Asperti, About the efficient reduction of lambda terms](https://arxiv.org/pdf/1701.04240)
- [Balabonski, Weak Optimality, and the Meaning of Sharing (ICFP 2013)](https://usr.lmf.cnrs.fr/~blsk/Publications/Balabonski-WeakOptimality-ICFP13.pdf)
- [Balabonski, A Unified Approach to Fully Lazy Sharing (POPL 2012)](https://public.lmf.cnrs.fr/~blsk/Publications/Balabonski-FullLaziness-POPL12.pdf)
- [Barenbaum & Bonelli, Optimality and the Linear Substitution Calculus (FSCD 2017)](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2017.9)
- [Asperti & Mairson, Parallel Beta Reduction Is Not Elementary Recursive](https://www.researchgate.net/publication/222245890_Parallel_Beta_Reduction_Is_Not_Elementary_Recursive)
