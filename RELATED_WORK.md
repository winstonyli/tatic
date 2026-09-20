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
scope properly (see the "harden against the staleness-bug class" option
surveyed but not yet started) rather than assumed.

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
