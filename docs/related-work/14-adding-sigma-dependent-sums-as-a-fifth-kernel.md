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

