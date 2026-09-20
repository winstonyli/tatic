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
top. This is the mathematically standard answer to exactly the problem
`build_universal`'s own `Ev` postulate (`src/proof.rs`) works around by
hand: a guarded-recursion-native kernel wouldn't need a bespoke
per-strategy recursor at all — the recursion would simply typecheck.
Adopting this would be a kernel-level (not proof.rs-level) change, well
outside anything scoped so far.

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
This new capability is **compile-time-only, with no kernel-checked proof
counterpart** — see `TYPES.md` §3.1/§6.3 for exactly why: `Γ`'s own
"one arity per variable" limitation is unchanged, and `denote_closure`'s
purely structural classification has no way to reason about a value
whose identity is only known by executing, not by term shape.

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
