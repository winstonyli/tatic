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
and its siblings, `resolve_closure_shape_to_leaf`, `build_ev_witness` --
all three deleted 2026-10-26, "CU3" --
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

