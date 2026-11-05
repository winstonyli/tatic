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

