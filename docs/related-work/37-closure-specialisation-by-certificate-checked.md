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
compiled runs. Before, the fuzz asserted `builder_bugs(BuilderBug::BadTrace) == 0`
without ever calling `compile_specialised`, so the assertion was vacuous.
A planted rejection in `compile_candidate` now fails it (645 failures),
and a planted `i64.add` -> `i64.sub` in `h'`'s WAT fails the compiled
comparison.

`compile.rs` covers the driver's two fallbacks. A trace the checker
rejects panics in debug and, in release, falls back to `h` and increments
`builder_bugs(BuilderBug::BadTrace)`. A checked `h'` that doesn't compile also falls back
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

