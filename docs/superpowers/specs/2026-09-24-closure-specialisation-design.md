---
status: done
---

# Closure specialisation by certificate-checked βv: design

Status: V3 implemented (RELATED_WORK.md §37); V1 and C open. It follows the
JIT IR design (`2026-09-23-jit-ir-design.md`, steps 1-4 implemented) and
closes that spec's future-work item "closure specialisation", V3 half only.

## Goal

Speed up closures that are known at compile time, by rewriting the source
term before it reaches the IR builder. The motivating case is
`partial_application_loop`, whose `caller (add acc) n` becomes `acc + n`. The
spike measured the hand-specialised form at 7.0-7.6x the current code
(RELATED_WORK.md §36).

Every rewrite is checked by a small independent checker. Nothing is taken on
trust from the rewriter.

## Decisions (and the options they beat)

- **Trust model: D, certificate-carrying specialiser; C later.** The
  specialiser emits `h'` plus a trace of steps. An independent checker
  replays the trace from `h` and must reach exactly `h'`. The options it
  beat:
  - A, a single trusted normaliser: too much trust in one piece of code.
  - B, an NbE-based normal-form checker: normalisation by evaluation has to
    track which terms are values, and it gives false rejections.
  - C, a kernel-proved `h ≡ h'`: planned as the upgrade, below.

  The same trace is meant to be the proof outline a later C builder
  consumes. RELATED_WORK.md §37 has the survey and the reasoning.
- **Scope: V3 only.** V3 is βv inlining of known closures. V1, hoisting a
  loop-invariant closure parameter out of the loop, is its own later step,
  as a second variant of the same step enum. It is worth 1.2-1.6x and has
  its own corner cases: nested `Rec`, partial self-application, and `f`
  used as a value.
- **Steps are addressed by redex hash and rewrite every occurrence.** The
  alternative was path-addressed steps. Hash addressing is sound because an
  equal subterm can be rewritten in any context. It gives shorter traces,
  paths that never go stale, and one congruence per step for C.
- **Evaluation stays strict.** Reconsidering lazy evaluation is parked; see
  the open questions.

## Semantics this must respect

`eval.rs` is strict: it evaluates `App`'s argument before the call. It can
fail with `DivByZero`, `TypeError`, `NotAFunction` or `UnboundVariable`, and
`Rec` has no fuel, so evaluation can diverge. Full β is therefore unsound:
`(\x. 0) (1/0)` fails, but its β-contraction `0` does not. The rewrite is
**βv**, `App(Abs(M), V) → M[0 := V]`, where V is a value:

- `Var` (bound: the source is closed, so every `Var` is bound by an
  enclosing binder). Every binder is bound to a value under strict
  evaluation. That covers an `Abs` parameter, `Rec`'s self-reference and a
  top-level parameter.
- `Lit`.
- `Abs`.
- `Rec`.

βv is an observational equivalence in the strict λv-calculus, and it is
closed under every context (Plotkin 1975). So it may be applied under
binders, inside `If` branches and inside a `Rec` body. A value evaluates in
no steps with no effect, so no error or divergence can appear or disappear.

`App(Rec(..), V)` is never a redex, because `Rec` is never unfolded.

**The checker requires a closed source** (amended in final review). An
unbound `Var` is not a value: `eval` starts from an empty environment, so
it evaluates to `Err(UnboundVariable)`. Contracting `(\x. 0) v5` to `0`
would then remove an error, and the JIT would install the result, because
its samples need not reach the redex and the universal proof is about
`h'`. The final review's probe was `\n. if n == 777 then (\x. 0) v5 else 1`.
Before the amendment the JIT returned `Ok(0)` at 777, where `eval` fails.
In a closed source every `Var` in every occurrence is bound by an
enclosing binder, and βv keeps a term closed, so every `Var` a step meets
is a value. `check` rejects an open source before replaying anything
("source term has free variables"). The specialiser returns the empty
trace for one, and for a source over `MAX_NODES`, since the checker
rejects both whatever the trace. The checker has its own free-variable
walk; it does not share the specialiser's.

## Architecture

```
compile_specialised(store, h):                          -- the one pipeline driver
  (h', trace) = specialise::specialise(store, h)        -- untrusted, private TermStore
  if trace is non-empty:
    spec_check::check(store, h, &trace, h')             -- trusted, independent
      Err -> SPEC_CHECK_FAILURES += 1; panic in debug; fall back to h
  try_compile(chosen store, chosen term)                -- unchanged: build -> ir::check -> decompile == chosen -> lower
    (if h' does not compile, try h)
```

The passes stay separate. `try_compile` is a pure translation, and its
contract ("every accepted module decompiles to the term it was given")
does not change. Specialisation is its own pass with its own certificate.
One driver composes them.

This was chosen over specialising inside `try_compile` during planning.
Existing `try_compile` tests deliberately build literal-lambda redexes to
exercise the closure machinery (`MakeClosure`, paps, allocation).
Specialising there would reduce those redexes away and silently weaken
what the tests cover.

- **`src/specialise.rs` (new, `pub mod`, untrusted).** `specialise(store: &TermStore, h: Hash) -> Specialised`,
  where `Specialised { store: TermStore, term: Hash, trace: Vec<Step> }`.
  - It copies what it needs into its own `TermStore`. Hashes are content
    hashes, so they agree across stores.
  - It returns `term == h` with an empty trace when nothing reduces.
- **`src/spec_check.rs` (new, `pub mod`, trusted).** `check(store: &TermStore, h: Hash, trace: &[Step], claimed: Hash) -> Result<(), CheckError>`,
  where `CheckError { step: usize, reason: &'static str }`.
  - It uses its own scratch `TermStore` and has its own `shift`, `subst`
    and `replace_all`, each memoised by `(Hash, depth)`, because hash-consed
    terms are DAGs.
  - Its independence allowlist permits only `crate::term` and `std`.
- **`Step` lives in `spec_check.rs`**, because the checker defines the
  certificate language and the specialiser depends on the checker, not the
  other way round:
  ```rust
  pub enum Step { BetaV { redex: Hash } }
  ```
- **The checker replays each step** as follows:
  1. `redex` occurs in the current term.
  2. It resolves to `App(f, a)` with `f = Abs(body)`.
  3. `a` is `Var` (bound, since the source is closed), `Lit`, `Abs` or `Rec`.
  4. Every occurrence is replaced by `subst(body, 0, a)`.

  It rejects an open source, a trace longer than `MAX_STEPS = 256`, or any
  term (the source included) with more than `MAX_NODES = 4096` distinct
  nodes. It succeeds only if the final hash is `claimed`.
- **The specialiser's limits** are `MAX_STEPS` and `MAX_NODES` too, imported
  from `spec_check`. For an open source, or one over `MAX_NODES`, it returns
  the empty trace at once. Otherwise, when it hits a limit, it returns the
  prefix it has reached; for such a source any prefix of a valid trace is
  valid.
- **`compile.rs`.**
  - `try_compile` is unchanged.
  - The new driver is `pub fn compile_specialised(store: &TermStore, h: Hash) -> Option<Compiled>`,
    with `pub struct Compiled { pub frag: CompiledFragment, pub specialised: Option<(TermStore, Hash)> }`.
    `specialised` is `Some` only when the certificate-checked `h'` is what
    was compiled.
  - The new counter is `pub fn spec_check_failures() -> usize`, a
    process-wide `AtomicUsize` like `ir_validation_failures`.
- **`jit.rs`.**
  - It calls `compile_specialised` instead of `try_compile`.
  - `verify()` still compares against `eval::apply_term(terms, h)`, the
    original term.
  - `kernel_verify` runs on `h'` (in the fragment's store) when the fragment
    is specialised, because the kernel theorems model the structure of the
    compiled term. The installation gate is unchanged: a universal proof is
    still required, now for the compiled term.
  - The cache stays keyed on `h`. `Stats` gains `specialised`.
  - The claim is: universal kernel proof for `h'`, plus certificate-checked
    `h ≡ h'`, not kernel-checked.

## Specialiser policy

Soundness never depends on the policy. It exists to avoid code that gets
slower. That happens when duplicated work turns into more closure
allocations at run time, the "OnceInLam" hazard from GHC's occurrence
analysis (Peyton Jones & Marlow 2002).

The specialiser works innermost-first over saturated spines
`App(…App(Abs^k b, a₁)…, a_k)` whose arguments are all values after their
own specialisation. A spine is reduced (k `BetaV` steps) only if, for every
parameter, the argument meets at least one of these:

- it is a `Var` or `Lit`;
- it is a closed `Abs`/`Rec` with no free variables. These compile to
  static table entries, and `compile.rs` dedupes combinators by hash, so
  copies cost nothing;
- the parameter occurs at most once in `b`, and not under an `Abs`/`Rec` in
  `b` that is left unapplied.

A spine is a maximal chain `App(…App(f, a₁)…, a_n)`, where `f` has `m`
leading `Abs` binders. Its reducible part covers the first
`k = min(n, m)` arguments; the rest stay applied to the result. The
policy judges a spine by the spine alone (its root, head and arguments),
never by the surrounding context.

Each step then rewrites every occurrence of its redex in one pass.
Occurrences that the contraction itself creates are not rewritten, and the
checker and the specialiser both follow this rule. As a result, a redex
shared with a spine the policy rejects is reduced there too. This is
sound, affects only performance, and should be rare.

A spine that fails the test for any parameter is left intact. A partial
application `App(Abs(Abs ..), Var)` is a length-1 spine with a `Var`
argument, so it reduces. Expected results:

- `partial_application_loop` becomes exactly `rec f n acc = if n <= 0 then acc else f (n-1) (acc+n)`.
- `capturing_closure_loop`'s `(\y. acc+y)(n)` becomes `acc+n`.
- `closure_typed_loop` is unchanged, because it has `Rec` in head position.

## Testing

1. **Checker unit tests.**
   - Accept one step with each kind of value argument (`Var`, `Lit`,
     closed `Abs`, capturing `Abs`, `Rec`).
   - Reject:
     - a non-value argument (`App`, `Prim`, `If`);
     - `Rec` in head position;
     - a redex that isn't in the term;
     - a correct replay with the wrong `claimed`;
     - traces and terms over the limits.
   - Substitution cases: shifting under binders, an argument with a
     variable free in the redex (but bound in the closed source)
     substituted under binders, and `Rec`'s self-index.
   - Reject an open source, even with an empty trace.
2. **Checker mutation test.** For valid `(h, trace, h')` triples from the
   corpus and fuzzer, apply each mutation below. Every mutant must be
   rejected unless its replay provably equals the claimed term, which the
   test checks directly.
   - drop a step;
   - swap adjacent steps;
   - retarget a step to another subterm's hash;
   - change one `Var` index or `Lit` in `h'`;
   - truncate the trace.
3. **Independence allowlist.** `spec_check.rs` may use only `term` and
   `std`, with both `crate::` and `super::` scanned. The scanner in
   `decompile.rs`'s `the_decompiler_imports_nothing_from_the_compiler`
   becomes a shared `#[cfg(test)]` helper, parameterised by file contents
   and the allowed module heads. Both tests call it.
4. **Differential fuzz** (`tests/compile_fuzz.rs`, extending
   `compiled_and_interpreted_agree_on_random_terms` and its generators,
   with `Div`/`Mod` included). Every random term is specialised and
   checked, with these requirements:
   - `spec_check_failures() == 0`;
   - `eval(h)` and `eval(h')` agree exactly on the sample arguments,
     including the `Err` variant;
   - compiled output matches `eval(h)`, as today. Since final review the
     fuzz also runs `compile_specialised`'s fragment directly, with no
     `verify()` in between, and requires it to match `eval(h)` (an error as
     a trap) wherever `eval(h)` is not a `TypeError`. Compiled code assumes
     well-typedness, for `h` as much as for `h'`, and `gen_redex_rich` can
     use a closure as an `Int`. *(Later: `verify()` catches that only when a
     sample reaches the ill-typed code. The JIT now declines ill-typed terms
     statically, and the fuzz compares every term `typing::well_typed`
     accepts; see `RELATED_WORK.md` §38.)*
   - open terms (`gen_unbound_variable`, bare and under a redex) get the
     empty trace, and the checker rejects them.
5. **Policy tests.**
   - A capturing lambda whose parameter is used inside a loop body is not
     reduced (`h' == h`).
   - The same position holding a closed lambda is reduced.
   - `partial_application_loop`'s `h'` equals the hand-built term, by hash.
6. **Planted-bug checks** (each must fail and is then reverted):
   - the checker accepts an `App` argument;
   - an off-by-one in the checker's `shift`;
   - the checker skips the final hash comparison;
   - the specialiser mis-shifts (the checker catches it, and debug panics);
   - the policy ignores the under-lambda condition (a policy test catches
     it).
7. **Integration.**
   - `partial_application_loop` is installed specialised with a universal
     proof on `h'`.
   - The JIT stats check stays at compiled 9, declined 0, or is updated
     deliberately with the reason.
   - The existing goldens and `try_compile` tests are unchanged, because
     `try_compile` is unchanged. That includes step 4's lambda-lifting
     test.
   - A new golden, `partial_application_loop_specialised.wat`, is produced
     by `compile_specialised` in `tests/golden_wat.rs`.
   - Benches `partial_application_loop`, `capturing_closure_loop` and the
     controls are run best-of-N on a shared machine and recorded in §37.
8. Full validation (checks 1-9) runs after each task.

## Docs

- **RELATED_WORK.md §37:**
  - the survey (CompCert, CakeML, CertiCoq, Œuf, Tristan-Govereau-Morrisett, Crellvm, Alive2, GHC);
  - why D now and C later, including the probe finding below;
  - Plotkin's βv;
  - hash-addressed steps as a weak form of Lévy family reduction;
  - the optimal-reduction verdict;
  - bench results.
- **§36:** a note that the `capturing_closure_loop` bench, which goes
  through the JIT, now measures specialisation. Lambda lifting stays
  covered by its `try_compile`-level test.
- **The IR spec's future-work entry** points here.
- **Trust statements:** `compile_specialised`'s docs, the `jit.rs` module
  docs and the README pipeline section say "compiles `h'`, which decompiles
  to itself and is certificate-checked ≡ `h`".

## Probe finding behind "C later" (2026-09-24)

A throwaway test ran `proof.rs`'s entry points on both loops and on their
specialised or hoisted forms. All six terms got universal-strength proofs:
`prove_tail_recursive_universal` for the open forms, `prove_closure_expr`
for the closed ones. So `denote` covers both `h` and `h'`.

But each theorem concerns a single term, `∀p v (e : Ev_h(p,v)). loop_val_h(p,e) = v`,
where `Ev_h` and the closure-call constants (`call_h`, with `call_eq` axioms
built from each body) are postulated per term. `h ≡ h'` therefore needs a
new builder:

- For V3, prove `Ev_h(p,v) → Ev_h'(p,v)` by `ev_rec_h`, with each step's
  next parameters equal by congruence plus `call_eq` rewriting.
- For V1, it has to relate `Ev` families of different arities.

## Open questions and future work

- **C: a kernel builder that consumes the trace.** It needs one congruence
  proof per `BetaV` step, then lifts the result through `Ev` by induction.
  It is sized like the core of `build_universal`.
- **V1** as `Step::HoistInvariant { .. }`, with its precondition checked
  syntactically.
- **Strict vs lazy evaluation**, parked. Under lazy evaluation the kernel's
  full-β `def_eq` would match the semantics, which removes C's
  evaluation-order argument. But it changes what programs mean (errors and
  divergence), touches every layer, and costs thunks on numeric loops. The
  middle ground is to stay strict and allow full β only on subterms proved
  total and error-free, which is roughly what `denote` assumes implicitly.
  Revisit when C starts, or if the corpus gains terms with expensive unused
  arguments.
- **Policy tuning**, such as size heuristics or inlining non-saturated
  spines, driven by benches.
- **Optimal reduction** (Lévy, Lamping, interaction nets such as BOHM and
  HVM) does not apply, and there are three reasons. It minimises
  normalisation steps under full β, not the cost of the residual program at
  run time. Full β is unsound here. And its bookkeeping cost is not bounded
  by any elementary function (Asperti & Mairson 1998). See §37.
