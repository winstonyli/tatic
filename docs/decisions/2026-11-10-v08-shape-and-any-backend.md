# The shape of v0.8, and any backend (discussion, 2026-11-10)

Question (from the user, after v0.7 closed and the sum-loop spike): what should v0.8 be without veering off the main
vision ("keep it general"), and how much of the code is wasm-specific? The aim, in the user's words: tatic should
"accelerate its reasoning with any backend, either with a provided formalization or thru exploration agent style".
Goal 1 of `ROADMAP.md` now says so and links here.

## Status

- **Decided 2026-11-10:** v0.8 is z5 "Recursion once", staged S0-S4 with its own spec (below); division by zero is a
  partial row whose trap is the no-value answer (below). The spec is not written yet; nothing is built.
- **Open:** the heap relation for callees (below), and whether `loop`/`br` survive: the no-loop spike says they need
  not (`docs/tier-cycle/`, "Tail self-calls as `return_call`, with no `loop` or `br`: a spike"); the spec decides.
- **Settled:** the "any backend" policy below. It extends the 2026-10-31 decision
  (`docs/decisions/2026-10-31-learned-target-model.md`) and does not change it.

## The test any v0.8 must pass

- It is judged by how general it is and by what it gives the 26 terms that still install on the model proof
  ("class C"; census in `docs/tier-cycle/`, "v0.7's first steps: the census and the emit spike").
- Anti-goal: a proof written for one loop, or a gate branch per program shape. One law per instruction kind and one
  simulation statement must cover every program the gate takes.

## Where the code stands (recon, 2026-11-10, checked by a second reader)

- **Backend split.** `crates/` holds 46,163 lines of Rust: about 38.6k are backend-independent (kernel, miner,
  IR, model prover), about 2.4k are wasm-only, and about 5.2k are mixed. These figures are a judgement per file; the
  file sizes were checked, the sums were not.
  - church-bv reaches tatic-wasm only through `tatic_wasm::encoding`, which holds bit-vector terms and not wasm.
  - The pre-v0.7 model prover (`crates/tatic/src/proof.rs` and `proof/` apart from the v0.7 `proof/gate.rs`) imports
    nothing from wasm. It mirrors
    `lower_wat.rs`'s closure-environment convention in intent (`proof/closures.rs`).
- **The machine is scattered.** One instruction lives in five places in `crates/tatic-wasm/src/wasm.rs`: the `Ins`
  enum, `ctor_ty`, `interp`'s vector, `seq_step` (which indexes the constructors by position) and `shape`, plus the
  printer; the call spike's `Ins::Call` also touched the constructor count in `ctors`. `local.set`, `call`, `call_indirect` and `rem_s` have no `Ins` and are emitted as `Raw` or as WAT text.
- **The class C terms**, split by reading each one's emitted WAT in the census run `2026-11-08-b1-census` (the
  per-term split is recorded only here):

  | kind | count | what they need |
  |---|---|---|
  | non-tail self-calls (factorial, `redundant_arithmetic_recursion`, fib) | 3 | a call |
  | direct calls | 4 | a call |
  | closure calls through the table, no memory | 11 | a call plus a table |
  | closure records in memory | 7 | a call plus a heap |
  | packs a closure only | 1 | a heap |

  "About 21 carried by one call law plus a heap" (this file's first reading) is a ceiling, not a count. Reassessed
  2026-11-10: term 28 needs bit rows (the closure word's split), not a heap; a call law with locals and frames reaches
  at most 8 of the 26 (1, 2, 3, 13, 23, 25, 28, 34), of which only 25 does not install today; the closure and record
  terms need the closure convention and a heap relation besides. Five (11, 17, 27, 32, 33) call a closure parameter
  (shape proved in `docs/tier-cycle/`, "Calling a closure parameter: the closure convention against its source, a
  spike"; 27 needs a type-indexed relation). 18 of the 26 install today on the model proof.
- **gcd** needs a signed-remainder row and a meaning for division by zero. The row's cost fits the gate (about 20 ms
  at n = 64, `docs/tier-cycle/`, "What a signed remainder costs the gate: a probe"); the meaning does not exist (eval
  errors, wasm traps, the circuit answers `x`), and the machine has no trap channel. It is its own rung.
- **Loops need a two-sided simulation.** Generalising `loop_law`'s invariant alone is not enough. The statement is
  the machine at fuel `N` against the source unrolled by `N` (`docs/tier-cycle/`, "The sum loop proved against a
  source recursion: a spike").

## Any backend: provided or explored, one trust story

- **What a backend is.** A table of instruction rows. Each row gives the constructor type, the meaning, the shape
  rule and the printer. The gate's statement, the simulation laws and the proof search do not change per backend.
  Wasm is the first table.
- **A provided formalization** is a table written from a spec, the way `wasm.rs` was written. Comparable systems
  treat an ISA interpreter as the formalization: Serval and Jitterbug
  (<https://unsat.cs.washington.edu/projects/jitterbug>), KWasm
  (<https://github.com/runtimeverification/wasm-semantics>), and Sail and WasmCert, which the repo already surveys (doc 15's options table).
- **An explored formalization** is a table proposed by an agent that runs instructions and fits their meanings,
  like stratified synthesis
  (<https://pldi16.sigplan.org/details/pldi-2016-papers/50/Stratified-Synthesis-Automatically-Learning-the-x86-64-Instruction-Set>),
  SemMC (<https://github.com/GaloisInc/semmc>) and InstrSem
  (<https://www.usenix.org/conference/usenixsecurity26/presentation/hetterich-lorenz-instrsem>).
- **Same trust either way** (inference, not built). A row enters the trusted base the way a provided row does: it is
  read, and it is tested against the real machine by differential tests. It is never accepted on a model's score.
  - The proposer is untrusted, as in goal 3. "Proof or interpreter" still holds: install needs a kernel proof against
    the row table.
  - What exploration saves is the writing of rows. It does not remove the trust in them.
  - The rows-first shape of v0.8 is what makes both routes the same, because a row is the unit both produce.

## Decided (v0.8 shape): z5, staged (2026-11-10)

The user picked the staged form of z5 (g1), after a survey of z5 (checked by a second reader) and the spike that drives
the generator from real terms (`docs/tier-cycle/`, "The generator on tatic's terms and the lowering's code: a spike":
both sum loops, factorial, `redundant_arithmetic_recursion` and fib install from emitted code through the unchanged
generator; 13 and 34 stop on `i32.const 0` and `call $c0`).

- **S0** the instruction table over today's constructors, checked by equality of the derived constructor types,
  meanings and printed WAT against the old ones, the existing tests, and an instruction count of `wasm_scaling`.
- **S1** locals as their own state component, `local.set` a row, the lowering emitting it, the printer naming slots
  `$p`/`$t` (today it prints every slot as `$p{i}`); the v0.7 gate suite unchanged.
- **S2** the generator on `Source::cps` with the self-call case; both sum loops and terms 1, 2, 3 install, and a
  function written after the generator is frozen. Then delete the loop law, fuel 1, `strip_loop` and `gate_with`.
  Go/no-go here.
- **S3** modules: a call that names its callee, the callee's law as a hypothesis, calls of any arity, an `i32` kind
  for the environment pointer (13, 23, 34).
- **S4** a toy second instruction table installs a straight-line term through the unchanged gate.
- Not in S0-S4: 25 and 28 need bit rows (`wrap`, `extend`, `shl`, `or`); gcd needs the partial row (below); the
  closure-record terms need the heap relation (below).
- The spec's Decide groups (from the survey): D1 the loop's meaning (a restart label, as the lowering emits, or a
  general loop), or no loop: tail self-calls as `return_call` prove every target through the unchanged walk, run
  10^6 iterations without growing the stack, and change 29 golden files; D2 the locals encoding and slot layout; D3 the call
  row's arity and callee naming, and the `i32` kind; D4 one relational statement for all terms (a convertible-first
  rule for straight-line code) or a kept `refl` path; D5 rows as data or as an enum with derived parts.

The options as they stood when picked:

Searched: removed a `Backend` trait (no second backend yet; the row table is the seam), and folded the straight-line
statement into the loop law, which removes fuel 1 and `strip_loop` (already unused: its one caller passes `false`).
Reassessment (2026-11-10): removed the separate loop law and call law, since `br` and `call` are one fuel edge (z5);
z1, z2 and z4 install none of the 26, so they rank below it.

- z5 **Recursion once** (recommended): one milestone in three parts. Leaf instructions become rows of one schema, with
  constructor types and shape rules derived from it; locals become their own state component, with a fresh frame per
  call; `br` and `call` share one relational fuel simulation whose proofs are generated by walking both sides
  (`docs/tier-cycle/`, "One generator for loops and calls, with locals apart from the heap: a spike": sum, factorial,
  fib, a nested call and three functions written after the generator was frozen prove, within about 70 ms each at n =
  64, and five mutants are rejected).
  - Done when: both sum loops, factorial, `redundant_arithmetic_recursion`, fib and direct calls 13 and 34 install from
    emitted code through the one generator; a function it was not written against also proves; a mutant per row and
    per call site is rejected with its reason read; the loop law, fuel 1 and `strip_loop` are deleted; a toy second
    instruction table installs a straight-line term through the unchanged gate. gcd is a later rung.
  - Pro: one statement for loops and calls, deletes the most, meets the anti-goal head on, and is the only option
    that tests the "any backend" seam. Con: the largest; the generator is a spike with one-argument calls, heap-free
    callees and a hooked `loop` whose meaning differs from the real row's unrolling, and is driven from a mirror of
    `Source::cps`, not tatic's terms.
- z1 **Rows, then loops** (first reading's pick; now the fallback if z5's generator does not carry real terms): make
  the machine a table, one row per instruction. Then add `LocalSet` and
  `RemS` as rows, prove one simulation loop law, and have the gate state recursive terms as the fuel-unrolled source.
  Done when both sum loops and both gcds install on the gate. The spec also says which of the (at most 8) call terms a
  later `call` row carries.
- z2 **Loops only**: the same loop law on the current five-site machine.
- z3 **Loops and calls**: z1 plus a `call` row in one milestone.
  - Its open risk was whether a call fits the universe levels. The call spike answers it at the meaning level
    (`docs/tier-cycle/`, "Calls by index proved against a source recursion: a spike"). The environment and the
    module's fixpoint check at Sort2, and factorial and fib each prove against their source by one fuel induction.
    That a constructor taking a program cannot express recursion is reasoning from the sort rules, not a run.
  - A second spike (`docs/tier-cycle/`, "`call` as an instruction, and a callee that touches the heap: a spike")
    adds `call` as a ninth constructor with load's type, built through `prog`, with the program type's level
    unchanged and the existing tatic-wasm tests and a filtered gate subset passing (scaling tests not run). A callee that writes a fixed heap cell before its call and reads it after proves
    against a source that threads the cell as state.
  - A store at a run-time address that a callee's write at the next address leaves intact also proves, with two
    bitvector lemmas and no induction; the call patch (the ninth constructor plus the environment threaded through the
    interpreter) makes `wasm_scaling` retire about 1.1% more instructions (doc 15, "A store at a run-time address across a call, the cost of `call`, and eta: three follow-ups").
  - Still open: closure records over a region whose depth is known only at run time (the address lemmas it needs,
    `eq (p + j) p = eq j 0` and cancellation, now prove with no overflow hypothesis:
    `docs/tier-cycle/`, "The region lemma: `p + j = p` exactly when `j = 0`, and offset `k = 2`"; the region
    invariant itself is untried), a heap relation for callees that write memory, the table, and term 27's
    type-indexed closure relation. Locals with per-call frames, the closure convention and proofs derived from the
    instruction list each have a spike now (z5's generator and the closure spike above).
- z4 **Backend boundary only**: the row table with no new instructions.

Why not the others: z1 brings back a proof per loop and installs none of the 26; z2 keeps the five-site machine; z3 is
z5 without the generator (proofs by hand per function); z4 is z5's S0 alone; z5 as one milestone has no checkpoint
before its deletions and its "Done when" needed module work nothing had tried.

## Decided: division and remainder by zero (2026-11-10)

The user picked h1 after a survey (checked by a second reader). Today eval errors (`DivByZero`), wasm traps, and the
remainder circuit answers `x`; the machine has no trap channel.

- **Picked: a partial row.** A row gets an optional domain condition (for `rem_s`, divisor not 0). Outside it the
  machine answers its existing no-value answer `z`, so the gate statement and every law keep their shape. The gate's
  source side emits the same guard, and the evaluator's error and the row's domain read one definition, not two
  copies. The table test checks the domain at b = 0 against eval's error and wasmtime's trap. Language, evaluator and
  lowering are unchanged.
- The gate cannot catch a wrong domain condition (both sides read it), only the table test can, as for circuits
  today. Trap and timeout are not told apart. The guard's cost is inside the run-to-run spread at n = 64, and gcd and
  its two-base-case variant install through the generator (`docs/tier-cycle/`, "The partial row's cost, and gcd
  through the generator").
- Not picked: a total row with a claim only where eval is defined (no new concept, but the kernel states a made-up
  value at b = 0 and that row stays unchecked); a total language (`x % 0 = x`; the printed guard is trusted, not
  proved, and CU1 removed a private `x / 0 = 0` evaluator as a bug on 2026-10-26); a precondition hypothesis (the
  partial row's guard written as a path condition, plus a run-time check); excluding `Div`/`Mod` from the fragment
  (status quo); an explicit guard and a `Trap` instruction (a new constructor and a guard per site that the engine
  already checks).
- Div's `MIN / -1` wrap still needs the lowering's wrapping sequence modelled as instructions.

## Open: a heap relation for callees (2026-11-10)

Closure records in memory, anything that allocates, and `iterate` against the gate need a relation between the heap
before and after a call. A survey recommended pointwise cell hypotheses plus an allocation world; its checker rejected
that as a first step: it needs order facts (`a < w`) on 64-bit words that nothing proves, most class C terms do not
need it, and a captured cell read each iteration (term 37) has no source value to name. One shape it missed now has a
spike (`docs/tier-cycle/`, "Fresh addresses by construction: the allocation pointer in the state, a spike"): with
the pointer in the state and cells as per-function hypotheses, a loop re-reading a captured cell, a record allocated
and read by a callee, an in-place update and two allocations prove with no order facts. Follow-ups
(`docs/tier-cycle/`, "The heap across a non-tail call, and an older record: a spike" and "A closure record's cells
inside the closure relation: a spike"): an older record read after a later allocation, and a cell a callee preserves
read after a non-tail call, prove; cells are derived from the machine code; the closure relation can carry a record's
invariant, hiding its layout from pass-through callers. Still open: a cell the callee writes and the continuation
reads, a record allocated before a call and read after it, term 37's loop through a closure, and composing the
per-function proofs. Rejected by the survey: heap
extensionality (not derivable without eta), separation-logic frames (need splitting of function-typed heaps), a list
heap (a machine rewrite), a counter-style invariant per cell (one hypothesis per cell). Term 27 needs a type-indexed
closure relation in any of these.
