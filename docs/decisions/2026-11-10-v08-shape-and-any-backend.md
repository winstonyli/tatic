# The shape of v0.8, and any backend (discussion, 2026-11-10)

Question (from the user, after v0.7 closed and the sum-loop spike): what should v0.8 be without veering off the main
vision ("keep it general"), and how much of the code is wasm-specific? The aim, in the user's words: tatic should
"accelerate its reasoning with any backend, either with a provided formalization or thru exploration agent style".
Goal 1 of `ROADMAP.md` now says so and links here.

## Status

- **Open:** which v0.8 (the options below). Nothing is started.
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

  About 21 are plausibly carried by one call law plus a heap. Five (11, 17, 27, 32, 33) call a closure parameter and
  also need a calling convention for closures. 18 of the 26 install today on the model proof.
- **gcd** needs a signed-remainder operator and a meaning for division by zero. The machine has no trap channel.
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

## Decide (v0.8 shape), open

Searched: removed a `Backend` trait (no second backend yet; the row table is the seam), and folded the straight-line
statement into the loop law, which removes fuel 1 and `strip_loop` (already unused: its one caller passes `false`).

- z1 **Rows, then loops** (recommended): make the machine a table, one row per instruction. Then add `LocalSet` and
  `RemS` as rows, prove one simulation loop law, and have the gate state recursive terms as the fuel-unrolled source.
  Done when both sum loops and both gcds install on the gate. The spec also says which of the about 21 call terms a
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
  - Still open: closure records at addresses computed at run time (an invariant over a region), locals and
    per-activation frames, the table, the closure convention for the five terms that call a closure parameter, and
    proofs derived from the instruction list (all so far are hand-written per function).
- z4 **Backend boundary only**: the row table with no new instructions.
