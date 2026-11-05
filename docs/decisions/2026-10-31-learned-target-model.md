# A learned model of the target machine (discussion, 2026-10-31)

Question (from the user): instead of a formalized target machine built into the JIT, expose arbitrary instruction
execution and let a model develop its own mental model of the machine, like a game AI learning the rules from actions
and results; or keep the formalization as the stable backing and the learned model as the efficient, possibly wrong
representation.

## Decision

- **Not instead of the formalization.** The installation gate installs compiled code only with a kernel proof over every
  `Int` (`src/jit.rs`, `NoUniversalProof`); a learned model is statistical and cannot meet it. Policy stays "proof or
  interpreter".
- **As an untrusted layer beside it: yes.** Same shape as goal 3 of `ROADMAP.md` (the model proposes, the kernel checks).
  The model's errors can cost speed or search effort, never correctness.
- The belief layer of goal 3 (P(kernel proves a claim) from shape and evidence) is the shared substrate for both uses
  below, so it goes first (spec: `docs/superpowers/specs/`, a3 of 2026-10-31).

## What exists already

- The screen (`SCREEN_INPUTS`), the miner's conjecture-then-prove loop and the class table already learn from execution
  and kernel results; the calibration of random testing is `docs/tier-cycle/`, "How much random testing is worth".
- Wasm semantics is small, specified and deterministic, and the formalization's remaining obligations are lemma-proving
  work (`PARKED.md`, "The formalised Wasm target machine's remaining obligations"). Learning the rules from interaction
  would give a statistical imitation of rules that can be written down.
- v0.6 stage 1 is a caution for any learned scorer: AUC 0.69 and no curve shift (`docs/tier-cycle/`, "A learned
  scorer over the extras").

## Where a learned model could add something

1. **Cost** (strongest, `PARKED.md` "Learned target-cost model"): the formalization says what code means, not how fast
   Cranelift's output runs. Train on `wasmtime` timings of lowering candidates; untrusted by construction.
2. **A target with no formalization** (`PARKED.md` "Execution-learned model for an unformalized target"): native ISA,
   where Sail models are large. Reaches only the sample tier, which the gate rejects today, so it first needs a policy
   decision.
3. **Pre-filtering** proof attempts: predict failure before the kernel spends time (a belief-layer consumer).

Limit: none of these unblocks goal 1. The JIT's blocker is that its programs lack arithmetic depth (and the specialiser
does not add any, 2026-11-01), plus a bridge from the loop's width-n laws to the JIT's i64; it is not missing knowledge
of the machine. A hand-written depth workload exists (Hacker's Delight, `docs/tier-cycle/`), and there the fixed table,
not mined rules, does the rewriting.
