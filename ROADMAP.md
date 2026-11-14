# Roadmap

The project's goals, then ordered milestones, each the question it answers (format: `~/.claude/VERSIONING.md`).
`kind: experiment`: a tag marks a step and its message is the milestone sentence; tagging moves the line out of this
file. Only the user tags. Tagged so far: `v0.1.0`, `v0.2.0` (2026-10-22), `v0.3.0` (2026-10-23), `v0.4.0` (2026-10-26) `v0.5.0` (2026-10-31), `v0.6.0` (2026-10-31) `v0.7.0` (2026-11-10), `v0.8.0` (2026-11-11), `v0.9.0` (2026-11-12) and `v0.10.0` (2026-11-14; `git tag -n99`). Deferred work is in
`PARKED.md`. The cleanup break from v0.5 (`docs/superpowers/plans/2026-10-26-cleanup.md`) is done (2026-10-27).

## Goals

Every milestone serves at least one of these; work that serves none needs a stated reason.

1. **A JIT on proved equivalence.** A higher-order term runs compiled once its compiled form is kernel-proved equal to
   it on every input (`README.md`, top; the code in `crates/tatic/src/`). Wasm is the first backend, not the only
   one: the aim is to accelerate reasoning on any backend, from a provided formalization or from one found by
   exploration (an untrusted proposer, as in goal 3). How that stays inside "proof or interpreter":
   `docs/decisions/2026-11-10-v08-shape-and-any-backend.md`.
2. **A kernel that improves itself.** It mines rewrite rules from the laws it proves, so later proofs are cheaper, and
   grows its own vocabulary through checked definitions, since a fixed vocabulary saturates (`docs/tier-cycle/`,
   "Idea" and "Risks"; the miner in `crates/church-bv/src/`).
3. **The KR&R tier of a cycle with a GPU model.** A learned model on the GPU tier (nothing
   built; the idea came from the tiered-AI direction of the inactive scratchtape repo, which this repo does not rely on) proposes what to explore; the kernel checks and proves it, and returns rules and signals.
   The model's output is untrusted (`docs/tier-cycle/`, "Idea").
   Between the two, a calibrated belief layer (design note, 2026-10-22; its first milestone stopped at its gate, see
   `PARKED.md`, "Belief layer stage 2", and `docs/tier-cycle/`, "The belief layer's calibration milestone stops at its first gate"). For each claimed equality it
   would estimate P(the kernel proves it) from the claim's shape and its evidence: random tests passed, small widths
   checked exhaustively, the model's score. Evidence that decides a claim outright sets it to 1, such as a pure bitwise
   term's values on the 0/1 inputs; a counterexample sets it to 0 for good. It learns from the outcomes: kernel-checked proofs and counterexamples. It
   would order and budget work (which claims to test, prove or train the model on) and never accept a claim:
   probabilities never reach the kernel. That would make fixed pass/fail filters such as the screen (`SCREEN_INPUTS`)
   one input among others. Open: whether a high-belief claim may enter the kernel as a tracked postulate (a `Const`,
   proved later). Its first calibration: `docs/tier-cycle/`, "How much random testing is worth", where a test's worth
   depends on the kind of claim.
   **Held (2026-11-07):** no claim source in reach has a label costly or uncertain enough for a model to save work
   (`docs/tier-cycle/`, "No claim source with room for a model"). Trigger: a claim source whose labels cost far more
   than a model's prediction, or are not decided by cheap checks.

Goals 1 and 2 meet in compiled hot transformations with learned compilations. That is not a milestone yet: the mined
rules find no work in the JIT's programs (`PARKED.md`, "Compile hot transformations", with its trigger; results in
`docs/tier-cycle/`, "Other ways to join the JIT and the loop").

## Milestones

v0.6 (`git tag -n99 v0.6.0`; findings in `docs/tier-cycle/`, "A learned scorer over the extras", "Q2 primary run" and "Selecting the extras by straggler verdict") closed with selection by `small` as the answer; what it left is in `PARKED.md`. Goal 3 is held (above), so the next
milestone serves goal 1 or 2.

v0.7 (`git tag -n99 v0.7.0`; goal 1) closed with the straight-line fragment's install gated on a kernel proof of the
emitted instruction list itself, where v0.6 proved a model of the compiler. What showed it: `jit.rs#prove_install`
sends the five fragment terms to `proof/gate.rs#gate` alone (`jit/tests.rs`: `fragment_terms_install`,
`the_gates_verdict_is_final_for_fragment_terms`), and seven mutations are rejected
(`proof/tests/gate.rs#gate_rejects_mutations`). Its decisions are in the spec
(`docs/superpowers/specs/2026-11-08-v07-straight-line-gate-design.md`); findings in `docs/tier-cycle/`, "v0.7's first
steps: the census and the emit spike" and "The gate's costs, and the rules they triggered".

v0.8 (`git tag -n99 v0.8.0`; goal 1) closed with loops, self-calls and module callees installing from the emitted
code through one generated simulation proof, on an instruction table with locals as a frame passed in. What showed it:
the workspace suite on main after the merge (806 passed, 0 failed), the Goal 1 and 2 verdict columns in
`proof/tests/baseline.rs#VERDICTS`, mutants in `proof/tests/{gate_mutants,modules}.rs`, `held_out_terms_are_accepted`
and `toy_table.rs` (the toy's "installs" read as the gate's verdict, confirmed at tag). Its decisions are in
`docs/decisions/2026-11-10-v08-shape-and-any-backend.md` and the spec
(`docs/superpowers/specs/2026-11-10-v08-recursion-once-design.md`); findings in `docs/tier-cycle/`, "v0.8's build:
measurements and checks" and "v0.8's modules: measurements".

v0.9 (`git tag -n99 v0.9.0`; goal 1) closed with a self-tail-recursive function installing as a wasm loop whose text
the kernel proved, at the v0.7 loop's speed. What showed it: `proof/tests/loop_form.rs#the_shipped_loops_install_in_loop_form`
(`capturing_closure_loop` and `held_out_b` gate `Accepted` with `br $top` and no self `return_call`), the 54 mutants in
the same file, and the timed bench run `pfl-bench-b1` (closure loop warm 4.416 us against v0.7's 4.4 us and main's
25.6 to 27.2 us). Spec and plan: `docs/superpowers/specs/2026-11-12-proved-loop-form-design.md`,
`docs/superpowers/plans/2026-11-12-proved-loop-form.md`; findings in `docs/tier-cycle/`, "The proved loop form:
measurements".

v0.10 (`git tag -n99 v0.10.0`; goal 1) closed with closures and partial operators installing from emitted code the
kernel proved: closure values and `call_indirect` dispatch over the table, and `%` guarded by its domain, take the
census from 17 to 27 rows `Accepted` with none `Rejected`. What showed it: `proof/tests/baseline.rs#VERDICTS` (27
`Accepted`, 13 `NotCovered`), the closure-convention mutants in `proof/tests/gate_mutants.rs`,
`a_closure_call_at_another_arity_is_not_covered` in `proof/tests/gate.rs`, and the suite run
`2026-11-14-final-fix-suite` (exit 0). Three of the eight closure rows have an empty dynamic set, so their `Accepted`
says only that each closure call traps on both sides. Along the way one instantiation memo cut the kernel's check work
(counts, untimed). Specs and plans: `docs/superpowers/specs/2026-11-13-partial-row-and-gcd-design.md`,
`docs/superpowers/specs/2026-11-13-closures-through-the-gate-design.md` and their plans; findings in `docs/tier-cycle/`,
"The proved loop form: measurements" (the memo), "The partial row and gcd through the gate" and "Closures through the
gate".

No milestone is open. Candidates are in `PARKED.md`.
