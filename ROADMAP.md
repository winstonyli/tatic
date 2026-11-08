# Roadmap

The project's goals, then ordered milestones, each the question it answers (format: `~/.claude/VERSIONING.md`).
`kind: experiment`: a tag marks a step and its message is the milestone sentence; tagging moves the line out of this
file. Only the user tags. Tagged so far: `v0.1.0`, `v0.2.0` (2026-10-22), `v0.3.0` (2026-10-23), `v0.4.0` (2026-10-26) `v0.5.0` (2026-10-31) and `v0.6.0` (2026-10-31; `git tag -n99`). Deferred work is in
`PARKED.md`. The cleanup break from v0.5 (`docs/superpowers/plans/2026-10-26-cleanup.md`) is done (2026-10-27).

## Goals

Every milestone serves at least one of these; work that serves none needs a stated reason.

1. **A JIT on proved equivalence.** A higher-order term runs compiled once its compiled form is kernel-proved equal to
   it on every input (`README.md`, top; the code in `crates/tatic/src/`).
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

No milestone is open. v0.6 (`git tag -n99 v0.6.0`; findings in `docs/tier-cycle/`, "A learned scorer over the extras", "Q2 primary run" and "Selecting the extras by straggler verdict") closed with selection by `small` as the answer; what it left is in `PARKED.md`. Goal 3 is held (above), so the next
milestone serves goal 1 or 2.
