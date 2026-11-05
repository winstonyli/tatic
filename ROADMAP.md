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
   grows its own vocabulary through checked definitions, since a fixed vocabulary saturates (`docs/tier-cycle.md`,
   "Idea" and "Risks"; the miner in `crates/church-bv/src/`).
3. **The KR&R tier of a cycle with a GPU model.** A learned model on the GPU tier (nothing
   built; the idea came from the tiered-AI direction of the inactive scratchtape repo, which this repo does not rely on) proposes what to explore; the kernel checks and proves it, and returns rules and signals.
   The model's output is untrusted (`docs/tier-cycle.md`).
   Between the two, a calibrated belief layer (design note, 2026-10-22). Its first calibration milestone (2026-11-01) built
   the claim dump and the statistics and stopped at its gate: no claim that passes the screen and the exhaustive width-4 check is refuted (on this claim distribution), so there was
   nothing for a belief about refutation to rank. The unproved ones are all provable at width 4 (spike, 2026-11-01), so
   unprovability is the cheap path's gap, not a truth to predict, and scoring it is decided against for now
   (`PARKED.md`, "Belief layer stage 2"; `docs/tier-cycle.md`, "The belief layer's calibration milestone stops at its first gate"). For each claimed equality it
   would estimate P(the kernel proves it) from the claim's shape and its evidence: random tests passed, small widths
   checked exhaustively, the model's score. Evidence that decides a claim outright sets it to 1, such as a pure bitwise
   term's values on the 0/1 inputs; a counterexample sets it to 0 for good. It learns from the outcomes: kernel-checked proofs and counterexamples. It
   would order and budget work (which claims to test, prove or train the model on) and never accept a claim:
   probabilities never reach the kernel. That would make fixed pass/fail filters such as the screen (`SCREEN_INPUTS`)
   one input among others. Open: whether a high-belief claim may enter the kernel as a tracked postulate (a `Const`,
   proved later). Its first calibration: `docs/tier-cycle.md`, "How much random testing is worth", where a test's worth
   depends on the kind of claim.

Goals 1 and 2 meet in compiled hot transformations with learned compilations (`README.md`, "Future work"). That is
not a milestone yet: neither the mined rules nor the class table find work in the JIT's programs, whose add/sub
trees are one operator over leaves, and the specialiser's inlining adds no depth (`docs/tier-cycle.md`, "Other ways to
join the JIT and the loop", option A's results, 2026-10-17 to 2026-11-01). A hand-written depth workload (Hacker's Delight)
shows the fixed table, not mined rules, doing the rewriting; and the loop's laws are at one small width, the JIT's `Int` is
i64 (`PARKED.md`, "laws uniform in the width").

## Milestones

No milestone is open. v0.6 (`git tag -n99 v0.6.0`; findings in `docs/tier-cycle.md`, sections on the learned scorer, straggler verdicts, `small` and the crossover) closed with selection by `small` as the answer; what it left is in `PARKED.md`.
