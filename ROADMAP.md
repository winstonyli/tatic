# Roadmap

The project's goals, then ordered milestones, each the question it answers (format: `~/.claude/VERSIONING.md`).
`kind: experiment`: a tag marks a step and its message is the milestone sentence; tagging moves the line out of this
file. Only the user tags. Tagged so far: `v0.1.0`, `v0.2.0` (2026-10-22) and `v0.3.0` (2026-10-23; `git tag -n99`). Deferred work is in
`PARKED.md`.

## Goals

Every milestone serves at least one of these; work that serves none needs a stated reason.

1. **A JIT on proved equivalence.** A higher-order term runs compiled once its compiled form is kernel-proved equal to
   it on every input (`README.md`, top; the code in `src/`).
2. **A kernel that improves itself.** It mines rewrite rules from the laws it proves, so later proofs are cheaper, and
   grows its own vocabulary through checked definitions, since a fixed vocabulary saturates (`docs/tier-cycle.md`,
   "Idea" and "Risks"; the miner in `tests/church_bv/`).
3. **The KR&R tier of a cycle with a GPU model.** A learned model on the GPU tier (scratchtape's `README.md`,
   "Direction: tiered AI") proposes what to explore; the kernel checks and proves it, and returns rules and signals.
   The model's output is untrusted (`docs/tier-cycle.md`).
   Between the two, a calibrated belief layer (design note, 2026-10-22; nothing built). For each claimed equality it
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
trees are one operator over leaves (`docs/tier-cycle.md`, "Other ways to join the JIT and the loop", option A's
results, 2026-10-17 and 2026-10-23).

## Milestones

- **v0.4 - Can the kernel extend its own vocabulary?** (goal 2, and goal 3 once the model proposes) A proposed
  definition enters only if checked conservative. Seeds: `PARKED.md`, "Proposer targets beyond ranking" (c) and
  "Boolean combinations of comparisons" (its machine side passed a spike).
- **v0.5 - Does closing the cycle push the frontier?** (goals 2 and 3) Experiment 3: train on accepted laws, repeat,
  and track the frontier, not only M on a fixed stream. The frontier: on a fixed held-out set of laws larger than the
  loops serve (the loops run on operator-set streams, the class-table spec's decision 11), the share proved free (with no whole-term machine proof, within the rule budget and the join's cap
  and visit budget, which must be fixed: from 1000 to 5000 it moves by up to 27 of 400 laws, `docs/tier-cycle.md`,
  "Why a sound rule costs the join") by law size, and the largest size still above a threshold. Serving proves every law, so the share proved at all
  would always be 1. Measured by a throwaway probe (`docs/tier-cycle.md`, "Free proofs by law size"): under the ref
  libraries the free share falls from .91-.96 to .78-.82 between sizes 7-9 and 11 on add3, sbo3 and mix3, and the
  libraries' gain over no rules grows with size. The 50% line lies beyond size 13, so the metric needs laws grown three
  or more times (`PARKED.md`, "Proposer targets beyond ranking" (a)).
