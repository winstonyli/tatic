# Roadmap

The project's goals, then ordered milestones, each the question it answers (format: `~/.claude/VERSIONING.md`).
`kind: experiment`: a tag marks a step and its message is the milestone sentence; tagging moves the line out of this
file. Only the user tags. Tagged so far: `v0.1.0` and `v0.2.0` (2026-10-22; `git tag -n99`). Deferred work is in
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

Goals 1 and 2 meet in compiled hot transformations with learned compilations (`README.md`, "Future work"). That is
not a milestone yet: the mined rules do not fire on the JIT's programs (`docs/tier-cycle.md`, "Other ways to join
the JIT and the loop", option A's result, 2026-10-17).

## Milestones

- **v0.3 - Does ranking which laws to mine on beat a random draw of the generator?** Answered no (2026-10-22), awaiting
  the tag; its sentence: "Choosing which generated laws to mine on moves M by a few percent, the frontier by a few
  points, and cost by nothing." Redrawn generator lists (`GEN_DRAW`) leave batch 0 and job CPU unchanged; the best of
  four draws per salt saves 51 laws of about 2230 in M, and lifts the free share at size 11 by 0.5-2.7 points over the
  mean draw, against 7-37 points for having a library at all (`docs/tier-cycle.md`, "How much choosing the extras can
  gain" and "Does the choice of extras move the frontier?"; `PARKED.md`, "A learned ranker over the generator's
  laws"). The model planned for it (goal 3: a custom model on the GPU tier, decided 2026-10-17, speaking the `show`
  syntax) takes its first job in v0.4 instead.
- **v0.4 - Can the kernel extend its own vocabulary?** (goal 2, and goal 3 once the model proposes) A proposed
  definition enters only if checked conservative. Seeds: `PARKED.md`, "Proposer targets beyond ranking" (c) and
  "Boolean combinations of comparisons" (its machine side passed a spike).
- **v0.5 - Does closing the cycle push the frontier?** (goals 2 and 3) Experiment 3: train on accepted laws, repeat,
  and track the frontier, not only M on a fixed stream. The frontier: on a fixed held-out set of laws larger than the
  families serve, the share proved free (with no whole-term machine proof, within the rule budget and the join's cap)
  by law size, and the largest size still above a threshold. Serving proves every law, so the share proved at all
  would always be 1. Measured by a throwaway probe (`docs/tier-cycle.md`, "Free proofs by law size"): under the ref
  libraries the free share falls from .91-.96 to .78-.82 between sizes 7-9 and 11 on add3, sbo3 and mix3, and the
  libraries' gain over no rules grows with size. The 50% line lies beyond size 13, so the metric needs laws grown three
  or more times (`PARKED.md`, "Proposer targets beyond ranking" (a)).
