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

- **v0.3 - Does ranking which laws to mine on beat a random draw of the generator?** (goal 3) The baseline is the
  generator's own draw at the same n (`v0.2.0`), not the hash-ordered stream. Mined-batch M is nearly exhausted (at
  f = 0.32 over salts 1-10: warm 54, cold 17; `docs/tier-cycle.md`, "The generator's n after the wider filter"), so a
  win is the same M at a smaller n, or a lower warm batch 0 (about 675 over the same salts and the four warm
  stages; it measures the ref libraries). Gate: the spread of M
  and loop seconds across redrawn generator lists (`GEN_DRAW`, runs `2026-10-22-gen-draw1` to `3`) bounds what any
  ranker can gain; if it is flat, this milestone closes as decided against and the proposer's job moves to v0.4. The
  ranker is a custom model (decided 2026-10-17) on the GPU tier; laws cross the boundary in the `show` syntax
  (proposed, `docs/tier-cycle.md`, "Interface (to settle)"), and its labels are what each law's mine gained (per-law
  credit, `scripts/transfer_score.sh`, the miner's gains).
- **v0.4 - Can the kernel extend its own vocabulary?** (goal 2, and goal 3 once the model proposes) A proposed
  definition enters only if checked conservative. Seeds: `PARKED.md`, "Proposer targets beyond ranking" (c) and
  "Boolean combinations of comparisons" (its machine side passed a spike).
- **v0.5 - Does closing the cycle push the frontier?** (goals 2 and 3) Experiment 3: train on accepted laws, repeat,
  and track the frontier, not only M on a fixed stream. The frontier is not in the code yet. Proposed definition, to
  settle before building: on a fixed held-out set of laws larger than the families serve (so it needs
  `PARKED.md`'s laws beyond 5 nodes, "Proposer targets beyond ranking" (a)), the share proved within a
  fixed budget (the rule budget and the join's visit cap), and the largest law proved.
