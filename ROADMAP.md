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

- **v0.4 - Do mined rules carry to laws the loop has not seen?** (goal 2) Measured by the held-out free share by band
  (11-17) and held-out M. Most held-out M is laws without `shr1` that the rules leave to a machine proof, and rules
  carry worst as laws grow: about one rule per law even among laws mined together (`docs/tier-cycle.md`, "Where a
  loop's definitions should come from"). Candidate levers, each tested on that measure: rule lifting (each rule made
  as general as still proves; tried 2026-10-25, held-out M -0.1%, same section); smaller rules (the cross-side cap at 9 or 7, tried 2026-10-26,
  held-out M +31%, same section); the pool route over three variables (tried 2026-10-26, held-out M -6.9%, job CPU
  1.84x, same section; with the lookahead off and rivals taken, -6.6% at 0.74x HEAD's CPU; kept 2026-10-26, the lookahead
  deleted); the `shr1` prover (`PARKED.md`, "A prover that knows what `shr1` means"); definitions,
  a vocabulary the kernel grows, entering only if checked conservative (seeds: `PARKED.md`, "Proposer targets beyond
  ranking" (c) and "Boolean combinations of comparisons"). Rescoped 2026-10-25 from "Can the kernel extend its own
  vocabulary?", after the probes in that section found no reach a vocabulary gives the miner.
- **v0.5 - Does closing the cycle push the frontier?** (goals 2 and 3) Experiment 3: train on accepted laws, repeat,
  and track the frontier, not only M on a fixed stream. The frontier: on a fixed held-out set of laws larger than the
  loops serve (the loops run on operator-set streams, the class-table spec's decision 11), the share proved free (with no whole-term machine proof, within the rule budget and the join's cap
  and visit budget, which must be fixed: from 1000 to 5000 it moves by up to 27 of 400 laws, `docs/tier-cycle.md`,
  "Why a sound rule costs the join") by law size, against the table alone. Serving proves every law, so the share proved at all
  would always be 1. The gate prints it per arm for bands 11-17 (`docs/tier-cycle.md`, "The frontier on the gate":
  .93 to .71 with mined rules since 2026-10-26, .76 to .60 without); no threshold, since no band nears 50% (the probe before it:
  "The frontier past the loops' sizes").
