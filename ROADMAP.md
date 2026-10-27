# Roadmap

The project's goals, then ordered milestones, each the question it answers (format: `~/.claude/VERSIONING.md`).
`kind: experiment`: a tag marks a step and its message is the milestone sentence; tagging moves the line out of this
file. Only the user tags. Tagged so far: `v0.1.0`, `v0.2.0` (2026-10-22), `v0.3.0` (2026-10-23) and `v0.4.0` (2026-10-26; `git tag -n99`). Deferred work is in
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

- **v0.5 - Does closing the cycle push the frontier?** (goals 2 and 3) Experiment 3: train on accepted laws, repeat,
  and track the frontier, not only M on a fixed stream. The frontier: on a fixed held-out set of laws larger than the
  loops serve (the loops run on operator-set streams, the class-table spec's decision 11), the share proved free (with no whole-term machine proof, within the rule budget and the join's cap
  and visit budget, which must be fixed: from 1000 to 5000 it moves by up to 27 of 400 laws, `docs/tier-cycle.md`,
  "Why a sound rule costs the join") by law size, against the table alone. Serving proves every law, so the share proved at all
  would always be 1. The gate prints it per arm for bands 11-17 (`docs/tier-cycle.md`, "The frontier on the gate":
  .94 to .72 with mined rules since 2026-10-26, .76 to .60 without); no threshold, since no band nears 50% (the probe before it:
  "The frontier past the loops' sizes"). First finding (2026-10-26): the loops miss rules that transfer because they
  serve few or no laws as large as the held-out ones; mining 500-1000 fresh laws of those sizes per band cuts held-out M
  22-28% (`docs/tier-cycle.md`, "Fresh laws of the held-out sizes do as well"). Design chosen 2026-10-26: draw the
  extras (laws a loop's mines take but it does not serve) from the sequence at 4 growths instead of 2, at every size
  (replacing the small ones cost band 11) and minus every held-out law and its twins; the extras' count is open, weighed against
  mining CPU (`docs/tier-cycle.md`, "As the loop's extras" and "At every size, and at three times the count"; rejected designs in `PARKED.md`, "Mine large laws after the
  loop" and "Serve laws of the held-out sizes").
