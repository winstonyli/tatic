# Roadmap

The project's goals, then ordered milestones, each the question it answers (format: `~/.claude/VERSIONING.md`).
`kind: experiment`: a tag marks a step and its message is the milestone sentence; tagging moves the line out of this
file. Only the user tags. Tagged so far: `v0.1.0`, `v0.2.0` (2026-10-22), `v0.3.0` (2026-10-23), `v0.4.0` (2026-10-26) and `v0.5.0` (2026-10-31; `git tag -n99`). Deferred work is in
`PARKED.md`. The cleanup break from v0.5 (`docs/superpowers/plans/2026-10-26-cleanup.md`) is done (2026-10-27).

## Goals

Every milestone serves at least one of these; work that serves none needs a stated reason.

1. **A JIT on proved equivalence.** A higher-order term runs compiled once its compiled form is kernel-proved equal to
   it on every input (`README.md`, top; the code in `src/`).
2. **A kernel that improves itself.** It mines rewrite rules from the laws it proves, so later proofs are cheaper, and
   grows its own vocabulary through checked definitions, since a fixed vocabulary saturates (`docs/tier-cycle.md`,
   "Idea" and "Risks"; the miner in `tests/church_bv/`).
3. **The KR&R tier of a cycle with a GPU model.** A learned model on the GPU tier (nothing
   built; the idea came from the tiered-AI direction of the inactive scratchtape repo, which this repo does not rely on) proposes what to explore; the kernel checks and proves it, and returns rules and signals.
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

- **v0.6 - Does a learned proposer push the frontier?** (goals 2 and 3) Experiment 3: train a model on accepted laws,
  repeat the cycle, and track the frontier of v0.5, not only M on a fixed stream. Stage 1 (offline scorer over the extras, spec
  `docs/superpowers/specs/2026-10-31-learned-proposer-design.md`) is done: AUC 0.69 offline but no curve shift, worse than
  random at every n (`docs/tier-cycle.md`, "A learned scorer over the extras"). Stage 2 (the cycle) is parked (`PARKED.md`). Second try, done: select the extras by the kernel's own straggler
  verdicts inside the mine (`docs/superpowers/specs/2026-10-31-context-aware-selector-design.md`): held-out M better at every n but 1.4-1.9x the CPU, null by the pre-registered rule (`docs/tier-cycle.md`, "Selecting the extras by straggler verdict"). Third try, `EXTRAS_SELECT=cheap` (the stragglers with the fewest rewrite steps): the pre-registered rule missed by 26 s of CPU, but at matched work cheap n 160 beats random by 111 and 205 held-out M on two salt sets (`docs/tier-cycle.md`, "The cheap variant"). Knee charted (`v06k-g1` to `g12`): cheap beats random of equal work at n 80 and 160 (104-205 held-out M) and loses at n 240 and with pool 8. Coverage keys (`novel`, `reinforce`) equalled `cheap` with the binary class (`v06n-g1` to `g4`) and lost to it with the graded reach (`v06g2-g1` to `g4`); a2 parked. Crossover charted (`v06h2-g1` to `g6`): wins at n 80-160, loses at n 200 and 240; the key is dead under an empty base. Open: whether a kernel-verdict selection that helps at small n (about 700-1100 s of job CPU) is the v0.6 answer; untagged. The rest is parked (`PARKED.md`).
