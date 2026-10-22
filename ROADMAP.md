# Roadmap

Ordered milestones, each the question it answers (format: `~/.claude/VERSIONING.md`). `kind: experiment`: a tag marks a
step, and its message is the milestone sentence; tagging moves the line out of this file. Only the user tags. Drawn on
2026-10-17 from the experiment plan in `docs/tier-cycle.md` ("Experiments" and the proposer bullets); deferred work is
in `PARKED.md`.

- **v0.2 - Does a bounded join in `prove_eq` remove the floor?** Every floor law joins within 5 steps over the rules in
  force ("Equational reach of the floor"); the milestone is that join turned into proof plans, measured on sweeps over
  salts 1-10. Answered yes, 2026-10-17, not tagged: own M 865 to 13, pooled 757 to 33, cold 4380 to 1568, every law
  kernel-checked, for 76% more sweep time ("The bounded join removes the floor"; its cost is in `PARKED.md`).
- **v0.3 - Can the kernel itself propose the laws that pay?** At matched counts, extra laws of shapes not being mined cut
  mined-batch M by 50% ("What kind of new law pays most"); a Ruler/Enumo-style generator would supply them without the
  test stream. First probe, 2026-10-17: a stream-blind wider grammar (`grammar_laws`) takes cold mined-batch M 221 to 28
  over salts 1-20, against 44 for the stream's own unseen laws: a tie (30 against 28 without salts 7 and 9); its padding-only slice gets 27 at 1.7-1.9 times their
  loop time ("A law generator"), but a quarter of its laws are served laws behind padding ("Why padding laws pay").
  With the same value-class twin filter on every source (salts 1-10), the padding laws lose to the stream (40 against
  29), the mixed grammar wins (21) at 9 times the stream's loop time, and the non-padding laws reach 10 at 26
  times, never worse than the stream on a salt ("One filter for every source"). Built as a stage, 2026-10-18: every
  mine with rule rounds mines a shared 16% slice of the generator's filtered non-padding laws; cold M over salts 1-20
  221 to 11, at 7786 loop seconds against 9, and at equal n it beats the filtered stream on 13 salts of 20, worse on 5
  ("The law generator as a stage"). Open: warm loops and ref mines, hidden twins (`PARKED.md`).
- **v0.4 - Does a learned proposer, ranking which laws to mine on, beat the hash-ordered stream?** Experiments 1 and 2
  with the custom proposer model in place of the uniform and n-gram baselines.
- **v0.5 - Does closing the cycle push the frontier?** Experiment 3: train on accepted laws, repeat, and track the
  hardest law provable within a fixed budget, not only M on a fixed stream.
