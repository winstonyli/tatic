# Roadmap

Ordered milestones, each the question it answers (format: `~/.claude/VERSIONING.md`). `kind: experiment`: a tag marks a
step, and its message is the milestone sentence; tagging moves the line out of this file. Only the user tags. Drawn on
2026-10-17 from the experiment plan in `docs/tier-cycle.md` ("Experiments" and the proposer bullets); deferred work is
in `PARKED.md`.

- **v0.1 - Can a small trusted kernel plus a rule miner turn a fixed law stream into rules that remove machine proofs?**
  Built: the mine-and-serve loop (`driver::loop_stream`, `search::rule_miner`), the proposal verdicts of experiment 1's
  kernel side, and the extra-laws, floor and equational-reach measurements. `Cargo.toml` is at `0.1.0`; not tagged.
- **v0.2 - Does a bounded join in `prove_eq` remove the floor?** Every floor law joins within 5 steps over the rules in
  force ("Equational reach of the floor"); the milestone is that join turned into proof plans, measured on sweeps over
  salts 1-10. Answered yes, 2026-10-17, not tagged: own M 865 to 13, pooled 757 to 33, cold 4380 to 1568, every law
  kernel-checked, for 76% more sweep time ("The bounded join removes the floor"; its cost is in `PARKED.md`).
- **v0.3 - Can the kernel itself propose the laws that pay?** At matched counts, extra laws of shapes not being mined cut
  mined-batch M by 50% ("What kind of new law pays most"); a Ruler/Enumo-style generator would supply them without the
  test stream. First probe, 2026-10-17: a stream-blind wider grammar (`grammar_laws`) takes cold mined-batch M 221 to 28
  over salts 1-20, against 44 for the stream's own unseen laws: a tie (30 against 28 without salts 7 and 9); its padding-only slice gets 27 at 1.7-1.9 times their
  loop time ("A law generator"). The generator's spec is next (`PARKED.md`).
- **v0.4 - Does a learned proposer, ranking which laws to mine on, beat the hash-ordered stream?** Experiments 1 and 2
  with the custom proposer model in place of the uniform and n-gram baselines.
- **v0.5 - Does closing the cycle push the frontier?** Experiment 3: train on accepted laws, repeat, and track the
  hardest law provable within a fixed budget, not only M on a fixed stream.
