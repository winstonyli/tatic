# Roadmap

Ordered milestones, each the question it answers (format: `~/.claude/VERSIONING.md`). `kind: experiment`: a tag marks a
step, and its message is the milestone sentence; tagging moves the line out of this file. Only the user tags. Drawn on
2026-10-17 from the experiment plan in `docs/tier-cycle.md` ("Experiments" and the proposer bullets); deferred work is
in `PARKED.md`.

Renumbered 2026-10-22 at the first tag: `v0.1.0` covers the old v0.1 (kernel and rule miner), v0.2 (the bounded join
removes the floor) and the cold-loop answer of v0.3 (the law generator as a stage); `git tag -n99 v0.1.0` has the
numbers. What v0.3 left open is now v0.2.

- **v0.2 - Does the law generator pay everywhere it runs?** On cold loops the stage cuts mined-batch M 221 to 11 over
  salts 1-20, better on every salt, but its join searches cost 7786 loop seconds against 9 ("The law generator as a
  stage"; lazy join steps and lanes cut that since). Warm loops and ref mines: measured 2026-10-22, the stage pays in
  both and stays on (salts 1-10: warm-loop M 735 against 1067 with the generator off everywhere and 911 with only the loops' extras off; cross
  better on 10 salts of 10; pooled the one stage that loses, weakly, `PARKED.md`; "The law generator on ref mines and
  warm loops"). Hidden twins, 2026-10-22: the filter now normalizes every node below a law's root, which drops 11% of
  the loops' extras as served laws in disguise and 30% as trivial, in every family; M rises to cold 1475 and warm 754,
  still better than the generator off on 9 and 10 salts of 10, mixed loops the one stage that loses ("Hidden twins
  beyond two-leaf nodes"). Answered yes; its control switches `GEN_SOURCE`/`GEN_N` are deleted.
- **v0.3 - Does a learned proposer, ranking which laws to mine on, beat the hash-ordered stream?** Experiments 1 and 2
  with the custom proposer model in place of the uniform and n-gram baselines.
- **v0.4 - Does closing the cycle push the frontier?** Experiment 3: train on accepted laws, repeat, and track the
  hardest law provable within a fixed budget, not only M on a fixed stream.
