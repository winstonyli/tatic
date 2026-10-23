# Roadmap

Ordered milestones, each the question it answers (format: `~/.claude/VERSIONING.md`). `kind: experiment`: a tag marks a
step, and its message is the milestone sentence; tagging moves the line out of this file. Only the user tags. Drawn on
2026-10-17 from the experiment plan in `docs/tier-cycle.md` ("Experiments" and the proposer bullets); deferred work is
in `PARKED.md`.

Renumbered 2026-10-22 at the first tag: `v0.1.0` covers the old v0.1 (kernel and rule miner), v0.2 (the bounded join
removes the floor) and the cold-loop answer of v0.3 (the law generator as a stage); `git tag -n99 v0.1.0` has the
numbers. What v0.3 left open is now v0.2. `v0.2.0` (2026-10-22) answered it: the generator pays everywhere it runs
(`git tag -n99 v0.2.0`).

- **v0.3 - Does a learned proposer, ranking which laws to mine on, beat the hash-ordered stream?** Experiments 1 and 2
  with the custom proposer model in place of the uniform and n-gram baselines.
- **v0.4 - Does closing the cycle push the frontier?** Experiment 3: train on accepted laws, repeat, and track the
  hardest law provable within a fixed budget, not only M on a fixed stream.
