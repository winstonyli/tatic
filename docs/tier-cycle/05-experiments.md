## Experiments
1. **Proposer yield** (kernel side done, see below). Given a proposer, what fraction of its samples parse, survive the screen, are
   new, and are hard? Baselines: uniform pool pairs and a character n-gram trained on verified laws. The model that replaces
   them is a custom ranker, not scratchtape's LM (below).
2. **Does a ranked choice of laws mine better rules?** Originally an LM-proposed stream against the hash-ordered stream; since
   `v0.2.0` the loops also mine on the law generator's extras, so the baseline is a random draw of the generator at the same n
   (milestone v0.3, `git tag -n99 v0.3.0`). Answered no at this n (2026-10-22): redrawn lists move M by a few percent and the frontier by a
   few points ("How much choosing the extras can gain", "Does the choice of extras move the frontier?").
3. **Close the cycle.** Train on accepted laws, repeat, and track the frontier, not just M on a fixed stream. The frontier is
   measured on the gate since 2026-10-25 ("The frontier on the gate"); closing the loop with a model is goal 3 in `ROADMAP.md`.

**The proposer model's target: ranking (decided 2026-10-17; design open).** The proposer will be a custom model architecture
built for this, not scratchtape's LM used directly. Its main job is (b) ranking which laws and candidates to try, ahead of (a)
laws beyond 5 nodes and (c) new definitions:
- **Why ranking.** The 5-node enumeration already yields every true law of that size, so the open question is choice.
  Labels exist: per-proposal credit, the transfer score ("Transfer score") and the miner's gains. There was a measured defect.
  Keeping one candidate per left side dropped add3's general `sub` chain orientation: serving add3 batch 0 gives M 46
  with its own library, 36 with sbo3's, and 27 with the chain rules swapped ("Why add3 did better with sbo3's library").
  Rival scoring has since fixed that case.
- **What bounds a ranker already.** Per-round re-ranking has been tried twice without a learned model. Each round's
  rival, winner and runner-up were finished greedily and the best kept: by in-sample value it lost (all loops M 1266 to
  1348); by held-out value it tied (1234 both ways), moving M between families ("Runners-up chosen held out"). A
  ranker over the same few alternatives can do no better than that. So the open question is whether any wider
  reordering has headroom. The miner logs only its winners (`RULEMINER chosen`), not every candidate's gain.
- **Literature.** Every learned win found reorders a complete, checked candidate set (premise selection, rewrite
  policies). Enumo shows plain size-5 enumeration already derives 327 of Halide's 725 rules. A survey's figures for
  LLM-proposed rules (28.1% / 69.7%; 36 of 977 unsound) were not found in the sources and are unverified. No learned
  proposer of new operators has a measured win.
- **Falsifier: oracle headroom (run 2026-10-17; not falsified).** At each round, take the top k candidates by gain,
  finish each greedily, value each on the batch served next, and keep the best. On the cold loops this lowers the
  mined batches' M by a quarter (248 to 187 over two salts) and saturates at k = 5 ("Oracle headroom for a ranker").
  It uses the test batch, so it measures what reordering could gain, not what a ranker would. The headroom sits in
  about 1 round in 10, and over 10 salts (-21%) nothing the miner sees predicts it: not in-sample lookahead (worse than
  nothing), gain, sizes or variables ("Can the miner see the headroom?").
- **More laws beat ranking candidates.** Valuing on 300 unserved laws of the same stream recovers 80% of the oracle's gain.
  Simply mining on those laws as well cuts mined-batch M by 59%, almost three times the oracle's gain (1169 to 479;
  "More laws beat any ranking"). So the proposer's ranking should be over which laws to mine on, not which candidates
  to keep. M falls steeply up to about 1000 extra laws (-82%) and levels off by 3000 at a per-family floor ("How
  many extra laws"). Part of that is renamed twins of the served laws among the extras; without them M still falls by
  two thirds (1169 to 388) and levels off near 400 ("Renamed twins"). Renamings of laws already served give only -20%:
  the proposer's lever is new laws.
- **The floor is permutations, not size.** Of the 171 laws left at the largest dose, 101 stay even when the miner mines
  on exactly them. 74 of those look like permutations of their other side (+ 1 on a different summand, `lt(~a, b)` against
  `lt(~b, a)`), and 61 hit a cycle cut ("What the floor is"). One path order for every rule instance joins more of
  them but makes whole loops 2-10x worse ("Ordered rewriting against the floor"). Adding the floor laws' normal-form
  pairs as rules (in-sample completion) removes up to 42 of cmp3d's 72 and none of add3's or sbo3's: for 59 of the 101
  the two sides already reach one rewrite cycle and the cut stops them at different members ("Completion on the floor").
  A bounded search with the rules in force used as equations, both ways, joins all 241 floor laws of both arms within 5
  steps and 0.01 s each, and no unequal control pair ("Equational reach of the floor"): the floor is a join problem.
  That search, building proof plans in `prove_eq`, removes the floor: over salts 1-10 own M 865 to 13, pooled 757 to 33,
  cold 4380 to 1568 (the rest is cold loops' first batch), every law kernel-checked, for 76% more sweep time ("The
  bounded join removes the floor").
- **Which new laws pay: other shapes of the same family.** At matched counts, extras with the shapes being mined give
  -17%, shapes the family never serves -19%, any shape not being mined -50%, as good as peeking at the next batches'
  shapes ("What kind of new law pays most"). The twins' extra gain (405 to 171) is mining on the test laws themselves:
  legitimate only when the stream is the proposer's own pool ("The twins gap").
- **Parked:** (a) laws beyond 5 nodes, since the floor turned out not to be about size; (c) until conservative
  definitions can be checked. All parked, deferred and unbuilt work, with triggers, is listed in `PARKED.md`.

