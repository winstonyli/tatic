# Does the rule-mining loop learn, and do its rules transfer?

Status: measured on one machine, single deterministic runs per cell (no repeated seeds); the only noise estimate is the spread across
streams and across hash salts. Reproduce with `scripts/loop_stream.sh` (header documents every option); the sweep scripts and raw logs
are local and not in the repository.

## Setup
- **Laws.** A family is a pool of bit-vector terms; its laws are the pairs of pool terms that agree at widths 1-6 (the machine prover then proves them at width 4). Families:
  `add3` (add/sub/xor reassociation), `sbo3` (add/sub/and/or), `cmp3d` (comparisons over add/sub terms), `mix3` (arithmetic, bitwise and
  `shl1` mixed), and `u3` (the union of add3, sbo3 and cmp3d).
- **Stream.** Laws are served in batches (B=100, three batches per stream in the loops reported here). A stream is a residue class of the family's law
  sequence (`STRIDE`, `SPHASE`), so different phases are disjoint. `RULEMINER_SHUFFLE=<salt>` orders that sequence by a hash instead of
  lexicographically, which makes each batch a random sample of the family.
- **Metric M.** The number of laws that still need a whole-term machine proof (rewriting plus the built-in rules did not close them).
  Lower is better. Total M is the sum over a stream's batches.
- **Loop.** Batch r is served under the rules mined from batches 0..r-1; after serving, the miner mines rules from the batch it just
  served. The last batch is never mined. A *cold* loop starts with no rules; a *seeded* loop starts with a library mined on a different,
  earlier stream (phase 0).
- **Mining.** Greedy: each round adds the rule that most reduces M on the mined laws; it stops at `RULEMINER_ROUNDS` (default 8) or when
  nothing helps. `RULEMINER_FAST=1` counts machine fallbacks without building their proofs (about 10x faster, approximate).

## Findings
1. **The loop learns within a stream.** Cold per-batch M falls (for example cmp3d 31, 20, 11).
2. **A seeded start beats a cold start on every stream**: 15 of 15 sorted streams, and 9 of 9 for each of two shuffled salts. Total M
   over disjoint streams (five sorted, three per shuffled salt), cold vs seeded with the family's own library:

   | family | sorted (5 streams, pooled ratio) | shuffled salt 1 | shuffled salt 2 |
   |---|---|---|---|
   | cmp3d | 398 vs 227 (.57) | 190 vs 80 (.42) | 182 vs 96 (.53) |
   | add3 | 341 vs 127 (.37) | 183 vs 62 (.34) | 165 vs 51 (.31) |
   | sbo3 | 260 vs 155 (.60) | 126 vs 46 (.37) | 117 vs 47 (.40) |

   Sorted batches are lexicographic ranges, so their per-batch M mixes learning with batch structure; shuffled streams remove that.

   All numbers on this page predate the dedup of the term pools (`pool3`, after commit `ff664d6`). Some small terms had appeared more
   than once, which made 2-6% of the laws trivial or repeated. Rerun at salt 1 after the dedup: cmp3d 231 vs 109 (.47), add3 183 vs 62
   (.34, unchanged), sbo3 128 vs 41 (.32), seeded better on 9 of 9 streams. The other cells were not rerun.
3. **Rules transfer between families.** Seeding with another family's library recovers most of the gain (salt 1 total M, cold / own /
   foreign): add3 183 / 62 / 56-65, sbo3 126 / 46 / 52-66, cmp3d 190 / 80 / 118-119. cmp3d needs its comparison rules, so it benefits
   least.
4. **A pooled library transfers to a held-out family.** The merged add3+sbo3+cmp3d library took mix3 from 66 to 13 (mix3 contributed no
   rule). It does not change the two-variable shl, shr or lt families.
5. **One library can be mined on a mixed stream.** On `u3` the miner stops by itself (25 rules salt 1, 28 salt 2): cmp3d 54 and 60 (own
   library 80 and 96); sbo3 within +-8 of its own library on three of four salts (126/46/54, 117/47/72, 133/50/52, 142/54/52 for
   cold/own/mixed); add3 66 vs own 62 and 51. The 8-round default cap, not the approximate miner, was the limit: exact mining produced the
   identical library.

## What this does not show
- **Single runs.** Per-cell noise is unmeasured; the salts and streams are the only replicates. Differences of a few proofs are not
  evidence.
- **Related families.** add3, sbo3, cmp3d and mix3 share add/sub structure. Transfer to different operator structure is untested
  (the shift families show none).
- **M is machine proofs, not time.** Seeded vs cold is a count of laws, not a speed measurement.
- **Not a generality claim about theories.** Everything is Church bit-vector arithmetic. Whether the loop works for an axiomatic theory
  is only probed: in a throwaway spike over commutative-ring terms (axioms only, proofs found by a budgeted search, no kernel; not in this
  repository), M defined as the laws not proved within the budget separated cold from seeded loops (total M over five streams about
  100-140 cold vs 0-33 seeded at budgets 100-1000 on three salts, one outlier at budget 100). With the constants 0 and 1 as leaves the stream is dominated by a few
  zero/negation lemmas; without constants the separation stays (total M 33-38 cold vs 1-11 seeded) but cold M is small, and the miner finds
  the key lemmas from sub-terms of the failing laws without a fixed candidate pool. This shows the metric is usable, not that the loop
  learns a rich theory.
