# The kernel as the KR&R tier of a cyclical system

Status: direction and experiment plan (2026-10-10). The kernel side is built; the language-model side is not. Update the Results
section as experiments land.

## Idea
The overall system has tiers (see scratchtape's `README.md`, "Direction: tiered AI": a gradient-trained model on the GPU, knowledge
representation and reasoning (KR&R) on the CPU, working memory, long-term memory). tatic is the KR&R tier: a small trusted proof
kernel plus a rule miner. The tiers form a cycle rather than a stack:

- **LM -> kernel: what to explore.** The model proposes conjectures, candidate lemmas, or which family and shape to try next. Its
  output is untrusted.
- **Kernel -> LM: efficient reasoning.** The kernel accepts, rejects or proves each proposal. Proved laws are compiled into rewrite
  rules that replace long derivations, so later work is cheaper; verdicts and cost signals train the model.

## What exists (kernel side)
- The mine-and-serve loop (`scripts/loop_stream.sh`, `search::rule_miner`): laws are served in batches, rules are mined from them, M
  (laws still needing a whole-term machine proof) falls. Results and limits are in `docs/loop-result.md`.
- The explorer is not learned: a hash-ordered stream of a fixed family, and the miner's greedy candidate pool.
- Rule libraries plateau at about 25 rules on the current families: the fixed vocabulary saturates.

## Interface (to settle)
- Syntax across the boundary: the `show` syntax (`op(a, b)`, `0`, `-1`, variables `x y z`), parsed by `parse_term`. A law is
  `lhs = rhs`, a rule `lhs -> rhs`.
- Verdict per proposal, kernel -> LM: parse error, refuted by the width 1-6 screen, trivial (`lhs == rhs`), duplicate, known (already
  in the family), novel and true; for true laws, cheap (machine-free under the rules in force) or hard (needed a machine proof), and
  later proof size.
- Signals up, per round: M, per-rule use counts, the laws over budget (the frontier).

## Experiments
1. **Proposer yield** (kernel side done, see below). Given a proposer, what fraction of its samples parse, survive the screen, are
   new, and are hard? Baselines: uniform pool pairs and a character n-gram trained on verified laws. Swap a scratchtape LM in later.
2. **Does an LM-proposed stream mine better rules?** Feed accepted proposals into the loop and compare the mined rules' M reduction
   against the hash-ordered stream.
3. **Close the cycle.** Train on accepted laws, repeat, and track the frontier (hardest law provable within a fixed budget), not just
   M on a fixed stream.

## Risks
- Degeneration: the proposer repeats what it knows. Needs a novelty and difficulty filter from the kernel's signals.
- Soundness: only kernel-checked rules may enter the library. Machine-proved laws are checked; the ring-theory spike's lemmas are
  not (value screen only).
- Fixed vocabulary: more rules stop helping. Growth needs new operators or definitions, proposed by the model and checked
  conservatively (see the Boolean-comparison spec, local).
- Evidence so far is single runs on related add/sub/bitwise/comparison families.

## Results
### Experiment 1, kernel side (2026-10-10)
`search::classify_proposals` gives each proposed `lhs = rhs` line a verdict (unparsed, trivial, refuted, duplicate, memorised, known or
novel, each cheap or hard); the ignored test `proposal_yield` samples a proposer and prints a `YIELD` line (env documented on the test).
Baselines, 2000 samples, shuffle salt 1, default 250-law training window, no mined rules, one run each:

| family | proposer | unparsed | refuted | trivial/dup/memorised | true and new to the stream |
|---|---|---|---|---|---|
| add3 | uniform pool pairs | 0 | 1940 | 1 | 59 cheap |
| add3 | char 8-gram | 1517 | 472 | 11 | 0 |
| sbo3 | uniform pool pairs | 0 | 1960 | 0 | 1 known cheap, 38 cheap + 1 hard outside the family |
| sbo3 | char 8-gram | 1883 | 117 | 0 | 0 |
| cmp3d | uniform pool pairs | 0 | 1945 | 0 | 51 cheap + 4 hard outside the family |
| cmp3d | char 8-gram | 1983 | 17 | 0 | 0 |

Reading: random pool pairs are about 97% false (2-3% true); the n-gram mostly does not even parse (76-99%) and yields no true new
law, so a proposer must clearly beat both to be worth wiring in. "Outside the family" means true laws that the family's windowed
sequence omits (for example fewer than three variables); `known` counts only the family's own laws. With no rules installed the cheap
and hard split reflects only the built-in rules. Not yet run: the same with a mined library (`CHECK_RULES`), and a learned proposer.
