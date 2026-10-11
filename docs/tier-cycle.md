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
and hard split reflects only the built-in rules. With a mined library installed (4000 pool samples, salt 1; none / family's own 8-rule library / 25-rule u3 library), the hard
true laws were add3 1/0/0, sbo3 2/1/1, cmp3d 5/4/2. Uniform pairs almost never hit the laws that M counts: the true ones are nearly
all cheap with no rules at all. A proposer is worth something to the miner only if it targets hard laws (idea 2 below).

### Difficulty band (2026-10-10)
`classify_proposals` now returns a `Cost` for each true, unmemorised law (machine proofs used, rule steps of the 200-step budget,
proved or not). The band is fixed: `Cost::hard` = still needs a machine proof, the laws M counts. `proposal_yield` prints a `BAND` line
and `BAND_OUT` writes the hard laws as a stream for the loop. `PROPOSER=stream` replays the family's own hash-ordered sequence from
`YIELD_SKIP`, the baseline experiment 2 compares against. Check, u3 library (salt 1), 300 held-out laws from skip 1000: the stream's
band is 30 (sbo3) and 9 (cmp3d), exactly M from `rule_set_kernel_check`. The pool proposer's band over the same 300 samples is 0 and 1.
The hard stream laws used 57 and 13 machine proofs with median rule steps 3 and 1, so the machine-proof count is the useful grade; rule
steps barely separate them. The stream also has 4-12 laws per 300 whose sides print identically, and 7-18 printed duplicates. All are
cheap, so M is unaffected.

### Mutation proposer and mining from the band (2026-10-10)
Setup: cold (no rules), shuffle salt 1, `RULEMINER_FAST`, 8-round cap, one run per cell. Seeds = the hard laws of the first 300 stream
laws (sbo3 75, cmp3d 100). `PROPOSER=mutate` (`MUTATE_SEEDS`, `MUTATE_KIND`) mutates them: `subst` (a variable becomes a small term on
both sides) and `wrap` (both sides under one operator with a small term) are true by construction; `edit` (one node of one side
replaced) mostly is not. The band (hard laws) per 1000 mutants:

| family | subst | wrap | edit | mix | pool pairs (per 1000, earlier) |
|---|---|---|---|---|---|
| sbo3 | 556 | 846 | 78 (895 refuted) | 534 | ~0.5 |
| cmp3d | 674 | none (every law is `lt`-rooted) | 75 (902 refuted) | 247 of 667 | ~1 |

So a proposer aimed at hard laws fills the band easily. But do the band laws teach better rules? `RULEMINER_LAWFILE` mines from a file.
Held-out M (300 laws, skip 2000 sbo3 / 5000 cmp3d; lower is better), each library 8 rules:

| mined from | sbo3 | cmp3d | mining time sbo3 / cmp3d |
|---|---|---|---|
| no rules | 94 | 109 | |
| stream, 300 laws (75 / 102 hard) | 19 | 27 | 47 s / 197 s |
| band, 300 hard laws from the first 1500 | 22 | 42 | 79 s / 306 s |
| mutants, 300 / 247 hard | 88 | 80 | 195 s / 253 s |
| stream + band | 22 | 44 | 105 s / 269 s |
| stream + mutants | 87 | 82 | 226 s / 261 s |

Reading: being hard is not enough. Hard mutants teach rules that barely transfer back to the family (M 80-88 vs 19-27), because they
are hard for reasons of their own (context, instances) rather than for the family's. Mining only from the stream's own hard laws is
no better than mining from the stream, and on cmp3d it is worse (42 vs 27, one run). The guard is not the cause: adding the stream's
cheap laws, which feed `RULEMINER_GUARD`, left it at 44. The 8-round cap binds in every cell, so more hard laws cannot buy more rules
here. For the cycle: the proposer's reward needs a transfer term (does a rule mined from its proposals lower M on the target
distribution), not difficulty alone. Experiment 2 has to measure that directly.

Salts 2 and 3 (stream vs band only, same setup), held-out M none / stream / band: sbo3 94 / 21 / 24 and 77 / 16 / 16; cmp3d 123 / 38 /
44 and 101 / 35 / 38. Mining from the band is never better than mining from the stream, and is usually within a few laws; salt 1's
cmp3d gap (27 vs 42) is the largest of the three.

**Transfer score.** `scripts/transfer_score.sh` (header documents it) mines rules from a law file and prints
`TRANSFER ... M_before M_after gain` on a held-out window of the target family: the batch-level reward a proposer needs. Check: the
salt-1 sbo3 stream file gives 94 -> 19 (gain 75), matching the table above. It costs one mine per batch (about 1-5 min FAST), so it
grades batches, not single proposals.

**Per-proposal credit.** `search::proposal_credit` (report test `proposal_credit_report`, env on the test). A rule's held-out gain is how
many more held-out laws are hard without it. A proposal *uses* a rule when it is cheap with the library but hard without that rule.
Each rule's gain is split evenly over its users. The cost is two passes per rule over the held-out window and the batch, seconds in
all, with no re-mining. Salt-1 libraries from the band-mining run, held-out windows as there (after the pool dedup, so M differs a
little from the tables above):

| library mined from | held-out M | sum of rule gains | proposals credited | rules with gain <= 0 |
|---|---|---|---|---|
| sbo3 stream | 92 -> 21 | 104 | 70 of 300 | 1 |
| sbo3 band | 92 -> 22 | 86 | 219 of 300 | 2 |
| sbo3 mutants | 92 -> 87 | 4 | 45 of 300 | 3 (one at -1) |
| cmp3d stream | 118 -> 44 | 82 | 83 of 300 | 1 (at -8) |
| cmp3d band | 118 -> 44 | 86 | 198 of 300 | 0 |
| cmp3d mutants | 118 -> 84 | 34 | 91 of 247 | 1 |

Reading: the credit separates useful proposals from useless ones within a batch. Mutants that led to non-transferring rules earn
about nothing, and the stream's credit concentrates on about a quarter of the laws. Ablation gains overlap: their sum exceeds the
batch gain (104 vs 71) because rules substitute for each other, so credit is a ranking signal, not an additive budget. A rule can
hurt held-out laws (cmp3d stream, gain -8), so credit can be negative, which is the signal to drop that rule. Every rule here had at
least one user, so all gain was attributed. Not yet used to train anything.

### Pool duplicates (2026-10-10)
The trivial and repeated laws in the stream come from the pools: `pool_duplicates` (ignored diagnostic) counts the add3 pool at 12680
terms but 12630 distinct, mix3 25245 / 23665, sbo3 26355 / 24105, cmp3d 18720 / 16560, cmp3 3600 / 3600. Depth-one terms such as
`add(-1, 0)` are built at more than one level. `pool_conjectures` pairs each group's first term with the rest, so a repeated term gives a
trivial law (the representative with its own copy) or repeated laws. Fixed: `pool3` now keeps each term once (test
`pools_have_no_repeated_terms`). This shifts every family's law sequence, so the experiments above (run before the fix) do not
reproduce exactly. The salt-1 headline was re-measured; see `docs/loop-result.md`.

### Derivability prune (negative, 2026-10-10)
Prototype (reverted): drop each rule that the built-in rules plus the earlier kept rules prove machine-free (`rewrite_law`, width 4),
in mining order as Enumo's `minimize`. It dropped 1 of 8 (add3), 0 of 8 (sbo3, cmp3d), 2 of 25 (u3, salt 1) and 3 of 28 (u3, salt 2)
rules. M on 300 held-out shuffled laws (salt 1, skip 1000; CHECK_FAST) rose with the pruned library: u3 salt 1 sbo3 30 -> 49,
cmp3d 9 -> 15; u3 salt 2 sbo3 49 -> 51, cmp3d 13 -> 14; add3 0 -> 0. A derivable rule is not redundant for a directed, budgeted
rewriter: it is a shortcut (Enumo's fast-forwarding makes the same point). The libraries are already almost irredundant, so the
25-rule plateau is not redundancy. Any prune must be judged by M, not derivability.

### Instruction count as a metric (2026-10-10)
Question: can a precise count of work replace M (a 0/1 count per law) as the efficiency signal? A hardware count of retired
instructions needs admin on Windows (ETW) and changes with every rebuild, and wasmtime fuel counts only JIT code, not the kernel. So the
count is the kernel's own deterministic work. `law_work_report` (ignored, needs `--features record-defeq`) writes one row per law:
fallbacks, rule steps, proof size, nodes built while building the proof, kernel node visits while checking it (instantiate, shift,
eq, conv and nf whnf, infer misses), beta steps, and the build and check wall times. The data is 300 held-out shuffled laws (salt 1;
skip 2000 sbo3, 5000 cmp3d), the same windows as the credit runs. The times are from the `record-defeq` build, whose probes make it
about 4x slower than a normal build (sbo3 own library: rule-law check 23 s there, 5.4-6.2 s normally); compare them only with each
other:

| family, library | M | kernel visits (M) | check s | build s |
|---|---|---|---|---|
| sbo3, none | 92 | 11.7 | 22.9 | 12.8 |
| sbo3, own (8 rules) | 17 | 12.9 | 22.1 | 6.3 |
| sbo3, from stream | 21 | 14.3 | 21.7 | 4.6 |
| sbo3, from band | 22 | 13.8 | 23.8 | 6.2 |
| sbo3, from mutants | 87 | 13.2 | 22.7 | 11.3 |
| cmp3d, none | 118 | 40.5 | 120.9 | 67.8 |
| cmp3d, own (8 rules) | 31 | 53.4 | 146.1 | 66.7 |
| cmp3d, from stream | 44 | 58.2 | 184.7 | 75.0 |
| cmp3d, from band | 44 | 38.2 | 104.8 | 47.3 |
| cmp3d, from mutants | 84 | 42.0 | 140.5 | 64.4 |

- **The count is a good proxy for time.** Per law, Spearman rho(visits, check time) is 0.97 on every sbo3 run and 0.86-0.96 on cmp3d.
  A samply profile of the sbo3 own-library run (non-feature build) puts about 67% of the time in the kernel check (`check_rc`,
  `def_eq`, `beta_spine`, `instantiate_n`, with hash-cons interning at 34% inclusive) and about 25% in building proofs (`rewrite_law`;
  the machine proofs' `add_tree_law` at 16%).
- **It ranks libraries differently from M.** The own, stream and band libraries cut M 3-5x, but kernel work stays flat or rises (sbo3 11.7M visits with no
  library, 12.9-14.3M with one; cmp3d 40.5M with none, 53.4M with its own). cmp3d's stream and band libraries tie on M (44) but differ
  by 1.5x in visits (58.2M vs 38.2M). Only build time falls (sbo3 12.8 s to 4.6-6.3 s).
- **Cause: each rule's proof is re-checked at every use.** `rule_step` applies the rule's proof term inline (`apps(law.0, ..)`), and
  each law is checked with fresh caches. A machine-free law under a mined library costs a median 32k visits, against 4.7k under the
  built-in rules alone. Checking the 8 sbo3 rule proofs once takes 0.76 s (`proof_cost_split`), against 22 s to check the 300 laws
  that re-check them. So under the current proof representation, M measures how many laws need a machine proof, not how much
  reasoning a library saves.
- **The count grades within M's classes, and the classes overlap.** Machine-free laws span 1.5k to 0.5-1.8M visits, machine-proved
  ones 25k to 0.4-3.7M. In every run, 28-122 machine-free laws cost more than the cheapest machine-proved law.

Next (not started): check each rule's proof once and pass the rule to the kernel as a typed parameter (`check_open` already types live
parameters), so a use costs one application. Then re-measure visits per library and decide whether visits (or visits plus a one-time
library cost, an MDL-like total) should replace M in the miner's objective and the proposer's reward.

### Hash-consing cost (negative, 2026-10-10)
Interning was 34% of the profiled time: about 15% in `instantiate_n` (interning its arguments for the memo key in `hc::args_id`, and
its results) and about 17% in the term constructors (`app2`, `lam`, `arrow`, `pi`, ...), almost all of it the table probe itself.
The hasher is already a pointer hash. Two prototypes (reverted) were run on `proof_cost_split`, sbo3 own library, 300 laws, pinned
to two cores (a mining job held six others), alternating runs:

| intern table | CPU s | peak memory | rule-law check s |
|---|---|---|---|
| one for the whole run (current) | 11.1-12.6 | 0.54 GB | 5.4-6.2 |
| one per law | 16.2-18.8 | 0.18 GB | 9.2-11.2 |
| none | 104-109 | 2.6 GB | 56-59 |

cmp3d (100 laws): 20.9 s and 0.99 GB with the table, 144 s and 9.6 GB without. The table is what makes the checks cheap: the proofs are
DAGs with about 140x sharing (sbo3 rule laws: 1.57M unique nodes against 220M without interning), and the table shared across laws
also reuses the instantiations of the inlined rule proofs. A table per law is slower, so it is not cleared between laws. What is left to
save is small: `args_id` re-interns arguments that are often already canonical (at most about 7% of the time, from the profile). The
real lever is not re-checking the rule proofs (above).

## Related work (surveyed 2026-10-10)
Three subagents read the primary sources; items they could not confirm are marked UNVERIFIED. The "for tatic" lines are our inference.

**Self-play conjecturer and prover.**
- *Minimo* (Poesia et al. 2024, arXiv 2407.00695): one LM conjectures and proves; the proposer is conditioned on a difficulty level taken from percentiles of proof log-likelihood; novel-goal-only hindsight relabeling stops `0=0` collapse. The library stays fixed, which the paper names as its main limit (proofs get longer, not deeper).
- *STP* (Dong & Ma 2025, 2502.00212): the proposer signal is the sampled pass rate; keeps "barely provable" conjectures (pass rate in (0, 1/4]), dedups, drops by an elegancy ratio, and re-weights by embedding similarity after mode collapse. No library growth.
- Expert iteration (Polu et al. 2022, 2202.01344): fixed statement set, no conjecturer. LeanConjecturer (2506.22005): novelty by `exact?`, non-triviality by `aesop`; truth of conjectures is its stated open problem.
- For tatic: every system gives the proposer a graded signal and has an explicit anti-degeneration filter. The kernel's proof cost is a deterministic analogue of Minimo's log-likelihood. Growing the library is the stated gap, which is what the miner fills. None of the sources read closes conjecture, verify, mine rule, retrain, so it is unclaimed in this sample, not necessarily in the literature.

**Library learning.**
- *DreamCoder* (2006.08381) scores libraries by MDL; *Stitch* (2211.16605) is a fast compression miner (utility = corpus cost reduction minus abstraction cost); *Babble* (2212.04596) mines modulo an equational theory with e-graphs, so tatic's rules could play the role of its theory; *LILO* (2310.19791) adds an LLM synthesizer, a cap of 10 abstractions per iteration, and re-derives the library each round. LILO's naming and documenting of abstractions mattered (anonymous names hurt).
- *LEGO-Prover* (2310.00656) and *Voyager* (2305.16291) admit on verification only; bloat control is a similarity dedup at most; only 24% of LEGO's solved problems used retrieved lemmas.
- *FunSearch* and *AlphaEvolve* are the only systems with explicit proposer-collapse control (islands, signature clusters, resets). *AlphaGeometry* trains on synthetic traceback targets (which constructions a proof needed) with a fixed rule set.
- For tatic: a net-utility score (Stitch/LILO style) is the principled library-size control found; our 25-rule plateau has no counterpart measurement in the literature read.

**Rule and conjecture synthesis.**
- *Ruler* (OOPSLA 2021, 2108.10436) and *Enumo* (OOPSLA 2023): enumerate terms, group them by values on sampled inputs (cvecs), verify with a user validator, and keep a rule only if the kept set cannot derive it by equality saturation. No rule-count budget. Enumo's stricter LHS-only derivability test and its minimize-against-prior-rules step look reusable. The Enumo arXiv id the subagent reported looks wrong; cite the venue only.
- *QuickSpec* and *Hipster*: test-based conjectures proved in Isabelle; routine-provable ones are pruned from display. *IsaCoSy*: each proved theorem constrains later synthesis; 38% precision on lists, many uninteresting.
- *Souper* ranks replacements by instruction-count benefit weighted by profile counts, the nearest precedent for ranking by downstream cost. No theory-exploration tool read ranks by proof cost, so greedy mining by machine-proof-count reduction has no direct precedent there.
- Learned conjecturing (Urban & Jakubuv 2020, 2005.14664): GPT-2 on Mizar; 9000-10000 proved but not the interesting ones. Gauthier's conjecturing work: UNVERIFIED, not found.

**Ideas to take, in order of cheapness.**
1. A Ruler/Enumo-style derivability prune on the mined library. Tried: negative, see Results.
2. Minimo/STP-style difficulty targeting: proposer samples scored by the kernel and kept only in a band. Done with a fixed band (see
   Results); a percentile band is not built.
3. Collapse control borrowed from FunSearch: signature-clustered sampling with a length preference, using our existing width 1-6 value signature.
4. AlphaGeometry-style traceback: train the proposer on the sub-terms or lemmas a kernel proof actually used.
