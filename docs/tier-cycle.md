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

Done next: lemmas as kernel parameters (below).

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

### Lemmas as kernel parameters (2026-10-10)
`shared_lemma` (rewrite.rs) checks each closed lemma's proof once and binds its statement as a parameter in a
`Postulates` scope of its own; the rewriter then uses the parameter (a `Free`) instead of the proof, and `ck` checks with
`check_open` against the parameters bound so far. One hook covers every closed lemma the proofs reuse: the mined rules, the built-in
add lemmas (assoc, identity, not, comm), `shrmask`, the GoodBv witness lemmas (`good_add`, `good_sub`, `good_shl1`, `good_shr1`) and
the machine proofs' case lemmas (`add_tree_law`'s `guarded`, which replaced its own `LEMMAS` cache). The `gbit` pairs stay inlined:
their first half is an operator that must compute. A lemma's proof may use lemmas bound before it (a mined rule proved through a
machine proof uses that proof's case lemmas), so the scopes nest in binding order. A law over parameters is not closed; `discharge`
closes the scopes innermost first, `(\r_0. .. ((\r_m. body) P_m) ..) P_0`, giving a closed term the plain checker accepts
(`a_law_over_lemma_parameters_discharges_to_a_closed_proof`, including a nested rule). M is unchanged.

This is the only path: the `LEMMA_PARAMS` switch that kept inlined proofs as the default was removed, and every check in the miner and
the tests goes through `holds`/`ck` (encoding.rs), which check against the parameters bound so far. The "off" columns below were
measured before the removal and are kept as the record of what inlining cost. The salt-1 cold and own-seeded loops (18 cells,
`scripts/experiments/cross_run.sh` with `CHECK_FAST=0`, so every served law is built and kernel-checked against the parameters) give
the same per-batch M and rule counts as the earlier count-only runs in every cell.

Kernel work (`law_work_report`, same windows and `record-defeq` caveat as above). `law_work_report` now also counts kernel visits
while building a proof, which is where the one-time lemma checks run:

| family, library | M | law-check visits (M), off / on | build visits (M), off / on | total (M), off / on | median machine-free law, off / on |
|---|---|---|---|---|---|
| sbo3, none | 92 | 11.7 / 2.5 | - / 22.9 | - / 25.3 | |
| sbo3, own | 17 | 12.9 / 1.2 | 8.6 / 11.5 | 21.5 / 12.7 | 32k / 2.3k |
| cmp3d, none | 118 | 40.5 / 4.8 | - / 99.0 | - / 103.9 | |
| cmp3d, own | 31 | 53.4 / 3.1 | 69.1 / 103.8 | 122.5 / 106.9 | 46k / 2.5k |

Normal build, `proof_cost_split`, own library, pinned to two cores, ABAB, machine quiet (7-15% CPU):

| family | CPU s off | CPU s on | law check s off / on (rule laws + machine laws) | build s off / on |
|---|---|---|---|---|
| sbo3 | 9.7, 10.0 | 5.1, 5.2 | 6.0, 6.3 / 0.37, 0.37 | 2.9, 2.9 / 4.1, 4.3 |
| cmp3d | 58.3, 58.6 | 44.9, 45.2 | 32.2, 32.4 / 1.2, 1.3 | 23.4, 23.5 / 42.1, 42.4 |

A first version that bound only the rewriter's lemmas (not the case lemmas) cut law-check visits to 2.4M (sbo3) and 28.0M (cmp3d).

- **Checking a law is now cheap and a library cuts it.** Law checks fall 16-25x in time and 11-17x in visits; a machine-free law
  costs a median 2.3-2.5k visits. With parameters on both sides, the own library cuts law-check visits 2.1x on sbo3 (2.5M to 1.2M)
  and 1.6x on cmp3d (4.8M to 3.1M), the direction M predicts.
- **Total CPU falls 1.9x (sbo3) and 1.3x (cmp3d).** The rest is building, which now includes the one-time lemma checks. cmp3d's
  case lemmas are numerous and specific to a machine, so checking each once saves less than the rules do (total visits 122.5M to
  106.9M).
- **Building uses the kernel more than checking does.** Even with parameters off, building the proofs costs 8.6M (sbo3) and 69.1M
  (cmp3d) kernel visits, uncounted before this column.

### Where the build visits went (2026-10-10)
An attribution prototype (reverted; per-call-site counters around the builders, parameters off) found the build visits were almost
all the kernel's `shift`, called by the proof builders themselves rather than by kernel checks. On cmp3d (69M): `lemma_n` 42.7M (its
motive and its leaf, about half each), `lemma_dd` 12.5M, other shifts 7.3M, `add_tree_law` 2.7M, `raw_table` normalisation 1.9M,
`nf_whnf` 1.1M. The source was `bool0()` (`Pi C. C -> C -> C`): written with `arrow`, which shifts its codomain, and `and`/`or`/`xor`
rebuild it at every call, millions of times while building the case-tree motives. `bool0` is now written with explicit `pi`s, which
removes the shift and leaves the term identical (per-law M, nodes and check visits unchanged). With parameters off, build visits
fell from 8.6M to 2.0M (sbo3) and from 69M to 17.3M (cmp3d).

The rest of cmp3d's builder cost is mostly `lemma_dd` (11.0M): `cong_n` and `trans_proof` shift the J motive at every node of a
decision diagram. Parked: removing it needs a different proof shape (for example a closed `cong_mux` lemma used as a parameter), and
these shifts are cheap in time (below), so it would change the visit count more than the run time.

Kernel work with parameters as the only path and the new `bool0` (same 300-law windows; M and law-check visits identical to the
"on" columns above):

| family, library | M | law-check visits (M) | build visits (M), before / after `bool0` | total (M), before / after |
|---|---|---|---|---|
| sbo3, none | 92 | 2.5 | 22.9 / 8.2 | 25.3 / 10.6 |
| sbo3, own | 17 | 1.2 | 11.5 / 4.9 | 12.7 / 6.1 |
| cmp3d, none | 118 | 4.8 | 99.0 / 32.8 | 103.9 / 37.7 |
| cmp3d, own | 31 | 3.1 | 103.8 / 52.0 | 106.9 / 55.1 |

- **Total kernel work and M now disagree on cmp3d.** The own library cuts M 3.8x and law-check visits 1.6x, but raises total visits
  1.46x (37.7M to 55.1M), because building under it costs more (52.0M against 32.8M). On sbo3 both agree (total 10.6M to 6.1M).

Split by region (prototype, reverted: exclusive attribution of counted visits to nested labelled regions, cmp3d, 300 laws, millions
of visits with lemma counts in parentheses):

| region | none | own | own, `NOBDD=1` |
|---|---|---|---|
| case-lemma checks, for the laws' machine proofs | 28.7 (683) | 29.9 (344) | 27.3 (344) |
| `lemma_dd` building (the case lemmas with nv >= 9) | 0 | 11.0 (15) | 0 |
| case-lemma checks inside the mined rules' proofs | 0.3 (104) | 3.8 (188) | 3.8 (188) |
| rewriting and the rest of building | 3.8 | 7.2 | 7.2 |
| law checks | 4.8 | 3.1 | 3.1 |
| total | 37.7 | 55.1 | 41.4 |

- **Checking case lemmas is most of the kernel work** (61-77%). The laws' machine proofs need half as many case lemmas under the own
  library, but each costs about twice as much (87k against 42k visits): the laws the library leaves are the ones with wider machines.
- **By visits the diagram proofs cost more than the case trees they replace, by time they cost less.** All 15 diagram lemmas come
  from the laws' machine proofs (none from the rule proofs). With `NOBDD=1` the same lemmas are case trees: building them costs no
  counted visits (after the `bool0` fix) and checking them costs 2.6M less, so the total falls 55.1M to 41.4M with M unchanged (31).
  But `proof_cost_split` (normal build, own library, pinned to two cores, five alternating runs each, machine load 7-66% from another
  program, so best-of) takes 52.2 s CPU with case trees against 47.1 s with diagrams: building 2^nv-leaf trees costs time the
  visit count does not see. Diagrams stay (`DDMIN=9`).
- **Shift visits are cheap.** The `bool0` fix removed 2-3x of the build visits but did not change time (same runs: sbo3 5.7-6.8 s old,
  5.5-6.3 s new; cmp3d 47.5-49.0 s old, 47.1-51.9 s new). So the visit count overweights `shift` and misses term construction; as
  a cost for the miner's objective it needs weights (or construction counts, `take_hc_built`) checked against time first.
- **Even without diagrams the library costs more kernel work than none** (41.4M against 37.7M): its rules' own machine proofs
  (3.8M, checked once) and the longer rewriting outweigh the cheaper law checks.

### A rewrite cycle behind cmp3d's leftover laws (2026-10-10)
Of the 31 cmp3d laws that need a machine proof under the own library, 20 used up the whole rule budget (200 steps; no law does
without a library; sbo3: 2 of 17). The cause is a cycle between a mined rule and the built-in ones:
`lt(x, sub(y, z)) -> lt(x, add(sub(x, y), z))` (mined) undoes `lt(x, add(x, y)) -> lt(x, sub(0, y))` and `sub(x, 0) -> x`
(built in), so `lt(y, add(y, z))` loops until the budget runs out. The budget is shared by both sides of a law, so the other side
is left half-normalised, and the pair needs a machine proof that is larger than the one without the library (more carries, for
example 6/4 instead of 4/4; `normal_forms` now prints them). 9 of the 31 laws need no machine proof at all without the library.
On the same 31 laws the kernel visits are 11.6M without the library and 48.1M with it.

The mined rule grows in the rule order (`x` occurs twice on the right), so the order check would reject it; it got in as a
*cross-side* rule (three or more variables, abstracted from the two sides of a law), which the miner admits without an order
check, leaving the budget as the only guard against cycles (`search.rs`, `ok_order`). Its reverse direction goes down in the order.
**Ordering cross-side rules makes M worse (negative, reverted).** Orienting each cross-side candidate by the rule order (reversed
when only the reverse goes down, dropped when neither does), re-mining the salt-1 libraries and re-running the loops (count-only)
raised total M everywhere: cold 542 to 624 (cmp3d, add3, sbo3), seeded cmp3d 109 to 153, add3 62 to 124, sbo3 41 to 122; the
libraries' own mining streams went from 45 to 80 (cmp3d). The growing cross-side rules do useful work in every family, not only the
one that cycles. Some ordered runs still used up the budget (sbo3 seeded: up to 6 laws in a batch), so the order alone does not
stop it either.

Kept: a tripwire. `rule_set_kernel_check` counts the laws that used up the rule budget (`CHECKED ..., N used up the rule budget`),
and `scripts/loop_stream.sh` writes it as the sixth column of `m.tsv` and as `exhausted=` in its last line. cmp3d's own library: 23
of 300 laws; no library: 0.

### Per-side rule budget; rejecting cycling candidates is a negative result (2026-10-11)
**Each side of a law now gets the whole budget** (`rewrite_law`). Afterwards the budget is what the hungrier side left, so the
tripwire still counts a law whose either side used it up. With libraries re-mined under it (salt 1; sbo3's library is unchanged,
add3's and cmp3d's differ by one rule each), total M against `loop_dd1` (shared budget):

| | cmp3d | add3 | sbo3 |
|---|---|---|---|
| cold | 231 to 224 | 183 to 183 | 128 to 121 |
| seeded (own library) | 109 to 74 | 62 to 67 | 41 to 40 |

On cmp3d's 300-law timing batch, the old library cut M from 31 to 24. Wall time pinned to two cores on a quiet machine
(load 9-14%, RTP off; best of two runs, alternating):

| exe | no library | own library |
|---|---|---|
| shared budget | 47.7 s | 46.1 s |
| per-side budget | 47.3 s | 34.6 s |

So the own library now saves 1.37× instead of 1.03×. sbo3's batch is unchanged at 5.8 s. The cycles themselves remain: 28-32
seeded cmp3d laws per stream still use up the budget, now on one side only.

**Rejecting a candidate that makes a mining-batch law use up the budget makes M worse (negative, reverted).** The miner scores at
40 steps (`RULEMINER_STEPS`). With the old libraries, 197 of sbo3's 200 mining-window laws normalize in at most 40 steps and 3
cycle, so a 40-step budget does detect the cycles. But rejecting every candidate that makes even one law cycle throws out the
best rules. sbo3 lost `add(sub(x, y), z) -> add(sub(z, y), x)` (+18 fixed). The libraries' own windows went from 12 to 24
(sbo3), 20 to 35 (add3) and 45 to 51 (cmp3d), and mining took about twice as long. Loops (with per-side budget too) gave seeded
cmp3d 103, add3 91, sbo3 56 against 74 / 67 / 40 without the rejection, and cold 222 / 195 / 144. No law used up the budget in
any of those runs. A cycle on a few laws costs time; a rejected rule costs M on many.

**Why ordered sbo3 still cycled** (the oriented runs above). It is a true cycle, not 200 steps being too few. On
`sub(sub(z, x), sub(y, z))` five steps repeat until the budget runs out:
`sub(sub(x, y), z) -> sub(x, add(y, z))`, `add(x, sub(y, z)) -> sub(x, sub(z, y))`, and three uses of the permutative
`sub(x, sub(y, z)) -> sub(z, sub(y, x))`. By default, a rule is checked once against the rule order, or for a tie against a rule-level
tie-break (`rule_order_or_tie`), and then fires on every instance unchecked. Only permutative rules are checked per instance, and
then by `show()` order. Those are different orders, so steps that mix them need not terminate. `PERM_ORDER=lpo` checks every tied instance against
one path order. On those three batches it removes all 7 exhausted laws, but M rises from 8 to 18, with libraries mined under the
default order.

Diagnostics kept: `rule_set_kernel_check` prints `EXHAUSTED <law>` per law; `normal_forms` gives each side its own budget and
prints `steps a/b`.

### Kernel cost calibrated against time (2026-10-10)
`law_work_report` now writes each counted slot separately for building (`b_`) and checking (`c_`), plus the terms built while
checking, and also runs in the normal build (counts zero, uninstrumented times). Per-law time (normal build, pinned to two cores,
the smaller of two runs; the machine was not quiet, 16-58% load from other programs) was fitted against the per-law counts (feature
build) by non-negative least squares on half of the 1,200 rows (sbo3 and cmp3d, own library and none), and tested on the other
half. Held-out error (sum of absolute errors over total time): 18% for the fit, 55% for raw visits with one weight. The weights
are collinear and not individually meaningful; building's `shift` visits got weight 0, as the `bool0` timing found.

| family, library | M | time s | fitted s | total visits (M) |
|---|---|---|---|---|
| sbo3, none | 92 | 10.9 | 13.5 | 10.6 |
| sbo3, own | 17 | 4.8 | 7.0 | 6.1 |
| cmp3d, none | 118 | 50.8 | 51.7 | 37.7 |
| cmp3d, own | 31 | 46.2 | 48.9 | 55.1 |

- **By time the own library is cheaper on both families** (sbo3 2.3x, cmp3d 1.1x), the direction M gives; raw visits ranked
  cmp3d's library the other way. cmp3d gains little because of the cycle above.
- **Decision: M stays the miner's objective.** It agrees in direction with time on both families, is deterministic, and can be
  counted without building proofs (`RULEMINER_FAST`), which a fitted cost cannot (it needs the feature build, about 4x slower, and
  weights tied to this machine). The fitted cost is a check to report beside M, not an objective. The cmp3d gap between M's cut
  (3.8x) and time's (1.1x) is a defect in the library (the cycle), not in M.

The cmp3d gap is now smaller (time 1.37×, see "Per-side rule budget" above), and the cycles that cost each exhausted law 200 steps
are cut (see "Cycle cut" below).

### Cycle cut; lpo and a cycling penalty are negative results (2026-10-11)
Three ways to stop the rewrite cycles, each with libraries re-mined under it (salt 1, per-side budget), total M (cmp3d / add3 / sbo3):

| | cold | own library | laws using up the budget, own |
|---|---|---|---|
| per-side budget (baseline) | 224 / 183 / 121 | 74 / 67 / 40 | 91 / 60 / 11 |
| `PERM_ORDER=lpo`, mined and served | 262 / 223 / 189 | 170 / 154 / 156 | 128 / 0 / 0 |
| miner penalty (`RULEMINER_CYCLE=1`) | 228 / 195 / 135 | 74 / 61 / 40 | 92 / 16 / 11 |
| **cycle cut** | **214 / 183 / 123** | **68 / 61 / 35** | **0 / 0 / 0** |

- **lpo (negative, deleted).** Checking every tied instance against one path order costs too much coverage: the libraries mined
  under it are worse everywhere, and cmp3d's unordered cross-side rules still cycle. `PERM_ORDER` is gone, with the older `tie`
  mode (section 87, never the default and not rerun), since the cut covers the cycles both modes targeted.
- **Penalty (negative, deleted).** A newly cycling law costs the candidate what a lost fix would. It helps own add3 (61 vs 67)
  and loses on every cold stream (+47 in all).
- **Cycle cut (kept, default).** Rewriting is deterministic apart from the step budget, so `rewrite(t)` called while `t` is
  already being rewritten further out can only repeat that work. `rewrite` keeps the path of terms in progress and returns `t`
  unchanged (proof `refl`) on a repeat, so the chain ends after one lap instead of at the budget. The rewrite memo does not cache a
  result that a cut shaped. Test: `rewrite_cycles_are_cut` (sbo3's five-step cycle; fails with the cut disabled).

Serving time with the cut, on the 300-law calibration batches (pinned to two cores, quiet machine at 5-15% load, RTP off; best of two
alternating runs):

| batch | no cut, per-side libraries | cut, same libraries | cut, libraries mined under it |
|---|---|---|---|
| cmp3d | 34.3 s (M 24, 23 exhausted) | 26.2 s (M 21, 0 exhausted) | 26.0 s (M 21) |
| sbo3 | 5.7 s (2 exhausted) | 5.2 s | 5.0 s |

So the cut alone makes cmp3d serving 1.31× faster. Against no library (47.3 s, measured earlier without the cut), cmp3d's own library now saves about 1.8×,
up from 1.37× (per-side budget) and 1.03× (shared budget).

Cross-family transfer was rerun under the per-side budget (`docs/loop-result.md`, findings 3-4).

### Miner speedups (2026-10-11)
On cmp3d's ref mine (`RULEMINER_FAST=1`, 2 threads, salt 1) the first two changes took the mine from 600 s to about 210 s (loaded
machine, alternating runs), with identical rules at each step unless noted:
- **No rule proofs while counting.** `shared_lemma` returns a placeholder under `SCORE_ONLY`. Rule lemmas had been re-proved in
  every round, because worker threads are re-spawned and the closed-lemma cache is per thread. Rounds went from 31-79 s to 2-9 s.
  `TREE_LAWS` does not cache placeholder proofs.
- **Exact fallback counts.** The `SCORE_ONLY` shortcut counted a machine fallback for any machine-shaped pair, even unequal operands
  (an `lt` congruence that the full build proves with one fallback counted 2-3). `machine_fallback` now first looks for a counterexample
  in 16 tuples, and both `prove_eq` and `rewrite_law`'s `lt` branch go through it. Straggler counts now match the full build exactly,
  so `RULEMINER_FAST` is no longer approximate. The chosen rules change with the exact counts, but the M total stays 37. The
  straggler phase also runs counting-only (57-79 s to 2 s).
- **False cross-side candidates.** Abstracting the cut subterms of a cross-side pair into variables can turn a true instance into a
  false rule (14 of cmp3d's 205, all `lt`). They were scored and then failed the proof filter. Worse, the one-per-left-side pass
  kept the false rule in place of a true one for the same left side. The generalized rule is now checked before it becomes a
  candidate.
- **Lazy proving.** Under `RULEMINER_FAST`, only each round's winner is proved, and an unprovable winner gives way to the next best.
  This replaces the 71-76 s up-front proof filter; winners take 0.1-1.3 s each. The net gain is smaller than that phase. The 7 true
  candidates that the false ones had displaced are general `lt(x, ...)` reassociations that cycle. They doubled the scoring rounds
  (7 to 14 s) until the cycle cut, which now ends those cycles after one lap.

All together, with the cycle cut, on a quieter machine (load 11-17%, adjacent runs): 100 s against 168 s for the build with only the
first two changes. Scoring rounds take 2-7 s and each winner's proof 0.1-1 s, and the mine's M is 30 against 37 (the rules differ
through the cut).

- **Gain bound (exact, small gain).** A candidate can change only the laws it affects, so its gain is at most 1000 per affected
  uncovered straggler, `guard_w` per affected uncovered guard law, plus the affected stragglers' sizes. Each round scores candidates
  in chunks (four per thread), highest bound first, and stops at a bound below the best gain so far. It skips 86% of the scorings
  on cmp3d (1367 of 1584) with identical rules (also at one thread on sbo3), but the mine only drops from 95 s to 87-90 s. The
  candidates with the highest bounds are the general patterns that rescore most laws, and they cost the most. They are also the
  ones that can win, so no exact bound skips them. Base evaluation and bounds take 0.3-0.4 s a round.
- **Seeded memo (exact, 1.5x scoring).** A candidate is tried after the chosen rules, so a memo entry whose trace its left side
  matches nowhere has the same result with it (`RewriteMemo::filtered`, the per-sub-term form of the `affected` argument; checked by
  `filtered_memo_entries_hold_under_an_extra_rule`). Each worker keeps a memo valid under the chosen rules for the round. It seeds
  every candidate's scoring with the entries that candidate cannot change, and it adds the entries the candidate computed without
  matching their traces. Workers are spawned once a round and fed chunks over a channel, since expressions are per thread and
  cannot be shared. On cmp3d's ref mine (2 threads, pinned to two cores, ABAB, machine load 30-60%), the scoring rounds take
  30.5-32.1 s against 45.7-49.1 s. sbo3's take 5.6-7.5 s against 7.0-7.1 s. Rules were identical in every run. A first version
  rebuilt each worker's memo from all laws every round: 1.4x at one thread but 1.19x at two.

**Where the time goes now (salt 1, committed miner).** A ref run (`transfer_mines.sh`) is mostly serving. cmp3d's 120 s splits into
66 s of full kernel checks on 400 laws, 34 s of mining, and about 20 s of process launches and the two machine-state lines. The
loops serve with `CHECK_FAST=1`, so there:

| loop (3 phases) | total | serving | mine phases |
|---|---|---|---|
| add3 own | 54 s | 15 s | 22 s |
| sbo3 own | 52 s | 20 s | 17 s |
| cmp3d own | 64 s | 17 s | 29 s |
| add3 cold | 70 s | 19 s | 28 s |
| sbo3 cold | 73 s | 26 s | 26 s |
| cmp3d cold | 132 s | 22 s | 90 s |

Serving includes its launch, and the remainder is mostly the mines' launches. Even `cmd /c exit` took 1.2 s from the loop's shell.

**Loop overhead (fixed, 2026-10-11).** The launch cost is Git Bash's fork, not Windows process creation or the exe. Measured from
PowerShell, `cmd /c exit` takes 12 ms, the test exe's `--list` 14 ms, and a one-law serve 0.24 s (building the law list). Run
directly, MSYS's `true.exe` takes 17 ms, but `bash -c true` takes 0.3-0.7 s and each further command bash runs adds 0.15-0.35 s
(about 1 s inside Claude Code's shell). A loop forked about 30 times: 5 exe launches, plus a `$(...)`, a pipe stage or a
`grep`/`sed`/`awk`/`wc`/`date` for every parsed line. `scripts/loop_stream.sh` and the local `cross_run.sh` now parse with bash
builtins (`[[ =~ ]]`, `read` loops, `mapfile`, `$EPOCHSECONDS`). On a seeded sbo3 loop (2 threads, pinned to two cores, ABAB, 12%
load, RTP off) that took 26.2-35.4 s down to 12.9-15.1 s, with identical m.tsv and rules. The cross-run sbo3 own loops went from
19-21 s to 12-14 s with identical rows. Running a whole loop in one process would save only the 0.24 s law-list setup per launch,
about 1 s a loop, so it is not worth doing.

Two other costs showed up:
- **A growing chain.** cmp3d's cold phase-1 mine spends 24 s of its 31 s in two rounds. Its first winner,
  `lt(x, sub(y, z)) -> lt(x, add(sub(x, y), z))`, and the candidate `lt(x, add(y, z)) -> lt(x, sub(sub(x, y), z))` rewrite into
  each other, and each lap copies `x` in. The term grows instead of repeating, so the cycle cut never fires and only the 40-step
  budget stops it. That one candidate took 17-24 s a round, and the seeded memo does not help (each lap is new). Fixed by the growth
  cut (below).
- **Identity candidates.** `add(x, y) -> add(x, y)`, `lt(x, y) -> lt(x, y)` and `sub(x, y) -> sub(x, y)` were scored every round
  (0.35 s each, affecting 90-100 laws) and can never gain. They come from the pool route (a pattern's pool group holds the pattern
  itself): 24 of the 92 candidates on cmp3d's cold phase-1 mine. As the smallest right side, an identity also displaced its left
  side's real candidates in the one-per-left-side dedup. The miner now drops them before the dedup. Re-mined at salt 1, the four ref
  libraries are identical and total M is unchanged except own add3 (61 to 60).

**Growth cut (kept, default, 2026-10-11).** The cycle cut now fires when a term on the rewrite path *embeds* in the term about to be
rewritten (homeomorphic embedding: the new term is the old one with nodes inserted), not only when it repeats. Between terms of equal
size, embedding is equality, so this subsumes the repeat check, and permutative rules are cut only on an exact repeat as before. Only
a strictly growing return is newly cut. On cmp3d's cold phase-1 mine, rounds 2-3 went from 18.5 s and 14.2 s to 1.1 s and 1.0 s,
and the first six rules are unchanged. Re-mined at salt 1, the sbo3, add3 and mix3 libraries are identical. cmp3d's changed: its ref
total M went from 30 to 28, cold cmp3d from 184 to 180, and the one cold law that used up the budget no longer does. Every other
loop is unchanged. Test: `growing_rewrite_chains_are_cut`. With only the repeat cut its law runs out the 200-step budget in 53 s;
with the growth cut it is proved with 196 steps left. Embedding is a heuristic: a chain that grows through an embedding copy and
would later shrink is cut early. No loop got worse.

**Miner budget = serving budget (2026-10-11).** `scripts/loop_stream.sh` had mined with `RULEMINER_STEPS=40` since the first loop
scripts, while serving uses 200. With both cuts, mining at 200 gives the identical four ref libraries and identical M on every own and
cold loop. No chain gets near 40 steps any more, so the two budgets no longer disagree. The override is gone, so the miner's default
of 200 applies.

### Why add3 did better with sbo3's library; scoring every orientation is a mixed result (2026-10-11)
The miner keeps one candidate per left side before scoring: the smallest right side, ties broken by `show()`. For add3's
`sub(sub(x, y), z)` that kept `sub(sub(x, z), y)` (permutative) and dropped `sub(x, add(y, z))`, which sbo3's library has. So add3's
library oriented its `sub` chains the other way. Serving add3 batch 0 (salt 1, phases 1-3) with its own library, sbo3's, and its own
with the two chain rules swapped for `sub(sub(x, y), z) -> sub(x, add(y, z))` gives M 46, 36 and 27.

Scoring every right side per left side (re-mined at salt 1, total M):

| | add3 | sbo3 | mix3 | cmp3d |
|---|---|---|---|---|
| mine, one per left side / every | 18 / 10 | 12 / 12 | 14 / 9 | 30 / 31 (96 s / 427 s) |
| own loop | 61 / 40 | 35 / 41 | | 68 / 91 |
| cold loop | 183 / 173 | 123 / 124 | | 184 / 214 |

It fixes add3 and mix3 but makes sbo3's and cmp3d's own loops worse and cmp3d's mine 4.5x slower (each left side's rivals are scored
separately). Kept one per left side.

Rescoring only the winner's rivals (a rival replaces the winner on a strictly higher gain, proved lazily) costs little. On add3's
mine it took `sub(sub(x, y), z) -> sub(x, add(y, z))`, the rule sbo3 has. Still mixed (salt 1, total M, committed miner / rivals):

| | add3 | sbo3 | mix3 | cmp3d |
|---|---|---|---|---|
| mine | 18 / 5 | 12 / 12 | 14 / 9 | 30 / 43 (96 s / 163 s) |
| own loop | 61 / 28 | 35 / 35 | | 68 / 83 |
| cold loop | 183 / 179 | 123 / 130 | | 184 / 211 |

cmp3d's loss comes from greedy myopia, not from the rival. Its round 3 took the rival `add(sub(x, y), z) -> sub(add(x, z), y)`.
Round 5 then took the inverse `sub(add(x, y), z) -> add(sub(x, z), y)` at -1 fixed laws for a 7697 size cut, and the pair cycles
(cut after one lap). Reverted; the patch is not kept.

Refusing such winners does not rescue it (salt 1, total M; a refused candidate scores gain 0):

| variant | own add3 / sbo3 / cmp3d | cold add3 / sbo3 / cmp3d |
|---|---|---|
| committed miner | 61 / 35 / 68 | 183 / 123 / 184 |
| refuse a winner that uncovers any covered law | 115 / 86 / 82 | 188 / 155 / 203 |
| rivals + that refusal | 89 / 79 / 71 | 173 / 154 / 219 |
| rivals + refuse a net loss in covered laws | 28 / 35 / 94 | 179 / 130 / 211 |

- **The per-law refusal is far worse everywhere.** Good rules that fix many laws often uncover one, and its mines fall behind too
  (ref M: sbo3 12 to 20, add3 18 to 38).
- **The net refusal does block cmp3d's inverse rule.** Its cold loops are identical to rivals alone, but cmp3d still loses (ref
  mine M 46, own loop 94 with 4 laws using up the budget). The rival itself is the problem there. `add(sub(x, y), z) ->
  sub(add(x, z), y)` scores +43 fixed under the miner's 40-step budget, yet serving the same laws under the 200-step budget leaves
  more machine proofs. Mining and serving disagree on it.

All variants reverted. A rival orientation is worth revisiting only once the miner scores rules the way serving uses them (the
same budget), or the gap between the two is understood.

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
