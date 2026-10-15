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
- The mine-and-serve loop (`driver::loop_stream`, `search::rule_miner`): laws are served in batches, rules are mined from them, M
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
Raw rows, run scripts and the patches of reverted switches are kept per day under `docs/runs/<date>/` (from 2026-10-12).
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
grades batches, not single proposals. Since 2026-10-11 it mines on serving's 200-step budget (it had kept the miner's old 40) with
no round cap; on a 30-law salt-1 sbo3 file both budgets mine the same 16 rules (held-out M 92 -> 61).

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
these shifts are cheap in time (below), so it would change the visit count more than the run time. Moot since 2026-10-13: the
diagram path is deleted ("Decision diagrams deleted").

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
  visit count does not see. Diagrams stay (`DDMIN=9`). Reversed on 2026-10-13: case trees are now faster at nv = 9 ("Case
  trees at nv = 9"), and at nv = 11 no slower; the diagrams are deleted ("Decision diagrams deleted").
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
  result that a cut shaped, and replays an entry only where the path in force cuts none of the terms it took up (law 168 under
  Open). Tests: `rewrite_cycles_are_cut` (sbo3's five-step cycle; fails with the cut disabled), `memo_hits_match_fresh_rewrites_under_cycling_rules`.

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
  `TREE_LAWS` does not cache placeholder proofs. (Superseded by proof plans: counting builds no proofs at all, so the placeholder
  and the guard are gone; see "Proof plans".)
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

The script was then replaced by a Rust driver, `driver::loop_stream`. It runs serve and mine as child processes of the same exe,
so it needs no shell and no refactoring of the env-read configs. The script's unused options (`WINDOW`, `POOL`, `WARM`) were
dropped. Same seeded sbo3 loop, three alternating rounds (pinned to two cores, 19-49% load from other work): Rust driver 9.4-12.2 s,
trimmed bash script 10.8-23.4 s, and the five exe calls launched straight from PowerShell 9.2-10.3 s. Outputs were identical. On a
quiet machine the driver saves about 1.4 s a loop and sits within 0.2 s of the direct-launch floor. Under load, bash's fork cost
grows and the gap widens. Confirmed with `scripts/quiet_ab` (5 clean pairs, other load 16-17%, RTP off, 12 cores): wall 10-12 s
against 11-13 s (best 10 vs 11, at 1 s resolution), CPU including children 7.77-8.73 s against 9.53-9.67 s. `pin.ps1` used to count only
the launched process's CPU, which for a driver whose children do the work would have shown up as other processes' load. It now
counts the children through a job object. Speed claims in this file should come from `quiet_ab` runs like this, not ad hoc ABAB. The sweeps (formerly local `transfer_mines.sh`, `cross_run.sh` and per-experiment wrappers) are now
`driver::sweep`. One sweep of ref mines, own, cold, cross, cold mix3 and pooled mix3 loops reproduced every library and every row
of the script runs, seconds aside. The pooled mix3 loops went from 15-24 s to 5-6 s each, so they had been mostly shell.

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

**Structural term equality (kept, 2026-10-12).** Terms had been compared, hashed and keyed by their `show()` text at about 40
sites: rewrite and normal-form memo keys, rule identity (`rule_text`), preference and conflict keys, `PROVING`, the miner's
candidate dedups and rivals, file dedups, and `classify_proposals`. `Term` now derives `Eq`/`Hash`/`Ord`; rules are keyed by
`RuleKey = (Term, Term)` and preferences by `Pref = (RuleKey, RuleKey)`, parsed once when read. Rule files are deduped on parsed
pairs (`parse_rules`, `read_rule_file`), and the driver matches the miner's `RULEMINER drop` lines against the rule file by parsed
pair, not by trimmed text. `show()` is injective, so the switch is exact. Two string costs left on hot paths were cut too:
`shared_lemma` took its key as a closure, so counting mode (`SCORE_ONLY`) never formatted it (no longer needed since proof plans:
counting never reaches `shared_lemma`), and the text orders compare through
`show_cmp`, which writes both sides into reused thread-local buffers instead of allocating (test `show_cmp_is_the_text_order`).
Both salts' sweeps (mines, own, pooled), run in parallel with HEAD on the same load, give identical rows and identical rule, unit
and preference files. Wall 690 s against 695 s (salt 1) and 502 s against 512 s (salt 2): the gain is small (the preference stage
about 10%, the ref mines within 3% either way). The A1/A2 dedup and drop matching, checked separately on salt 1's
pooled stage, reproduce the rows and all pooled libraries through 9 real drops.

Text stays where it is the data or the order: files, logs, lemma names, and the rewriter's orders (operand sort, comm/assoc,
permutative rules, candidate sort, `shuffled`'s hash), which the mined rules assume (see "Operand order"); the derived `Ord` only
makes canonical keys. Parked:
- Typed lemma keys: `shared_lemma` and `Machine::key` (a `Debug` string) still key the lemma caches by formatted text. A typed key
  is the structural fix; it matters only outside counting mode (proofs of chosen rules, serving).
- The miner writing its chosen rules, preferences and drops to an output file, so the driver no longer parses its log.
- A structural operand order in place of `show_cmp`: rejected, since it would change every mined library.
- Cached `show()` text on terms: not needed while `show_cmp` does not allocate.
- `machine.rs` orders candidate terms by `show().len()` as a size proxy.

**Where the time goes after it (samply, 2026-10-12).** Profiled cmp3d's ref loop (`driver::loop_stream`, 2 threads, salt 1;
`RULEMINER_FAST` was in fact not set, see the correction under "Where the time goes after proof plans"; 320 s under the profiler, load 46%, RTP off; 384k samples over the loop's processes). Text work is gone from
the profile: `show`, `show_cmp`, formatting, `parse_term` and `Machine::key` each round to 0.0%, and `Term` hashing and cloning
are 1.7% and 5.3% of the mine. The cost is kernel term construction:
- The mine process is 70% of the samples. 63% of it is under `rewrite_law` and 58% under the kernel's hash-consing
  (`hc::intern`), although scoring runs counting-only: the rewriter still builds every step's proof term (interning under
  `witnessed` 13% of the mine, under `rewrite_uncached`'s own steps 10%, `find_constant_carry` 3%, `k_var_law_to` 3%; `ops_for`,
  which rebuilds the eight operator circuits per call, is 10.7% inclusive), and `SCORE_ONLY` only short-circuits lemmas and machine fallbacks. Winner proofs (`prove_rule`) are 10.5%.
- The four serving processes (`rule_set_kernel_check`, 29%) build and check real proofs: 57% under `hc::intern`, 40% in the
  kernel check, 10-13% each rebuilding the constant gate encodings (`bool0`, `xor_`, `and_`).
- `hc::intern`'s own frames are 45% of all samples (the table lookup inside `intern_as`, plus 2-5% table growth).

One mechanism covers most of this: a rewrite returns its term plus a proof *plan* (the steps as data), and a compiler with a
per-width context (`ops`, literals, `good_*`, gate encodings, built once) turns the plan into a kernel term only where a proof is
wanted (serving, winner proofs). Counting then builds no proof terms, the constant caches live in the context instead of in
scattered per-function caches, the lemma keys there can be typed (the parked typed-key item), and the miner's intern table holds
only real work. `hc::intern`'s per-lookup cost stays a separate kernel item.

**Decisions that read kernel terms (2026-10-12).** The plan only works if no rewriter decision depends on a proof term. Five sites
do, all the same shape: Boolean evaluation by building Church terms and kernel-normalizing them.
- `raw_table` (`machine.rs`): the carry machines' truth tables for `moore_encoding`, through `Machine::step` over `GoodOps`
  (rebuilt by `GoodOps::new()` on every `add_tree_law` call) and `normalize(..) == t()`. It decides whether `add_tree_law` (so
  `tree_step` and `prove_eq`'s machine) finds a proof.
- The collapse step in `rewrite_uncached`: a bitwise node's truth table, `normalize(t.bit(..))`.
- `prove_eq`'s `eq_truth`: the same check for equality.
- `find_constant_carry` (`chain_step`): the constant carry, by `normalize`.
- `nf_cached`/`fingerprint`: only the ignored `conjecture_miner` probe; it also hashes `Debug` text.

Nothing else on the rewrite path reads a term: `rule_step` gets its lemmas through `shared_lemma` (placeholders when counting, at the time),
winner proofs run outside scoring, and the integer screens (`plausibly_equals`, `refute`) already use `Term::interp`. Plan:
first decide at these sites by plain evaluation (a `bool` `Term::bit`, a `bool` implementation of `Gates` for `raw_table`, so
`GoodOps` is built only for proofs); rows must stay identical, since the Church gates compute the same Boolean functions. Then the
proof plans. Also left: `add_tree_law`'s `guarded` formats its lemma key eagerly (for `LEMMA_HITS`), so counting still builds
that string (under 0.05% of the profile; part of the typed-key item).

Done (e49535f): the five sites evaluate plain Booleans (`search::Bools`, a third `Gates` implementation beside `GoodOps` and
`DdGates`; `term_gb(&Bools, ..)` for the truth tables), `conjecture_miner` groups by `Term::interp`, and `NfCache`/`nf_cached`/
`fingerprint` are deleted. `plain_steps_match_the_kernel_gates` checks `Machine::step` over `Bools` against the normalized Church
gates on four machines. Pair sweep against 2bf9c7a, same load (CPU 36% at launch, RTP off), `SWEEP="mines own pooled"`
(`docs/runs/2026-10-12/rows/pl_*`): rows, preferences and all 27 rule and unit files identical on both salts; wall 519 against
573 s (salt 1) and 616 against 659 s (salt 2), 7-9% less.

**Proof plans (2026-10-12).** The rewriter now decides and a compiler proves. `rewrite(t, n, k)` returns the rewritten term and
a `Plan` (`Refl`, `Cong(op, ..)`, `Trans`, `Sym`, `Law(kind, lhs, rhs, args)`), with no `Expr` built. Every lemma instance
was `law` applied to the values and witnesses of some terms, so one `Law` node covers them all; its `LawKind` names the prover:
`Rule(name)` (`prove_rule`, as a shared lemma; `shr_mask_eq`'s side is `Rule("shrmask")`), `Assoc`, `Comm`, `Bitwise`
(`bitwise_law_k`: collapse, the swap, `eq_truth`, `eq_pos`), `Chain` (`carry_chain_law`), `Tree` (`add_tree_law`).
`rewrite_plan(n, k, t1, t2)` decides; `rewrite_law` is `rewrite_plan` plus `law_proof`, whose `Compiler` holds one width's
operator circuits, goods and their values and builds the proof bottom up. Callers that only ask whether a law holds (the base
pass, `score_laws`, `law_cost`, the borrow probes, `rule_set_kernel_check` under `CHECK_FAST`) call `rewrite_plan`; serving
compiles and checks every law. Supporting changes:
- `add_tree_law` is split into `tree_encoding` (the decision: screens, then the carry encoding over all or the reachable states,
  cached per thread past the cheap screens) and `tree_proof`; `tree_step` and `machine_fallback` ask only `tree_encoding`.
- `SCORE_ONLY` now means only that `machine_fallback` takes a fallback when 16 tuples agree, without searching for an encoding;
  a plan made under it may not compile. `shared_lemma`'s placeholder, `add_tree_law`'s don't-cache guard and `shared_lemma`'s
  lazy key are gone, since counting never reaches a lemma.
- Inner proofs get a fresh rewriting context: `prove_rule`'s rewrite and `shr_not_law` run under `proving(blocked, f)`, which
  saves and restores `PROVING`, `REWRITE_PATH`, `REWRITE_MEMO`, `RULE_TRACE`, `RULE_BUDGET` (10 000 inside), `MACHINE_FALLBACKS`
  and `CYCLE_CUTS`. Before, in proof mode, an inner proof ran in the middle of the outer rewrite: the outer path could cut it,
  its results (made with a rule blocked) entered the shared memo, and its fallbacks counted toward the outer law. With plans
  inner proofs run at compile time anyway; only proof mode changes, toward what counting already did.

Test `plans_compile_to_checked_proofs`: seven laws (comm+assoc, `shl1` over `and`, `x + (x ^ -1) = -1`, `-1 - y = y ^ -1`,
a collapse, an `lt` root, the shr mask) have a plan with and without `SCORE_ONLY`, the compiled sides are the law's, and the
proof checks. (Profile after it: see "Where the time goes after proof plans".) Pair sweep against e49535f, same load (CPU 39-43% at launch, RTP off), `SWEEP="mines own pooled"`
(`docs/runs/2026-10-12/rows/pp_*`): rows, preferences and all 27 rule and unit files identical on both salts, so the
proof-mode context change did not move serving M; wall 333 against 535 s (salt 1) and 236 against 429 s (salt 2), 38-45%
less. The mines gain most (cmp3d 141 against 216 s and 75 against 119 s; add3 18 against 53 s). Parked: typed lemma keys
(`CLOSED` keyed by kind and terms, `guarded`'s tree key, `Machine::key`; now a
cleanliness item, since counting formats no keys); caching `ops_for` per width (proof mode only; measured below: dropped).

**Where the time goes after proof plans (samply, 2026-10-12).** The same cmp3d ref loop as before (`driver::loop_stream`,
2 threads, salt 1; load 43-49%, RTP off) ran 160 s under the profiler, against 320 s; 235k samples. Correction: neither
profile set `RULEMINER_FAST` (`loop_stream` only passes it through; the sweeps set it), so both mines ran the eager filter
that proves every candidate and scored in proof mode. Here the filter was 76 s of the mine's 87 s (all 170 candidates
provable), the rounds 10 s, winner proofs 0.4 s; serving took 60 s. The earlier profile's "the rewriter still builds every
step's proof term although scoring runs counting-only" was proof-mode scoring by configuration; the sweep pair (which does
set it) is the measure of proof plans. In this profile:
- Counting is small: the whole rewriter (`rewrite`, `rewrite_plan`) is under 5% of all samples.
- `add_tree_law`'s proof half (`tree_proof`) is 59% of all samples: in the eager filter (`prove_rule`, 59% of the mine
  process, which is 73% of all samples) and in serving (`law_proof`, 61-66% of each serving process, of which `prove_rule`
  for rule lemmas is 40-63%: each serving process re-proves the rules in force). Inside it, the case lemmas
  (`lemma_n`'s elimination, 47%), their table lookups (`table_app`/`mux`, 34-39%), and the kernel check (34%).
- `hc::intern` is still 58% of all samples, now almost all under `tree_proof`. The constant gate terms are rebuilt and
  re-interned on every use: `and_` 15%, `bool0` 11%, `xor_` 11%, `or_` 7.5%, `bool2` (their wrapper) 20%, all inclusive.
- Text is gone (formatting, `Machine::key`, `show` all 0.0%), so typed lemma keys have no speed value; `ops_for` is 0.3%, so
  caching it per width is dropped.
- With `RULEMINER_FAST=1`, as the sweeps run (same loop, load 25-35%, 104 s under the profiler, 106k samples, same M): the
  mine is 44% of all samples, its rounds 35 s. Half of it (22% of all) is `prove_rule` on the mine's main thread: lazy
  winner proving, which proves each round's best candidate and, when that fails, the next. The scoring workers are 16%
  (`rewrite_plan` 8%). Serving is the other 52%, as above (61-66% `tree_proof`, 40-64% `prove_rule`). `tree_proof` is 50% of
  all samples; the gate constants `and_`/`bool0`/`xor_`/`or_` are 12/9/9/6% inclusive.
- Winner proofs are not repeated: `proofs` holds each candidate's result for the whole mine, and under `RULEMINER_FAST` only
  winners are proved (0.4 s here). Rule lemmas are repeated across processes instead: the mine and every serving process
  prove the rules in force from scratch (`CLOSED` is per thread and per process).
- Caching the gate constants is safe: `hc` stamps each node with its scope's generation, and a node from an older
  generation is only non-canonical (its parents compare structurally, and `check_in`'s `canonical_inputs` re-interns large
  inputs), never wrong. A cache keyed on the current generation keeps the pointer-equality fast path; the miner's and
  serving's scopes are long (one per worker, per law or per rule set), so it would hit. `hc::generation` is private to the
  kernel, so the key needs a public accessor.

**Gate constants built once per generation (2026-10-12).** `bool0`, `t`, `f`, `and_`, `or_` and `xor_` go through
`encoding::constant`, a per-thread cache keyed on `kernel::intern_generation()` (new: the current `hc` generation, 0 while
the table is off). Test `constants_are_built_once_per_generation`: inside a scope the cached gate is the table's node (a
fresh build interns to the same children) and shared between uses; a new scope rebuilds it. Pair sweep against e1d28d9, same
load (CPU 27% and 39-42% at launch, RTP off), `SWEEP="mines own pooled"` (`docs/runs/2026-10-12/rows/gc_*`): rows,
preferences and all 27 rule and unit files identical on both salts; wall 201 against 276 s (salt 1) and 207 against 270 s
(salt 2), 23-27% less; the mines about 35% less (cmp3d 71 against 114 s and 68 against 103 s).

**Serving's lemma cost is checking, not building (probe, 2026-10-12, reverted).** For a lemma cache shared across processes
(draft `docs/superpowers/plans/2026-10-12-lemma-cache.md`: a binary `Expr` format, typed lemma keys, a lemma file per loop),
timers around `shared_lemma` (outermost calls, and the `ck` inside) on the cmp3d ref loop at 6ff357d (`RULEMINER_FAST=1`, salt
1, 68 s): in the four serving processes the lemmas are 95% of the serving time (11.3 of 11.8 s, 9.1/9.6, 6.3/6.6, 1.2/1.5) and
their kernel checks 73-77% (8.7, 6.9, 4.8, 0.8 s; 347, 364, 260, 168 lemmas). Building is only 22-24% of serving. A cache that
re-checks loaded lemmas would save about that (about 6 s of the loop's 68); one that trusts them, about 95% of serving (about
28 s). Decided: trust them (below, "A trusted lemma cache per loop").

Which lemmas repeat (probe, reverted; one `LKEY hash build-ns check-ns kind` line per lemma built, rows in
`docs/runs/2026-10-12/lemma_keys/`, same loop): the mine builds 268 lemmas (2.8 s build, 9.9 s check), the four serving
processes 347/364/260/168 (6.9 s build, 22.6 s check in all). Machine case lemmas (`tree`) are 91% of the lemma time, rule
lemmas 8%. Of serving's 29.5 s of lemmas:
- built earlier by another serving process (what one serving process per loop would save): 8.0 s (27%);
- built earlier by the mine or another serving process (what a trusted cross-process cache would save): 20.6 s (70%).

**`mux` and `not` as one gate each (2026-10-12).** `mux c x y` was `or (and c x) (and (not c) y)` with `not c = xor c true`,
four gate applications per node of every truth table (`table_app`, the case lemmas' statements); it is now one cached gate,
`\c x y C t f. c C (x C t f) (y C t f)`, and `not` is `\a C t f. a C f t` (`encoding::constant` slots 6 and 7; `good_bool`
cached too, slot 8). The decision-diagram prover had relied on the old `mux` being its gates by definition: its canonical
nodes are now `mux`es with a `GoodBool` witness from `good_mux` (eliminating at the motive's `P`, as `good2` does; `GoodBool`
itself is too large for a motive), and a table node built from arbitrary signals goes through the gates and the new
`DdLemmas::gates` (`mux c x y = or (and c x) (and (xor c true) y)`, by case analysis). Pair sweep against 9f1d23e, same load
(CPU 44% at launch from other sessions, RTP off), `SWEEP="mines own pooled"` (`docs/runs/2026-10-12/rows/mx_*`): rows,
preferences and all 27 rule and unit files identical on both salts; wall 194 against 245 s (salt 1) and 163 against 210 s
(salt 2), 21-22% less; cmp3d's mine 58 against 92 s and 35 against 62 s.

**A trusted lemma cache per loop (2026-10-12).** A lemma is only ever used as a parameter of its statement, so a loop's
processes share statements, not proofs: each statement a process checks goes to `LOOP_OUT/lemmas.bin` (`LEMMA_CACHE`, set by
`driver::run_loop`, deleted when the loop starts and ends; `tests/church_bv/lemma_cache.rs`), and a later process binds it
with no build and no check. Sound as long as every statement in the file was checked by this build: the header holds a
hash of the exe, and a wrong key can only make a later check fail. Statements are stored in a new binary `Expr` format
(`kernel::bin`, a node table, closed terms only). `LEMMA_RECHECK=1` builds and checks every lemma anyway and asserts the
file's statement is the one built. The rule lemmas' key gained `k`. Audit, the cmp3d ref loop (`RULEMINER_FAST=1`, salt 1):
no mismatch; the mine saves 286 statements (475 KB) and the four serving processes hit 142, 121, 128 and 143 of them and
build 204, 52, 29 and 23 (729 KB at the end); serving takes 4, 3, 3, 3 s per batch against 12, 12, 13, 14 s audited, and
the loop 67 against 111 s, run side by side; M and rules identical. Pair sweep against 639cdcd, same load (CPU 58% at
launch from other sessions, RTP off), `SWEEP="mines own pooled"` (`docs/runs/2026-10-12/rows/lcp_*`): rows, preferences and
all 27 rule and unit files identical on both salts; wall 323 against 351 s (salt 1) and 149 against 161 s (salt 2), only
7-8% less, because the gain is confined to the `mines` stage (106 against 156 s and 42 against 61 s; cmp3d 71 against 113 s
and 18 against 32 s): the `own` and `pooled` loops serve with `CHECK_FAST=1` and build no lemmas, and their mines few.

**Where the time goes after the lemma cache (samply, 2026-10-12).** The same cmp3d ref loop with `RULEMINER_FAST=1` as the
last profile above (2 threads, salt 1; that one predates the gate constants, `mux` and the cache), at e720392 (CPU 20% at
launch, RTP off): 33.6 s under the profiler against 104 s, 33k samples against 106k. About 12 s of the 33.6 is the driver's two machine-state checks (PowerShell, before the mine and
after the last batch), not loop work. The mine took 15.0 s and the four serving processes 3.3, 1.3, 1.0 and 0.5 s.
- Serving is 18% of all samples (6.1k, against 55.7k: 9 times fewer). The mine is 72% (23.7k against 47.2k).
- The mine's proving fell 6 times (`prove_rule` 2.9k samples against 17.6k; the mine starts with an empty cache, so this is
  the gate constants and the one-gate `mux`). Proving is now 12% of the mine (`prove_rule`, `add_tree_law`; `shared_lemma` 12%, kernel checks
  11%). 16% of the mine's samples are its threads waiting.
- The rewriter is now the mine's largest part: `rewrite` 41% of the mine, almost all of it in `rule_step` (32%). Two thirds
  of `rule_step` is overhead that does no matching. `rules()` rebuilds and clones the whole rule list on every call (the
  built-ins, the promoted rules, the rule set, the mined rules): 10.5% of the mine inclusive, much of it `Term::clone`.
  `ablated` reads and splits the `ABLATE` variable for every rule tried: 11% of the mine (`RtlQueryEnvironmentVariable`
  alone 3% self).
- Next target: build the fixed part of the rule list once (built-ins, promoted, rule set, with `ABLATE` parsed once and
  applied when the list is built), try it and then the mined rules (`EXTRA_RULES`) by reference, and clone only the rule that
  fires. `ablated`'s other callers (`prove_eq`, `tree`, `chain`, `collapse`, `assoc`, `comm`) read the same parsed set. The one
  runtime `set_var` (`rule_miner`'s `<exe>.env`) runs before anything reads the environment.

**The rule list built once (2026-10-12).** `rules()` is gone: `fixed_rules()` builds the built-ins, the promoted rules and the
`RULESET` rules once per process, and `rule_step` tries them and then `EXTRA_RULES` through borrowed `RuleRef`s, cloning only
the sides of the rule that fires. `ablated` parses `ABLATE` once per process. Pair sweep against 34ea646, same load (CPU 38% at
launch, RTP off), `SWEEP="mines own pooled"` (`docs/runs/2026-10-12/rows/rsp_*`): rows, preferences and all 27 rule and unit
files identical on both salts; wall 144 against 156 s (salt 1) and 104 against 117 s (salt 2), 8-11% less (`own` 40/22
against 43/26 s, `pooled` 22/20 against 25/26 s, cmp3d's mine 29/12 against 30/16 s). Less than the profile's 21% of the
mine suggested; why is not yet profiled (the sweep's loops have other mixes of mining and serving than the cmp3d ref loop).

**Where the time goes in the sweep's loops: every process rebuilds its family's law pool (samply, 2026-10-12).** The `own` and
`pooled` stages of a salt-1 sweep at 84072cd (libraries from its `mines` stage; CPU 32% at launch, RTP off): 129 s under the
profiler, 102k samples, 39 mine and 66 serving processes (serving with `CHECK_FAST`). Mines are 67% of the samples and serving
26%.
- `family_laws` is 86% of serving and 19% of the mines, about 35% of all samples. Every child process rebuilds its family's
  whole conjecture pool (`pool3`, `pool_conjectures`: a 4096-byte behaviour signature per distinct pool term, `SigMemo::id`
  56% of serving) only to take its 100-law window. The pool depends only on the family and `RULEMINER_DEEP3`; the order on
  the salt; the window on the shape, phase, stride and skip. So one computation per family serves every child of a sweep.
- Rewriting is small in these loops (4.5% of serving, 6% of the mines, after the rule-list fix), which is likely why that fix
  gained 8-11% of a sweep rather than the 21% of the cmp3d ref mine.
- In the mines, kernel checks are 36% (`shared_lemma` 16%, `prove_rule` 17%), interning 18%, rewriting 6%.

**A lemma file shared by a whole sweep (probe, reverted; built after the law files, see "One lemma file per sweep").** A temporary `LEMMA_SWEEP=<file>` in `run_loop` (no deletes; one
file for every loop) at 84072cd; the `own` and `pooled` stages with and without it, side by side on the same libraries (CPU
30% at launch, RTP off; `docs/runs/2026-10-12/rows/lsp_*`, `scripts/lemma_sweep_probe.sh`): rows identical; the loops' mines
hit 252 of their 1002 lemmas (without it: 0, so within a loop the second mine uses none of the first's lemmas); wall 85
against 95 s, `own` 31 against 40 s, `pooled` 20 against 19 s; the file ends at 316 KB. One pair, so the 10 s is a rough
size. Smaller than removing the law-pool rebuild (35% of the samples above).

**Law files from the driver (2026-10-12).** The driver writes each child's laws (its window of the family's sequence) to
`LOOP_OUT/laws_<mine|serve>_<name>.txt` and passes it as `RULEMINER_LAWFILE` (the miner already read it) or the new
`CHECK_LAWFILE`; `family_laws` keeps each three-variable family's pool conjectures per process (`pool3_conjectures`, keyed by
family, `RULEMINER_DEEP3` and width), so the driver builds a family's pool once and every child reads 100 lines. Test
`law_windows_survive_a_law_file`: a window written and read back gives the same laws and names. Pair sweep against 3ac4e20,
same load (CPU 11% at launch, RTP off), `SWEEP="mines own pooled"` (`docs/runs/2026-10-12/rows/lfp_*`): rows, preferences
and all 27 rule and unit files identical on both salts; wall 78 against 104 s (salt 1) and 59 against 84 s (salt 2), 25-30%
less (`own` 20/10 against 32/17 s, `pooled` 8/7 against 15/14 s).

**One lemma file per sweep (2026-10-12).** `sweep` gives every loop the same `SWEEP_OUT/lemmas.bin` (deleted at the sweep's
start and end); `loop_stream` keeps one per loop. The trust argument is unchanged: the driver and all its children are one
exe, so every statement in the file was checked by this build, and the loops run one after another, so there is still one
writer at a time. Pair sweep against ed00b7a, same load (CPU 15% at launch, RTP off), `SWEEP="mines own pooled"`
(`docs/runs/2026-10-12/rows/slp_*`, `scripts/sl_pair.sh`): rows, preferences and all 27 rule and unit files identical on both
salts; wall 63 against 76 s (salt 1) and 58 against 64 s (salt 2), 9-17% less (`own` 11/10 against 20/11 s summed over its
rows; `pooled` loops now each take under a second). About 12 s of each sweep's wall is the driver's two machine-state checks.
`MACHINE_STATE=0` now skips them in a sweep as well as in `loop_stream` (`machine_state` reads it).

**Where the time goes in a whole sweep (samply, 2026-10-12).** A salt-1 sweep, `SWEEP="mines own pooled"`, `MACHINE_STATE=0`,
at c00cf8b plus that switch (debug-info build; CPU 36% at launch from other sessions, RTP off; rows identical to `slp_sl_1`): 85 s
under the profiler, 82.6k samples. Processes are split by stage by their start time against the stage files' times.
- The `mines` stage is 64% of the samples: its mines 53% (6 processes, 2-4 threads each) and their full-check serving 10%. In
  those mines kernel checks are 26%, `prove_rule` 20%, `shared_lemma` 19%, interning 17% and rewriting 17%; 14% of their
  samples are threads waiting. This is proof work with no single overhead in it.
- The `own` and `pooled` mines are 24% (37 processes). `SigMemo::id`, called from `rule_miner` itself, is 35% of the `own` mines
  and 42% of the `pooled` mines, about 9% of all samples and single-threaded. It is the miner's goal-directed candidate pool
  (`rule_miner`, "a pool of all terms up to 5 nodes"): 5804 terms indexed by behaviour signature, rebuilt in every mine. Its
  terms and the patterns looked up in it have at most two variables (`V(0)`, `V(1)`; `abstractions(sub, 2)`), but the memo is
  `SigMemo::new(n, kv)` with `kv` = 3 for the three-variable families, so every signature is 4096 bytes where 256 give the same
  equalities. Untested: `SigMemo::new(n, 2)` should give identical candidates at a sixteenth of the cost.
- The driver is 9% of the samples, and its work is on the critical path (children wait for it). `write_laws` is 69% of it;
  the pool itself (`pool3_conjectures`) only 17%. The rest is each child's window taken from the whole pool again: the
  conjecture list cloned (17%) and shuffled again (`shuffled` hashes every law's `show()` text: `show_into` 14%), then
  shape-filtered. Keeping the shuffled sequence per family and salt, as `pool3_conjectures` keeps the pool, would remove most of
  it. `joinability_units` is 7%.
- `CHECK_FAST` serving in `own` and `pooled` is 3%.

**The candidate index over two variables, and the law sequence kept per salt (2026-10-12).** Both fixes from the profile above.
`rule_miner`'s candidate index uses `SigMemo::new(n, 2)`. `pool3_conjectures` became `pool3_sequence`, which keeps the
shuffled sequence of laws that use all three variables, keyed also by the salt. Each window is then taken by reference,
cloning only the laws it takes. Pair sweep against 99475ac, same load (CPU 40% at launch from other sessions, RTP off,
`MACHINE_STATE=0`), `SWEEP="mines own pooled"` (`docs/runs/2026-10-12/rows/spp_*`, `scripts/sp_pair.sh`): rows, preferences
and all 27 rule and unit files identical on both salts. Wall 82 against 91 s (salt 1) and 64 against 85 s (salt 2); the
in-test times were 67 against 83 s and 55 against 80 s. Summed over their rows, `own` took 15/6 against 22/18 s and `pooled`
2/3 against 12/14 s. The two fixes were measured together, and the heavier load makes these walls longer than the earlier pairs'.

**Where the ref mines' time goes: winners proved one at a time (samply, 2026-10-13).** The `mines` stage of a salt-1 sweep at
fcb0985 (`MACHINE_STATE=0`, debug-info build; CPU 27% at launch, RTP off): 28 s under the profiler, cmp3d's mine 13.0 s of it.
Times below use samply's sample weights. A blocked thread's samples carry its whole wait, so counting samples (as the sections
above do for CPU shares) undercounts waiting. With `RULEMINER_FAST=1` (every sweep stage) a mine scores candidates on
`RULEMINER_THREADS` = 2 workers and proves only each round's winner (`proved_lazily`). That proof runs on the main thread,
inside the scoring scope, while both workers wait for the next chunk.
- cmp3d's mine (32 rounds, each scoring 12-15 of 176 candidates): the main thread is busy 6.2 s and waits 6.8 s, which is
  the scoring. About 5.0 s of its busy time is the winners' proofs: `prove_rule` inside the scope, plus kernel checks on
  stacker's segment, whose caller frames are cut off but which always sit between proof samples. The rest is serial set-up,
  1.2 s. The workers are busy 10.1 s of their 23.7 s: they wait about 10 s while the winners are proved and about 3.6 s at
  chunk ends. Each chunk (`threads * 4` candidates) is split by a fixed stride, and the main thread waits for all of it.
- add3's mine (2.6 s) has the same shape: 0.56 s of its 1.09 s busy main thread is winners' proofs.
- So the "14% of the mines' samples waiting" in the whole-sweep profile is not load imbalance. It is mostly the main thread
  waiting for scoring (by design) and the workers waiting for the serial proof. A chunk's imbalance costs about 1.8 s of
  cmp3d's 13 s at most. Ways to recover the proof time: prove the winner while the next round is scored, assuming it is
  provable (redo the round when it is not), which would hide up to 5 s of the 13 s; or have the workers take candidates
  from a shared queue within a chunk, which would hide up to 1.8 s and keep the bound-ordered chunks that make the choice
  independent of the thread count.

**Winners proved in the background (2026-10-13).** With `RULEMINER_FAST=1`, `pick` no longer proves a round's winner before
the next round is scored. It assumes the proof holds, sends it to a thread of its own (`prove_any`, against the fixed base
rules and preferences, so it does not depend on the round), and moves on. Each round stays open, holding its state before the
choice, its pending proof and its `RULEMINER chosen` line. A round is settled once its proof is in: the line is printed then,
in order. When a proof fails, the miner prints `RULEMINER rolled back to round N`, drops the `picks` cache entries of that
round and every later one, and resumes from the failed round's state with the winner marked unprovable. That reproduces what
proving in turn would have chosen. Lookahead rounds and the last round settle every open round first. `RULEMINER lazy proofs:
P proved, F failed` closes each fast mine. Rollback check (`scripts/spec_rollback.sh`: add3 ref mine offered three false,
attractive rules through `RULEMINER_EXTRA`): it rolls back at round 0, and its chosen rules equal 514b7a2's. Pair sweep against
514b7a2, same load (CPU 22% at launch, RTP off, `MACHINE_STATE=0`), `SWEEP="mines own pooled"` (`docs/runs/2026-10-12/rows/bpp_*`,
`scripts/bp_pair.sh`): rows, preferences and all 27 rule and unit files identical on both salts; no proof failed. Wall 42 against
46 s (salt 1) and 31 against 37 s (salt 2); cmp3d's mine 12 against 17 s and 7 against 11 s.

**One queue for the scoring workers (2026-10-13).** `pick`'s workers used to get a fixed stride of each chunk, so a chunk
ended when the slowest worker's share did. They now take candidates one at a time from one shared queue. The chunks keep
their bound order and every chunk is scored in full before the next is chosen, so the choice still does not depend on
which worker scored what. Pair sweep against 5c4618f, same load (CPU 61% at launch from other sessions, RTP off,
`MACHINE_STATE=0`), `SWEEP="mines own pooled"` (`docs/runs/2026-10-12/rows/qp_*`, `scripts/q_pair.sh`): rows, preferences
and all 27 rule and unit files identical on both salts. Wall 62 against 67 s (salt 1) and 48 against 52 s (salt 2); cmp3d's
mine 16 against 20 s and 10 against 12 s. The heavier load makes these walls longer than the previous pair's.

**Where the ref mines' time goes after both (samply, 2026-10-13).** The `mines` stage of a salt-1 sweep at a77c027
(`MACHINE_STATE=0`, debug-info build; CPU 44% at launch, RTP off; 30 s in-test under the profiler), with sample weights:
- cmp3d's mine took 10.2 s. Its main thread is busy 1.3 s and waits 8.9 s, 8.0 s of that inside `pick`'s scoring scope. The
  two scoring workers are busy 14.4 s together (`score_rule` 7.2 s; the rest is `RewriteMemo::filtered` and hash-map work
  around it), so each is busy about 7 s of the 10 s. The winners' proofs (`prove_rule` inside `prove_any`, 4.8 s) all run on
  their own threads, overlapping the scoring. The mine is now bound by scoring on 2 workers.
- add3's mine (3.6 s) has the same shape: the main thread is busy 1.8 s, 0.8 s of it winner proofs that its lookahead
  rounds prove in turn: lookahead's greedy paths still pick without speculating, and add3 has three lookahead rounds (since moved to the background, next section).
- Negative result: proving the rivals in the background would save nothing here. No `prove_any` sample sits on a main
  thread in cmp3d's mine, so no rival was proved on the main thread; the main thread's busy time is set-up and `then`.
- The ref mines run with `threads: 2` (`driver::sweep`, `RULEMINER_THREADS`), while the loops use 6. A chunk holds `threads * 4`
  candidates in bound order, and a candidate is skipped only when its bound is below the best gain found, so it can neither
  beat nor tie the winner. The choice therefore does not depend on the thread count, and more scoring workers are the next
  lever (next section).

**Six scoring threads, and lookahead's proofs in the background (2026-10-13).** The ref mines and the pooled preference mines
now take the sweep's default of 6 scoring threads (`driver::sweep`; they had 2). Lookahead's greedy paths (`finish`) now pick
speculatively too: each pick's winner is taken as provable and proved on a thread of its own. Once the paths are played, the
lookahead waits for every proof they assumed (`assumed`). If one failed, it prints `RULEMINER lookahead played again`, drops
the picks that offered the failed rule and every finished value, and plays the paths again; the failed rule is then known
unprovable and never picked. Rollback check (`scripts/spec_rollback.sh`, now with four more false rules that win only on
greedy paths): one main-path rollback at round 0 and one lookahead replay, and the chosen rules equal 8f348b9's. Pair sweep
against 8f348b9, same load (CPU 13% at launch, RTP off, `MACHINE_STATE=0`), `SWEEP="mines own pooled"`
(`docs/runs/2026-10-12/rows/lap_*`, `scripts/la_pair.sh`): rows, preferences and all 27 rule and unit files identical on
both salts; no proof failed. Wall 35 against 37 s (salt 1) and 25 against 28 s (salt 2).
- The mines' scoring rounds (summed `round over` times): cmp3d 4.5 against 5.6 s and 2.7 against 3.2 s; add3 0.2 against
  1.2 s and sbo3 0.1 against 0.7 s on salt 1, where the in-turn lookahead proofs had sat.
- Three times the workers gave cmp3d only about 1.2× faster scoring. The bigger chunks (24 candidates against 8) scored only
  3-8% more candidates, so the chunking is not why. Two other likely causes, neither measured: each worker's `RewriteMemo`
  starts empty every round, so six workers reuse less than two did; and the pair's two runs shared 12 cores. Both are
  refuted in the next section.

**Why six threads gave little (2026-10-13).** Neither guess above holds.
- Not shared cores. Running the same two builds one at a time (`scripts/la_seq.sh`, rows `las_*`; CPU 8% at launch, RTP off)
  gave identical outputs again. Walls were 31 against 34 s (salt 1) and 20 against 24 s (salt 2). cmp3d's summed rounds took
  4.4 against 5.0 s and 2.5 against 2.8 s, still only about 1.12× faster.
- Not lost memo reuse. A samply profile of cmp3d's mine alone at a045cfb (`SWEEP=mines:cmp3d`, salt 1, CPU 4% at launch, RTP
  off) took 4.1 s. Scoring was busy 6.1 s in all, against 14.4 s at 2 threads in the previous profile, though that one ran
  under 44% load. `RewriteMemo::filtered` and the hash-map work around it fell from about 6.4 s to 1.2 s. Each worker now
  scores fewer candidates a round, so its memo stays smaller and is cheaper to filter: the memo's reuse was partly a cost.
- The proofs are back on the critical path. The main thread waits 1.85 s for scoring and 1.39 s for winners' proofs
  (`resolve`). The winners' proofs take 2.7 s over 31 rounds, about 87 ms each, while a round's scoring now takes about
  60 ms. A round settles the round before it (`settle(&mut open, 1)`), so each proof has only one round's scoring to hide in.
  Keeping more rounds open would give each proof several rounds to hide in; a failed proof already voids every later round
  (next section).
- The summed `round over` times include that wait: `settle` runs after the `rule-set evaluation` phase, so the next round's
  phase time absorbs it.

**Three rounds kept open (2026-10-13).** The main path now settles a round only once three newer rounds are open
(`settle(&mut open, 3)`), so each winner's proof has three rounds of scoring to hide in. The rollback check
(`scripts/spec_rollback.sh`) still gives one rollback at round 0 and one lookahead replay, and the chosen rules equal
e9a8be1's. Sequential pair against e9a8be1 (`scripts/o3_seq.sh`, rows `o3s_*`; CPU 8% at launch, RTP off): rows,
preferences and all 27 rule and unit files identical on both salts; no proof failed. cmp3d's summed rounds took 3.0 against
4.3 s and 1.8 against 2.6 s, about 1.43× faster. Wall 29 against 32 s (salt 1) and 21 against 21 s (salt 2).

**Where `own` and `pooled` spend their time: the winners' proofs (samply, 2026-10-13).** A whole salt-1 sweep at 9d86b24
(`MACHINE_STATE=0`, debug-info build; CPU 7% at launch, RTP off) took 31 s in-test under the profiler: `mines` about 14 s,
`own` 12 s, `pooled` 5 s. With weights, over the 39 miner processes started after `mines.tsv` was written:
- Their test threads spend 9.45 s waiting in `settle` for winners' proofs, 0.73 s waiting for scoring and 3.4 s busy. These
  mines are short (106 rounds over 39 mines, so about 3 each), so there are few later rounds for a proof to hide behind.
- Their other threads: proofs 3.6 s inside `prove_rule` (`tree_proof` 3.6 s, `Dd::apply` 1.7 s) plus 6.3 s of kernel
  checks (`check_rc`) whose callers are cut off. As in the ref mines' profile, those sit on the proof threads. Scoring
  takes 1.35 s. Lemma-cache lookups are 0.15 s.
- Half the proofs repeat work done in another process: the 39 mines chose 67 rules, only 34 of them distinct, and proved 65
  winners (none failed). The lemma cache (`shared_lemma`) holds only the case lemmas inside machine proofs. A rule's own
  proof (`prove_any` → `prove_rule`, then its kernel check) is rebuilt and rechecked in every process that picks it.
- A profile of `own pooled` alone, on the same libraries (so starting with an empty lemma file), looked the same: 10.3 s in
  `settle` of the miners' 15.3 s.
- What would recover it: keep each winner's verdict across the sweep's processes, as the lemma file keeps lemmas. The
  verdict depends on what the proof may use (the base rules and preferences, the step budget), so the key must hold
  those, or the choice could change. Whether the repeats share those inputs (pooled loops share a base; an `own` loop's
  batches grow theirs) is not yet counted (next item).
- Negative result: they almost never do. A temporary probe (reverted, no patch kept) printed a hash of each own/pooled mine's
  proof inputs: its base rules, preferences and step budget. A salt-1 sweep at a8259d0 gave 67 chosen rules: 34 distinct
  rules, but 64 distinct (inputs, rule) pairs across 32 distinct inputs. Only 3 proofs repeat with the same inputs, so a
  verdict cache keyed exactly would save about 3 of the 65 proofs. Not built. Getting the rest would mean keying a verdict
  by the rule alone. That is sound, since a proved rule is a true law, but it could change a choice where a rule is provable
  under one base and not another. No such case has been seen (no winner proof has failed in a sweep), but a pair sweep would
  have to show identical output.

**Winner verdicts kept across the sweep (negative, reverted, 2026-10-13).** A prototype (reverted, no patch kept) keyed each
winner's verdict by the rule alone. `prove_any` looked up `rule_proved_<l>_<r>_<n>_<k>` in the sweep's lemma file and took a hit
as provable; a built proof recorded its statement under that key. In the sequential pair against 84242e0 (`scripts/vc_seq.sh`,
rows `vcs_*`; CPU 23% at launch, RTP off), rows, preferences and all 27 rule and unit files were identical on both salts. But
nothing got faster. Wall was 44 against 42 s (salt 1) and 22 against 30 s (salt 2). Summed `own` mine time was 14.6 against
12.0 s and 3.3 against 3.6 s; `pooled` was 3.3 against 2.7 s and 3.3 against 3.6 s. The reason is where the wait sits. Almost
all of `own`'s time on salt 1 is one mine, `own_cmp3d_1`'s second (9-12 s), whose rounds take about 0 s; every other
own/pooled mine takes 0.2-1.2 s. Its time is three lazy proofs. One of them is a rule no earlier process had proved, so no
verdict cache can hit it. The repeated proofs the cache does skip are the cheap ones. The 9.45 s that the miners spent in
`settle` in the profile above (salt 1 too) is most likely that one proof (next section).

**Case trees at nv = 9 (2026-10-13).** A timing probe (reverted, no patch kept) did three things. It timed each winner proof in
`prove_any`, summed the check time in `holds` by the kind of check, and timed each case lemma that `tree_proof` built (build
plus check) by nv and by whether a diagram proved it (`lemma_dd`, used at `nv >= DDMIN`, then 9).
- One proof is half of all proof time. A salt-1 sweep's winner proofs took 16.1 s, and 7.9 s of it was `own_cmp3d_1`'s
  `lt(sub(x, y), add(sub(x, add(shl1(x, 0), y)), z)) -> lt(add(-1, add(sub(y, z), x)), sub(x, sub(z, x)))`. Of that, 5.8 s
  was checking its 14 case lemmas at nv = 9, 3 operand bits plus 6 carries, proved as diagrams. Every other proof took at
  most 0.35 s.
- At nv = 9 the diagrams cost more than case trees, in time as well as visits. Every lemma the probe built, across whole
  sweeps (`mines own pooled`, one at a time, CPU 20% at launch, RTP off), compared `DDMIN=9` against `DDMIN=99` (case trees
  only):

| lemmas | salt 1, diagrams | salt 1, case trees | salt 2, both |
|---|---|---|---|
| nv = 9 | 12, 0.87 s each (10.4 s) | 12, 0.32 s each (3.8 s) | none |
| nv = 7 (case trees in both) | 220, 0.039 s each (8.6 s) | 219, 0.033 s each (7.2 s) | 169, 0.036-0.039 s each |
| all | 23.4 s | 15.0 s | 10.4 / 9.3 s |
| sweep wall | 44 s | 34 s | 33 / 32 s |

- `proof_cost_split` agrees. It ran on cmp3d with a 37-rule own library (salt 1's `own_cmp3d_3`) and 300 laws, ABBA. The
  same 12 lemmas at nv = 9 took 2.52 and 0.95 s each as diagrams against 0.39 and 0.47 s as case trees. The rule proofs took
  37.3 and 18.1 s to build against 14.6 and 12.9 s. Laws, node counts and occurrences were identical.
- That reverses the 2026-10-10 measurement above (diagrams 47.1 s CPU against 52.2 s for case trees), which kept `DDMIN=9`.
  Since then the case trees got cheaper relative to the diagrams; why was not traced. No lemma wider than nv = 9 occurred in
  these sweeps or in `proof_cost_split`, so the threshold is now `DDMIN=10`. At that setting the diagrams prove nothing seen
  so far. They stayed for wider lemmas until measured there and deleted ("Decision diagrams deleted").
- Sequential pair against 84242e0 (`scripts/dd_seq.sh`, rows `dds_*`; CPU 33% at launch from other sessions, RTP off):
  rows, preferences and all 27 rule and unit files identical on both salts. Wall 45 against 51 s (salt 1) and 27 against
  36 s (salt 2); summed `own` mine time 7.7 against 15.8 s and 3.8 against 4.1 s.
- The case lemmas at nv = 7 are now the largest proof cost: 7-8.6 s per sweep, about 0.035 s each.

**One motive for a case tree (2026-10-13).** `lemma_n` proves `body` by splitting on every bit, so a tree over k bits has
2^k - 1 internal nodes. Each node used to carry its own motive, `\y. body(args)`, with the bits fixed so far as literals.
Checking a node means typing its motive, so the kernel typed `body`, a large `Id` over gate terms, once per node. Now every
motive applies one closed `P = \v_0..v_(k-1). body(v)` to its arguments (`\y. P args`). The kernel types `P` once, and its
pointer is shared, so each node's motive is a cheap application. The statement and the leaves are unchanged, and so is the
kernel: a node's branch types are `P` applied to literals, which beta-reduce to the old motives' bodies.
- `proof_cost_split` (cmp3d, the 37-rule own library from "Case trees at nv = 9", 300 laws), five alternating runs with an
  `OLDMOTIVE=1` switch in the prototype (removed). The rule proofs' build, which includes their case-lemma checks, won every
  pair: 8.3-10.9 s (best 8.27) against 11.2-14.4 s (best 11.25), about 1.36x. Node counts and occurrences were identical.
- Sequential pair against 50ba04f (`scripts/mot_seq.sh`, rows `mos_*`; the head side is the prototype with
  `OLDMOTIVE=1`, which runs HEAD's motives; CPU 22% at launch, RTP off): rows, preferences and all 27 rule and unit files
  identical on both salts. Wall 25 against 31 s (salt 1) and 23 against 24 s (salt 2); summed `own` mine time 4.9 against
  8.1 s and 2.9 against 3.2 s.

**Leaves that state the computed bit (negative, reverted, no patch kept, 2026-10-13).** A case-tree leaf proves `Id(a, b)`
at fixed bits with `refl(a)`, so the kernel normalizes the gate terms `a` and `b` and compares them. A prototype (`LEAFV=1`)
gave the leaf `refl(bit(v))`, with `v` the value computed outside the kernel, hoping the conversion would be cheaper.
- Computing `v` with the kernel's `normalize` was slower: `normalize` alone took about 3.2 s over about 36k leaves.
- Computing `v` in plain Booleans (`Bools` through the side machine, F lemmas only), `proof_cost_split` (cmp3d, the 37-rule
  own library, 300 laws): wall won 7 of 10 alternating pairs, best 7.23 against 8.48 s, medians about 8.8 against 9.5 s, CPU
  about 22% from other sessions. Process CPU time over 6 alternating pairs (`scripts/cpu_ab.ps1`) was mixed, best 9.41 against
  9.52 s. The kernel still normalizes both `a` and `b` against the literal, so the leaf's work barely changes. Not kept.

**Decision diagrams deleted (2026-10-13).** After "Case trees at nv = 9" the diagram path (`lemma_dd`, `DdGates`, `Dd`, `Sig`,
the `DdLemmas` and `good_mux`; `DDMIN`, `NOBDD`) ran only at nv >= 10, which no workload reaches. To measure it there, a probe
(reverted, no patch kept) proved three 4-variable laws with `add_tree_law(4, 4, ..)`, each substituting into the nv = 9 law
above (`lt(sub(x, y), add(sub(x, add(shl1(x, 0), y)), add(z, u)))`, the same with `sub(z, u)`, and
`lt(sub(x, add(y, u)), ..)`): 7 carries on each side, so lemmas at nv = 11, unguarded. Three runs each, same load:
diagrams 18.9-31.2 s per law, case trees 18.0-29.0 s. No gain at nv = 11 either, so the path is deleted; every case lemma is
now a `lemma_n` case tree. Also gone: the `Gates::table` method (only the diagram used it) and the diagram test (74 tests
remain). `CARRY_CAP` (10) still bounds the trees at 2^(k + 10) leaves.
- Sequential pair against 5f65267 (`scripts/nodd_seq.sh`, rows `nds_*`; CPU 40% at launch from other sessions, RTP off):
  rows, preferences and all 27 rule and unit files identical on both salts, as expected, since no lemma reached nv = 10.
  Wall 29 against 31 s (salt 1) and 34 against 29 s (salt 2): no change beyond noise.
- The mul laws, where the carry cap matters (`mul_conjecture_miner`, `MULMINER_MAX=7`, all 91 laws, `CARRY_CAP` 10; their
  widest machines have 9 carries, so unguarded lemmas at nv = 11), one run at a time, 5f65267 against 0cb4e6c
  (`scripts/cap_ab.sh`, order old head head old; CPU 41% at launch from other sessions, RTP off): both prove 90 laws, none
  over the cap, and leave `(1*1)x = 1(1x)` unproved. Totals 43.3 and 42.7 s with diagrams against 45.7 and 38.5 s without;
  the widest law, `7(x-y) = 7x - 7y` (carries 5 and 9), took 7.1 and 9.2 s against 13.4 and 8.0 s. Within noise, so the cap
  stays at 10.

**Where the case lemmas' time goes (samply, 2026-10-13).** `proof_cost_split` (cmp3d, the 37-rule own library, 300 laws) at
0cb4e6c, debug-info build, CPU 19% at launch, RTP off; 10.4 s in-test, 10.4k busy samples (idle leaves dropped). Analysis:
`docs/runs/2026-10-12/scripts/prof_cases.py` (reads `prof11/pcs.json.gz` and the symbol table samply writes beside it; the
profile itself is not kept).
- `tree_proof`'s case lemmas (`shared_lemma`) are 52% of all busy samples. Of that, the kernel check (`ck`) is 63% and building
  the tree (`lemma_n`) 36%.
- Building is mostly the leaves. Each leaf rebuilds both sides at its literal bits (`Machine::step` over `GoodOps`, then
  `table_app`): 32% of the lemma time. `table_app` alone is 19%, and 4% is `tab_bdd` recomputing the same table's diagram
  at every leaf.
- Checking is beta reduction. `def_eq` 54%, `beta_spine`/`instantiate_n` 52%; under them hash-cons interning (`hc::intern`)
  takes 46%, with 26% self time in `intern_as`'s table probe and 11% in `inst_get`. The kernel instantiates `P` at each
  leaf's literals and normalizes both sides; every intermediate term is interned.
- Not yet tried: building each table's diagram once per lemma rather than once per leaf; building the leaves from a cheaper
  statement. Leaves stating a precomputed bit did not help (above), because the kernel still normalizes both sides.

**Truth tables built once (2026-10-13).** `table_app` now builds its closed lambda once per truth table, interning generation
and thread, as `constant` does for the gates; the key is the table's rows, so `tab_bdd` and the `mux` nodes are built only on
a miss. Terms are unchanged (hash-consing already made a rebuilt lambda the same node). Check:
`table_bodies_are_shared_per_truth_table`.
- `proof_cost_split` (cmp3d, 37-rule own library, 300 laws), process CPU time over 6 alternating pairs with a temporary
  `NOTABMEMO` switch (removed; `scripts/cpu_ab.ps1`, CPU 20% at launch, RTP off): the memo won all 6, 8.61-9.64 s (best 8.61)
  against 9.53-10.70 s (best 9.53), about 10%; rule-proof build 6.3-7.2 s against 7.2-8.0 s.
- Sequential pair against 51cd960 (`scripts/tab_seq.sh`, rows `tbs_*`; the head side is the prototype with `NOTABMEMO=1`;
  CPU 17% at launch, RTP off): rows, preferences and all 27 rule and unit files identical on both salts. Wall 31 against 30 s
  (salt 1) and 32 against 30 s (salt 2): the sweeps' proof work is too small a share for 10% of it to show.

**What else could be memoized (survey, 2026-10-13).** From the profile above and the code:
- *The side machines' step at each leaf, across a tree's lemmas.* `tree_proof` states m + 1 F lemmas per side (output and
  each next phi bit) over the same k + c bits, and each leaf of each recomputes `Machine::step` over `GoodOps` at its literal
  bits, then the phi tables of the next carries. One `(side, bits) -> (out, next)` memo per `tree_proof` would build each
  step once instead of m + 1 times. Building leaves was 32% of lemma time, `table_app` included; open what is left now.
  Done: "One builder memo, and each step once per leaf", below.
- *Normal forms of closed terms across `def_eq` calls (kernel).* `ReductionCache` lives for one top-level `def_eq`/`whnf`/
  `nf` call (`src/kernel.rs` near 1424), so every leaf renormalizes the same closed gate applications (`and` of two literal
  bits, say). A cache keyed by canonical pointer, per interning generation, for closed terms would collapse them. Reduction
  is context-free for closed terms, so it is sound, but it touches the trusted kernel. Gain unmeasured: first count distinct
  canonical closed `App` nodes normalized per lemma. Counted: at most about 1%, not worth it ("A closed-term normal-form
  cache would save about 1%", below).
- Smaller: `GoodOps::new` per `tree_proof` (rebuilds three `good2` proofs; not visible in the profile); the guarded leaves'
  `hty` and `inv_expr` (now hit the table memo).

**Interning in the kernel's reduction (survey, 2026-10-13; read-only, a subagent's report checked at the cited lines).** The
hash-cons table (`mod hc`, `src/kernel.rs` near 828) already uses a pointer hash (`PtrHasher`) and shallow keys (child
pointers); removing or narrowing it lost badly ("Hash-consing cost", above). Open options, most promising first:
1. `args_id` (near 1136) re-interns every argument of every `instantiate_n` (`intern((*a).clone(), None)`, a clone and a
   probe) although `beta_spine`/`whnf_step` hold canonical `Rc`s; taking `&Rc<Expr>` and skipping canonical ones removes
   that. `args_id` was 11-14% inclusive of lemma time; "Hash-consing cost" estimated at most about 7%. Done: "Canonical
   arguments are not interned again", below.
2. `inst_rec`'s per-child work makes up to four separate `TABLE.with` borrows (`uses`, `inst_get`, `intern`, `inst_put`);
   fusing them saves TLS and `RefCell` traffic. Inside `hc` only; gain unmeasured.
3. Pre-reserve `nodes`, `inst`, `uses` when the table switches on: `reserve_rehash` was 5-9%. One line per map.
4. The closed-term normal-form cache above (measured below: about 1%; dropped).
5. A separate, non-interning normalizer for closed Bool terms: largest change, adds to the trusted base; last.
Minor: `arg_sets` still uses SipHash (`Vec<usize>` keys).

**One builder memo, and each step once per leaf (2026-10-13).** `constant` and `table_app` now share one helper, `gen_memo`
(`encoding.rs`): a thread's values by key for the current interning generation, emptied when the generation changes, with the
kernel's multiply-rotate hasher (`Fx`). Moving the two onto it changed nothing measurable: 8.02-8.34 s against 8.05-8.41 s
CPU over 4 alternating pairs of `proof_cost_split` (cmp3d own, against 4da7e02).
- Left off it on purpose: `CLOSED`/`shared_lemma` (rewrite.rs) and `TREE_LAWS`/`TREE_ENCS` (machine.rs) live for the whole
  thread. The generation changes mid-run (the table switches on after `WARM_UP` calls, and every outermost `InternScope`, one
  per scoring worker and per `prove` call in the miner, starts a new one), and
  `CLOSED` binds each key to a lemma parameter in `PARAMS`; emptying it per generation would rebind lemmas and could change
  outputs. `TREE_*` cache decisions and closed proofs that stay valid across generations.
- The step memo is local to `tree_proof`, not a `gen_memo`: its key would have to name the machine and the encoding tables,
  while within one `tree_proof` `(side, bits)` suffices. `guarded` now hands its case function the leaf's bits (`None` in the
  statement), and the F and P lemmas take a side's `(output, next carries, phi of the carries)` from the memo, so each leaf's
  step and its m phi values of the carries are built once instead of once per lemma (m + 1 F lemmas plus P). The `core`
  proof keeps the direct path (symbolic bits, built once per position).
- `proof_cost_split` (cmp3d own, 300 laws), CPU time over 16 alternating pairs with a temporary `NOSTEPMEMO` switch (removed;
  `scripts/cpu_ab.ps1`; CPU 17-35% from other sessions, RTP off): the memo won 13 of 16 (2 of 4, 5 of 6, 6 of 6 per round);
  summed 161.1 against 180.4 s, about 11%; rule-proof build 6.6-8.3 s against 8.5-10.1 s in the last round.
- Sequential pair against 4da7e02 (`scripts/step_seq.sh`, rows `sts_*`; covers the helper and the step memo; RTP off): rows,
  preferences and all 27 rule and unit files identical on both salts. Wall 29 against 28 s (salt 1), 27 against 28 s (salt 2).

**A closed-term normal-form cache would save about 1% (negative, 2026-10-13).** A temporary probe at 464e24f (reverted, no
patch kept) recorded, in the kernel's `whnf_rc` on a cache miss, every closed node (`loose_of == 0`) by pointer for the
interning generation. It counted the nodes reduced again, whether in the same public `check`/`infer` call or an earlier one,
and timed the outermost such repeats. `proof_cost_split` (cmp3d own, 300 laws, one run, 8.6 s CPU):
- Inside `check`/`infer`: 6.76 s over 1134 top-level calls, so the kernel is about 78% of the run (lemma checks fall in
  "build").
- Closed `whnf_rc` misses: 2.22 M, of which only 72.8 k reduced anything; the rest were already in weak head normal form.
- Repeats: 34.5 k within the same call (a later `def_eq` with a fresh `ReductionCache`) and 86.1 k from earlier calls, of which
  0.7 k and 23.5 k reduced anything. All repeats together took 70 ms.

So a cross-call cache of closed normal forms could save at most about 70 ms of 6.76 s (1%), and it would add to the trusted
kernel. Not built. A limit of the count: nodes are matched by pointer, so a closed redex rebuilt outside the hash-cons table
(e.g. `beta_spine`'s fresh head `Rc`) is never a repeat. Those heads are mostly gate lambdas, already in weak head normal
form. The kernel's time is in the reductions that do run and in interning (items 1-3 of the survey above), not in repeats.

**Canonical arguments are not interned again (2026-10-13).** `subst_top`, `instantiate` and `instantiate_n` now take their
arguments as `&Rc<Expr>` (every kernel caller already held them so; `beta_spine` passes its spine's `Rc`s through, and the
unit tests wrap theirs). `hc::args_id` uses a canonical argument's own address, which is its table node by definition, and
interns only the others; before, it cloned every argument and probed the node table for it on each substitution. Check:
`args_id_is_the_same_for_a_canonical_argument_and_its_twin` (the id of a canonical node and of a twin built outside the
table agree). The kernel's results are unchanged: the id is the same either way.
- `proof_cost_split` (cmp3d own, 300 laws), CPU time, `scripts/cpu_ab.ps1` in its two-build mode, HEAD 01018d6 against the
  change, RTP off. Other sessions' builds made the load swing (13-57%), and one round at 100% was dropped. Over the four
  other rounds (24 pairs) the change won 17, with 1 tie: summed 252.0 against 280.4 s, best 7.58 against 8.44 s, about 10%
  either way. In the quietest round it won 5 of 6, 8.03-11.11 s against 9.09-15.28 s.
- Sequential pair against 01018d6 (`scripts/aid_seq.sh`, rows `ais_*`): rows, preferences and all 27 rule and unit files
  identical on both salts. Wall 46/46 s against 39/30 s, with 57% load from other sessions' builds at the end; the
  sweeps' proof share is too small for a 10% gain on it to show, and the walls are not evidence either way.

**Where the time goes after the memos (samply, 2026-10-13).** Run on be98b3e, `proof_cost_split` (cmp3d own, 300 laws), built
with debug info, analysed by `scripts/prof_cases.py` with its directory pointed at the new profile (profile not kept; 9227
busy samples; CPU 21% at launch). Against the 0cb4e6c profile ("Where the case lemmas' time goes"):
- Case lemmas (`shared_lemma`): 41.6% of busy samples (was 52%). Inside them, the kernel check `ck` is now 81% (was 63%) and
  building (`lemma_n`) 17% (was 36%): the builder memos removed most of the build side.
- The kernel dominates the whole run: `infer` 74.5% inclusive, `def_eq` 59%, `beta_spine` 57%, `instantiate_n` 60%. Of the
  substitution, hash-consing is most: `hc::intern` 32% inclusive overall, `args_id` now 6.3% of lemma time (was 11-14%).
- Self time is table probes, not reduction logic. Under the case lemmas: the node table probe (`intern_as`'s `TABLE.with`)
  17.4%, the instantiation memo probe (`inst_get`) 11.7%, `reserve_rehash` 6.4%, `intern` 5.8%, the `uses` memo 3.9%,
  `RawTable::insert` 2.8%, `args_id`'s set lookup 2.6%, `inst_put` 2.3%. `beta_spine` itself is 3.1%.
- Dropping the table at the end of each outermost scope (`hc::Scope::drop`, mostly `drop_inner_table`) is 5.6% of all.

Open leads from this, cheapest first (none tried yet):
1. Growth and teardown: `reserve_rehash` (6.4% self, 9.2% inclusive overall) and the per-scope drop (5.6%) together
   are about 15%. The table could keep its allocations across scopes (`clear()` keeps the capacity) or reserve on switch-on.
   Either one is a few lines inside `hc`.
2. The probes themselves (`intern_as` 17.4%, `inst_get` 11.7% self) are hash lookups in large tables, likely bound by
   cache misses. Fusing the `TABLE.with` borrows (survey item 2) saves thread-local and `RefCell` traffic, not misses.
   Fewer or smaller entries would, but no candidate has been identified or measured.
3. `hc::uses` (6.8% inclusive in the lemmas) recomputes per (node, depth, count); smaller.

**Keeping the table across scopes would save under 1% of a sweep (negative, 2026-10-13).** Lead 1 above. Probe: a temporary
line in `hc::Scope::drop` (reverted, no patch kept) logged each outermost table drop's sizes and drop time. Result from one
`mines own pooled` sweep on be98b3e, salt 1, 58 s wall:
- The sweep makes 160 outermost drops across 54 processes. A miner, server or pooled process drops 1-4 times; only the
  three `mine_ref` processes drop often (19-31 times each, 76 in all).
- Tables reach 0.4-1.2 M nodes and up to 3.5 M instantiation entries.
- All 160 drops together take 1.35 s, against up to 58 s × 12 threads of CPU (CPU time not measured). Growth reinserts about one final table's
  worth of entries per scope, which is the same order.
- So the 15% in `proof_cost_split` is that benchmark's shape: one scope that grows a large table and tears it down at
  exit. Retaining capacity helps only on a second scope in the same thread, and sweeps have few. Pre-sizing would need a
  size hint, and sizes vary 3× between processes. Neither was built.

**The spine's head reduced as its own node; `args_id` without a Vec per call (2026-10-13).** Two items from an
allocation scan of the hot paths. Allocator work (malloc, Vec growth, drop glue) was about 5% of the samply profile above;
the table probes are the bulk.
- `beta_spine` used to reduce a fresh `Rc` copy of the spine's head. That was one allocation per spine, and its
  `ReductionCache` entry could never hit again, because the cache is keyed by pointer. When the head was stuck, every
  level of the spine reduced the head again. It now reduces the head node the spine holds, and collects the arguments
  only once the head is a lambda.
- `hc::args_id` built a `Vec<usize>` of ids on every call, including the one-argument case, which returns at once. It
  then moved the Vec into the set, which freed it on a hit. Now one argument returns its id directly. Up to 8 ids go in a
  stack buffer, the set is probed with `get`, and the Vec is allocated only for a new list. Check:
  `args_id_is_stable_for_short_and_long_lists`.
- `proof_cost_split` cmp3d own, against a1ad219, two rounds of 12 alternating pairs. CPU load was 16-24% at the round
  boundaries; Defender RTP was off.
  - Round 1: new won 10 pairs, summed CPU 123.2 against 128.7 s.
  - Round 2: new won 7 pairs, 106.6 against 112.5 s.
  - Together: won 17 of 24, about 5% less CPU. The best single runs don't confirm it: 9.61 against 9.41 s in round 1,
    and 7.03 against 8.17 s in round 2.
- Sequential pair (`scripts/bsp_seq.sh`, rows `bss_*`): rows, preferences, pooled rules and units, and the 26 rule and
  unit files are identical on both salts. Only `own.tsv`'s elapsed-seconds column differs. Wall 36/21 s against 32/24 s.

**The builder side is about 8% (samply, 2026-10-13).** Run on af20655, `proof_cost_split` as above (profile not kept; 7206
busy samples; CPU 11% at launch). It answers whether the case-tree builder has allocations worth removing.
- Building (`lemma_n`) is 8.5% of busy samples. Of that:
  - Interning the built nodes is 65% (`intern_as`'s table probe alone is 33% self).
  - The machine step at the leaves (`Machine::step`, the gates) is 31%.
  - `table_app` is 29%.
  - Vec collects are 14%, and the `gen_memo` lookups 5%.
- `table_app`'s row evaluation, which the allocation scan suspected, is small: `table_app`'s own self time plus
  `tree_proof::closure$3::closure$0`, which is probably the row closure, come to 3.4% of building, about 0.3% of the run. Keying its memo by the caller instead of the rows would save
  about that much. The rest of `table_app` is applying the memoised body to the leaf's variables, which is interning.
- Each builder slice is at most about 2.5% of the run, and most of that is node interning that a build has to do. No
  builder change was made. The kernel's table probes (`intern_as` 27% inclusive, `inst_get` 14%) and growth
  (`reserve_rehash` 9.4%) remain where the time is.

**Reducing a built term without copying it when stuck is neutral (negative, 2026-10-13).** Five `whnf_step` sites pass a
term built for the call to `whnf_impl`, which copies it when it is stuck. A `whnf_owned(e: Expr)` returning `e` itself
(reverted, no patch kept) changed nothing measurable. `proof_cost_split` cmp3d own against aba7d83, 16 alternating
pairs: it won 8, summed CPU 115.1 against 115.7 s, best 6.27 against 6.08 s.

**Hit rates of the hc tables (2026-10-13).** Probe: counters in `hc` (reverted, no patch kept), written at the outermost
scope's end. Run on aba7d83, `proof_cost_split` cmp3d own. The counts were identical on two runs.

| Table | Lookups | Hits | Entries at the end |
|---|---|---|---|
| `nodes` (`intern_as`) | 16.77 M | 81% | 3.17 M |
| `inst` (`inst_get`) | 11.05 M | 39% | 6.77 M |
| `uses` | 8.48 M | 93% | 0.60 M |
| `arg_sets` (two or more arguments) | 2.09 M | 70% | 0.63 M |
| `shifts` | 1.66 M | 61% | 0.64 M |

- The instantiation memo is the largest table and has the lowest hit rate. Each miss costs a probe and an insert.
  68% of its misses (4.61 M) rebuild a node the node table already holds.
- Nodes whose children are all leaves (`Var`, `Sort`, `Const`, `Free`) are 40% of `inst_get`s (4.47 M), and only 36%
  of those hit. `App` nodes are 65% of `inst_get`s (7.16 M), and 36% of those hit.
- Lead, not tried: skip the instantiation memo for nodes whose children are all leaves.
  - That saves 4.47 M gets and 2.85 M inserts, and makes the table 42% smaller, which cuts growth and teardown too.
  - It costs 1.62 M rebuilds. Each is a node-table probe, plus a `shift` of the argument when it lands under binders,
    which is memoised.
  - The outputs cannot change: the memo only shares results that are built the same way anyway.

**Small nodes skip the instantiation memo (2026-10-13).** This is the lead above, with the cutoff measured.
- `inst_rec` now neither looks up nor stores a node at most two levels above its leaves (`hc::low`); it rebuilds it.
  Check: `low_is_height_at_most_two`.
- The cutoff was chosen with a temporary knob over heights 1-4 in one build (removed). Each step is 12 alternating pairs
  of `proof_cost_split` cmp3d own:

  | Step | New won | Summed CPU, new against old | Best, new against old |
  |---|---|---|---|
  | height ≤ 1 against no skip | 10 | 74.9 against 82.0 s | 6.00 against 6.53 s |
  | ≤ 2 against ≤ 1 | 11 | 76.6 against 81.4 s | 5.84 against 6.09 s |
  | ≤ 3 against ≤ 2 | 2 | 81.9 against 80.5 s | 6.66 against 6.41 s |
  | ≤ 4 against ≤ 3 | 0 | 76.8 against 67.4 s | 6.00 against 5.80 s |

  Beyond height 2 a node's rebuild costs more than its probe and insert.
- The final build against 8cd8dfa, 12 alternating pairs: won 11, summed CPU 76.9 against 86.6 s (11% less), best 5.70
  against 6.28 s. CPU load was 5-27%; Defender RTP was off.
- Sequential pair (`scripts/low_seq.sh`, rows `lws_*`): every file is identical on both salts (rows, preferences,
  pooled rules and units, the rule and unit files), apart from the elapsed-seconds column of `pooled_prefs.tsv`.

**After the skip; the same cutoff for `uses` and `shifts` does not pay (negative, 2026-10-13).** Probe as before
(counters, reverted, no patch kept) on 0fb9cad:

| Table | Lookups | Hits | Entries | Small nodes (height ≤ 2): lookups, hits |
|---|---|---|---|---|
| `nodes` | 18.77 M (was 16.77 M) | 83% | 3.17 M | |
| `inst` | 5.91 M (was 11.05 M) | 44% | 3.28 M (was 6.77 M) | skipped |
| `uses` | 8.52 M | 93% | 0.60 M | 1.70 M, 99.99% |
| `shifts` | 1.67 M | 61% | 0.64 M | 0.48 M, 99.7% |

The skip halved the instantiation memo's lookups and entries, for 2.0 M more node-table probes. Unlike the
instantiation memo, `uses` and `shifts` almost always hit on small nodes. Skipping their memo there was tried with
temporary knobs (removed), 12 alternating pairs each on `proof_cost_split` cmp3d own:
- `uses`: won 5, 85.6 against 86.5 s. Neutral. The memo hit costs about as much as walking a small node.
- `shifts`: won 3, 133.2 against 131.5 s, with other sessions' load at 54% during the round. Rebuilding a shifted node
  interns it, which costs a probe per node instead of one hit.

**How many lookups are keyed by a leaf (probe, reverted, no patch kept, 2026-10-13).** This is the ceiling for one shared
node id: an immediate tagged value for a leaf (`Var`, `Sort`, `Const`, `Free`), the address otherwise, plus per-table
height cutoffs in place of `hc::low` and the scattered shape checks. Counters on 1b7dad9, one `proof_cost_split` cmp3d own:

| Structure | Lookups | Keyed by a leaf | Other |
|---|---|---|---|
| `nodes` (by the interned node's height) | 18.77 M | 2.27 M (12%), 99.98% hit | height 1: 0.06 M; taller: 16.44 M, 81% hit |
| `args_id` arguments | 9.43 M | 2.56 M (27%), none non-canonical | |
| `shifts` | 1.67 M | 0.48 M (29%), 99.7% hit | |
| `ShiftMemo` (local) | 1.37 M | 0.26 M (19%) | |
| `whnf_rc` cache | 2.75 M | 0.04 M (1.5%) | 60% hit |
| `InferCache.types` (memo path) | 3.61 M | 0.98 M (27%) | 53% hit |
| `InferCache::enter` binder types | 0.62 M | 0.37 M (59%) | |

- Height-1 nodes are 0.3% of node lookups, so inlining them in the id would save nothing.
- Leaves in `args_id` are already canonical, so immediate ids would only remove the address-reuse risk there, not work.
- Probes an immediate id could drop: about 4.0 M of the 28.8 M across the hash tables (14%; `nodes` 2.27, `infer` 0.98,
  `shifts` 0.48, `ShiftMemo` 0.26, `whnf` 0.04). Most are hits on hot entries, cheaper than the instantiation misses the
  height-2 skip removed (5.1 M lookups and 3.5 M inserts for 11%), so the expected gain is a few percent at most.

**Leaves skip the infer and shift memos (negative, 2026-10-13).** The cheapest test of that ceiling: a temporary knob
(`LEAFSKIP`, reverted, no patch kept) skipping the memo for leaf keys in `infer_rc`, `shift_child` and `shift_memo_child`,
12 alternating pairs each on `proof_cost_split` cmp3d own (`scripts/cpu_ab.ps1` with a value), Defender RTP off:

| Memo skipped for leaves | New won | Summed CPU, new against old | Best, new against old | CPU load |
|---|---|---|---|---|
| `InferCache.types` | 8 | 110.1 against 112.1 s | 8.95 against 9.02 s | 59% |
| `shifts` | 6 | 94.2 against 91.0 s | 5.63 against 5.45 s | 31% |
| `ShiftMemo` | 4 | 82.2 against 81.6 s | 5.52 against 5.83 s | 12% |

All three are within noise: a leaf's memo hit costs about what inferring or re-interning the leaf does. So the shared
node id with an immediate leaf value and per-table height cutoffs is not worth building for speed (parked).

**Where the node table's time goes (samply, 2026-10-13).** Profile of `proof_cost_split` cmp3d own at 1f4db8b (profile not
kept; `scripts/prof_callers.py`), 5870 busy samples:
- `hc::intern` is 34% of busy samples. Its callers: `inst_rec` 22%, the builders' `app`/`app2`/`app3` 7%, `shift_child`
  and `shift_memo_child` 3%, the rest under 2%.
- Inside it, the probe itself (the `intern_as` closure's own samples) is 18%, `RawTable::insert` 7% and growth
  (`reserve_rehash`) 3%; allocation is the rest. With 3.2 M entries of 56 bytes (a 48-byte `NodeKey` and the `Rc`), the
  table is at least 180 MB, so most probes miss the cache.
- Growth across all tables is 10%: the node table 3.2%, `inst` 2.2%, `InferCache.types` 1.2%, `args_id` 0.9%, `whnf` 0.6%.
  Freeing the tables at the outermost scope's end is another 6%.
- Lead: keep the node table as a set of node pointers with their stored hashes (hashbrown's `HashTable`, comparing
  against the candidate node itself), 16 bytes per entry instead of 56. A hit already touches the node to bump its count,
  so comparing there costs no extra miss, and the smaller table caches better and grows more cheaply.

**Most infer-memo entries are never read (probe, reverted, no patch kept, 2026-10-13).** Hits per `InferCache.types`
entry, counted when its cache drops, same run:

| Node | Entries | Read at least once | Hits |
|---|---|---|---|
| `App`, closed | 0.25 M | 42% | 0.27 M |
| `App`, open | 1.02 M | 15% | 0.26 M |
| `Lam`, closed / open | 0.02 / 0.11 M | 70% / 10% | 0.29 / 0.01 M |
| `Pi`, closed / open | 0.004 / 0.03 M | 57% / 3% | 0.22 / 0.007 M |
| leaf, closed / open | 0.003 / 0.15 M | 57% / 45% | 0.13 / 0.70 M |
| other, closed / open | 0.03 / 0.07 M | 4% / 8% | 0.003 / 0.02 M |
| all | 1.70 M | 21% | 1.91 M |

79% of entries are never read. Open non-leaf nodes are 1.24 M entries (73%) for 0.30 M hits (16%). Skipping the memo
for them (knob `INFERSKIP`, reverted, no patch kept) is far worse: 12 alternating pairs, won 0, summed CPU 203.1 against
66.4 s, the check stage about 10 s against 1 s. Each lost hit re-infers a whole subtree, so the unread entries are the
price of the few hits that matter (negative).

**The node table holds node pointers with their hashes (2026-10-13).** This is the lead from the profile above.
- `hc::Table::nodes` is a hashbrown `HashTable<(u64, Rc<Expr>)>`. A lookup hashes the new node's key as before, then
  compares the stored hash and, only when it matches, the candidate node's own key (`hc::key_of`). An entry is 16 bytes
  instead of 56, and growth rehashes from the stored hash without reading any node.
- Check: `intern_finds_equal_nodes_after_growth`.
- Against 6cd8948, two rounds of 12 alternating pairs of `proof_cost_split` cmp3d own: won 8 (80.0 against 82.0 s, load
  9-23%) and 12 (67.7 against 73.2 s, load 11-15%). Together won 20 of 24, summed CPU 147.7 against 155.2 s (5% less);
  best 4.81 against 5.11 s. Defender RTP was off.
- Sequential pair (`scripts/pset_seq.sh`, rows `pss_*`): every file is identical on both salts (rows, preferences,
  mines, the 26 rule and unit files), apart from the elapsed-seconds columns. The sweeps took 22 and 19 s wall on both
  builds, too short for the difference to show.

**The memos store only their results (2026-10-13).** `inst`, `shifts` and `uses` no longer hold a copy of each entry's
source node. A source the node table does not already keep (one that is not canonical) goes once per insert into one
list, `Table::keep`, which lives to the scope's end, so no node built later takes an address a memo key holds. Entries
shrink from 40 to 32 bytes (`inst`, `shifts`) and 32 to 24 (`uses`), and a hit or insert no longer touches the source's
count.
- Check: `memo_sources_outlive_their_callers`, which fails when `pin` keeps nothing (a node built after the caller drops
  its source takes the address and inherits the entry).
- Against 9fab09a, 24 alternating pairs of `proof_cost_split` cmp3d own: won 16, summed CPU 138.8 against 141.0 s (2%
  less), best 4.97 against 5.05 s; load 7-12%, Defender RTP off. Small, but the entries are smaller and the code no
  simpler or more complex, so it stays.
- Sequential pair (`scripts/slim_seq.sh`, rows `sls_*`): every file identical on both salts, apart from the
  elapsed-seconds columns.
- `ShiftMemo` (the builders' local shift memo) still keeps source and result pairs; it is outside the table and its
  scope.

**Profile after the two table changes (samply, 2026-10-13).** Same run as "Where the node table's time goes", at 849bf22
(profile not kept; `scripts/prof_callers.py`): 5221 busy samples against 5870, load 4%.

| | 1f4db8b | 849bf22 | 0fdd223 (after the `uses` slot) |
|---|---|---|---|
| `hc::intern` (from `inst_rec`) | 34.4% (22.3%) | 30.9% (18.8%) | 33.2% (20.4%) |
| its own lookup (`intern_as` closure, self) | 18.0% | 18.1% | 17.4% |
| growth, all tables (node table) | 9.6% (3.2%) | 7.1% (1.1%) | 5.7% (1.0%) |
| `inst_get` (self) | 8.6% | 9.8% | 10.2% (9.0%) |
| freeing the table at the scope's end | 5.9% | 6.3% | 6.7% |
| `hc::uses` | | | 2.1% |

The 0fdd223 column (`scripts/prof_callers.py` and `scripts/prof_self.py`) has 6372 busy samples at 28% machine load,
so compare its shares, not its counts. The `uses` walk is down to 2.1%, and the two table probes are now 26% of busy
samples on their own (node table 17.4%, `inst` 9.0%). The next largest self times are `drop_glue` 5.7%, `intern`'s
own body 5.3%, `height_at_most` 2.8% (the instantiation memo's small-node test), `args_id` 2.7% and `key_of` 2.3%.

The lookup's own time did not shrink: a hit still reads the candidate node, at a random address, to compare it and
bump its count, so the cost is that one miss per hit rather than the table's size. Growth fell by a quarter, most of it
the node table's. Freeing the table is now mostly dropping its nodes (`Rc::drop_slow` 4.3%), not its arrays.

**Rebuilt nodes equal to their source (negative, 2026-10-13).** Probe (reverted, no patch kept) of the node-table
interns `inst_rec` makes, same run at f73a52e:

| Nodes | Interns | Found in the table | Result is the source node itself |
|---|---|---|---|
| small (no memo, height ≤ 2) | 5.49 M | 90% | 1.15 M (21%) |
| memoized | 3.28 M | 52% | 204 |

`Table::keep` stayed empty: every memo source was canonical. The 1.15 M can be recognized without a probe: when the
rebuilt node has its source's key and the source is canonical, the table's node is the source. `hc::intern_from`
(reverted, no patch kept) did that. Against f73a52e, 24 alternating pairs: won 8, summed CPU 134.2 against 126.2 s,
median pair +0.07 s. The probe it saves lands on the source, which the walk has just read and is cached, so it was cheap;
the key comparison costs on every intern.

**A per-scope arena for the table's nodes (survey, not viable, 2026-10-13).** Freeing the table is 6% of the profile;
an arena freed in bulk would skip touching each node. Probe (reverted, no patch kept), same run: the one outermost scope
interned 3.17 M nodes, and 0.49 M of them (16%) were still alive after its table dropped, held by the proofs, types and
caches the scope returned. Those are ordinary `Rc`s pointing into the scope's memory, so the arena could not be freed
while any is alive, and they cannot be moved. Dropping the table took 270 ms of the 6 s run. Also ruled out: dropping
it on another thread (`Rc` is not `Send`) and keeping it across scopes (under 1%, above). Fewer nodes interned is the
only way left to shrink it.

**Who looks up what, and how much a one-entry slot per node would catch (probes, reverted, no patch kept,
2026-10-13).** Same run at 35efc0f.
- The builders (`app`, `pi`, `lam` and the rest) interned 7.67 M terms, all with the table on, and 7.09 M (92%) were
  already there (0.74 M of those leaves). They take `Expr` by value, so a term the caller already holds as a node is
  rebuilt and found again. That is 41% of all node-table lookups, though only 7% of busy samples, since a found node
  was usually built moments before and is cached.
- `inst_get`: 0.86 M of its 5.91 M lookups (15%) use an argument-list id with no entry yet and so cannot hit. Skipping
  them would save at most about 1.4% of busy samples (parked: too small for the per-id flag it needs).
- A one-entry memo slot per node (the key of that node's previous lookup in the same table):

  | Table | Lookups | Hits | Hits the slot would also give |
  |---|---|---|---|
  | `inst` | 5.91 M | 2.63 M | 0.61 M (23%) |
  | `shifts` | 1.67 M | 1.03 M | 0.67 M (66%) |
  | `uses` | 8.52 M | 7.93 M | 7.03 M (89%) |
  | `InferCache.types` | 3.61 M | 1.91 M | 1.47 M (77%) |

Two unifying mechanisms follow (the first is built in the next section; the second is sized and parked two sections down):
- **Pure per-node facts in the node.** `loose` and `free` already live in the node header; `uses(x, d, m)` is a finer
  fact of the same kind and never changes. A slot for it fits the header's 4 padding bytes (no larger nodes), needs
  no generation tag, no keep-alive and no pointer-keyed table, and would answer 7.0 M of the 8.5 M lookups from a node
  the walk is already reading. It does not fit facts that are nodes themselves: a `shifts` or `infer` slot holding a
  result `Rc` makes reference cycles possible (a shift by +1 and back), and the infer cache also lives per call.
- **Canonical handles end to end.** Builders and their callers keep terms as interned nodes rather than `Expr`
  values, so a term already built is passed on, not rebuilt. It would remove most of the builders' 7.1 M re-finds,
  `canonical_inputs`' interning on entry and `args_id`'s interning of non-canonical arguments, but it changes the
  builder interface across `tests/church_bv`.

**Per-node facts in the node header (2026-10-13).** Each node keeps its last `hc::uses(x, d, m)` answer in a `Cell<u32>`
that fills the header's former padding (`Node<Expr>` stays `Expr` + 16 bytes): the query (d and m below 2^15) and the
bit, packed by `Rc::uses_slot`. `uses` answers from the slot before walking and writes the slot after. Check:
`uses_slot_is_free_and_agrees_with_the_walk`. `proof_cost_split` cmp3d own CPU, alternating pairs, Defender off:
- Slot plus the per-scope `uses` table behind it, against 7fe880f: 24 pairs, won 16, summed 122.6 against 127.2 s, best
  4.38 against 4.53 s.
- Slot alone (the table switched off by a temporary `USESNOTABLE` knob) against slot plus table: 12 pairs, won 8,
  summed 54.2 against 55.2 s, best 4.27 against 4.44 s.

So the `uses` table, its `pin` and the knob are deleted; a slot miss walks. (Since 2026-10-14 a miss goes to a per-scope
table of bounds instead, keyed by (node, d) rather than (node, d, m): "The slot in front of bounds".) Sequential sweep pair (rows `uss_*`, script
`uslot_seq.sh`): identical outputs on both salts. The slot can't hold `shifts` or `infer` results, which are nodes
(above).

**How many builder inputs the caller already holds (probe, reverted, no patch kept, 2026-10-13).** Sizes "canonical
handles end to end". `#[track_caller]` on the builders and `hc::intern_new`, counting node-table interns and hits per
call site, and `apps` tagging its first application, later ones, and the argument side. Same run at ec49e4c:
`intern_new` interned 9.36 M terms with the table on, 8.63 M of them found.

| Where | Hits | What is found again |
|---|---|---|
| `apps`: its head and every argument | 2.34 M (of 2.36 M) | held: `Expr` values the caller keeps (`Gb::go`'s `x.g`, `x.e`, the lemma heads) |
| `apps`: each later prefix `f a1 .. ai` | 1.28 M (of 1.52 M) | rebuilt: the same spine built again |
| `and`/`or`/`xor` (`app2` of a constant) | 1.23 M | about 3/4 held (the constant and the two operands), 1/4 the rebuilt prefix |
| `shift_memo_child`'s result | 0.98 M | rebuilt: a shift that equals an existing node |
| `arrow` | 0.47 M | about half held (the domain), half the shifted codomain |
| `infer_rc`'s `Pi`, `Refl` and `J` types | 0.71 M | mostly held: `(**a).clone()` of the term's own children |
| other sites | about 1.6 M | not classified |

So about 4 M of the 8.6 M hits (45-50%) are inputs the caller already held as a term; about 2.8 M are rebuilt terms,
which handles would not remove. The builders were about 7% of busy samples for 7.1 M finds (above), and a held input's
find lands on a node just read, so canonical handles would save at most about 3.5%, less in practice. Most of the held
inputs come through a few places: `apps` (callers pass `Vec<Expr>`), the `and`/`or`/`xor` wrappers, `arrow`, and
`infer_rc`. Parked: at most about 3.5% for a builder-interface change across `tests/church_bv`.

**Two shift memos (probe, reverted, no patch kept, 2026-10-13).** Of the 2.8 M rebuilt terms, 0.98 M are
`shift_memo_child` results. `postulates`' `cong1`, `trans_proof` and `cong_n` shift through a `ShiftMemo` that lives
for one call. It never reads or writes hc's per-scope `shifts` table, which `shift_child` uses. Same run at 0fdd223:
`ShiftMemo` hit 0.34 M times and missed 1.03 M times, every miss inside an interning scope. hc's table already held
the answer for 0.40 M of the misses (39%), the same node each time, although `ShiftMemo`'s own results are never
added to it. One shift memo, hc's table with `ShiftMemo` deleted, would take all of these. The question was whether
anything shifts large shared terms through `cong_n` outside a scope, where hc's table is off. There a shift without
`ShiftMemo` would walk every path of the shared term. It does: `src/proof` builds its `cong_n` and `trans_proof`
chains with no scope open, and that is where `ShiftMemo` made the proof DAG 5x smaller (7f78291).

**One shift memo (2026-10-13).** `cong1`, `trans_proof` and `cong_n` now each open an `InternScope` and shift through
hc's `shifts` table. Inside a scope this costs a depth count. Outside one it gives the call its own table, the same
per-call sharing `ShiftMemo` gave. `ShiftMemo`, `shift_memo`, `shift_memo_child`, `cong1_in`, `trans_proof_in` and
the test `shift_memo_matches_shift` are deleted. New check: `cong_n_shares_shifted_copies_outside_a_scope`, which
builds `cong_n` over a 2^20-leaf DAG outside a scope; with the scopes removed it fails after 12 s. `proof_cost_split`
cmp3d own CPU against ff3eb86, two runs of 24 alternating pairs, both under other load:
- Run 1: won 16, median pair -0.06 s; summed 125.7 against 120.1 s, from four pairs inflated by load, one at 10.1 s.
- Run 2: won 12, median -0.005 s, summed 141.8 against 153.9 s.

Neutral in speed; kept as one memo instead of two. Sequential sweep pair (rows `sms_*`, script `smemo_seq.sh`):
identical outputs on both salts.

**Why the table lookups stay at a quarter of the profile: `whnf` repeats across `def_eq` calls (survey and probe,
reverted, no patch kept, 2026-10-13).** The node-table and `inst` lookups (17.4% and 9.0% self at 0fdd223) cost one
cache miss per hit (above), so only fewer lookups would shrink them. `instantiate_n` is 55% of busy samples, and
46.8% of it is `beta_spine` under `whnf_step`. `whnf` is a pure function of the node: it unfolds no constants and
reads no context. Yet its memo, `ReductionCache.whnf`, lives for one `def_eq` (or `whnf`, `nf`) call. Probe of
`whnf_rc` in the same run at 0064aa7:

| | Count | Time |
|---|---|---|
| `whnf_rc` cache misses (work done) | 1.09 M | |
| misses on a node already reduced earlier in the same interning scope | 0.86 M (79%) | |
| outermost misses (all time under `whnf_rc`) | | 3.95 s |
| repeats not nested in another repeat | | 0.83 s (21%) |
| outermost misses that reduce, and the repeats among them | 189 K, 93 K | |

The probe's timers ran about 1 M times and add overhead; an earlier run without the nested-repeat count gave 2.08 s
outermost. Most repeats are cheap, stuck terms. The repeats that reduce carry the time: about a fifth of `whnf`'s
time, so at most about 10% of busy samples. A per-scope `whnf` memo would catch them, kept like `inst` and `shifts`:
keyed by node in hc's table, results kept alive by `pin`. The result is a node, so it can't go in the header (cycles,
above). Following "one shift memo", `ReductionCache.whnf` could then be deleted for the table, with `def_eq`, `whnf`
and `nf` opening a scope of their own. (Built in the next section.) The other sources of lookups were sized above: the
builders' held inputs (at most about 3.5%) and `inst_get`'s argument lists with no entries yet (at most about 1.4%).
The `apps` prefixes (1.28 M finds, "How many builder inputs the caller
already holds") have no memo to share: the same spine is rebuilt from held arguments, which only canonical handles or a memo keyed by the caller would avoid.

**Weak head normal forms kept for the scope (2026-10-13).** While the table is on, `whnf_rc` reads and writes hc's
new `whnf` map (node -> its weak head normal form, sources kept alive by `pin`) instead of `ReductionCache.whnf`,
which now serves only calls with the table off. Check: `whnf_memo_outlives_one_def_eq_in_a_scope`, which fails with
the table path disabled. `proof_cost_split` cmp3d own CPU against 3892f3d, 24 alternating pairs, load 15%: won 17,
median pair -0.20 s, best 4.39 against 4.66 s. Summed 122.5 against 136.7 s, but one pair alone accounts for 6.2 s
of that. Sequential sweep pair (rows `whs_*`, script `whnf_seq.sh`): identical outputs on both salts.

**`conv` repeats pairs across `def_eq` calls (probe, reverted, no patch kept, 2026-10-13).** `conv_rc(a, b)` is pure
too: its result is whether `nf(a) == nf(b)`. Same run at 3892f3d, interning on:

| | Count | Time |
|---|---|---|
| `def_eq` calls | 1.88 M | 3.58 s in all |
| `conv_rc` comparisons (pointer-unequal) | 215 K | |
| pairs already compared earlier in the scope | 112 K (52%) | 1.88 s, counted where not nested in another repeat |
| `eq_noting`'s `unequal` notes | 193 K | |
| notes on a pair already met in the scope | 60 K (31%) | |
| `nf_rc` misses | 0 | |

A per-scope memo from pair to result (with `unequal` folded in) would answer those repeats without reducing either
side: at most about half of `def_eq` time. It would also cover much of what the `whnf` memo saves, so measure it
against the `whnf` build. `nf` does not run in this workload; its cache stays per call.

**Built and measured against f77238e (both reverted, no patch kept, 2026-10-13): neutral.** `proof_cost_split` cmp3d
own CPU, 24 alternating pairs each, Defender RTP off, about 12-16% other CPU load at the start:

| Variant | Won | Median pair | Best new / old |
|---|---|---|---|
| unordered node pair -> result in hc's table, read and written by `conv_rc` while the table is on | 10 of 23 | +0.08 s | 4.61 / 4.66 s |
| no memo; `conv_rc` skips `==` and the `unequal` note when both sides are canonical (distinct canonical nodes are structurally unequal) | 10 of 24 | +0.01 s | 4.80 / 4.80 s |

The first variant passed a check that a `def_eq` answer stays in the table for the scope and is gone without the memo;
the probe's 1.88 s was timed with its own timers on (inflated, as in the `whnf` probe), and after the `whnf` memo a
repeated pair costs only its walk over memoized weak head normal forms. Folding `unequal` into the table is moot: while
the table is on, canonicity already answers `==` for the pairs it would hold, and skipping it saved nothing measurable.
Closed.

**Profile at 8334948 (= f77238e's code; samply of `proof_cost_split` cmp3d own, profile not kept, 2026-10-13).** 9656
busy samples; about 11% other CPU load, Defender RTP off. Little moved after the `whnf` memo:

| Share of busy samples | 0fdd223 | 8334948 |
|---|---|---|
| `instantiate_n` inclusive | 55% | 54.4% |
| ... under `beta_spine` (from `whnf_step`) | 46.8% | 44.3% |
| ... under `infer_node` | | 8.4% |
| `whnf_rc` inclusive, all from `conv_rc` | | 35.0% |
| node-table lookup (`intern_as`'s closure), self | 17.4% | 16.4% |
| `inst_get`, self | 9.0% | 7.1% |
| `hc::intern` callers: `inst_rec` / `app` / `app2` / `shift_child` | | 19.7 / 4.6 / 2.5 / 2.1% |

Where the lookup's self time goes, by sampled instruction (`prof_addr.py` plus `llvm-objdump`; samples land on
the instruction after the one that waited): 29% just after the indirect call that fetches the thread-local `TABLE`
(its lazy-initialization accessor) and the copy of the moved `Expr` out of the closure; 18% on the probed slot's stored
hash and 12% on the group of control bytes (cache misses on the table itself); 8% writing a new entry; 4% building a
new node. Comparing a candidate's key (reading the candidate node) is not among the hot spots: the stored hash filters
almost every mismatch. So about a third of the lookup is memory latency inherent in a table this size, and about a
third is call overhead around it. Leads: a `const`-initialized `TABLE` (no lazy accessor; hashbrown's tables and the
default hasher can be made in a `const`), and interning without moving the `Expr` through the closure. At most about 5%
of busy samples between them.

**Both built (2026-10-13): `TABLE` is `const`-initialized (`Table::new`; `arg_sets` moved to the pointer hasher, whose
ids come from insertion order, not the hash), and `intern_as` looks up under a shared borrow that captures only the key,
moving `e` once into `build` on a miss and inserting under a second borrow.** `proof_cost_split` cmp3d own CPU against
8334948, two runs of 24 alternating pairs, Defender RTP off, about 12% other CPU load at the start: won 14 (median pair
-0.06 s, best 4.61 against 4.61 s) and 16 (median -0.12 s, best 4.81 against 4.98 s). A small win, about 1-2.5%, less
than the 5% ceiling. Sequential sweep pair (rows `cts_*`, script `ctab_seq.sh`): identical outputs on both salts.

**Fewer substitutions: what was tried before (survey, no code, 2026-10-13).** `beta_spine` -> `instantiate_n` is 44% of
busy samples. Doing fewer substitutions rather than cheaper ones was explored on 2026-09-30 (the git-ignored
`docs/superpowers/specs/2026-09-30-bitvector-interface-design.md` §25-§35, and `src/kernel_lazy.rs`): a closure-based
(call-by-need, Rocq-style) `def_eq` was 13-25x slower without sharing, 8-18x with a pointer-keyed memo, and level with
the kernel from n = 32 once it memoized closed nodes only; it took 467x the kernel's beta steps (each one cheap), so a
step-certificate kernel was dropped. That comparison predates hash-consing, the per-scope instantiation and `whnf`
memos and n-ary `beta_spine`, each of which made the substituting kernel faster, so the lazy evaluator likely trails it
now (not re-measured). What has not been measured is how much of what `instantiate_n` builds is ever read: `conv` reduces only where the
sides differ, so a built subterm that no later `whnf`, `conv` or `infer` visits is pure cost, and only that share is
what laziness (building on demand) could save.

**How much of what `instantiate_n` builds is read (probe, reverted, no patch kept, 2026-10-13).** At 7643319, one
`proof_cost_split` cmp3d own run with a flag byte in the node header: set when `inst_rec` interns a new node, when the
checker reads a node (`whnf_rc`, `conv_rc` on a pointer-unequal pair, `eq_noting` recursing into a non-canonical pair,
`nf_rc`, `infer_rc`, `beta_spine`'s spine walk), and when `inst_rec` or `shift_child` recurses into it. Tallied over
every node in the table at each outermost scope drop:

| | Count |
|---|---|
| nodes in the tables at their drops | 3.17 M |
| `inst_rec` interns | 8.56 M: 2.16 M new nodes, 6.40 M (75%) already in the table |
| new nodes later read by the checker | 0.95 M (44%) |
| ... read only by a later instantiation or shift | 0.27 M (12%) |
| ... never read | 0.94 M (44%) |
| instantiation memo (`inst_get`) lookups | 5.23 M, 1.95 M hits (37%) |
| children skipped by the `uses` shortcut (shifted instead) | 0.44 M |
| children below the memo's height cutoff (not memoized) | 5.28 M |

So more than half of the new nodes instantiation builds are never looked at by the checker, and three quarters of
what it rebuilds already existed. A delayed substitution (a node holding body, argument set and depth, forced when
`whnf`, `conv` or `infer` first reads it) could skip the unread half, but it is a new trusted constructor that every
reader must force, and new nodes are only a quarter of the interns; the saving is bounded by about half of
instantiation's 44% of busy samples, less the forcing overhead. Open: lead, not built.

**The instantiation memo still pays after the `whnf` memo (2026-10-13).** `go` with `memo` forced to false (reverted, no
patch kept) against 7643319, 24 alternating pairs, Defender RTP off: lost all 24, median pair +0.44 s, best 4.89 against
4.45 s (about 9% slower). Kept.

**The instantiation memo keyed by the arguments a child uses: neutral (reverted, no patch kept, 2026-10-13).** A child
whose loose variables reach only the last `j < m` arguments instantiates the same under any list ending in those `j`, so
`inst_rec` keyed it by that suffix's `args_id` (made once per `instantiate_n` call and suffix length, up to 8) instead
of the whole list's. It did what it was meant to: memo lookups fell from 5.23 M to 4.19 M (hits found higher in the
tree), hits rose from 37% to 41%, and 1.76 M lookups used a suffix key, hitting 52%. But `proof_cost_split` cmp3d own
CPU against 136bbe5, two runs of 24 alternating pairs: won 11 (median pair +0.005 s, best 4.70 against 4.69 s; about
28% other load at the start) and 10 (median +0.035 s, best 4.80 against 4.86 s; about 14%). The rebuilds it avoids
were cheap ones. Kept from it: `instantiate_n_matches_sequential_substitution_in_a_scope`, which checks
`instantiate_n` against one `subst_top` per argument inside one scope with arguments from a small pool, so the memo
answers across lists; it fails when the memo key ignores the argument list.

**Design note: delayed substitution (no code, 2026-10-13).** The question was whether `instantiate_n` could build a
child only when something reads it (the 44% of new nodes no one reads, above). Two shapes:

| | A: a new constructor `Subst(body, args, d)` | B: a node whose value is computed on first `Deref` |
|---|---|---|
| Readers | every `match` on `Expr` gains an arm that forces (238 `Expr::` uses in `kernel.rs`, 204 in its tests, 78 in `kernel_soundness_fuzz.rs`); exhaustive matches make the compiler list them, but any of the 10 `_ =>` arms in `kernel.rs` that match an `Expr` would take `Subst` silently | none change: the kernel's `Rc::deref` forces |
| Cost on every read | only where `Subst` is matched | a check on every `Deref` of every node, the kernel's hottest path |
| Missed force | through a `_ =>` arm: a wrong shape, so `same_shape` answers unequal and `infer` errors; incomplete rather than unsound only if each such arm is audited | impossible, but the suspension and its value have different addresses, so address-keyed memos see two nodes |
| Header (`loose`, `free`) | must be known unforced: an upper bound from the body and the arguments is safe (it only skips less) | the same |

Both lose to hash-consing, which is what the kernel's speed now rests on. A node is canonical only if everything under it
was interned; a suspension can't be interned (its children are unknown until forced), so every term holding one is
non-canonical. That turns off the pointer shortcuts for all its ancestors: `==` and `eq_noting` compare canonical
pairs by address and stop, `conv_rc` and the per-scope memos key by address, and the 75% of instantiation interns that
find an existing node are the sharing that lets later comparisons stop at an address. Forcing could intern the result
only by forcing all of its children too, which is eager substitution again. The closure-based evaluator was measured on
2026-09-30, level with a kernel that had none of today's tables (hash-consing came on 2026-10-01).

The saving is also smaller than the 44% suggests. Unread new nodes are 0.94 M of 8.56 M instantiation interns (11%), and
each suspension left at the frontier still costs an allocation and a memo lookup, likely close to what building the node
costs (not measured).
If unread table hits were as common as unread new nodes, the bound would be about 44% of instantiation's 44% of busy
samples (about 20%); counting new nodes only, about 5%. That is before the losses above. Parked. Gate to reopen: a
probe weighting each `inst_rec` result (new or found) by the work below it and counting how much of that work is never
read by the checker in the same scope; reopen only if it is over about 15% of busy samples, and then prototype B
behind a feature with `kernel_soundness_fuzz` and the scoped `instantiate_n` test as the checks.

**What `conv` reduces, and the type checker's own substitution (probe, reverted, no patch kept, 2026-10-13).** The
profile at 8334948, by caller: `whnf_rc`'s 35.0% of busy samples is all `check_rc` -> `def_eq` -> `conv_rc` (34.0%
through `def_eq` from `check_rc`, 1.5% through `same_shape`), and 34.1 of `beta_spine`'s 44.3 points are inside it, so
the two leads above are mostly one cost. The other `instantiate_n` caller is `infer_node`'s `App` rule (`subst_top(cod,
a)`, 8.4%). One `proof_cost_split` cmp3d own run at a73c6a1 with thread-local counters (`inst_rec` and `shift_via`
visits; each pair `conv` or `conv_rc` reduces, classed by which side `whnf` changed; the `App` rule's calls):

| Pairs reaching `whnf` | Pairs | `inst_rec` visits in their `whnf` |
|---|---|---|
| all (`conv` at the top: inferred against expected) | 113 k | 1.81 M |
| all (`conv_rc`, below the top) | 327 k | 8.16 M |
| only the first side reduces | 52 k | 0.16 M |
| only the second side reduces | 83 k | 0.95 M |
| both sides reduce | 148 k | 8.86 M (89%) |
| neither reduces | 157 k | 0 |
| same head (pointer or `==`) and arity | 20 k | 0.68 M (7%) |
| ... arguments pairwise convertible | 8 k | 0.20 M (2%) |

Comparing heads before reducing does not pay: same-head pairs carry 7% of the reduction work, the argument check
succeeds for under half of them, saving 0.20 M visits, and the argument checks themselves cost 1.17 M visits. Not built.
The work is in pairs where both sides are redexes with different heads.

The `App` rule: 1.27 M calls, all with the table on. In 1.05 M (83%) `cod` is closed and comes back as is; in 142 k it
has loose variables but not `Var(0)`, so it is only shifted (0.28 M shift visits); the rest use the argument. In all,
0.65 M `inst_rec` visits and 0.44 M shift visits, against about 10 M under `conv`'s reductions. 0.87 M of the calls
(69%) are on an `App` spine, but substituting a spine's arguments at once could only save the repeated walks of the
non-closed codomains, a small part of the 8.4%. Not built.

**The pairs where both sides reduce are equal redexes with different lambdas (probe, reverted, no patch kept,
2026-10-13).** The same run at 4bad241 without the argument checks (which had added pairs of their own above), counting
only pairs where `whnf` changed both sides, in `conv` and `conv_rc`:

| Both sides reduce | Pairs | `inst_rec` visits in their `whnf` |
|---|---|---|
| all (of 10.29 M in the run) | 124 k | 8.52 M |
| results `==` (never the same pointer) | 90 k | 7.13 M |
| results with the same constructor, not `==` | 33 k | 1.39 M |
| results with different constructors | 0 | 0 |
| `conv` answers equal | 124 k (all) | 8.52 M |
| both heads are a literal `Lam` | 124 k (all) | |
| heads `==` | 5 k | |

So the bulk of the reduction work goes into showing that two applications of different lambdas, `(\x. s) a` against
`(\y. t) b`, are equal, and in 73% of the pairs both reduce to the same term. The results are never pointer-equal
because `whnf_rc` wraps the reduct's top node in `Rc::new` rather than interning it (its children are interned). Where these redexes come
from is answered below (`lemma_n`'s case-tree leaves), and interning the reduct is measured below (neutral).

**Where those redexes come from: `lemma_n`'s case-tree leaves, each a different computation (probe, reverted, no patch
kept, 2026-10-13).** The same run at 3e7e019, with each pair where both sides reduce charged to the `App` rule whose argument
check it fell under (keyed by the spine heads of the function and the argument), and counted again by structure (a
hash over each side's tree) across the whole run:

| Function <- argument | Pairs | Visits | Structurally new pairs |
|---|---|---|---|
| `Var` with 1 argument <- `Refl` | 32.8 k | 4.13 M | 30.3 k (all the visits) |
| `Var` with 2 arguments <- `Refl` | 32.8 k | 3.28 M | 30.3 k (all the visits) |
| `Var` with 1 or 2 arguments <- `Var` with 3 (top-level pairs) | 34.9 k | 0.95 M | 33.1 k |
| `J` <- `J` | 20.7 k | 0.16 M | 6.1 k (all the visits) |

The first two rows are the leaves of case trees: at each split, `g motive on_true on_false` with `g : GoodBool b`
eliminating a bit, and `refl` at a leaf. Checking a leaf `refl(a)` against the motive at that leaf's bits reduces both
sides: the motive `(\b. body) bit` on the expected side, and on the inferred side `a`, a gate term written as
Church-encoded lambdas applied to bits. A first reading charged them to `bit_lemma`, which has the same shape, but a
count of builder calls in the same run (temporary prints, reverted) found `bit_lemma` called 0 times and `lemma_n` (`tests/church_bv/encoding.rs`) 392 times:

| Case bits `k` | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 9 |
|---|---|---|---|---|---|---|---|---|---|
| trees | 4 | 2 | 14 | 19 | 83 | 46 | 30 | 182 | 12 |
| leaves (`2^k` each) | 4 | 4 | 56 | 152 | 1328 | 1472 | 1920 | 23296 | 6144 |

34.4 k leaves in all, matching the 32.8 k leaf checks per row above. Most are `machine.rs`'s `guarded` trees over the
`k + c` operand and carry bits, one per side, tag (`F0..Fm`, `P`, `D`) and encoding, each memoized by `shared_lemma`
and checked once per process. Every pair is structurally new across the run, and repeats within a scope already cost
nothing (the memos answer them).

A memo spanning scopes would find nothing either. A count of every `whnf_rc` miss with the table on (a structural hash
of the term, kept for the whole run) found 227 k misses, 7.74 M `inst_rec` visits under the outermost ones, and none
structurally repeated, closed or not. The trees for `F0..Fm` of one side evaluate the same step at the same bits, but
`beta_spine` instantiates each leaf's body whole, so no reduction is shared at `whnf`'s granularity.

So 72% of the reduction work under `conv` is the kernel evaluating gate terms on concrete bits, once per leaf. It is
the proof by computation itself, not a redundancy, and a kernel memo cannot remove it. Only fewer or smaller leaves
(fewer case bits; decision diagrams lost to the case tree at `nv` = 9 and 11, "Decision diagrams deleted"), leaves
whose sides the builder states already evaluated, or a cheaper evaluation per visit can.

**Leaves stated evaluated, or one tree per side: neither pays (probes, reverted, no patch kept, 2026-10-13).** Two
builder changes were surveyed against the leaf work above, at cacb94b.

*A leaf whose sides are already evaluated.* A leaf proves `refl(a) : Id(a, a)` against the statement at its bits,
`Id(a', b')`. A counter in `check_rc` after each successful check of a `Refl` (about 50 k, sampled every 5000) found `a`
pointer-equal to `a'` in all of them, and `a` structurally equal to `b'` in 32%. So `conv` evaluates `a` and `b'`, and
nothing in that 32%. A leaf `refl(v)` with the value `v` written by the builder would need `a'` and `b'` evaluated against
`v`: the same two evaluations, and more work in the 32%. No gain.

*One tree per side for all its `F_j`.* Temporary prints in `guarded` (`machine.rs`) for the same run:

| Tag | Trees | Leaves |
|---|---|---|
| `F1..Fm` | 291 | 32 662 (96%) |
| `D` | 66 | 968 |
| `F0` | 25 | 550 |
| `P` (no invariant here) | 0 | 0 |

Mostly four `F_j` trees of 7 bits per side (47, 47, 47 and 40 of them). One tree proving the four equalities at once
would keep every leaf evaluation (each `F_j` is a different function of the step, and no `whnf` repeats structurally
across the run, above) and save only the splits: the pairs charged to `Var` <- `Var` with 3 arguments above, 0.95 M of
10.29 M visits, about three quarters of which would go. That is at most about 7% of the reduction work, for leaves that
are conjunctions (a `Sigma` of four `Id`s and its pairs, with their own checking cost). Parked: not worth the change to
the proof format unless the split cost grows.

*Which side the evaluation is on.* `conv_rc`'s two `whnf_rc` calls counted apart (probe, reverted, no patch kept): of
7.74 M `inst_rec` visits, 4.22 M (54%) under the first side's (the inferred one: a leaf's step term) and 3.52 M (46%)
under the second's (the statement: `G_j` as a table over the bits). Neither dominates, so a cheaper table encoding
could save at most the second side's share, and only the part of it that is the table rather than the shared shape.

**The table sized for the last scope: neutral (reverted, no patch kept, 2026-10-13).** Rehashing is 8.4% of busy
samples in the profile at 4bad241 counting callers (5.5% under `inst_rec` and `instantiate_n`, 1.1% under `infer_rc`'s
cache). The prototype merged the table's three switch-on sites into one that reserved the node, instantiation, shift
and `whnf` maps for the sizes the last scope with the table on ended with. `proof_cost_split` cmp3d own CPU against
3e7e019, Defender RTP off, three runs of 24 alternating pairs: won 16 (median pair -0.21 s, best 4.81 against 4.88 s),
6 (median +0.05 s, best 5.28 against 5.09 s; about 74% other load at the end) and 14 (median -0.015 s, best 4.97 against
5.05 s; about 37%). 36 of 72 in all. A likely reason (not measured): scopes differ too much in size for the last one to
predict the next, so a small scope pays to clear a large reservation, and a large one after a small one rehashes as
before.

**Interning the reduct's top node in `whnf_rc`: neutral (reverted, no patch kept, 2026-10-13).** With the table on,
`whnf_rc` interned the reduced term (`hc::intern(r, None)` in place of `Rc::new`), so equal reducts are one node.
`proof_cost_split` cmp3d own CPU against 3e7e019, Defender RTP off, two runs of 24 alternating pairs: won 9 (median
pair +0.015 s, best 4.80 against 4.80 s; three new runs took 10.7-11.3 s, both phases about 2.4x slower) and 10
(median +0.11 s, best 4.89 against 4.80 s; runs over 8 s in both builds, about 13% other load after). The slow runs
were load, not the change. The reducts are compared child by child at canonical pointers already, so making them one
node saves nothing.

**Profile at 4bad241 (samply, profile not kept, 2026-10-13).** `proof_cost_split` cmp3d own, CPU about 9% before the
run, Defender RTP off; 5031 busy samples (the run at 8334948 had 9656; shares compared, not counts). `instantiate_n`
55.4% (46.8% under `beta_spine`, 7.3% under `infer_node`); `conv_rc` 39.3%, all from `check_rc` -> `def_eq`, with
`whnf_rc` 38.9% and `beta_spine` 38.1% inside it; `hc::intern` 30.3% (19.3% from `inst_rec`). Leaves: `intern_as`'s
lookup 9.7%, `inst_get` 8.8%, rehashing 5.2%, `Rc::drop_slow` 4.4%. The const `TABLE` did not change the picture.

**Kernel speed-up thread: closed (2026-10-13).** Every lead that avoids work has been measured and closed above: the
head-first `conv` shortcut, interning `whnf`'s reduct, pre-sizing the table, any memo across scopes (no `whnf` miss
repeats), leaves stated evaluated, one tree per side (at most about 7%, parked), a cheaper table encoding (at most the
statement side's 46% of the leaf work, only in part), and delayed substitution (parked behind its gate). What remains is
the proof by computation itself: 72% of the reduction work under `conv` is gate terms evaluated on concrete bits, once
per case-tree leaf, and every such evaluation is distinct. Reopen only for a new proof shape (fewer leaves, for example
a symbolic per-gate lemma in place of `lemma_n`'s 2^k trees; "Decision diagrams deleted" and the parked closed
`cong_mux` lemma are the earlier attempts) or a cheaper evaluator (below).

**Compiled evaluation for conversion, and the wasm JIT (survey, no code, 2026-10-13).** The profile now favors
evaluating faster rather than less, the case Rocq's `vm_compute` and `native_compute` serve. The repo's JIT
(`src/jit.rs`, `compile.rs`, `lower_wat.rs`) is not that tool:
- It compiles `term.rs` programs typed `Int -> ... -> Int` to wasm, not kernel `Expr` (with `J`, `WRec`, `SigRec`).
  Nothing in `kernel.rs` or `tests/church_bv` calls it; the kernel checks the JIT's proofs, not the reverse.
- It is not end-to-end sound by its own account: its kernel theorem is stated over `proof.rs`'s `denote`, a model of
  the compiler, not over the WAT that runs (`src/jit.rs` header). Using it, or anything like it, for conversion would put
  the compiler, wasmtime and the postulated `Int` in the trusted base.
- The 2026-09-30 options table (bitvector spec §35, row 7) already rated native/VM reflection "trusted base grows; does
  not help the symbolic lemma", verdict "different problem".
- The ceiling is modest (estimate, not measured): `conv_rc` is 39% of busy samples and the leaf evaluation 72% of its
  reduction work, so even free evaluation would save about 28% of the run.
- "Self-improving" in these docs is the rule-mining loop (proved laws compiled into rewrite rules), not a kernel
  compiling its own hot paths; no design for the latter exists.

The cheapest test of the idea is an untrusted evaluator timed on the same conversions: if a closure-based one cannot
beat the kernel there, a compiled one would have to win on constant factors alone.

**`kernel_lazy` on today's conversions: 64-100x slower (probe, reverted, no patch kept, 2026-10-13).** At a357781,
`proof_cost_split` cmp3d own's work (the 300 laws, building and checking, then the rule proofs) with each `check_rc`
query whose sides are not `==` timed in place (the kernel's `def_eq` as it runs, with that check's memos), logged, and
replayed through `def_eq_lazy_shared` (closed-node memo, reset per query). CPU about 28% at the start, Defender RTP off.
The run was stopped by a 3 GB memory guard during the 27th rule proof (`kernel_lazy` reached 3.3 GB; an unguarded run
reached 5.9 GB after 10 CPU-minutes):

| | Batches | Queries | Kernel in place | `kernel_lazy` | Ratio (per batch, kernel over 5 ms) |
|---|---|---|---|---|---|
| laws (build and check) | 300 | 36.2 k | 0.22 s | 22.2 s | 100x (19-69x) |
| rule proofs (26 of them) | 26 | 45.1 k | 1.13 s | 72.8 s | 64x (23-146x) |

Agreement was counted but not printed before the guard stopped the run, so it is not known here. Replaying the kernel after the check instead, while
the outer scope's tables still held the reductions, took 3 µs a query, which is why the kernel is timed in place. On
2026-09-30, before hash-consing, the same evaluator was level with the kernel at n = 32; the tables since then put the
kernel about two orders of magnitude ahead on this workload. So a faster untrusted evaluator is not in reach by changing
the evaluation strategy, and a compiled one would need a constant-factor gain above 60x over closure evaluation just to
draw level, before its trusted-base cost. Not pursued; the JIT thread stays separate from conversion.

**A general symbolic mechanism in place of the case trees? (survey, no code, 2026-10-13).** Ranked by end-state design,
not effort. `lemma_n` is already one general mechanism: any Boolean equality over `k` good bits, proved by splitting
every bit with `refl` leaves. Its callers are the machine proofs' `F`, `P` and `D` lemmas (`guarded`, `machine.rs`),
`bitwise_law_k` (`rewrite.rs`), `pos_law`'s per-bit lemmas (`machine.rs`), and a few tests. No caller special-cases a
gate. Candidates:

| Candidate | End state | Verdict |
|---|---|---|
| Per-gate symbolic lemmas (`and`, `xor`, mux laws), composed by congruence | One lemma per gate, plus a canonical form to meet the table side `G_j`, which is a mux tree, not a gate circuit | More special cases than now; rejected |
| Proof-producing canonical forms (decision diagrams with a proof per node) | One mechanism, as general as `lemma_n` | Built and measured: lost at nv = 9 and 11, deleted ("Decision diagrams deleted") |
| Reflection: a Boolean-expression syntax (a `W` type), its denotation, a checker, and one kernel-checked soundness theorem; each lemma is the theorem applied to syntax with `refl(true)` | One mechanism, as general as `lemma_n`, with four new concepts in place of a 40-line builder (`lemma_n`, `lemma_n_ty`); trusted base unchanged | Not cleaner. Faster only if the kernel's evaluation of the checker beats the leaves. A truth-table checker repeats the same 2^k evaluations with interpretation on top. A diagram checker means the kernel runs diagram operations on Church-encoded data, at k <= 9 (mostly 7), where the proof-producing diagrams already lost (estimate, not measured) |
| One tree per side for all its `F_j` | Same mechanism, fewer trees | Parked above (at most about 7%) |

So no candidate is a cleaner end state than `lemma_n`: the case tree is the general mechanism, and the alternatives are
either special cases or the same generality with more parts. The thread stays closed. One by-product of the
`kernel_lazy` probe: the 26 rule proofs carry 1.13 of the 1.35 s of conversion `proof_cost_split` timed (84%). The
loop checks each rule proof once per library (`shared_lemma`), so `proof_cost_split` weights them more than serving
does.

**Other ways to join the JIT and the loop (survey, no code, 2026-10-13).** The two already state one idea: `jit.rs`
opens with "if a high-level transformation is found to be equivalent to a low-level sequence of operations on the
target machine, use that for future invocations", and the loop compiles proved laws into rewrite rules. Today they
share nothing:

| | JIT (`src/`) | Loop (`tests/church_bv`) |
|---|---|---|
| Terms | `term.rs`: `Int` is i64, wrapping (`eval.rs:137-150`); `Add Sub Mul Div Mod Lt Le Eq` (`term.rs:15-23`), `Lt` signed; no bitwise ops or shifts | `rewrite.rs` `Term`: width-n words; `add sub xor and or shl1 shr1 lt`, `lt` unsigned (`rewrite.rs:58`) |
| What is proved | a term equals its compiled form, over `proof.rs`'s `denote` (a model of the compiler) with `Int` postulated | a law, by the kernel, at one width (`prove_rule(n, ..)`); width-generic proofs are not built |
| Reuse unit | a term's content hash | a rewrite rule (and closed lemmas as parameters, `shared_lemma`) |
| Rewriting | `specialise.rs` only inlines known closures; `spec_check` accepts only beta-v steps | `rule_step` over the mined library |

Options, ranked by end-state design (fewer concepts, fewer special cases):

| | Option | End state | Risks and open questions |
|---|---|---|---|
| A | One term language and one rule library for both: `term.rs` gains the loop's word operators (i64 as width 64), mined laws become rewrite steps the specialiser may take, and `spec_check` accepts a step that instantiates a kernel-checked law; the JIT's compiled terms feed the miner as conjectures, scored by compiled cost (as Souper ranks by instruction count) | Two term languages, two rewriters and two notions of "proved equivalent" become one each; the cycle closes on real workloads | Laws are proved at one width (4 in `proof_cost_split`), and the width 1-6 screen does not imply width 64: needs width-generic proofs or proofs at 64. Signed `Lt` against unsigned `lt`. `proof.rs`'s `Int` is a postulate with no bits, so it needs a bridge to the bitvector encoding. Compilation itself stays trusted (`lower_wat`, wasmtime) |
| B | Compile the mined library into a matcher (for example a discrimination tree), rebuilt when the library changes | Same concepts, faster `rule_step`; untrusted, the kernel still checks every proof | Rewriting is 4.5-6% of the sweep's loops after the rule-list fix ("Where the time goes in the sweep's loops"); wasm adds nothing over a Rust matcher |
| C | The JIT as the miner's evaluator (screens, signatures, scoring) | A second evaluator for the same `Term` | The one large evaluation cost found, the pool's behaviour signatures (`SigMemo`, 56% of serving), was a rebuild per process, fixed by building each family's pool once ("Law files from the driver"); no later profile puts the screens high. Rejected |
| D | Compiled evaluation for kernel conversion | | Closed above (`kernel_lazy` 64-100x behind; trusted base grows) |

A is the only option that removes concepts; B and C each add a second implementation of something that exists. A's
cheapest falsifier is additive and leaves no rework: on the JIT's own corpus (`src/test_corpus.rs`), count the terms
that the mined `add`/`sub` rules would rewrite (ring identities, which hold at every width) and the change in compiled
instruction count. If the mined rules never fire on the JIT's programs, A's cycle has nothing to run on. Not run.

**Compiling hot transformations, with learnable compilations: two falsifiers (probes, reverted, no patch kept,
2026-10-14).** The goal: the kernel compiles hot transformations natively, and the compilations are learned, not fixed.
Of three ways to trust compiled code (trust the compiler, as `native_compute` does; a certificate per output; prove each
compilation step once against a small fixed target semantics), the third gives one object kind and one fixed trusted
piece: optimisations are term-to-term rules, lowerings are term-to-IR rules proved against an IR semantics stated in the
kernel, a hot transformation is compiled by lowering its rule's matcher and builder, and learning a compilation is mining
lowering rules by target cost, with hotness from rule-use counts (not built; precedents from memory, not re-checked:
Alive, STOKE, Souper). Two cheap tests of its base:

1. *Can lowering templates be stated and proved as kernel laws?* Yes. `tests/lowering_law_probe.rs` (deleted) stated a
   typed-stack IR as a shallow kernel semantics: `Code = Pi S:Sort0. S -> Sigma(Int, S)` (runs on any stack, pushes one
   Int) and `Spec(c, m) = Pi S. Pi s:S. Id(Sigma(Int,S), c S s, pair(m, s))`, with `Int`, `add` and `sub` postulated as
   `proof.rs` does. Checked by the kernel: Lit (`Spec(lit n, n)`, by `refl`); Add (`Spec(c1,m1) -> Spec(c2,m2) ->
   Spec(add_template c1 c2, add m1 m2)` for arbitrary code `c1`, `c2`, by `cong1` and `trans_proof`); and If (a
   bool-pushing `cc`, then `ct` or `ce`, by `cong1`, `cong_n`, `sym` and `trans_proof`). Negative controls were
   rejected: the Add template lowering to `sub` under the same statement, and If with its branches swapped. A concrete
   term's compiled code (`add(lit k1, lit k2)`) was proved by applying the two template laws, with no per-term search.
   One obligation surfaced: If needs its condition to be *natural* (`f (b x y) = b (f x) (f y)` for every `f`), which a
   Church boolean does not give for free; `tt` and `ff` are natural by `refl`, so each instruction that pushes a
   condition (`lt`, `eq`) must prove it in its own spec. Limits: the IR semantics is a model in the kernel, as `denote` is,
   so the step from it to wasm stays trusted; that is the fixed piece this design keeps. All checks took under 0.01 s.
2. *Does scoring by compiled cost pick different rules than scoring by M?* Yes, mostly, and the two objectives conflict
   on cmp3d. A `RULEMINER_LAWW` weight (default 1000, the weight of a fixed law and of the guard laws) was set to 0, so a
   rule scores only by the cut in the stragglers' normal-form size (`measure`: operator weight times 16 plus variable
   occurrences, a proxy for a stack IR's instruction count, one instruction per node; not counted from `lower_wat`). Ref
   loops on phase 0 (`LOOP_MODE=ref`, B=150, K=4, `RULEMINER_FAST=1`, `CHECK_FAST=1`, 2 threads; each loop 2-5 s):

   | | rules | shared | stragglers fixed | serve M | size cut |
   |---|---|---|---|---|---|
   | add3, scored by M | 14 | 2 | 87 of 87 | 1 | 1075 |
   | add3, size only | 8 | | 34 of 87 | 83 | 1075 |
   | cmp3d, scored by M | 27 | 5 | 250 of 264 | 16 | 457 |
   | cmp3d, size only | 24 | | 171 of 264 | 120 | 4205 |

   On add3 both reach the same total size, and the M-scored library also fixes every straggler: size-only stops when no
   rule cuts size, before the zero-cut rules that close proofs. On cmp3d, seven of the M-scored rounds grow normal forms
   (1803 in total) to fix 41 laws, so the M-scored library cuts 9x less size; the size-only library leaves 7.5x more
   machine proofs. Learning by compiled cost is therefore not subsumed by today's miner, and one miner can serve both
   with one objective of two weighted terms (proof cost and compiled cost) rather than two miners. The mul and shl
   families gave no test: under today's built-in rules mul (`MULMINER_MAX=5`) has 0 stragglers of 50 laws, and shl
   (`RULEMINER_LAWS=300`) has 5 stragglers of 305 laws and 0 oriented candidates.

**The fixed-law weight between 1000 and 0 (probe, reverted, no patch kept, 2026-10-14).** The same ref loops with
`RULEMINER_LAWW` at 1000, 300, 100, 30, 10, 3 and 0 (seconds per loop; the 1000 and 0 rows repeat the runs above
exactly). "Fixed" is stragglers fixed in the mine; serve M is on the same 600 (cmp3d) or 204 (add3) laws, so both are
in-sample, one phase, one salt:

| weight | cmp3d rules | fixed of 264 | serve M | size cut | add3 rules | fixed of 87 | serve M | size cut |
|---|---|---|---|---|---|---|---|---|
| 1000 | 27 | 250 | 16 | 457 | 14 | 87 | 1 | 1075 |
| 300 | 28 | 250 | 16 | 457 | 14 | 87 | 1 | 1075 |
| 100 | 30 | 253 | 14 | 3740 | 14 | 87 | 1 | 1075 |
| 30 | 32 | 249 | 17 | 4044 | 16 | 85 | 3 | 1075 |
| 10 | 36 | 228 | 39 | 4469 | 12 | 82 | 5 | 1075 |
| 3 | 32 | 244 | 20 | 4249 | 13 | 82 | 5 | 1075 |
| 0 | 24 | 171 | 120 | 4205 | 8 | 34 | 83 | 1075 |

At weight 100, cmp3d's library is better on *both* terms than at 1000: 3 more stragglers fixed, serve M 14 against 16,
and 8.2x the size cut. On add3, 100-1000 give the same library. So the greedy miner at 1000 is not M-optimal either:
rules that grow normal forms to close a proof now block cheaper closures later. Not yet a default change: it is
in-sample, and an `own` loop on phases 1-3 (held out) at weight 100 against 1000 is the test (not run). Below 100, M
degrades; the curve is not monotone (10 is worse than 3 on cmp3d).

**Formalizing the target machine (survey, no code, 2026-10-14).** What the kernel would have to state to prove
lowerings against the real target, and what exists. What `lower_wat.rs` emits today (by counting its instruction
strings): i64 `add sub mul div_s rem_s lt_s le_s eq or shl shr_u const extend`, `local.get/set/tee`, `i64.load/store`
(closure environments in linear memory), `call`, `call_indirect` (unknown calls through a table), `block`, `br`, `if`.
Today the IR-to-WAT lowering is trusted, validated per compilation by the decompiler (a hash check, IR to term) and
per template by differential tests against `eval.rs` at edge values (`docs/superpowers/specs/2026-09-23-jit-ir-design.md`,
steps 2-3).

Options, ranked by end-state design:

| | Option | End state | Risks and open questions |
|---|---|---|---|
| B | Deep embedding of the emitted wasm subset in the kernel: instructions as data (a `W` type), an interpreter by `WRec` over code, `i64` as the loop's Church bitvectors at width 64 | One semantics for both systems: the ops both have (`add`, `sub`, `or`, unsigned compare) are the same functions at n=64, so a mined law over them applies to compiled code directly (`mul`, `div_s`, `rem_s`, `eq` and shifts by a variable amount still need defining over bits), and signed `lt_s` is definable from unsigned `lt` (flip the sign bits). Lowering rules are term-to-instruction-list rules, proved once against the interpreter; `lower_wat`'s templates become data the kernel checks, so `lower_wat` and the decompiler leave the trusted base (wasmtime stays) | Proof cost at n=64: `add x 0 = x` is gated at under 400 k nodes at n=64 and about 3x per doubling (`encoding.rs:599-612`), and the universal lemma checks at n=64 (`encoding.rs:1001`), but mined rules at n=64 are not measured. Traps (`div_s` by zero, `MIN / -1`) need a partial result type. Memory and `call_indirect` need a heap and a table model; a straight-line i64 fragment first (no memory) is an additive stepping stone |
| A | The shallow typed-stack semantics of the probe above, with `Int` postulated | Lowering laws over a model; the model-to-wasm step stays trusted | Values have no bits, so the loop's laws do not connect without a postulated bridge, and instructions are kernel functions, not data, so a lowering cannot be compared with `lower_wat`'s output. A probe, not an end state; B restates its three laws deep |
| C | Import a mechanized Wasm semantics: WasmCert-Coq (Wasm 2.0 per its author's 2025 thesis), WasmCert-Isabelle, or SpecTec (the spec written once; its generated interpreter passes the official 2.0 test suite, PLDI 2024) | Fidelity to the standard without hand-writing it | Different logics (Coq's CIC, Isabelle/HOL) from this kernel's small MLTT; SpecTec's prover backends are prototypes (an IL-to-Coq translator for Wasm 1.0; Lean and others as future work, per a Dagstuhl abstract and ECOOP 2025). Rejected as the kernel's semantics; kept as B's differential oracle (run SpecTec's interpreter or the official test suite against B's interpreter on the emitted subset) |
| D | Go below wasm: a native ISA semantics (Sail models of Arm-A and RISC-V, with Isabelle, Coq and HOL4 output, and a Lean target used by sail-riscv per a 2026 project script) | Removes wasmtime and Cranelift from trust | The ISA models are large and the native code is Cranelift's, not ours. Crocus (ASPLOS 2024) already verifies Cranelift's ISLE lowering rules against aarch64 semantics with SMT, finding a 9.9-severity CVE among known bugs: evidence that lowering-as-rules works at production scale, not a part to rebuild. Parked |
| E | SMT-checked lowering rules (Crocus, Alive style) in place of kernel proofs | Fast checks | A second checker, which the one-kernel design avoids. Usable as a screen before the kernel proof, as the width 1-6 screen is for laws |

B is the only option that removes concepts: the JIT's postulated `Int`, `proof.rs`'s `denote` model of the compiler
and the decompiler's role as the trusted check all collapse into one interpreter over bitvectors that the loop already
uses. Cheapest falsifier, additive: state `i64.add` and `i64.lt_s` over width-64 Church bitvectors, re-prove the
probe's Add and If templates deep (instruction lists interpreted by `WRec`), and time the proof of one mined cmp3d rule
at n=64 against n=4. If the n=64 rule proof is out of reach, B needs width-generic proofs first. Run in part, with
the shallow templates rather than deep ones: see the next paragraph.
Sources: [Crocus](https://cs.wellesley.edu/~avh/veri-isle-preprint.pdf), [WasmCert](https://hal.archives-ouvertes.fr/hal-03353748),
[SpecTec](https://pldi24.sigplan.org/details/pldi-2024-papers/64/Bringing-the-WebAssembly-Standard-up-to-Speed-with-SpecTec),
[Iris-Wasm](https://pldi23.sigplan.org/details/pldi-2023-pldi/46/Iris-Wasm-Robust-and-Modular-Verification-of-WebAssembly-Programs)
(a separation logic over WasmCert-Coq, for programs rather than compilers), [Sail](https://www.cl.cam.ac.uk/~pes20/sail/popl2019.html),
[sail-riscv Lean script](https://raw.githubusercontent.com/Verified-zkEVM/evm-asm/main/scripts/regen-sail-model.sh).

**Mined rules at width 64, and compiled programs proved equal from them (probes, reverted, no patch kept,
2026-10-14).** Two probes in `tests/church_bv/rewrite.rs` at e49847e, on the 37 rules of cmp3d's own library
(`cmp3d_own_rules.txt` without its `OVER` lines). Machine load about 30% CPU at the start of each; Defender real-time
protection off.

*Width.* Every rule's law (`prove_rule`) builds and checks at n = 4, 8, 16, 32 and 64:

| n | check, all 37 (s) | slowest rule (s) | mean proof nodes |
|---|---|---|---|
| 4 | 2.96 | 1.12 (includes warm-up) | 5306 |
| 8 | 1.18 | 0.08 | 9860 |
| 16 | 3.32 | 0.23 | 18987 |
| 32 | 10.89 | 0.74 | 37319 |
| 64 | 40.36 | 3.59 | 74294 |

Nodes about double per doubling of n (linear); check time grows about 3.7x from 32 to 64. The largest proof at n=64
has 175544 nodes and checks in 3.5 s. So this library needs no width-generic proofs to reach wasm's i64; the survey's
question "is the n=64 rule proof out of reach" is answered no, for these rules.

*End to end.* Both sides of each rule compiled with the stack templates (shallow: `Code = Pi S. S -> Sigma(V, S)`, as
in the first falsifier above, now with `V` the Church words of width n instead of a postulated `Int`), each side's spec
proved by composing the Lit and Bin template laws, and the goal `Pi S s. Id(c_l S s, c_r S s)` proved by
`trans(spec_l, cong(push, law), sym(spec_r))` from the rule's own kernel law. The Bin law needs an output value type:
`lt_u` returns a one-bit word, not an n-bit one (as `i64.lt_s` pushes an i32), so the law is stated once per output type
(`Bv_n`, `Bv_1`); each checks in about 1-2 ms. Results, 37 rules:

| n | equivalences proved | spec proofs by template laws (s, all) | same spec by `refl` | equivalence check (s, all / slowest) | mean / max proof nodes | mean code nodes |
|---|---|---|---|---|---|---|
| 4 | 37 | 0.11 | 37 | 0.85 / 0.07 | 6321 / 13903 | 1155 |
| 64 | 37 | 0.43 | 37 | 68.2 / 10.2 | 81317 / 183582 | 11569 |

The equivalence check includes checking the embedded rule law, which alone is 40.4 s of the 68.2 at n=64 (width table).
Controls: with the rule law replaced by `refl`, all 37 equivalences are rejected; each Bin law is rejected against the
other output type's statement. Two traps met on the way, worth knowing for any code that reuses mined laws: the laws
refer to shared lemmas bound as parameters of the thread-local `PARAMS` postulates (`shared_lemma`), so they check
only in that scope (in a fresh `Postulates` the check fails with "free parameter escaped its scope"); and a pushed
`lt` value has `Bv_1` as its inferred type, so pairs need the output type explicitly.

*What this changes in the survey.* The step that option B's first falsifier was to measure, mined rule proofs at the
target's width, is cheap, and a mined law transfers to compiled code through one congruence, with per-compile spec
proofs from the template laws costing well under a second. Not shown here: signed `lt_s` (the miner's `lt` is
unsigned) and any op outside the loop's eight; the If template is the next paragraph. On deep syntax: a `W` type of
instructions is costly in this kernel, which has no computing finite tag type; `NatPostulates` gets one only through
postulated computation axioms (`child_ty_true_eq`, `bool_rec_true_eq`, `src/kernel/postulates.rs:472-485`) and a
transport per constructor, which would grow the trusted base. Two ways around it: keep the semantics shallow and trust
only the printer from the template-built instruction list to WAT text, or Church-encode instruction lists; the second
is tested two paragraphs down and works.

**The If template with a compiled `lt` condition, and instruction lists as Church-encoded data (probes, reverted, no
patch kept, 2026-10-14).** Both on a fresh cmp3d library: a ref loop at e49847e (`LOOP_MODE=ref FAMILY=cmp3d
RULEMINER_FAST=1 CHECK_FAST=1`), 27 rules, 24 of them `lt` rules. (The 37-rule list of the paragraphs above was a
scratch copy of a run directory that no longer exists, and was deleted by mistake, so the two libraries differ.)
Machine load 21-29% CPU; Defender real-time protection off.

*If.* The first falsifier's If needed its condition at the stack's universe (`b (Sigma(V,S)) ..`, with naturality).
That route is closed for the loop's words: their bits are Church booleans in Sort0 and stacks live in Sort2, and the
kernel has no large elimination, so a bit cannot choose between two stacks. What a bit can choose is a bit: a
word-level `select c x y` built from the existing `mux` gate per bit is definable and checks (on literal words it
returns the named branch, and not the other). So the If template pops the one-bit condition, runs both branches on
the rest of the stack and pushes `select w v_t v_e`, which is what wasm `if` computes when both branches are pure;
control flow proper (only one branch runs, effects) is not modeled. Its law, `Spec(c_c,m_c) -> Spec(c_t,m_t) ->
Spec(c_e,m_e) -> Spec(if c_c c_t c_e, select m_c m_t m_e)`, is three congruences and checks in about 1-2 ms; against
the swapped-branch statement it is rejected. For each `lt` rule `l -> r`, `if l then x else y` and `if r then x else y`
(branches the rule's first two words) were compiled and proved equal from the rule's law:

| n | equivalences proved | spec proofs (s, all) | equivalence check (s, all / slowest) | mean / max proof nodes |
|---|---|---|---|---|
| 4 | 24 of 24 | 0.09 | 0.53 / 0.04 | 6625 / 7694 |
| 64 | 24 of 24 | 0.32 | 29.3 / 1.86 | 78953 / 94034 |

With the rule law replaced by `refl`, all 24 are rejected. Not shown: an If whose branches are themselves compiled
terms, and `if true then a else b = a` for a symbolic `b` (with Church tuples `select` nests both branches'
eliminations, so that holds by computation only for literal `b`; it would need `GoodBv`).

*Instruction lists as data.* A naive Church list does not work: `fold (l1 ++ l2)` is `fold l2 . fold l1` only by
induction on an abstract `l1`. Two choices make it hold by beta. A program is encoded by its end stack type,
`Prog S T = Pi F:(Sort2 -> Sort2). F T -> (Pi A B. Instr A B -> F B -> F A) -> F S`, so appending puts `p2` where `p1`'s
nil is (`p1 ++ p2 = \F n c. p1 F (p2 F n c) c`). And a program means its continuation-passing run,
`M p R k = p (\A. A -> R) k (\A B i rest a. rest (I i a))`. Then `M (p1 ++ p2) R k` is `M p1 R (M p2 R k)` and checks by
`refl` for abstract `p1`, `p2` (about 1-2 ms). An instruction is an indexed Church sum,
`Instr A B = Pi G. (Pi A. V -> G A (V,A)) -> (Pi A. (V->V->V) -> G (V,V,A) (V,A)) -> (Pi A. (V->V->V1) -> G (V,V,A) (V1,A)) -> G A B`
(push a word, a word op, a compare), interpreted by its eliminator at `G A B = A -> B`; all of it lives in Sort3, and
nothing is postulated. With the spec stated over every continuation, `Spec(c,m) = Pi S R k s. Id(R, M (c S) R k s, k (m,s))`,
the Bin law for `c1 ++ c2 ++ [bin op]` is two transitivity steps with no congruence; each output type's law checks in
about 5-12 ms and is rejected against swapped operands. Each rule's two sides, compiled to instruction lists, proved
equal from its law (`cong` of the continuation-after-push on the law):

| n | equivalences proved | compile + spec + equivalence checks (s, all / slowest) | mean code nodes |
|---|---|---|---|
| 4 | 27 of 27 | 0.96 / 0.06 | 1390 |
| 64 | 27 of 27 | 36.3 / 2.19 | 11603 |

With the rule law replaced by `refl`, all 27 are rejected (n=4). And the code is data: run on free `F nil cons`, the
weak head normal forms of every compiled side are `cons A B i rest` down to `nil`, and each instruction on free
`G c0 c1 c2` is `c_k A payload`, so a printer walks the list without unfolding payloads. On all 54 sides at both
widths it reads back exactly the term's postfix order (rule 0's left side: `push x, push y, add, push z, sub`). A
printer that fully normalized the program instead stalled at n=64: normalizing the ripple-carry op payloads unshares
them into a tree.

*What this changes in the survey.* Option B's end state is reachable without a `W` type or new axioms: instructions
are kernel data a printer reads, template laws over them are cheap, and mined laws transfer to compiled instruction
lists at width 64. The trusted step that is left is the printer from the instruction list to WAT text (a syntactic
map), plus wasmtime. Still open: control flow and memory (control flow is tried in the next paragraph; `if` with effects, `block`/`br`, `i64.load/store`,
`call_indirect`), the wasm ops the loop lacks, and whether lowering rules can be mined over this encoding.

**Control flow over Church instruction lists, with answers in Sort0 (probe, reverted, no patch kept, 2026-10-14).**
The `select` If above runs both branches, which is wrong once a branch can loop. Real `if` needs a bit to choose
between two runs, and a bit eliminates only into Sort0. Without a primitive Bool or sum type, the option tried here
moves the answer instead: the meaning `M p N R k z` takes the answer type `R : Sort0`. One gap remains: a one-bit
word `Pi X:Sort1. (Bool0 -> X) -> X` opens only at Sort1, and the kernel has no cumulativity. It is closed by
opening the word at `Lift R = Pi Y:Sort0. (R -> Y) -> Y` (in Sort1) and projecting at `Y := R`. So
`choose w x y = w (Lift R) (\c Y g. g (c R x y)) R id`, and no kernel change is needed. Programs gain two
constructors:
- `if : Pi A. F A -> F A -> F (V1,A)`, taking a then-rest and an else-rest;
- `loop : Pi A. (F A -> F A) -> F A`, a body over its own label, where `br L` is the label used as the rest.

Instructions gain `dup`. `if` means "pop the bit, `choose` a rest". `loop` unrolls its body `N` times (`N` a
Church numeral, the fuel) and answers `z` when the fuel runs out. Specs quantify over `N` and `z`.

Results, on the same 27-rule cmp3d library:
- **Append** still composes by `refl` for abstract programs.
- **Bin laws** check in about 10-25 ms at n=4 and n=64, and are rejected against swapped operands.
- **The If law,** `Spec(c_c,m_c) -> Spec(c_t,m_t) -> Spec(c_e,m_e) -> M (c_c ++ if c_t c_e) N R k z s = choose m_c (k (m_t,s)) (k (m_e,s))`,
  checks in 14-28 ms (two transitivity steps and two congruences). It is rejected against swapped branches.
  Its right side is a case split rather than one pushed word: an If is not an operand of a later Bin law. Code after
  the If lands in `k`, so it is duplicated into both arms, as in symbolic execution.
- **Rule transfer.** For each `lt` rule, `if l then x else y` was proved equal to `if r then x else y` from the
  rule's law:
  - 24 of 24 at n=4, 1.13 s for all;
  - 24 of 24 at n=64, 27.7 s for all.

  With the law replaced by `refl`, all 24 are rejected at n=4. The same control at n=64 hit the 4 GB guard on its
  first rule, so it was not measured: rejecting the false conversion normalizes two 64-bit words.

Concrete runs were checked by `refl` against both answers:
- `loop L { dup; push 1; lt; if (exit) (push 1; sub; br L) }` from 3 gives `k(0, rest)` with fuel 4 and 50, and
  times out (`z`) with fuel 3. From 0 with fuel 1 it gives `k(0, rest)`.
- `if lt(a,b) then loop L {br L} else push 7`, with fuel 1000, gives `k(7, rest)` for `lt(1,0)` and `z` for
  `lt(0,1)`. Only the taken branch runs.
- All programs typecheck.

These concrete checks hit a reduction wall below n=48:

| n | 8 | 12 | 16 | 24 | 32 | 40 | 48, 64 |
|---|---|---|---|---|---|---|---|
| countdown from 3, fuel 4 (s) | 0.02 | 0.08 | 0.24 | 1.14 | 3.5 | 7.6 | over 4 GB within ~10 s |

The time grows about n^3.5-4 up to n=40, then memory blows up. This is the same unsharing of ripple-carry terms
that stalled the full-normalize printer. It is a limit of evaluating concrete words by kernel reduction. It is not a
limit of the laws: the laws and the rule transfer stay at n=64. (Lifted by a kernel change the same day; see
"Closed function values are reduced once" below. Countdown at n=64 now takes 15 ms.)

Machine load: 51% CPU before the rule runs and 24% after them; Defender real-time protection off.

Not tried:
- memory (`i64.load/store` as a store threaded on the stack, with load-after-store needing `eq_bv a a = true`);
- a loop law (an invariant over fuel);
- nested Ifs as operands.

*What this changes.* Control flow where only the taken branch runs, plus fuelled loops, is expressible and provable
with no kernel change and no postulate. The costs:
- answers are confined to Sort0;
- specs are observational (`k` and `z` are quantified);
- an If composes only through the continuation;
- concrete evaluation at wide widths needs sharing in reduction (or the JIT itself) rather than raw beta.

**Memory and a loop law over the same encoding (probe, reverted, no patch kept, 2026-10-14).** Memory sits outside the
operand stack, as wasm's linear memory does. It is the CPS machine's state, `Mem = V -> (V -> R) -> R` (Sort2), and
`F A = A -> Mem -> R`. Two more program constructors:
- `store : Pi A. F A -> F (V,(V,A))` pops the value, then the address, and continues with
  `upd a v mu = \b k. (eq a b) R (k v) (mu b k)`. `eq_bv` gives a Bool0, which eliminates at `R : Sort0`.
- `load : Pi A. F (V,A) -> F (V,A)` pops an address and runs `mu a (\w. rest (w,s) mu)`.

Specs now quantify over the memory: `Spec(c,m) = Pi S N R k z s mu. Id(R, M (c S) N R k z s mu, k (m,s) mu)`.

Store-to-load forwarding at a symbolic address needs only `eq a a = true`.
- **That lemma** is `Pi a. GoodBv a -> Id(Bool0, eq_bv a a, true)`. The motive is in Sort1, since `Id` lives in its
  type's universe, so it goes through `lift_good`. Per bit, `GoodBool a_i` gives `not(xor a_i a_i) = true`, and two
  congruences per bit fold the `and` chain down to `true`, so the proof is linear in n. The kernel has no eta, but
  `and(true, true)` computes to `true`.
- **The law** is `Spec(c_a,a) -> Spec(c_v,v) -> eq a a = true -> M (c_a ++ c_a ++ c_v ++ store ++ load) s mu = k (v,s) (upd a v mu)`:
  three Spec steps, a reduction, and one congruence on the `eq` premise.
- **A use:** `push a; push a; push v; store; load` for symbolic `a`, `v` with `GoodBv a`, proved from the law, the
  push specs and the lemma.
- **Concrete:** after `store 5@3; store 9@4`, a load from 3, 4 and 6 gives `k(5)`, `k(9)` and the untouched
  `mu 6 ...` by `refl`. Literal `eq` computes.

**The loop law** is fixpoint induction over fuel. Church numerals have no induction, so fuel carries a
`GoodNat N = Pi P:(Nat -> Sort2). P 0 -> (Pi j. P j -> P (S j)) -> P N` hypothesis: parametricity as a hypothesis,
the same idiom as `GoodBv`. A loop body is `Pi F. F A (label) -> F B (after) -> handlers -> F A`. With
`Good f = Pi s mu. I s -> Q (f s mu)`, for an invariant `I : A -> Sort0` and a postcondition `Q : R -> Sort0`, the law is:

`GoodNat N -> (Pi s mu. I s -> Q z) -> (Pi f. Good f -> Good (B f)) -> Good (M (loop body) N R k z)`

Its proof is one line: `gn (\m. Good (m _ B out)) hz (\j ih. hs _ ih)`. The base and step types match by conversion.
- **Instance:** `loop L { push 1; sub; br L }` times out (`= z`) for every fuel with `GoodNat`. The step discharges
  `Good (B f)` by applying `Good f` to the decremented stack.
- **At fuel 50,** the theorem with the canonical `GoodNat 50` agrees with `refl`.

Controls, all rejected:

| what | how |
|---|---|
| `eq a a = true` lemma | stated `= false` |
| forwarding law | claims the address is loaded back |
| forwarding law | `eq` premise replaced by `refl` |
| loop instance | same proof stated as "answers `k(x, mu)`" |
| concrete loads | `= k(7)` |

Check times (s), on a machine at 60% CPU from other jobs; Defender real-time protection off:

| n | eq refl | forwarding law | forwarding use | loop law | loop instance |
|---|---|---|---|---|---|
| 4 | 0.0009 | 0.020 | 0.004 | 0.013 | 0.004 |
| 16 | 0.003 | 0.022 | 0.004 | 0.013 | 0.003 |
| 32 | 0.010 | 0.025 | 0.013 | 0.015 | 0.005 |
| 64 | 0.049 | 0.083 | 0.021 | 0.020 | 0.008 |

Only the `eq` lemma grows with n; the rest stays near flat.

Not shown: an invariant across an `if`. With `Q` in Sort0, the step must case-split the condition bit at Sort0.
That should be derivable, but this is unverified: for any bit with a `GoodBool` witness, eliminate at the motive
`\b. GoodBool0 b`, which is a Sort1 type, as `lift_good` does. The witness for a compare's output bit is not built
here.

**Closed function values are reduced once (kernel change, kept, 2026-10-14).** The n=48 wall above was unsharing
in `whnf`. A word's bit is a shared node such as `s = xor_ a b`, and each use applies it to its own continuations
(`s C X Y`). The whnf memos are keyed by node, and every application is a new node, so they never hit. `beta_spine`
also peeled past `s` to the gate constant at the bottom of the spine, so `s` was never a key either. Each bit was
evaluated again once per path that reached it. `sub` chains grew about 0.7n-fold per level (n=16: 1.5, 9.9, 69 and
407 ms at depth 1-4).

The mechanism is in `src/kernel.rs`:
- `closed_prefix_spine` runs first for every `App` in `whnf_step`. It finds the longest proper prefix `P` of the
  spine with no loose variable, with `d` arguments left over.
- `hnf_rc(P, d)` is `P`'s head normal form to depth `d`: its whnf, then the body's whnf under each of up to `d`
  lambdas.
- The result is instantiated with the `d` arguments by `instantiate_n` and reduced on.
- `hnf_rc` is memoised by `(P, d)`, in the scope's `hc` table while it is on, else in the per-call
  `ReductionCache`. An application recurses on its function at depth `d + 1`, so `s` gets an entry at depth 3
  whichever prefix of `s C X Y` was asked for.
- Head reduction commutes with substitution, so this does no more reduction than the application would have done.

Check: `closed_function_values_are_reduced_once` (`src/kernel/tests.rs`). It builds
`b(i+1) = \C x y. b(i) C (b(i) C y x) (b(i) C x y)` to depth 30, both outside a scope and inside one. With
`closed_prefix_spine` disabled, depth 20 took 9.6 s for one `def_eq`, doubling per level. With it, the whole test
reports 0.00 s.

Results (machine at 15-46% CPU from other sessions, about 60% for the n=16 "before" row; Defender real-time
protection off):

| `sub^d(7) = 7-d` (`reduction_probe`, reverted) | before | after |
|---|---|---|
| n=16, d = 1, 2, 3, 4 | 1.5, 9.9, 69, 407 ms | 0.57, 0.27, 0.31, 0.38 ms |
| n=64, d = 1, 2, 3 | 17.5, 818 ms, over 4 GB | 1.7, 1.5, 1.6 ms (d = 4-6: 1.8-2.2 ms) |

| countdown from 3, fuel 4 (`control_flow_probe`, reverted) | n=16 | 32 | 48 | 64 |
|---|---|---|---|---|
| before (table above) | 0.24 s | 3.5 s | over 4 GB | over 4 GB |
| after | 2.7 ms | 8.0 ms | 9.2 ms | 14.8 ms |

Every concrete answer and every control in that probe came out as expected at n = 16, 32, 48 and 64. Rule transfer
on a regenerated 27-rule cmp3d ref library came out as before:
- 24 of 24 at n=4 in 0.84 s;
- 24 of 24 at n=64 in 30.6 s (27.7 s before, under other load; not an A/B);
- the NEG control 0 of 24 at n=4.

The NEG control at n=64 still went over 4 GB. Its words are symbolic: the bits are variables bound under the
probe's binders, so no prefix is closed.

`proof_cost_split` (cmp3d, 37-rule own library, 300 laws, `cpu_ab.ps1`, own CPU, 10 alternating pairs against
85daf95):
- new won all 10 pairs; best 4.19 against 5.16 s; median pair -1.15 s;
- summed rule-proof build time 27.9 against 40.6 s, and kernel check 6.5 against 6.0 s;
- an earlier build without the stuck-spine shortcut won 8 of 8 pairs;
- law counts, node counts and occurrences identical;
- peak working set about 654 against 607 MB.

`loop_stream` (ref, cmp3d) wrote identical rules, laws and `m.tsv`. The kernel lib tests (366) and church_bv's
tests (75) pass.

Tried and dropped: keying every prefix, open ones too, behind a throwaway switch. It was slower everywhere:
countdown at n=64 took 155-194 ms, and rule transfer at n=64 took 51.8 s. The n=64 NEG control still went over
4 GB. So that wall is not this unsharing (it is traced below, "The NEG control's wall was the error message").
`cpu_ab.ps1` reads `cmp3d_own_rules.txt` next to itself, and that file had never been committed. Salt 1's
`own_cmp3d_3_cmp3d/rules.txt` from the `cts_*` sweep was used for this run. That is 37 rules with no `winner  OVER
loser` preference lines, and every 2026-10-13 sweep (`sls`, `uss`, `sms`, `whs`, `cts`) wrote the same file. It is
now committed as `docs/runs/2026-10-12/scripts/cmp3d_own_rules.txt`. The older file that earlier rows used also
carried preference lines (the 2026-10-14 width probes above dropped them with `grep -v OVER`). `check_laws` reads
those preferences, so absolute times before this row may not match runs on the committed file. A/B pairs within
one run are unaffected.

Related, from memory and not re-checked: this is full laziness (sharing maximal free expressions, as in
Peyton Jones's "The Implementation of Functional Programming Languages", 1987) applied to the spine prefixes the
reducer meets, rather than by lambda lifting ahead of time. Rocq's `Zupdate` (section 77 of `RELATED_WORK.md`)
shares an evaluated closure in a similar way.

**The NEG control's wall was the error message (kernel change, kept, 2026-10-14).** With the law replaced by
`refl`, `def_eq` rejects the two `lt` circuits quickly. What blew up was `check_rc`'s `type mismatch` message. It
printed `brief(&nf(inferred))` and `brief(&nf(expected))`, so it built two whole normal forms of 64-bit symbolic
circuits and then printed 400 characters of each.

How it was found:
- Rule 21 (`lt(add(x, y), sub(shl1(y, 0), z))`) was the slowest rule alone. It grew about n^3 in time and memory:
  0.05, 0.29, 1.03, 2.83 and 11.6 s, with peaks of 70, 133, 293, 639 and 2142 MB, at n = 8, 16, 24, 32 and 48.
  The positive check (the real law) took 0.9 s and 242 MB at n=48.
- A samply profile at n=32 put 81% of busy samples under `nf_rc`. Most stacks lost their callers past `grow`'s
  stack segments, and `conv` calls no `nf`. The only `nf` caller on this path is the message.
- Printing the raw terms instead brought rule 21 to 16 ms (n=32) and 19 ms (n=64), with peaks under 70 MB.

The fix is `brief_nf(e)`, a printer that normalizes as it prints:
- `Debug for Expr`'s single `match` became `write_expr`, generic over how children are printed.
- `brief_nf` whnfs each node through one `ReductionCache` when the printer reaches it.
- `brief`'s character limit stops the writer, so only the printed prefix is ever reduced.
- The text is the same as `brief(&nf(e))`. The wrec children-type message uses it too. The other `nf` callers
  are semantic (`infer_sup`'s occurs check, `typecheck`'s returned type, `normalize`) and stay as they were.

Check: `brief_nf_normalizes_only_what_it_prints` (`src/kernel/tests.rs`). It compares the output with
`brief(&nf(..))` on three small terms, and prints the Church numeral `16 4`, whose normal form has 4^16 nested
applications. With `brief(&nf(e))` restored, the test went over 4 GB within 8 s.

After the fix, `control_flow_probe` on the 27-rule cmp3d ref library (machine at 14% CPU; Defender real-time
protection off):

| | n=4 | n=24 | n=64 |
|---|---|---|---|
| NEG control, 24 rules | 0/24, 0.32 s | 0/24, 0.42 s (24.6 s before) | 0/24, 0.58 s, peak 585 MB (over 4 GB before) |
| rule transfer, 24 rules | 24/24, 0.75 s | | 24/24, 26.5 s, peak 2.2 GB |

Rejecting is now about 45 times cheaper than accepting at n=64.

*The accepting side is the rule laws, not the transfer.* A probe (reverted, no patch kept) timed each rule's
phases. It used the committed 37-rule `cmp3d_own_rules.txt` (32 `lt` rules) rather than the ref library above,
with the machine at about 20% CPU and Defender real-time protection off. At n=64:

| | 32 rules, sum of checks |
|---|---|
| program proof with the rule law inlined (as above) | 46.9 s |
| the same proof with the law as a hypothesis of its type | 0.38 s |
| the laws checked alone | 43.8 s (32 of 32 hold) |

Proving the law (`prove_rule`) takes 0.03-1.6 s per rule, and building the program proof takes about 0.02 s. The
inlined law is 86-95% of each proof's unique nodes (rule 0 at n=64: 51,784 of 60,292). Unique nodes grow about
linearly in n (rule 0: 9,958 at n=8, 31,531 at n=32), but checking the inlined proof slows faster (rule 0: 33 ms at n=8,
0.24 s at n=32, 0.64 s at n=64). A samply profile of the inlined run at n=64 (profile not kept) puts it in type
inference: `check_rc` and `infer_rc` cover nearly all samples, `expect_pi` 13%, and `InferCache` rehashing 11%.
Freeing hash tables of per-call `ReductionCache`s (under `whnf` and `def_eq`) and `InferCache`s costs about 8%; which maps fill them was not checked.

So the transfer to compiled programs costs about as much as rejecting it: 0.86 s for 32 rules with the law as a
hypothesis (0.38 s of it checking), against the NEG control's 0.58 s for 24. The remaining cost is
checking each law, a cost per rule rather than per program. The mechanism for paying it once already exists and the
miner uses it: `shared_lemma` checks a law's proof once and returns a parameter whose type is the law's statement.
A proof that uses the law mentions the parameter, and the checker only looks up its type (`Plan::Law` with
`LawKind::Rule` goes through it). The probe called `prove_rule` directly and inlined the proof, so it paid for the
law in every check; its "law as a hypothesis" row is what `shared_lemma` gives. Every `Plan::Law` kind now goes
through it (see "Every law by name" below).

*Why checking a law slowed faster than it grew.* `infer_rc`'s memo missed about 20 times per node: rule 0 at n=64
had 1,036,365 misses for a 51,784-node proof, counted with a probe (reverted, no patch kept). There were two causes:
- The key (node, window of the innermost binders down to the node's highest loose variable) fell back to the whole
  context past `MAX_WINDOW` = 8 binders. A rule law nests about 6n per-bit binders (`k_var_law`), so 99.96% of
  misses were fallbacks. Removing the cap alone left 1,035,100 misses.
- `trans_proof`, `sym` and `cong1` (`postulates.rs`) build a J motive per use. Shared subterms of its endpoints then
  sit under that use's binders, which they never mention, so the window differs per use. The most-missed nodes were
  missed about 18n times each.

Fix: the window now starts at the node's lowest loose variable `lo`. The `lo` innermost binders are never looked up,
and the type mentions only positions at or above `lo`, so the answer is the same in any context that agrees above
`lo`. The key is (node, `lo`, window from the `lo`-th binder up), with no cap. Rule 0 at n=64 now has 59,195 misses
(about 1.1 per node), and every counter grows linearly in n. Check: `infer_memo_skips_unused_inner_binders`, where a shared
node sits under 30 nested binders, each with two types it never mentions. It passes in 0.29 s; before the fix it ran for
over a minute and then aborted on a 35 GB allocation. The laws checked alone (the probe above, three alternating pairs, machine
at about 11% CPU, Defender real-time protection off):

| | n=8 | n=16 | n=32 | n=64 |
|---|---|---|---|---|
| rule 0, before | 25 ms | 57 ms | 0.21 s | 0.71 s |
| rule 0, after | 23 ms | 54 ms | 0.11 s | 0.24 s |
| rule 33, before | 0.13 s | 0.37 s | 1.13 s | 3.9 s |
| rule 33, after | 0.10 s | 0.24 s | 0.54 s | 1.22 s |

Middle values of three. Time still grows 2.2-2.3 times per doubling of n, against linear unique nodes and misses,
so something outside the memo is still superlinear. On `proof_cost_split`, whose widths are
small, the change is neutral: 6 alternating `cpu_ab.ps1` pairs, median CPU 4.86 s before and 4.85 s after.

*What is still superlinear.* A samply profile of rule 33's law at n=64 (8 checks in one process, profile not kept;
machine at about 15% CPU, Defender real-time protection off) puts 18.8% of samples in `hc::lowest_loose`
(the memo key's `lo`) and 16% in `hc::uses` (called from `inst_rec`), with `hc::intern` at 10.5% and `infer_rc` at 8.1%. The first check
takes 1.25 s and each repeat about 0.49 s, since the node table's memos persist within the scope. Counted with a probe
(reverted, no patch kept), over n = 8, 16, 32, 64:
- `lowest_loose`'s (node, depth) memo entries per check grow linearly: 120k, 234k, 462k, 926k.
- `uses` walks (slot misses) grow 3.6-3.9 times per doubling from n=16: 1.16M, 1.13M, 4.06M, 15.3M on the first check, and
  0.16M, 0.59M, 2.28M, 8.95M on a repeat.

`uses(x, d, m)` is `lowest_loose(x, d) < m`, so the two can share one mechanism. A prototype (reverted, no patch kept) did that:
the node header's slot held (d, lowest loose variable) and replaced both the (d, m) slot and `InferCache`'s `lows` map.
It made repeats faster (0.43 to 0.25 s at n=64) but the first check slower (1.41 to 1.68 s, 64M walks). The single slot
thrashes between the memo key's depth-0 queries and `inst_rec`'s other depths, and repeat walks stayed at about 9M. Those
walks follow `inst_rec`'s own work, which is keyed by (node, depth): instantiating a shared node at each depth it occurs
under is the quadratic part, not the cache in front of it. A key that doesn't depend on depth (each node's set of loose
variables, computed once) would answer both queries without walking.

Two prototypes followed, both in a throwaway worktree; the second has since landed (below). Both were
timed with the probe above against 75e9ece, alternating runs, machine at 12-14% CPU, Defender real-time protection off.
- *Loose-variable bitsets, negative.* The node table mapped each node to a bitset of its loose variables, built once
  from its children. `uses` and `lowest_loose` became bit scans while the table is on. Repeat checks got faster (rule 33
  at n=64: 0.40 to 0.30 s) but first checks did not (1.17-1.27 to 1.30-1.34 s), and the process's CPU rose from 5.0 to
  5.3 s. The `uses` walks were not what made the first check slow.
- *Inferring an application spine at once, positive.* A samply profile of the first check alone (rule 33, n=64) has
  `hc::intern` at 17.4%, `inst_rec` at 17.2%, `uses` at 10.4%, the scope's drop at 10.3% and `shift_child` at 8.1%,
  with `infer_rc` at about 3%: instantiation, not inference. (Stacks are cut at `stacker::grow`, so callers above it
  can't be attributed.) `infer` typed `App(f, a)` as `subst_top(cod, a)`, so a spine `f a1 .. ak` copied the rest of
  `f`'s telescope once per argument. The prototype walks the spine, instantiates each domain with the arguments before
  it, and instantiates the codomain once with all of them (`instantiate_n`). If a codomain is not syntactically a Pi,
  it first instantiates the pending arguments and takes its weak head normal form. Results:
  - Rule 33 at n=64, first check: 1.39-1.41 to 0.78-0.87 s; rule 0 at n=64: 0.25-0.28 to 0.14-0.17 s.
  - The probe process's CPU: 5.7 to 4.1-4.3 s.
  - `proof_cost_split`: 6 of 6 alternating pairs won, check 500-570 to 339-385 ms, median CPU 4.16 to 3.95 s.
  - Kernel (368) and church_bv (75) tests pass.

  Rule 33's first check still grows about 2.3 times from n=32 to 64.

  Landed as the prototype was, in `infer_node`'s `App` case; the per-argument path is gone. Check:
  `infer_types_an_application_spine_at_once`, `f a .. a` with 1,000 arguments against a telescope whose codomain
  mentions every binder. It takes under 5 ms, against 0.64 s in release and 4.6 s in debug with the per-argument path.

*After the spine change.* The laws checked alone (one run, machine at about 5% CPU, real-time protection off), first check / repeat:

| | n=8 | n=16 | n=32 | n=64 |
|---|---|---|---|---|
| rule 0 | 20 / 11 ms | 24 / 15 ms | 60 / 35 ms | 187 / 101 ms |
| rule 33 | 76 / 33 ms | 169 / 77 ms | 408 / 191 ms | 875 / 400 ms |

Rule 33 still grows 2.1-2.4 times per doubling. A samply profile of its first check at n=64 (profile not kept) is still
mostly instantiation:

| self time | |
|---|---|
| `inst_rec` | 19.3% |
| `hc::intern` | 15.3% |
| the scope's drop | 12.7% |
| `lowest_loose` | 7.9% |
| `uses` | 4.9% |
| `shift_child` | 4.8% |
| `infer_rc` | 2.2% |
| `prove_rule` (building the law, inclusive) | 11.8% |

46% of samples are under `instantiate_n`, and the callers above it are attributable this time. Nearly all of it is reduction, not typing:
`hnf_rc` 21.5% (15.5% from itself), `closed_prefix_spine` 13.6% and `beta_spine` 6.6%, all under `whnf_step`, against
2.9% from `infer_node`. What is left is conversion evaluating the law's Church-encoded circuits (the closed-function
head normal forms of e7d4347), and freeing what that allocates.

*The work is linear; each operation slows.* A probe (reverted, no patch kept) counted, for one law check in a fresh scope, the node table's new entries and its lookups:

| rule 33 | n=8 | n=16 | n=32 | n=64 |
|---|---|---|---|---|
| check | 56 ms | 132 ms | 351 ms | 807 ms |
| new interned nodes | 41,761 | 90,191 | 178,111 | 353,951 |
| new instantiation / shift / whnf / hnf entries (thousands) | 40 / 38 / 5.8 / 0.13 | 78 / 76 / 12 / 0.15 | 155 / 151 / 24 / 0.15 | 308 / 300 / 47 / 0.15 |
| `intern` calls | 113,370 | 225,114 | 446,314 | 888,714 |
| `inst_rec` calls | 61,104 | 120,930 | 239,138 | 475,554 |
| `instantiate_n` memo lookups | 60,792 | 120,057 | 238,041 | 474,009 |

Rule 0 is the same: everything doubles per doubling of n. Head normal forms are a fixed 153 (rule 33) and 52 (rule 0).
So the distinct reduction results and the lookups grow linearly, and what grows faster is the time per operation:
about 0.5 µs per `intern` call at n=8 and 0.9 µs at n=64, for both rules. Part of that is the `uses` walks, which grow
3.6-3.9 times per doubling (measured before the spine change) and are 5% of samples at n=64 (13% with `lowest_loose`). The rest is presumably
memory: at n=64 the tables hold over a million entries, well past the 16 MB L3.

*The scope's drop.* Timed in the same probe: freeing the table after rule 33's check takes 14, 40 and 83 ms at n = 16,
32, 64 (about 10% of the check, linear, about 80 ns per entry). At n=8 it took 212 ms, because that scope also held
the 1.19M nodes `prove_rule` built first. Rule 0 takes 2-14 ms. It is a linear cost, so it does not explain the growth. Options, none tried:
- *Keep the table across checks.* No drop per check, and repeats hit its memos: a repeat check of rule 33 at n=64 takes 0.40 s against 0.88 s for the first. Memory grows with every check, so it needs a bound and an eviction rule.
- *Allocate a scope's nodes in an arena and free them in bulk.* This needs every node that outlives the scope to be copied out, a larger change to `Rc`.
- *Free on another thread.* Not possible as is: the kernel's `Rc` is not `Send`.

*Where the miner's drops fall* (read from `search.rs`, not timed). The table and its depth are thread-local
(`hc::TABLE`, `hc::DEPTH`), so a scope on the main thread does not cover a worker thread: each worker's first scope
is outermost there, and dropping it frees that worker's table.
- `proof_cost_split` is single-threaded inside one `scoped` call, so its checks already share one table and it drops once per run. It is the "keep the table" option already, without a bound.
- `rule_miner`'s main-thread scope covers only main-thread work. Its proofs and scores run on workers, each with its own table:
  - eager proving: one scope per worker per batch of candidates;
  - scoring: one per worker per round;
  - each round's winner (`prove_any`): one thread and one scope per rule, so one table and one drop per rule proof.

  The winner's proof runs beside the main thread's search, so its drop is off the main path but still uses a core.
- Separately, under the driver (`LEMMA_CACHE=<file>`, set by `driver::run_loop`), `shared_lemma` reads statements that an earlier process of the same build recorded, so a loop's later processes skip those checks (unless `LEMMA_RECHECK=1`).

So keeping a table across checks would change only `rule_miner`'s per-rule threads, and those would need a long-lived prover thread to hold it.

*Every law by name.* `Plan::Law` now checks every kind once through `shared_lemma`: `Bitwise`, `Chain` and `Tree`
as well as `Rule`, `Assoc` and `Comm`. All use one key, (prover, both sides, n, k). On `proof_cost_split` the non-rule
laws are 280 assoc, 272 comm and 163 tree uses, with 6 distinct tree statements and no `Bitwise` or `Chain`. The checked
proofs shrink: the rewriter's 296 laws go from 327,190 to 200,994 nodes (check 191 to 107 ms), and the machine proofs
from 23,146 to 4,152 nodes (46 to 3.3 ms). Each law's one check now runs during build, so total CPU is neutral: 6
alternating `cpu_ab.ps1` pairs, median 5.06 s before and 5.10 s after, machine at about 11% CPU, real-time protection off.

The "printer stall" seen earlier with full-normalizing printers has the same cause as the NEG wall, and it can't be fixed in the
printer. A probe (reverted, no patch kept) normalized `add`, `sub` and `lt` on two free words and counted unique
nodes against occurrences:

| n | 8 | 10 | 16 | 32 | 64 |
|---|---|---|---|---|---|
| `add` without interning: unique nodes, time | 518k, 0.31 s | 8.4M, 6.7 s | over 6.5 GB at n=12 | | |
| `add` in an `InternScope`: unique nodes, time | 527, 0.5 ms | 813, 0.7 ms | 2,055, 3.4 ms | 8,183, 11 ms | 32,727, 58 ms |
| occurrences (both) | 5.2e5 | 8.4e6 | 3.4e10 | 1.5e20 | 3.4e38 |

`sub` behaves like `add` (about 2 times slower in a scope); `lt` has 976 unique nodes at n=64. Without interning,
`nf` builds the tree: about 16 times larger for every 2 more bits. Interned, the normal form is a DAG of about
8n² nodes, so `nf` itself is cheap. Any printer that walks the term still visits every occurrence, so printing it in
full is infeasible either way. Printers have to stop early, as `brief_nf` does, or print the DAG with shared nodes
named.

*Table size alone.* Hardware cache-miss counters are not available to a session here: AMD uProf is not installed, and
xperf's PMC sources need an elevated kernel trace. Instead, a probe (reverted, no patch kept) checked a law at
n=8 twice: in a fresh scope, and in a scope that had just built and checked the n=64 law. For rule 33 the n=64 work left 507k
nodes, 306k instantiations and 327k shifts in the table. The n=8 check makes about 154k new entries in a fresh scope, counting
the input that `check_in` interns, and 147k after n=64, which shares a few nodes with it. The filled check does slightly less
work, so its extra time comes from the size of the table and heap. Three
rounds per rule, Defender real-time protection off, machine at 4-6% CPU, pinned to 12 cores at below-normal priority:

| µs per new table entry | n=8, fresh scope | n=8, after n=64 | n=64, fresh scope |
|---|---|---|---|
| rule 33 | 0.33-0.39 (51-61 ms) | 0.45-0.54 (66-79 ms) | 0.57-0.71 |
| rule 0 | 0.20-0.42 (8-17 ms) | 0.36-0.46 (14-17 ms) | 0.44-0.59 |

The large table alone makes each entry 1.3-1.5 times slower. That accounts for about 40% of rule 33's rise from
n=8 to n=64, and most of rule 0's. Rule 0's times are small and noisy, and its fill (127k nodes) is a quarter of rule 33's.
It is an upper bound: the filled n=8 check runs against the table at the size the n=64 check reaches only at its end.
This shows that size slows each entry. It does not show which mechanism does it: cache misses on the table and the nodes,
longer probe sequences, or a scattered heap all fit.

*What else grows per entry.* The node table's key is fixed in size (constructor, leaf, up to five child pointers), and so
are the instantiation, shift, whnf and hnf keys. Hashing and comparing a node therefore cost the same at every n; wider
terms do not make them dearer. A second probe (reverted, no patch kept) counted the per-entry work of one law check in a
fresh scope (same machine state: Defender real-time protection off, 4-5% CPU, pinned, below normal):

| per new table entry, rule 33 | n=8 | n=16 | n=32 | n=64 |
|---|---|---|---|---|
| µs | 0.38 | 0.55 | 0.65 | 0.61 |
| `intern` calls | 0.92 | 0.88 | 0.88 | 0.92 |
| `inst_rec` calls (mean depth) | 0.40 (2) | 0.47 (2) | 0.47 (2) | 0.40 (3) |
| argument-set lookups (mean length) | 0.038 (6.1) | 0.044 (6.2) | 0.044 (6.2) | 0.038 (6.2) |
| `lowest_loose` nodes walked | 0.78 | 0.91 | 0.91 | 0.78 |
| `uses` calls past the cheap exits | 1.95 | 3.85 | 6.81 | 10.75 |
| `uses` nodes walked (header-slot misses) | 1.14 | 2.50 | 4.71 | 7.73 |

Rule 0 is the same: everything is flat except `uses`, at 0.63 nodes walked per entry at n=8 and 4.14 at n=64. Stack-segment
switches are 1 per check at every n. So the only work per entry that grows with n is the `uses` walks: they grow about
linearly per entry, and so quadratically in total. Each node's header slot keeps one (d, m) answer, and a node gets asked
at more (d, m) pairs as n grows. Both earlier fixes for `uses` were negative: a one-slot (d, lowest loose) header cache
and per-node loose-variable bitsets (see "What is still superlinear").

*The rise, priced by a profile diff.* Two samply profiles on c19808a (profiles not kept) recorded the same law check
repeated in fresh scopes: 120 checks at n=8 and 10 at n=64, each after one warm-up check. Each run printed wall-clock
marks around its repeated checks; `scripts/prof_diff.py` keeps only the samples between the marks and divides each
function's self time by the new table entries (154,275 and 1,185,460 per check). Busy time per entry was 240 ns at n=8
and 491 ns at n=64. The rise of 251 ns:

| self ns per entry | n=8 | n=64 | rise |
|---|---|---|---|
| `TABLE.with` bodies (the inlined node-table and memo probes) | 57 | 123 | +66 |
| `hc::uses` and its closure | 15 | 75 | +61 |
| `hc::lowest_loose` | 29 | 72 | +43 |
| `reserve_rehash` (table growth) | 19 | 29 | +10 |
| `infer_rc` | 11 | 21 | +10 |
| everything else, each +5 or less | | | +61 |

The earlier guess priced `uses` at about 0.03 µs from a profile taken before the spine change; it is 0.06 µs now.
`lowest_loose` rises without doing more: a third probe (reverted, no patch kept) counted 1.32 memo lookups per entry
at n=8 and 1.37 at n=64, and the walks are flat (above). What grows is its memo (`InferCache::lows`, one per check):
66k entries on average at a lookup at n=8, 515k at n=64. That is the table-size effect again, in a map the fill
probe above did not fill (its memo is per check). So the rise splits about evenly:
- **Size:** larger maps, with the same lookups per entry, cost about 120 ns: the node table and memos, `lows`, and rehashing.
- **More work:** the `uses` walks cost about 60 ns.
- **Spread out:** about 60 ns is spread thinly across the rest.

*Why `lowest_loose` cannot move into the node header* (reasoned, not prototyped). A node's lowest loose variable is
not a function of its children's. Take `Lam(A, body)` where `body` mentions `Var 0` and `Var 5`. The body's lowest
loose variable is 0, the one the `Lam` binds, and the `Lam`'s own lowest loose variable, 4, comes from the body's
second-lowest. A node needs each child's answer at every depth: the (node, depth) key of `lows`. The smallest summary
that composes is the whole set of loose variables, which was the bitset prototype (negative, "What is still
superlinear"). So the `lows` memo can only get cheaper per lookup, not go away.

*The rise after the bounds memo (2026-10-14).* The same two profiles, repeated on ded1a96 plus the probe (reverted, no patch kept; profiles not kept). Load was 33–36% from other work throughout, and both runs ran back to back. Absolute times are inflated: 526 ns busy per entry at n=8 against 240 above, and 83 against about 45 ms per check unprofiled. So only the rise within this pair is compared, still divided by the entry counts above. Busy time per entry was 526 ns at n=8 and 689 ns at n=64, a rise of 163 ns (251 before). By first non-std frame:

| self ns per entry | n=8 | n=64 | rise |
|---|---|---|---|
| `hc::intern` (node-table probes) | 77 | 114 | +37 |
| `hc::lowest_loose` (`InferCache::lows`) | 94 | 126 | +31 |
| `shift_child` | 47 | 63 | +17 |
| `infer_rc` | 24 | 40 | +16 |
| `hc::canon` | 22 | 34 | +12 |
| `hc::uses` and its closures | 15 | 26 | +11 |
| `height_at_most` | 9 | 15 | +6 |
| everything else, each +4 or less | | | +33 |

- **`uses`' share of the rise fell from about 24% (+61 ns) to about 7% (+11 ns).**
- **What is left is mostly size:** probes into the node table (`intern`, `canon`) and the per-check `lows` map, with `shift_child` and `infer_rc` behind them. These are what Stage 2 of the id arena targets.
- **`lowest_loose` is now the largest single cost at n=8 as well (94 ns per entry).** The `lows` memo needs exact minima, so the bounds memo cannot answer it.

*What `lows` does per call (probe on 77fe8a9, reverted, no patch kept, 2026-10-14).* Counters for one fresh-scope check of rule 33's law, after a warm-up check:

| n | `memo_context` calls | `lowest_loose` calls | gets at d=0 (hit) | gets at d>0 (hit) | `lows` size at the end |
|---|---|---|---|---|---|
| 8 | 36,732 | 289,570 | 60,634 (62%) | 143,552 (32%) | 120,475 |
| 64 | 280,948 | 2,228,402 | 478,898 (64%) | 1,140,324 (34%) | 926,455 |

- **The work per call is flat in n:** 7.9 `lowest_loose` calls and 5.6-5.8 memo gets per `memo_context` call at every width, with 41-43% of gets hitting.
- **Every miss stays in the map**, so it ends near one entry per new table node (926k against 1.19M at n=64). That is over 20 MB, past the L3, so the rise is the per-probe cost of a growing map, as for the node table.
- **Skipping the memo for small nodes (`hc::low`, height at most 2, as the instantiation memo does) removes almost nothing:** gets fall 0.4-0.5% and the map 0.7%. The memoised nodes are large, so it was not timed.
- **Left:** no `lows` lookup can be skipped, so only cheaper probes help.
  - Under the id arena, the d=0 entries (30% of gets, 64% hit) could live in a dense side array indexed by node id, with no probe at all.
  - Sharing the `uses` bounds table was the "shared memo" variant above, which did not help.

**Allocation schemes against the size cost (survey, 2026-10-14).** The size cost is about 120 ns per table entry at
n=64 (profile diff above): node-table and memo probes (a hit reads the candidate node at a random address), the
`lows` memo, and rehashing. Today a node is one mimalloc block of 80 bytes: `std::rc::Rc`'s two counts (16), the
header (`loose`, `free`, `generation`, `uses`: 16) and `Expr` (48; `size_of` checks in `kernel/tests.rs`). mimalloc is
v3 (`libmimalloc-sys` 0.1.49), the global allocator of every binary. `RELATED_WORK.md` §64 surveyed node
representations for linearity ("Allocation"), and "A per-scope arena for the table's nodes" above ruled out a
bulk-freed arena of `Rc` nodes, because 16% of a scope's nodes outlive it. The schemes:

1. *Large OS pages (measured, positive).* mimalloc maps its arenas in 2 MB pages when `MIMALLOC_ALLOW_LARGE_OS_PAGES=1`,
   which needs the account's "Lock pages in memory" privilege. This account holds it (disabled until a process enables
   it, which mimalloc does). With it set, mimalloc reserved 1 GiB of large pages at start (`MIMALLOC_VERBOSE=1`). Fewer TLB
   misses on the same random accesses, presumably (no counters measured it). A probe (reverted, no patch kept) timed rule 33's law in fresh scopes, three
   alternating pairs. At n=64 large pages won 3 of 3, median 483-489 → 433-436 ms (-10%, about 42 ns per entry). At
   n=8: no change (medians 32-36 ms). On `proof_cost_split` (`scripts/cpu_ab.ps1`, 6 pairs) they won 6 of 6: CPU 3.02-3.20
   → 2.69-2.75 s (-12%), build 1.80-1.92 → 1.56-1.62 s, check 256-283 → 227-240 ms. Defender RTP off, load 2-8%.
   **Adopted (2026-10-14).** `.cargo/config.toml` compiles mimalloc's defaults in: large pages and a 64 MiB
   `arena_reserve`. `mi_option_set` from `main` would be too late, because mimalloc reads its options and enables the
   privilege when the process loads. `MIMALLOC_ALLOW_LARGE_OS_PAGES=0` turns them off for one run. The test
   `machine::mimalloc_defaults_to_large_pages` fails if the define stops reaching mimalloc (checked by building
   without the config). Every timing's machine-state line now ends `lockpriv=… pages=large|normal`. **Every timing in
   this file before this entry is on normal pages; later ones are on large pages unless they say otherwise.**
   - *The reservation's size* (`scripts/cpu_arms.ps1`, `proof_cost_split`, 6 rotating rounds, load 7-18%, RTP off).

     | Arm | CPU (s) | Peak private (MB) |
     |---|---|---|
     | normal pages | 3.66-4.80 | about 700 |
     | 1 GiB | 3.30-3.92 | 1090 |
     | 256 MiB | 3.22-3.72 | 1090 |
     | 64 MiB | 3.22-4.14 | 898 |

     The size makes no measurable difference to CPU, so the smallest was kept, since it locks the least.
   - *A full sweep* (`SALT=1`, `mines own cold pooled`, 178 processes, measured as one job object: the job's CPU and
     its largest process's peak commit). Five rotating rounds; the outputs are identical apart from the seconds columns.
     - At load 10-36% (rounds 3-5), large pages won 3 of 3: job CPU 53.1-56.2 s against 55.0-58.6 s, about 4%.
     - At load 20-69% (rounds 1-2), they lost 2 of 2: 61.0-61.7 s against 55.3-61.3 s.
     - The gain is smaller than `proof_cost_split`'s 12% because most of the sweep's processes are short.
     - Memory: the largest process peaks at 578 MB against 413-419 MB (+40%), and the whole job at 769-834 MB against 498-506 MB.
       Presumably because Windows commits large pages when they are reserved and cannot decommit them.
   - Risks: large pages are locked, never paged out. Each process locks what it reserves, so parallel sweeps each lock
     their own, out of the machine's 62 GB. Without the privilege mimalloc falls back to normal pages, so a machine
     without it times differently.
2. *A node in 64 bytes (unmeasured).* mimalloc's size classes step 64 → 80, so dropping only the unused weak count
   (an own `Rc`, as `triomphe`) leaves 72 bytes in the 80-byte class and saves nothing. Reaching 64 also needs 8 bytes
   off the header, e.g. 16-bit `loose`/`free` (saturating; rule laws nest about 6n binders, 384 at n=64). 20% less node
   memory, so fewer misses on node reads, at the cost of hand-written `unsafe` refcounting in the trusted kernel.
3. *A per-scope mimalloc heap for interned nodes (unmeasured).* `mi_heap_new` gives the scope's nodes their own pages,
   not interleaved with `Vec` buffers and memo arrays. The toolchain is nightly, so `Rc::new_in` with a zero-sized
   allocator that reads a thread-local heap is possible. Only locality is gained: `mi_heap_destroy` (free without
   walking) is unsound while 16% of nodes escape, so the heap would have to be released with `mi_heap_delete`, which
   keeps live blocks. mimalloc already places same-size blocks contiguously in a page, so the gain may be small.
4. *A two-space arena of 32-bit ids, hash-consed (nanoda_lib's design, §64).* The end-state design: `Expr` children are
   4-byte ids (a node about 40 bytes, no counts), equality is an id compare, ids are the memo keys (`lows` entries 12
   bytes instead of 24, node-table entries 8-12 instead of 16), allocation is sequential, and a scope frees in bulk.
   The 16% that escape a scope are copied into the persistent space when it ends, remapping their ids. Costs, from §64:
   every constructor and pattern goes through a context across the kernel and `proof.rs`; garbage stays until the
   scope ends; an id used with the wrong space names another term. It addresses the whole size cost (smaller maps,
   smaller nodes, and the scope's drop) and is the only scheme here that does.
5. *Rejected before, still rejected.* A bump arena with `&'a Expr<'a>` children (lifetimes through every proof record
   and the JIT, §64). A tracing GC (slower than `Rc` in Rust, no cycles to collect, §64). An `Rc` arena freed in bulk
   (escaping nodes, above). Freeing on another thread (`Rc` is not `Send`).
6. *Adjacent, not allocation.* Reserving the maps' capacity ahead (rehashing is about 10 ns per entry at n=64) needs a
   size estimate per check. Reordering nodes for locality does not apply: hash-consing shares a node among many parents,
   so there is no one order to put it near.

Ranking by end state: 4, then 1, which presumably stays useful under 4 (its maps and nodes would still exceed the TLB's reach at large
n), then 2 and 3. Only 1 is measured; it is additive and leaves no rework.

*Against the directions in this file (reasoned, not measured).* Scheme 4 gains under most of them:
- **Proofs about the target at n=64** (option B of "Formalizing the target machine") run where the size cost dominates.
- **Compiled transformations** can read ids, as indices into linear memory, where they cannot read `Rc` pointers.
- **The two spaces match the tiers:** the per-check region is working memory, the persistent space long-term memory, and ids are stable keys for proved statements (today `lemma_cache` keys by printed strings).
- **Parallel checking** could share a frozen persistent space read-only across threads, which `Rc` (not `Send`) cannot.

Its shortcomings there, with mitigations:
- **The persistent space only grows** (nanoda never reclaims it), and a cycle keeps what it learns: rules, lemmas, statements. Mitigation: a major collection at quiescent points, between rounds. The roots are explicit and few (the rule library, the lemma statements, whatever caches are kept), so copying the live set into a fresh space costs what is live, not what was built. Rebuildable memos are dropped, not copied. The cheapest form exists already: the driver runs each loop's work in separate processes, with long-term memory in files (`LEMMA_CACHE`, rule files), so a process boundary is a major collection.
- **An id used with the wrong space names another term.** Mitigation: two id types, a generation-checked handle (`Expr`) and a persistent id (`PExpr`), with a copy-out function (`persist`) the only way from one to the other. Two ids alone do not make returning a region id fail to compile, since neither carries a lifetime. What does: `scoped(|| ..)`, whose result must implement an `Escape` trait, and which copies the result out when it opened the region. A dead handle panics on every read, in release builds too; it never names another term. Branded lifetimes would also catch stores, but were rejected for spreading (§64). Specified in the id-arena spec (`docs/superpowers/specs/2026-10-14-id-arena-spec.md`, local).
- **Every constructor and pattern through a context** (§64's main cost). Mitigation: the current space is thread-local, as `hc::TABLE` is now, so constructors take no context parameter. A node of id children (24 bytes as an enum, plus 12 in side arrays) is `Copy`, so a pattern matches a copy (`match id.node()`) and needs no borrow from the arena.

*The id-arena spec (draft 3, 2026-10-14, 5 review rounds).* Its decisions:
- **Copy-out is eager**, with a twin map. A persisted node reads as its region twin until the region closes, so equality stays an id compare and a `PExpr`'s hash never changes.
- **One interning rule:** a node over persistent children looks in the persistent space first.
- **The checking entries are `scoped`**, so a check outside a region frees its transients.
- **Returns are checked by `scoped` with `Escape`** at compile time (D1, decided 2026-10-14); stores by the generation check on handle reads.
- **Stage 1, built first (decided 2026-10-14), is a trace replay** of rule 33's table and memo traffic in three layouts: today's; ids; and a hybrid of `Rc` nodes with dense u32 memo keys, which shrinks the maps without the port.
  - It is a one-sided filter: a loss stops the port.
  - Its gate is re-profiled on large pages first.

*Measured for it* (probe reverted, no patch kept):
- The miner builds no node outside a scope, and none in a scope before the table switches on (`proof_cost_split` and a full salt-1 sweep).
- 19-21% of the nodes built are not in the table when it drops.
- 17% (`proof_cost_split`) to 22% (largest sweep child, 0.42 M) of interned nodes are still alive after it. This is the live set, not the copy-out volume, which is unmeasured.
- **Small checks gain little.** Mitigation: share one region across a batch of checks, as `proof_cost_split` shares one scope, and reset a region by its pointer, keeping its pages mapped.
- **The compiled hot path should not allocate at all.** When it must produce terms (proof witnesses), it bump-allocates into the region through linear memory. Not a shortcoming of the arena; the arena fixes the format at the boundary.

Scheme 1's caveats, with mitigations:
- **Each process locks its reservation for its whole life.** Mitigation (done): `arena_reserve` is 64 MiB. Large pages were on in every process at first, because the sweep of short processes seemed to gain a little at low load. Rechecked, they lost, so `driver::sweep` now turns them off for its children ("How often the large-page stall hits a sweep").
- **A machine without the privilege falls back to normal pages.** Mitigation (done): the machine-state line logs `pages=`, as it logs Defender's state, so baselines compare.

*Stage 1 result (2026-10-14; tracer and replay throwaway, reverted, no patch kept): continue.*
- **The trace:** one law check of rule 33 after a warm-up, at n=8, 16, 32 and 64 (5.4 to 44 MB). Its new entries (intern misses plus memo puts) are 154,427, 301,740, 596,364 and 1,185,612, against the 154,275 and 1,185,460 above. Every arm reproduces every lookup's hit or miss and every `uses` and `lowest_loose` answer.
- **The arms:** (a) 80-byte `Rc` blocks, pointer-keyed maps, `keep`; (b) 24-byte nodes in a vector with side arrays, u32-keyed maps, a bulk clear at scope end; (c) (a)'s nodes in 96-byte blocks with a u32 id, memos keyed and valued by ids.
- **ns per new entry,** decoding subtracted, work plus the scope's drop, median of 5 alternating processes (load 25% at the start, Defender RTP off, large pages):

  | n | (a) today | (b) ids | (c) hybrid |
  |---|---|---|---|
  | 8 | 229 | 153 | 183 |
  | 16 | 286 | 186 | 255 |
  | 32 | 342 | 253 | 314 |
  | 64 | 406 | 326 | 378 |

  A second rotation (load 70% falling to 16%) gave, best of 5 at n=64: (a) 411, (b) 314, (c) 367.
- **Gate passes:** (a) rises 177 ns from n=8 to n=64, against the ~206 ns re-profiled on large pages for the maps, `uses` and `lowest_loose` (at 23-26% load): a ratio of 0.86.
- **Stop rule not met:** (b) is 20% below (a) at n=64 (24% in the second rotation). Without the drop phase it is 13.5% (17.6%), so the scope drop carries part of the gain.
- **The hybrid is not the cheaper end:** (c) is 7% (11%) below (a), about a third of (b)'s gain.
- **The rise is unchanged.** (b) rises 173 ns from n=8 to n=64, as (a) does. In the replay, ids take a near-constant ~75 ns off each entry; the growth with n does not come from node or entry size.
- **Not in the replay:** the `ReductionCache` (no traffic while the table is on), `context_of`, the reducer's own node reads (which understate (b)), and the port's own costs (which overstate it).
- **Next, per the spec:** the narrower real prototype (`shift`, `instantiate`, `uses` and `lowest_loose` on ids, on a branch, timed against `main`). **Dropped before it was built (2026-10-14):** callers use its results as `Rc` at once, so its boundary would build every new node twice. That cancels the intern and node-build gains, and the per-op costs below leave about zero net at n=64 (`lowest_loose` +20, memo get +15, memo put −26, `uses` −11 ns per entry). Stage 2 went first instead ("Id arena Stage 2" below).

*Where the rise comes from (the same replay, 2026-10-14; reverted, no patch kept).* Cycles were charged to each trace op, one run at n=8 and n=64 per arm, with 3 reps and the quietest kept (the profiler adds its own cost, about equally per op). Top-level op counts per entry hardly change with n: memo gets 0.97 against 1.00, `uses` calls 0.52 against 0.53. So the rise is in what each op costs. ns per entry, n=8 → n=64:

| op | (a) today | (b) ids |
|---|---|---|
| `uses` | 18 → 68 (+50) | 21 → 79 (+57) |
| `lowest_loose` | 55 → 94 (+39) | 42 → 74 (+32) |
| intern | 50 → 92 (+42) | 33 → 44 (+11) |
| memo get | 34 → 66 (+32) | 25 → 51 (+26) |
| memo put | 25 → 31 (+6) | 31 → 57 (+26) |
| node build | 26 → 37 (+12) | 14 → 27 (+13) |
| all ops | 277 → 478 (+201) | |

- **`uses` (a quarter of the rise) is algorithmic.** Nodes visited per call grow linearly with n: 5.5, 9.1, 16.3 and 30.5 at n=8, 16, 32 and 64. The cost per visit falls (6.3 to 4.2 ns), so this is more walking, not slower walking, and no layout changes it.
- **The rest is lookups in tables that grow:** `lowest_loose` (its visits per call stay at 7.9, but each one probes the `lows` memo), intern, memo gets and puts. Ids remove most of intern's rise (an 8-byte table entry) and little of the memos'.
- **Tried and rejected: a 64-bit set of loose `Var`s per node,** which would answer `uses` and `lowest_loose` without walking. It is exact only when no node beneath has loose above 64. Most nodes at n≥16 have more (515,113 of 523,216 at n=64; the context is deep), so it covers 81% of `uses` calls and 16% of `lowest_loose` calls at n=64. A fixed-width set does not scale with n. Checked against every traced answer where it applies.

*Why `uses` walks grow, and what table growth costs (the same replay, 2026-10-14; reverted, no patch kept).*
- **The walks revisit old nodes whose slot holds another query.** At n=64, 0.8% of visits are a node's first. Per call, slot misses with a different query are 14.5 and misses on an empty slot 0.24. Nodes are asked at many depths (d up to 384), so a slot keyed by d alone does no better (30.2 visits per call).
- **A memo fixes it at every n.** Visits per call:
  - an unbounded `(node, d, m)` memo: 1.59;
  - `lowest_loose` with its `(node, d)` memo, answering `uses(x, d, m)` as `lowest_loose(x, d) < m`: 1.57.
- **Timed in arm (a),** ns per new entry with decoding subtracted: median, then best of 7 in brackets. The reps alternate, at load 23% falling to 13%:

  | n | today (slot) | `(node, d, m)` table behind the slot | `uses` through `lowest_loose`'s per-scope memo, no slot |
  |---|---|---|---|
  | 8 | 266 (194) | 242 (217) | 256 (230) |
  | 64 | 483 (449) | 427 (367) | 388 (376) |

  - At n=64 the shared memo wins 6 of 7 paired reps, and the rise from n=8 to n=64 falls from 217 to 132 ns. An earlier rotation (load 40%) gave 445 → 360 best-of-5 at n=64 with the table.
  - At n=8 it is within noise: 4 of 7 paired reps.
  - This does not contradict "Per-node facts in the node header", where slot alone beat slot plus table 8 of 12 on `proof_cost_split`. That workload is small-n; at n=64 the walks are 5.5 times longer.
  - In the replay the shared memo is the one mechanism: it subsumes the slot and the `uses` walk. In the real kernel it loses on small work, with or without the slot in front (next paragraph).
- **Most memo entries are never read:** inst 85%, shift 78%, whnf 62% and types 77%, the same at n=8 and n=64. Hit rates are flat in n (inst 35%, shift 44%, whnf 58%, types 74%).
- **Pre-sizing the tables to their final size gains nothing** (2 rotations, within noise). The growth cost is probes into tables larger than the caches, not resizing.
- **Bounded memos keep most hits only for some tables.** A 2-way cache of 2^16 entries at n=64 keeps 97% of inst's hits, 98% of whnf's, 88% of types' and 75% of shift's (2^14: 93, 85, 70, 62). A lost hit means recomputation, which the replay cannot time, so this needs a real prototype.
- **A one-entry slot per node** would answer all of whnf's hits, 99.9% of hnf's, 86% of types', 66% of shift's and 38% of inst's.

*The shared memo in the real kernel: negative (2026-10-14; branch reverted, no patch kept).* On 012e4c5, the node's `uses` slot was deleted, and `uses(x, d, m)` became `lowest_loose(x, d) < m` through a `(node, d)` memo in the `hc` table (pinned like the other memos). `InferCache::memo_context` used that table while it was on, and its own map otherwise. The kernel unit tests passed. Alternating pairs, BelowNormal on 12 cores, load about 25%, real-time protection off:

| workload | today (slot) | shared memo | pairs won by the memo |
|---|---|---|---|
| rule 33's law, n=64, 5 checks per process: median of medians | 672 ms | 586 ms (−13%) | 6 of 6 |
| rule 33's law, n=8, 61 checks per process: best | 42.9–45.4 ms | 45.1–48.4 ms (+6%) | 0 of 6 (medians: 2 of 6) |
| `proof_cost_split`, CPU per process: median | 3.84 s | 4.36 s (+13%) | 0 of 8 |

- `proof_cost_split`'s check rose 350 → 418 ms and its build (which also runs the kernel) 2.35 → 2.70 s.
- So the replay's n=64 gain is real (−13% against its −20%), but small checks pay more for a hash probe into the table than the slot's one header read saves. This agrees with "Per-node facts in the node header", where the slot beat slot plus table on `proof_cost_split`.
- **The slot first, with the memo only behind its misses, also loses on small work.** Two variants of that hybrid, against today's, with load 8–30% for `proof_cost_split` and rising to 42% by the end of the rule 33 runs:
  - With `memo_context` also on the table's memo: `proof_cost_split` CPU median 3.83 → 4.11 s (+7%, the hybrid won 1 of 8), check 344 → 406 ms.
  - With `memo_context` on its own map as today: `proof_cost_split` 3.84 → 4.03 s (+5%, won 2 of 8), check 340 → 373 ms. Rule 33 at n=64, median of medians 635 → 576 ms (−9%, 4 of 6); at n=8 neutral (3 of 6, by best and by median).
  - So the slot's misses alone carry the loss. A likely cause, not measured: `lowest_loose` must visit every child to find the minimum and hashes each node it visits, while the `uses` walk stops at its first hit and hashes nothing. On small terms that walk is cheaper than the memo.
  - The memo pays only where walks are long (large n). Choosing between walk and memo by term size would be a size threshold, not a general mechanism; not tried.

**The slot in front of bounds (2026-10-14, adopted).** `uses(x, d, m)` keeps the node's slot and today's walk, which stops at its first hit. A slot miss looks up the `hc` table's `bounds[(x, d)] = (lo, hi)`, bounds on `lowest_loose(x, d)` that start at `(0, loose − 1 − d)`. A query with `m > hi` is true and one with `m <= lo` is false, without a walk. Otherwise the walk runs, and its answer narrows the entry to `(lo, m − 1)` if true or `(m, hi)` if false. So one (node, d) entry answers every `m` its bounds decide, as `lowest_loose`'s memo does, without visiting every child for an exact minimum. Check: `uses_bounds_agree_with_lowest_loose`, which asks every (d, m) in three orders. Against main's kernel (012e4c5, unchanged to 981540b), alternating pairs, BelowNormal on 12 cores, real-time protection off:

| workload | today (slot) | slot, then bounds | pairs won by bounds |
|---|---|---|---|
| `proof_cost_split`, CPU median, rotation 1 (load 12–20%) | 3.73 s | 3.69 s | 6 of 8 (1 tie) |
| `proof_cost_split`, CPU median, rotation 2 (load ~25%) | 3.63 s | 3.68 s | 6 of 10 |
| `proof_cost_split` check, median, rotations 1 and 2 | 348, 335 ms | 345, 348 ms | 5 of 8, 4 of 10 |
| rule 33's law, n=64, 5 checks per process: median of medians | 644 ms | 541 ms (−16%) | 5 of 6 |
| rule 33's law, n=8, 61 checks per process: median of bests, of medians | 41.0, 50.7 ms | 41.2, 50.6 ms | 2 of 6, 2 of 6 |

- Neutral on small work and −16% at n=64, so it is adopted.
- Bounds without the slot lose on small work: `proof_cost_split` check 343 → 369 ms (won 1 of 8), CPU median 3.78 → 3.77 s (won 2 of 8). The slot's one header read still beats a hash probe when it hits.
- This supports the cause guessed above: the `lowest_loose` hybrid lost on small work while this one, with the same slot in front, does not. The difference is the walk that stops at its first hit.
- `InferCache`'s `lows` stays as it is: it needs the exact minimum.
- Sequential sweep pair (rows `bnd_*`, script `bounds_seq.sh`; CPU 24% at launch, RTP off): identical outputs on both salts (181 files each, lemma caches included; logs differ only in timings and their own paths). Walls 18 against 20 s (salt 1) and 19 against 18 s (salt 2).

**Id arena Stage 2 (2026-10-14, adopted on branch `id-arena-stage2`).** The types the arena needs, on today's `Rc` nodes:
- **`PExpr`** is a term kept past its scope. Only `persist` makes one, and it lends no `&Expr` (`get` hands out a clone), because an id cannot lend one.
- **`kernel::scoped(f)` replaces `InternScope`** at its 79 sites. The call that opens the scope passes `f`'s result through `Escape`, which is `persist` on every term, before closing it. So returning a type that holds terms without an `Escape` impl fails to compile.
- **The checking entries open their scope the same way,** without switching the table on: `def_eq`, `infer_in` and `check_in` use `hc::scoped(false, ..)`.
- **Long-lived stores hold `PExpr`:** `Globals`, `Postulates`' parameters (`PARAMS` and `PRELUDE` keep a `Postulates`), `CLOSED`, `TREE_LAWS` and `PARAMS`' lemma proofs. `CONSTANTS` and `BODIES` stay `Expr`, since they are rebuilt per generation.
- **Behaviour unchanged:** every suite passes with the base's counts (lib 371 = 370 + the new `scoped` test, church_bv 76).
- **Sequential sweep pair** (rows `s2_*`, script `stage2_seq.sh`; CPU 24% at launch, RTP off): identical outputs on both salts. Logs differ only in timings and their own paths, and `mines.tsv`/`pooled_prefs.tsv` only in their seconds column. Walls are 22 against 21 s (salt 1) and 18 against 21 s (salt 2).
- **Timing:** `proof_cost_split`, 8 alternating pairs against 4769775 (load 23%, RTP off). CPU median 3.98 → 3.94 s (new won 5 of 8), check median 370 → 363 ms. Within noise.
- **What the copy-out would copy.** A feature `copy-volume` records each node's region (outermost scope) and gives every node `persist` reaches an id in a simulated persistent table, once per node. The counts:
  - `copied`: nodes from the open region;
  - `outside`: nodes built outside any region, persistent already in the arena;
  - `stale`: nodes from an earlier region that were never persisted, which would be dead handles;
  - `unique`: the table's size.

  | workload | `persist` calls | copied | outside | stale | unique | interned (spec probe) |
  |---|---|---|---|---|---|---|
  | `proof_cost_split` | 1,712 | 493,753 | 0 | 0 | 494,561 | 2.98 M (0.49 M alive after) |
  | salt-1 sweep, 125 children | 9,620 | 1,554,721 | 0 | 0 | 1,559,422 | 10.8 M (2.61 M alive after) |

  - The copy-out is 17% of `proof_cost_split`'s interned nodes, and matches the 0.49 M the spec's probe found alive after the table drops.
  - For the sweep it is 14%, below the 2.61 M alive after. So that live set also holds nodes no `persist` reaches, such as memo entries and terms dropped later.
  - `stale` = 0: no converted store and no return keeps a region node unpersisted.
  - Each of the 125 children printed one `COPYVOL` line, and the `copy-volume` build's sweep totals equal the default build's.
- **The port's risk "an outermost `scoped` copies out large results"** is small on this workload. Copying 0.49 M nodes at about an intern's cost (50-90 ns per entry in Stage 1's replay) would be about 25-45 ms of `proof_cost_split`'s 3.9 s, about 1%. That is an estimate, not timed.
- **Departures from the spec:**
  - The counter counts by region, not generation: 19-21% of a scope's nodes never enter the table, but every node built in a region is a region node.
  - `Postulates` holds `PExpr`, which the spec did not list.
  - `NO_SCOPE` and the other A/B toggles stay as `if c { scoped(body) } else { body() }`; the port deletes them.
  - An outermost `infer_in` (as in every `Postulates::push` outside a scope) persists the type it returns, since the arena copies it out too.
- **Two plan misses fixed on the way:**
  - `uses_slot_is_free_and_agrees_with_the_walk` asserts the 64-byte node as well, so it is off under `copy-volume`, like `a_node_is_64_bytes`.
  - `kernel_soundness_fuzz`'s `to_globals` now takes the `Globals` its callers pass.
- **Next:** the Stage 3 decision (the port). It rests on Stage 1's replay (ids 20% below today at n=64, 33% at n=8, the rise with n unchanged) and on this copy-out volume.

**Id arena Stage 3 (2026-10-14, adopted on branch `id-arena-stage3`).** Terms are ids into two hash-consed spaces. Plan `docs/superpowers/plans/2026-10-14-id-arena-stage3.md` (main checkout only), in two phases:
- **Phase A** (3be0e79): the API port on `Rc` storage. `Expr` is a handle over `Node<Expr>`, the old enum's variants with children `C`, read with `e.node()` and built with `mk`. Internals take `s: &Spaces` first. Twin functions merge (`whnf_impl`+`whnf_rc` into `whnf_in`, likewise `nf_in` and `conv`). `copy-volume`, `hc_probe`, `with_ranges` and `LEAF` are deleted. `shared` (two or more parents, counted at build) replaces `strong_count > 1`.
- **Phase B** (1166b0e `spaces.rs`, ff173a6 the switch): `Expr` is `Copy`, 8 bytes: a node `Ref` and the region epoch it was made in. `Spaces` (thread-local) holds a persistent space and one region, both hash-consed, so equal structure is one resolved `Ref` and `==` is an id compare. A handle from a closed region is dead: reading it panics ("dead handle"), and `Debug` prints `<dead handle>`. `scoped` opens the region and persists its result on close. The memos (instantiation, shifts, `whnf`, `hnf`, `nf`, argument lists, `uses` bounds) live in `Spaces.memos`, keyed by `u32` node ids, and clear on close. Every public entry (`whnf`, `def_eq`, `normalize`, `infer_in`, `check_in`, `typecheck`) runs in a region.
- **Deleted in B:** `Drop for Header`, `ReductionCache`, `PtrHasher`/`PtrMap`/`PtrSet`/`PtrKey`, `ShiftKey`, `eq_noting` with its `unequal` set, `whnf_fresh`, `canonical_inputs`, and `hc::Scope`/`activate`/`intern`/`generation`. Tests deleted with the mechanism each asserted: `memo_sources_outlive_their_callers`, `args_id_is_the_same_for_a_canonical_argument_and_its_twin`, `dropping_a_deep_term_does_not_overflow_the_stack`, and `infer_memo_changes_no_answer` (under hash-consing its "unshared copy" is the same node).
- **Behaviour unchanged.** Every suite passes with the base's counts except lib: 371 in the base, 370 in A (`a_node_is_64_bytes` deleted), 374 in B (+6 `spaces` unit tests, −4 deleted, +2 dead-handle tests). church_bv stays at 76, and no dead handle fired in the suite or the four sweeps. Sequential sweep pairs against the base 6833fb9 (Stage 2 plus the `law_time` harness; rows `s3a_*`, `s3b_*`, script `s3_seq.sh`, RTP off) give identical outputs on both salts for both phases. Logs differ only in timings, their own paths and the filtered-out count, and `LEMMA_CACHE` lines match. One log, `lib_sbo3/mine_ref.log`, moves its `LEMMA_CACHE starts empty` line by one: the base exe moves it between its own runs too (stdout and stderr interleave).
- **Tests whose expectation changed** (hash-consing now holds outside a region too):
  - `bin_round_trips_and_shares_nodes`: the encoding's size is equal in and out of a region;
  - `constants_are_built_once_per_generation`: the second region's rebuilt gate is the copy `scoped` persisted from the first;
  - `close_is_linear_in_the_dag_of_a_shared_body`: 64 nodes, not 93, because the postulate `f` is one node.
- **Timing, Phase A** (informational; load 30-41%, RTP off): `proof_cost_split` CPU median 3.79 → 3.90 s (A won 2 of 8). Rule 33's law at n=64: median 555-632 → 489-497 ms; n=8 within noise.
- **Timing, Phase B** (RTP off, load 9-24% at each block's checks; another session's `tier_eval_nn` was resident):

  | workload | base 6833fb9 | B | |
  |---|---|---|---|
  | `proof_cost_split`, 8 alternating pairs: CPU median | 3.73 s | 2.54 s | −32%, won 8 of 8 |
  | the same: build / check median | 2213 / 352 ms | 1737 / 221 ms | |
  | rule 33's law, n=8, median of each run (3 pairs) | 50-54 ms | 21-25 ms | won 3 of 3 |
  | n=16 | 89-246 ms | 43-136 ms | won 3 of 3 (noisy) |
  | n=32 | 215-507 ms | 110-273 ms | won 3 of 3 (noisy) |
  | n=64 | 478-491 ms | 252-315 ms | won 3 of 3 |
  | salt-1 sweep in a job object, 3 alternating rounds: job CPU median | 51.5 s | 51.1 s | won 3 of 3 |
  | the same: peak commit, largest process / job | 578 / 769-833 MB | 514 / 705 MB | |
  | gcd benches (criterion, 3 alternating runs, pinned): median of the 3 point estimates, 7 benches | 5.5 µs-551 µs | 3.3 µs-275 µs | 0.43-0.59 of base, gate 1.10 |

  The n=16 and n=32 rows swing about 2× between pairs for both arms (contention). Every pair at every n goes to B, at 0.42-0.64 of the base's median.
- **Decision rule** (plan): keep the port if rule 33 at n=64 is faster and `proof_cost_split` is not slower beyond its spread. Both hold by a wide margin, and the gcd gate passes (plan departure 11 expected small proofs to pay the full interning; they take about half the time instead).
- **Departures from the spec** are listed in the plan (1-13) and recorded in the spec. Made during execution:
  - every `benches/proofs.rs` iteration runs in its own region, not only the gcd ones;
  - `Spaces::from_key` became `expr_of`, since it reads the epoch through `self` (clippy's `wrong_self_convention`).
- **`docs/learned-vs-fixed.md`:** no row changes; no learned or fixed part moved.
- **Parked:**
  - departure 2's raw-`Ref` walks (`inst_rec`, `uses`, `conv_whnf`), if a profile shows `resolve`;
  - departure 12's bitset for `hc::exceeds`, if its walk shows;
  - the spec's own parked list.
- **Next:** profile B on rule 33 at n=8 and n=64, to see what the rise with n is made of now (the per-entry costs in "The rise after the bounds memo" were measured on `Rc` nodes). Done below.

**What rule 33's rise with n is made of on B (2026-10-14; probe reverted, no patch kept).** The probe proves the law once outside a region, then checks it in fresh regions, counting the nodes each check adds to the region. It ran 300 checks at n=8 and 25 at n=64 under samply (RTP off, load 4%), and compared them with `prof_diff.py` per new node. The checks add 50,487 and 385,032 nodes. These units are not the old table's entries: the proof is persistent and hash-consed, so only the check's own nodes count, and the numbers compare only within this pair.
- **Busy time per new node:** 322 ns at n=8, 604 ns at n=64. Self time per new node, by first non-std frame:

  | | n=8 | n=64 | rise | calls per node, n=8 / n=64 | ns per call, n=8 / n=64 |
  |---|---|---|---|---|---|
  | `Spaces::mk` (with its hashbrown probe) | 62 | 130 | +68 | 2.15 / 2.19 | 29 / 60 |
  | `hc::lowest_loose` | 33 | 66 | +34 | 2.16 / 2.24 | 15 / 30 |
  | `infer_rc` | 18 | 43 | +25 | 0.95 / 0.91 | 19 / 47 |
  | `hc::shift_get` | 18 | 41 | +23 | 1.44 / 1.52 | 12 / 27 |
  | `hc::uses` | 23 | 43 | +20 | 2.16 / 2.23 | 11 / 19 |
  | `hc::inst_get` | 11 | 28 | +18 | 1.16 / 1.18 | 9 / 24 |
  | `spaces::hash` | 12 | 25 | +13 | one per `mk` | 6 / 11 |
  | `shift_child` | 8 | 19 | +12 | 1.86 / 1.92 | 4 / 10 |
  | `hc::whnf_get` | 7 | 17 | +10 | 1.11 / 1.06 | 6 / 16 |
  | `hc::height_at_most` | 19 | 28 | +9 | 3.90 / 3.95 | 5 / 7 |

- **The calls per new node stay flat** (a second probe counted the calls of these nine functions; each count moves by about 5% or less between n=8 and n=64). So the rise is the cost per call. It is broad: hash probes, memo lookups and walks each take about twice as long per call.
- **The rise looks like memory, not work.** `spaces::hash` is register arithmetic over a node's tag and child ids, yet its time per call doubles too. That is most likely samples landing on it while the loads around it stall.
  - ns per node climbs smoothly with region size: about 460-540 at n=2-4 and 990-1070 at n=128 (two sweeps), with no sharp knee. These runs were contended (another session's `tier_eval_nn` and one other job, about one core each); idle n=8 reads about 340.
  - The same contention, at a total load of only 17-18%, slowed n=8 by about 1.6×. That fits a shared L3 between jobs.
  - **Ballast test:** before each n=8 check, 335,000 unrelated leaves were interned into the region, bringing it to n=64's size. They grow the node table and the per-node vectors but not the memos. ns per node rose 5-27% over three alternating rounds; n=64's own figure stood 39-54% above n=8's in the same rounds. With 1,000,000 leaves the rise was 6-49% (noisy).
  - So the node table's size explains part of the rise. The rest is plausibly the memos' size and the check's nodes being spread over a larger region; this was not measured.
- **What it points at:** the region's footprint per node, not its algorithms. Each node has an entry in `nodes`, `loose`, `free`, `uses`, `parents` and the table, plus its memo entries. Candidates, unmeasured: a footprint count of bytes per node at n=64; smaller memo entries; and denser layouts for the walks (departure 2's raw-`Ref` walks, still parked).

**Footprint per node of rule 33's check on B (2026-10-14; probe reverted, no patch kept).** The probe measured a law check in a fresh region, the second of two. It read the region's vectors and table, the `Spaces` memos, and `check_in`'s `InferCache` (read before it drops). It counts bytes in use (entries × entry size) and bytes allocated (capacity, or hashbrown's `allocation_size`), per new node. The probe missed `CtxScope` and `check_open`'s `FreesMemo`.

| per new node | used B | allocated B | entries per node |
|---|---|---|---|
| `region.nodes` (`Node<Ref>`, 24 B) | 24.0 | 36.0-37.8 | 1 |
| `region.loose`, `free`, `uses` (4 B each) | 12.0 | 18.0-18.9 | 1 each |
| `region.parents` | 1.0 | 1.5-1.6 | 1 |
| `region.table` | 8.0 | 11.7-12.3 | 1 |
| `memo.inst` | 12.6-12.7 | 22.1-23.1 | 0.79-0.80 |
| `memo.shifts` | 13.2-13.6 | 22.1-23.1 | 0.83-0.85 |
| `ic.lows` (`lowest_loose`'s memo) | 9.0-9.4 | 16.9-17.7 | 0.75-0.79 |
| `memo.bounds` | 5.1-5.4 | 11.0-11.6 | 0.32-0.34 |
| the rest (`whnf`, `arg_sets` and its keys, the other `ic` maps, `hnf`) | 7.6-8.4 | 12.5-14.9 | |
| **total** | **92.5 / 94.4** | **151.7 / 160.9** | |

- **The footprint per node is flat in n**, at about 93 B in use and 150-160 B allocated. So the region and its memos grow linearly: 7.7 MB at n=8 (50,487 nodes) and 62 MB at n=64 (385,032).
- **That straddles this machine's caches:** 1 MB of L2 per core and 16 MB of L3. n=8's set fits in L3 and n=64's is about 4× it. At about 155 B per node, L3 fills near 100,000 nodes, which is n=16. In the contended sweep above, ns per node is 547-688 up to n=16, 691-749 at n=24-32, and higher beyond. The rise above therefore matches a working set that leaves L3, consistent with the flat call counts and the doubled cost per call.
- **The hash maps hold about half the bytes, and they are the random-access ones.** The memos plus `region.table` come to about 56 B used and about 100 B allocated per node. Their allocation is 1.5-2.2× their use (load factor and power-of-two growth), and a probe can land anywhere in it.
  - `memo.inst`, `memo.shifts` and `ic.lows` each have about 0.8 entries per node, at 16 B (shifts, inst) and 12 B (lows) per entry before overhead.
- **`Node<Ref>` is 24 B because of `J`'s five children** (`WRec` has four). Every other variant fits in 16 B: a tag and three `u32`s.
- **Candidates, unmeasured:**
  - make `Node<Ref>` 16 B, by moving the children of `J` and `WRec` out of line;
  - shrink the memo entries, or hold the common case (one entry per node) in side vectors, as `uses` does;
  - make the region's per-node vectors one struct-of-arrays row.
  - Each attacks bytes per node; the test is rule 33 at n=64 against n=8.

**16-byte stored nodes, rejected (2026-10-14; reverted, no patch kept).** The first candidate above, built and timed against 41f48c1.
- **Change:** `Space.nodes` held a 16 B `Slot` (a tag byte, then three `u32`s) in place of `Node<Ref>`. A leaf kept its value in the first word, and a node with up to three children kept them inline. `J` and `WRec` set a `WIDE` bit in the tag, kept their first two children inline and the rest in a per-space `wide: Vec<[Ref; 3]>`, indexed by the third word.
  - One generic `Node::from_parts(tag, leaf, kid)`, the inverse of `tag_leaf` with `for_kids`, decoded every variant. `push` encoded and `node_at`/`find`/`persist` decoded; nothing outside `spaces.rs` changed.
  - Every suite passed (lib 375, the base's 374 plus a round-trip test of all 16 constructors through build, dedup and persist; church_bv 76).
- **Timing** (RTP off; load 17-42%, another session's `tier_eval_nn` on about one core throughout):

  | workload | base | slot | |
  |---|---|---|---|
  | rule 33's law, n=8, 8 alternating pairs × 15 reps: median of the run medians | 27.2 ms | 27.4 ms | +0.7%, within spread |
  | the same at n=64 | 436 ms | 429 ms | −1.5%, within spread |
  | `proof_cost_split`, 8 alternating pairs: CPU median | 2.79 s | 2.94 s | +5%, slot lost 6 of 8 |
  | the same: build median | 1.91 s | 2.05 s | +7% |

- **Why it doesn't pay:** 8 B off about 155 B allocated per node is 5% of the footprint, too little to move n=64 measurably. Meanwhile, encoding on every push and decoding on every read and table compare (a `from_parts` match where a 24 B enum copy was) costs about 7% of proof building.
- **Conclusion:** node size is not the lever. A footprint change has to come from the hash-map half (about 100 B of the 155 B allocated per node).

**Memo census of rule 33's check (2026-10-14; probe reverted, no patch kept).** For each memo the probe counted lookups and hits during one law check, and at the end the entries per node and how many sit on `hc::low` nodes (height at most 2). Values are n=8 / n=64.

| memo | lookups | hit rate | entries | nodes with entries (of 50,487 / 385,032) | share of those nodes with one entry | entries on low nodes |
|---|---|---|---|---|---|---|
| `shifts` | 72,892 / 584,060 | 0.43 / 0.44 | 41,729 / 329,094 | 21,491 / 165,271 | 53% / 54% | 3.0% / 2.7% |
| `inst` | 58,591 / 454,455 | 0.32 / 0.33 | 39,792 / 306,408 | 5,979 / 34,046 | 60% / 61% | 0 (gated) |
| `ic.lows` | 68,446 / 567,070 | 0.51 / 0.53 | 33,398 / 267,870 | 21,621 / 171,869 | 66% / 66% | 0.5% / 0.6% |
| `bounds` | 26,946 / 198,637 | 0.09 / 0.11 | 22,049 / 171,849 | 18,531 / 143,355 | 83% / 83% | 0.2% / 0.03% |
| `whnf` | 56,184 / 408,872 | 0.80 / 0.79 | 11,539 / 86,747 | 11,539 / 86,747 | 100% | 0.2% / 0.02% |

- **A low-node cutoff for the other memos is falsified, not built.** It would remove 3% of `shifts` entries and under 1% of the others. Those entries are among the best: `shifts` lookups on low nodes hit 81% / 83%, against 43% overall. (The 2026-10-13 leaf-only skip was neutral for the same reason.)
- **Per-node side arrays don't pay either.** Holding each node's first entry in a per-node array costs a slot for every node, but only 43% of nodes have a `shifts` entry.
  - For `shifts`, the array would be 12 B × every node (606 KB at n=8). It would take 21,491 entries out of the map, at about 27 B allocated each (about 580 KB). That is break-even.
  - For `whnf` (one entry on 23% of nodes) it loses. For `ic.lows` it saves about 1.6 B per node.
- **What stands out instead:**
  - `inst` has 6.7 / 9.0 entries per memoized node (many argument lists and depths per node), rising with n, and a 32% hit rate.
  - `bounds` has 0.11 / 0.13 hits per entry: 16 B entries, about 11 B per node allocated, almost never read back. But a hit can save a deep `uses` walk, so its value isn't its hit rate.
  - Neither is a footprint fix by itself.

**Removing the `bounds` memo: negative (2026-10-14; reverted, no patch kept).** `uses` kept its per-node slot and its `loose`-based shortcut, and walked on every slot miss. Against 5bab407, rule 33's law over 8 alternating pairs × 15 reps (RTP off, load 25%, two other sessions' jobs on about one core each):

| | with `bounds` | without | |
|---|---|---|---|
| n=8, median of run medians | 27.9 ms | 28.7 ms | +3%, removal lost 7 of 8 |
| n=64 | 425 ms | 524 ms | +23%, removal lost 8 of 8 |

The decision was clear from the law alone, so `proof_cost_split` was not run. `bounds` stays: its rare hits save deep walks, as its adoption measured (−16% at n=64, "The slot in front of bounds").

**Why `inst` has many entries per node, and the unshared nodes (2026-10-14; probe reverted, no patch kept).** A census of rule 33's check (values n=8 / n=64; hits counted during the check only):
- **Argument lists, not depths, make the entries.** Every (node, argument list) pair has exactly one entry, and no node has more than 2 depths.
  - There are 1,911 / 14,287 distinct argument lists, and 88% / 91% of entries are for lists of several arguments.
  - 17% of entries repeat another entry's result on the same node. So a coarser key would merge little; the lists really differ.
- **87% of entries are never hit** (34,739 of 39,792; 267,251 of 306,408).
  - Hits concentrate on hub nodes instantiated with many lists: nodes with 16 or more entries (447 / 782) hold 70% / 79% of the entries and get 92% / 98% of the hits.
- **Entries on unshared nodes** (one parent, `Spaces::shared` false) **get almost no hits**, across every memo that serves one walk:

  | memo | entries on unshared nodes | hits on unshared nodes |
  |---|---|---|
  | `inst` | 77% / 77% | 14 / 14 (of 18,799 / 148,047) |
  | `ic.lows` | 70% / 69% | 0 / 0 |
  | `shifts` | 69% / 69% | 4.6% / 4.4% |
  | `bounds` | 77% / 77% | 27% / 29% |
  | `whnf` (one memo for the whole region, not one walk's) | 88% / 88% | 73% / 76% |

  - The reason is the one `infer_rc` and `abstract_frees_in` already rely on: an unshared node is reached only through its one parent, so a repeat of the walk stops at the parent's entry first.
  - `shifts` keeps some unshared hits through parents with no entry of their own (call roots, and `inst_rec`'s low nodes, which take the shift path). `bounds` keeps more because `uses` reaches a child again for each new `m`.
  - `whnf` serves calls on arbitrary terms, not one walk, so the rule doesn't apply to it.
- **Candidate, not built:** one rule, "a walk's memo stores only shared nodes", for `inst`, `ic.lows` and `shifts` (`bounds` to be measured separately).
  - At n=64 it would drop about 650,000 of the region's memo entries, 1.7 per node, about 45 B of the 160 B allocated per node (at each memo's allocated bytes per entry). It would also skip their inserts and missed lookups.
  - It loses only `shifts`' unshared hits, on nodes small enough to re-walk cheaply.

**Walk memos store only shared nodes (2026-10-14, adopted).** The candidate above, built.
- **Change:** `inst_rec` memoizes a child only if it is shared and not `hc::low`. `shift_child` shifts an unshared node without the memo. `lowest_loose` reads and writes `lows` only for shared nodes.
  - The rule is stated once, in `hc`'s module doc. It is the one `infer_rc` and `abstract_frees_in` already followed, so every walk's memo now follows it.
  - `whnf`, `hnf`, `nf` and `bounds` keep every node, as the module doc says why.
- **Check:** `walk_memos_store_only_shared_nodes`. A shared node gets an `inst` and a `lows` entry and an unshared one neither; the test fails with `inst_rec`'s old gate. Every suite passes with the base's counts plus this test (lib 375).
- **Timing** against b0404ef (RTP off; load 26-28%, other sessions' `tier_eval_nn` and `manifold` resident):

  | workload | base | shared only | |
  |---|---|---|---|
  | rule 33's law, n=8, 8 alternating pairs × 15 reps: median of the run medians | 26.6 ms | 20.1 ms | −25%, won 8 of 8 |
  | the same at n=64 | 426 ms | 317 ms | −26%, won 8 of 8 |
  | `proof_cost_split`, 8 alternating pairs: CPU median | 2.95 s | 2.74 s | −7%, won 7 of 8 |
  | the same: build / check median | 2067 / 266 ms | 1891 / 227 ms | |

- **Sweep pair** (`s3_seq.sh shm`, rows `shm_{old,new}_{1,2}`): every unit file is identical on both salts, and so are the `LEMMA_CACHE` lines with paths masked. Only `own.tsv`'s elapsed-seconds column differs (one row on salt 1, 1 s against 0 s). Wall 19/17 s against 17/18 s.

**`bounds` under the same rule: neutral, not adopted (2026-10-14; reverted, no patch kept).** `uses` read and wrote `bounds` only for shared nodes, keeping its per-node slot. Against 0d50e97 (RTP off, load 23-33%):

| workload | base | shared only | |
|---|---|---|---|
| rule 33's law, n=8, 16 alternating pairs × 15 reps: median of the run medians | 21.6 ms | 20.6 ms | −4%, won 8 of 16 |
| the same at n=64 | 321 ms | 301 ms | −6%, won 11 of 16 |
| `proof_cost_split`, 8 alternating pairs: CPU median | 2.68 s | 2.64 s | −1%, won 4 of 8 |

- No workload clears the noise: per-pair differences ran from −7.5 to +3.3 ms at n=8 and from −91 to +67 ms at n=64.
- This fits the census: unshared nodes hold 77% of `bounds`' entries, which the rule no longer stores, but they took 27-29% of its hits, which now walk.
- `hc`'s module doc keeps `bounds` as the exception. Adopting it only for one uniform rule would need its own sweep pair.

**Footprint per node after shared-only walk memos (2026-10-14; probe reverted, no patch kept).** The probe from "Footprint per node of rule 33's check on B", rebuilt unchanged and run on 4ba3f6c. The checks add the same 50,487 and 385,032 region nodes as before. Values are n=8 / n=64, in B per new node:

| | used before | used now | allocated before | allocated now | entries per node now |
|---|---|---|---|---|---|
| `memo.inst` | 12.6 / 12.7 | 2.8 / 2.9 | 22.1 / 23.1 | 5.5 / 5.8 | 0.18 (was 0.79-0.80) |
| `memo.shifts` | 13.2 / 13.6 | 4.0 / 4.2 | 22.1 / 23.1 | 5.5 / 5.8 | 0.25 / 0.26 (was 0.83-0.85) |
| `ic.lows` | 9.0 / 9.4 | 2.6 / 2.7 | 16.9 / 17.7 | 4.2 / 4.4 | 0.22 / 0.23 (was 0.75-0.79) |
| `memo.bounds` (unchanged) | 5.1 / 5.4 | 5.1 / 5.4 | 11.0 / 11.6 | 11.0 / 11.6 | 0.32 / 0.34 |
| region vectors and table (unchanged) | 45.0 | 45.0 | 67.2 / 70.6 | 67.2 / 70.6 | |
| the rest | 7.6-8.4 | 7.6 / 8.2 | 12.5-14.9 | 12.6 / 14.7 | |
| **total** | **92.5 / 94.4** | **67.1 / 68.4** | **151.7 / 160.9** | **106.0 / 112.9** | |

- **The rule saved 46-48 B allocated per node (−30%),** as the census predicted (about 45 B). A check's working set is now 5.4 MB at n=8 and 43 MB at n=64, against 7.7 and 62 MB.
- **The region's own arrays are now the largest part:** 67-71 B of the 106-113 allocated. These are `nodes` (36-38 B at 24 B used), `loose`/`free`/`uses` (18-19 B), and the table (12 B). `bounds` is now the largest memo, at 11-12 B.
- **The vectors' growth slack is not a cache cost** (read from `spaces.rs`, not timed). The vectors' allocation is 1.5-1.6× their use, but capacity past `len` is never touched. `Space::clear` (`reset_vec`) keeps capacity unless the region used under a quarter of it, so repeated checks of one size never reallocate after the first. The hash maps are different: a probe can land anywhere in them, so their slack is touched.
- **What the cache sees** is therefore the vectors' used bytes plus the maps' allocated bytes:
  - now: about 38 + 50-54 ≈ 88-92 B per node, so 4.4 MB at n=8 and 35 MB at n=64, about 2.1× the 16 MB L3, which fills near 185,000 nodes (about n=32);
  - before the rule: about 38 + 95-102 ≈ 133-140 B per node, so 54 MB at n=64, with L3 full near 120,000 nodes (about n=20).
  - The "about n=16" in the first footprint entry used allocated bytes, so it overstated the working set.
- **Rule 33's law still rises with n:** 20.1 ms at n=8 against 317 ms at n=64, 15.8× for 7.6× the nodes.
- **Candidates left:** a struct-of-arrays region row (fewer cache lines per node visit), and the hash maps' load factor and entry size (they now hold most of the touched bytes). The 16-byte node was rejected above.

**ns per node against n after shared-only walk memos (2026-10-14; probe reverted, no patch kept).** This is the Stage 3 B sweep (rule 33's law proved once, then checked in fresh regions; 1,500 reps at n=2 down to 6 at n=128). b0404ef and cb36ad2 alternated per n, over 4 rounds. Load was 43-63%: `manifold`, two `renno` processes and `tier_eval_nn` were resident, so the figures are best-of-4 and the gaps within an arm are noise-sized. RTP was off.

| n | 2 | 4 | 8 | 12 | 16 | 24 | 32 | 48 | 64 | 96 | 128 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| region nodes (both) | 14,579 | 26,588 | 50,487 | 74,384 | 98,280 | 146,072 | 193,864 | 289,448 | 385,032 | 576,200 | 767,368 |
| b0404ef, ns per node | 510 | 560 | 720 | 748 | 718 | 916 | 931 | 1099 | 1219 | 1039 | 1146 |
| shared only, ns per node | 459 | 491 | 509 | 589 | 611 | 621 | 683 | 863 | 805 | 901 | 808 |
| ratio | 0.90 | 0.88 | 0.71 | 0.79 | 0.85 | 0.68 | 0.73 | 0.79 | 0.66 | 0.87 | 0.70 |

- **Shared-only is 10-34% cheaper per node at every n,** and its rise is smaller: from about 460-510 at n=2-8 to 800-900 at n≥48 (about 1.7×), against old's 510-720 to 1,040-1,220 (about 2×).
- **The knee is not resolved.** The footprint above predicts L3 filling near n=20 before and n=32 now. Under this load, best-of-4 still has non-monotone steps (old at n=96 reads below n=64; new at n=128 reads below n=96), which are larger than any knee to be read. A quiet-machine rerun is parked until the other sessions' jobs are gone.

**The hash maps' load and entry size (2026-10-14; analysis, nothing built).** hashbrown allocates buckets × (entry size + 1) + 16 bytes, and that formula reproduces every allocation in the footprint probe above exactly. So each map's bucket count and load follow from it (n=64 on cb36ad2):

| map | entries | entry B | buckets | load | allocated B per node |
|---|---|---|---|---|---|
| `region.table` | 385,032 | 8 | 524,288 | 0.73 | 12.3 |
| `memo.bounds` | 129,123 | 16 | 262,144 | 0.49 | 11.6 |
| `memo.inst` | 68,673 | 16 | 131,072 | 0.52 | 5.8 |
| `memo.shifts` | 100,072 | 16 | 131,072 | 0.76 | 5.8 |
| `ic.lows` | 87,571 | 12 | 131,072 | 0.67 | 4.4 |
| `memo.whnf` | 86,747 | 8 | 131,072 | 0.66 | 3.1 |
| `ic.types` | 37,658 | 16 | 65,536 | 0.57 | 2.9 |
| `ic.window_of` | 31,945 | 16 | 65,536 | 0.49 | 2.9 |
| `memo.arg_sets` | 15,761 | 32 (plus heap keys) | 32,768 | 0.48 | 2.8 + 0.7 |
| `ic.context_of` | 20,411 | 20 | 32,768 | 0.62 | 1.8 |

- **No load-factor lever.** Tables are powers of two with a 7/8 maximum load, so load is 0.44-0.875 by where the count lands. `bounds` just doubled, and the size below (131,072 buckets) cannot hold 129,123 entries at 7/8. Pre-sizing cannot help either: tables already keep their capacity between regions.
- **Little entry-size lever.** Nearly every entry is 8-16 B of `u32`s.
  - Packing `bounds`' `(lo, hi)` into one `u32` saves about 2.7 B per node (about 3% of the ~90 B the cache sees), and needs a fallback past 65,535.
  - Packing `shifts`' cutoff and amount saves at most about 1.5 B.
  - Dropping the table's stored hash halves its 12.3 B, but makes every probe read `nodes`.
- **Merging the memos into one table** would pool their power-of-two slack, but they clear at different times (`ic` per check, `Memos` per region). It is a large restructure for at most about 15 B per node, unmeasured.
- **Verdict: parked.** The maps hold about 30 B used and 54 B allocated per node, and the cheap levers left are worth about 3%. Shrinking bytes per node has reached diminishing returns.

**Where `proof_cost_split` spends its time on B (2026-10-14; probe reverted, profiles not kept).** Two samply profiles of `proof_cost_split` (cmp3d own, 300 laws) on fc68b43 (kernel code as of 0d50e97) built with debug info. A throwaway wrapper test set `cpu_ab.ps1`'s environment in-process, because samply's task cannot pass one. Analysed with `prof_cases.py` (pointed at each profile), `prof_callers.py`, `prof_self.py` and `prof_addr.py` with `llvm-symbolizer`. RTP off.
- **The first profile caught a slow large-page state.** Load not recorded; 7,673 busy samples; the rule proofs' build took 5,673 ms against its usual 1.7-2.0 s.
  - `Space::push` was 43% of busy samples. 29% was `RawVec::grow_one`, reaching mimalloc's realloc and then the kernel's `NtAllocateVirtualMemory`, and 12% was the table's `reserve_rehash`.
  - An A/B of large pages on against `MIMALLOC_ALLOW_LARGE_OS_PAGES=0` followed (4 alternating pairs, load 19%, user and kernel CPU per process). The first run with large pages took 2.20 s of kernel time and a 3,897 ms build. Every other run, either arm, took 0.23-0.67 s of kernel time and 1,651-1,922 ms.
  - So committing large pages is sometimes very slow, presumably when the OS must find and zero contiguous memory. One event in 4 runs: how often a sweep's short processes pay it is unmeasured.
- **The second profile is the steady state** (load 17%, 2,856 busy samples, rule-proofs build 1,980 ms). Inclusive shares of busy samples:
  - kernel checking (`check_rc`) 66%: `whnf_in` 52%, `conv` 51%, `instantiate_n` 45%, `hnf_rc` 30%;
  - the 37 rules' own proofs (`prove_rule`) 50%, made of their case lemmas' kernel checks (`ck`, 38.5%) and their building (`lemma_n`, 11%);
  - the 296 laws (`check_laws`) 7.5%.
  - `Space::push` is 5.4% here, so growth is not a steady-state cost.
- **Interning is the largest single cost:** `Spaces::mk` is 37% inclusive and 19% self.
  - 384 of its 542 self samples (13.4% of all busy samples) sit on one instruction. It follows the load of the region table's first control group in `region.find` (`spaces.rs:317`, `Group::load` in hashbrown's `find_inner`), which is a cache miss on the probe.
  - hashbrown's find closure, which reads the bucket's stored hash and on a match the node, adds 10.6%.
  - `mk`'s callers: `inst_rec` 23.4% of busy samples, `app` 4.9%, `shift_unchecked` 2.3%. So instantiation's hash-consing in a large region is about a quarter of the run.
- **What it points at:** the cost per `mk` is about three random cache lines (control group, bucket, node), not instructions. The census entries above give the volumes on rule 33: 19-21% of built nodes are not in the table when it drops, and 87% of `inst` entries are never hit. So building fewer transient nodes is the lever on `mk`, not cheaper probes. Candidates, unmeasured:
  - a software prefetch of the control group, issued as soon as `hash(n)` is known;
  - instantiation that does not intern intermediate spines (`closed_prefix_spine` is 45% inclusive) where only the head normal form is kept;
  - for the large-page stalls: count how often they hit a sweep's processes before choosing between keeping large pages and a smaller reserve.

**Instantiating only the head would save little (2026-10-14; probe reverted, no patch kept).** `proof_cost_split` on fb5c176, with a probe at each of the four beta sites. Per site, it counted the `mk` calls in the instantiation, the region nodes the instantiation newly built, and how many of those the reduced result still reaches. The reduced result is the whnf, or for `hnf_rc` its head normal form.

| site | frames | `mk` calls | new nodes | reached by the result |
|---|---|---|---|---|
| `whnf_step`, one argument | 57,279 | 175,608 | 65,616 | 768 (1%) |
| `beta_spine` | 15,576 | 174,793 | 33,024 | 23,783 (72%) |
| `closed_prefix_spine` | 293,670 | 1,272,208 | 639,215 | 633,967 (99%) |
| `hnf_rc` | 261,280 | 2,403,958 | 1,728,809 | 1,382,575 (80%) |
| all four | 627,805 | 4,026,567 | 2,466,664 | 2,041,093 (83%) |

- **The run made 10.1 M `mk` calls; 4.27 M of them (42%) are inside `instantiate_n`,** and the four sites account for 4.03 M of those. Instantiation's calls are more often new nodes (61%), which fits their larger share of `mk`'s time in the profile above (23.4 of 36.6 points).
- **The bound:** only the 425,571 unreached nodes (17%) could be skipped by instantiating just what the head needs. That is 4.2% of all `mk` calls, so at most about 2% of the run, even before paying for the closures a lazy instantiation needs.
  - "Reached" means kept in the result, not read later. A fully lazy, environment-based machine could skip more. But hash-consed equality compares built nodes, so `conv` would build most of them anyway.
  - The one-argument beta in `whnf_step` throws away 99% of what it builds: a Church boolean picking a branch. But it is only 2.7% of these nodes.
- **Verdict: dropped.** `mk`'s cost is the price of each interning, not wasted work. What is left is the price per probe: a software prefetch of the region table's control group, issued as soon as the node's hash is known (unmeasured).
- The build took 3,561 ms under the probe (its reachability walks), against about 1,900 unprobed; the counts are deterministic.

**How often the large-page stall hits a sweep (2026-10-14).** Six full sweeps (`sweep_job.ps1`, salt 1, `mines own cold pooled`, 178 processes each) on fb5c176, alternating large, normal, normal, large, large, normal pages. RTP off, load 14-22%. `sweep_job.ps1` now also prints the job's kernel time.

| pair | large: job CPU / kernel / wall | normal: job CPU / kernel / wall |
|---|---|---|
| 1-2 | 57.3 / 23.02 / 40.5 s | 54.4 / 20.17 / 37.3 s |
| 3-4 | 53.1 / 22.55 / 38.3 s | 52.8 / 20.13 / 37.2 s |
| 5-6 | 52.9 / 19.69 / 37.1 s | 51.8 / 19.97 / 36.7 s |

- **Normal pages give a flat 20.0-20.2 s of kernel time.** Two of the three large-page sweeps took 2.4-2.9 s more; the third took none. That is about one `proof_cost_split`-sized stall per sweep, or the per-process commit below plus noise; these runs cannot tell the two apart.
- **Large pages lost all 3 pairs on job CPU** (by 0.3-2.9 s), against winning 3 of 3 by about 4% when adopted. One reading: the adopted gain was within the pairs' spread. The job's peak memory is 545-609 MB against 380-382 MB.
- `proof_cost_split`'s 12% gain from large pages is unaffected: it is one long process.
- **Large pages cost every process an up-front commit.** An empty launch of the test exe (a test name matching nothing, 20 per arm in a job object, `floor_job.ps1` in the scratchpad, not kept) took 3.9-23.4 ms of kernel time per process with large pages (median 7.8, 14 runs; all reserved 64 MiB, see below) against 2.3-5.5 ms without (median 3.9, 3 runs), at loads up to 94%. About 4 ms more for each of 178 processes is about 0.7 s a sweep.
  - A smaller reservation can't cut it: `MIMALLOC_ARENA_RESERVE=8MiB` still reserved 65,536 KiB (`MIMALLOC_VERBOSE=1`), so 64 MiB is the floor as built.
  - A bare number there is read as bytes ("8192" is 8 KiB, rounded up to the same floor).
- **Decided: `driver::sweep` turns large pages off for its children** (`MIMALLOC_ALLOW_LARGE_OS_PAGES=0` in the environment it passes them). Its machine-state line now runs with that environment, so `pages=` reports the children's pages. Single long runs (`proof_cost_split`, the law checks, loops) keep them.
  - A sweep on the change: `pages=normal`, 1.26 M faults and a 270 MB peak process (the normal arm's), and outputs identical to round 1 apart from the seconds column.
  - Its timing is void: load 78-99%.
- **Kernel time is 37-40% of the sweep's CPU in both arms,** about 112 ms per process, as Windows accounts it. That accounting turned out to be unreliable (last bullet).
  - Not the launch: an empty launch takes 2.3-5.5 ms.
  - Not page faults alone: normal pages took 1.33 M faults and large 0.56 M, at the same 22 s of kernel time.
  - samply doesn't see it. A profile of the sweep (a throwaway wrapper test setting its environment, reverted) has only 8.0% of busy samples with a kernel-mode leaf, about 4.4 s of 54 s. The single-process `proof_cost_split` profile shows the same gap: 2.1% kernel-mode leaves against 10-22% of its accounted CPU.
  - A pure user-mode loop is charged 3% kernel time (0.16 of 5.0 s), so the accounting isn't simply biased. Sampling the machine's privileged-time counter during a sweep was swamped by other sessions' 14.6% baseline.
  - **Resolved (2026-10-14): the accounted kernel/user split is unreliable on this machine; the sweep doesn't spend 40% in the kernel.**
    - **xperf trace of a salt-1 sweep on 10b68ad** (`sweep_xperf.ps1`, run elevated by the user: sampled profile with stacks, context switches, all page faults, virtual allocations; no lost events).
      - The job reported 50.8 s CPU, 20.6 s of it kernel, and 1.37 M faults.
      - The profile saw 48.3 s in the sweep's 166 processes, so the totals agree.
      - Only about 4.5 s of that was in kernel modules (`ntoskrnl.exe` 3.9 s, `Ntfs.sys`, `ahcache.sys`, `vgk.sys`, `FLTMGR.SYS` and the GPU driver the rest). The rest was in the test binary, which agrees with samply.
    - **Not page faults:** touching fresh committed memory costs about 0.5 µs per demand-zero fault, so 1.37 M faults are under 1 s.
    - **The split moves between identical runs:** eight `proof_cost_split` runs were charged 0.11-0.61 s of kernel time, while kernel plus user stayed at 2.70-2.91 s.
      - Turning mimalloc's purging off (`MIMALLOC_PURGE_DELAY=-1`) changed nothing (old 0.11-0.47 s, new 0.16-0.61 s), so decommits and the TLB flushes they cause aren't it.
      - Windows charges whole timer ticks of time to a thread's kernel or user mode, and the machine runs under the hypervisor (virtualization-based security is on, no services under it). What misattributes the ticks is not known.
    - **Consequence:** compare total CPU (kernel plus user), never kernel time alone, as `cpu_ab.ps1` and `sweep_job.ps1`'s `jobcpu` already do. Where the time actually goes, use samply or xperf samples.

**Prefetching the region table's control group: neutral, not adopted (2026-10-14; reverted, no patch kept).** `Spaces::build` issued a `_mm_prefetch` (T0) of the region table's first control group as soon as the node's hash was known. That is before the persistent lookup and the region lookup, which "Where `proof_cost_split` spends its time on B" found to be a cache miss worth 13.4% of busy samples.
- **Reaching the control bytes:** hashbrown 0.16.1 has no prefetch hook. But an `OccupiedEntry` from `insert_unique` gives its entry's address and bucket index, and the entries lie downwards from the control bytes. So the control array starts at the entry's address plus (index + 1) × 8 B, refreshed on every insert since a resize moves it. The group is at that start plus (`spread(h)` & bucket mask).
  - This depends on hashbrown's undocumented layout. A debug check (the inserted bucket's control byte equals the hash's top 7 bits) held across all 126 kernel unit tests.
- **`proof_cost_split`, prefetch on against `NO_PREFETCH=1`, same binary** (`cpu_ab.ps1`, 8 alternating pairs, load 58% at the start and 24% at the end, RTP off):
  - CPU median 2.59 s on against 2.61 s off; prefetch won 3 of 8 pairs.
  - Build median 1,762 against 1,764 ms.
- **Why nothing:** the prefetch issues no earlier than the out-of-order core already issues the load. The lookup's address depends only on the hash, which is ready at the same point. When a node has persistent children, the region lookup sits behind a branch on the persistent lookup that is almost always predicted, so it already runs speculatively in parallel. The two misses after the control group (the entry, then the node to compare) depend on the first one and cannot be prefetched from the hash.
- **Having the hash earlier is not possible (checked 2026-10-14).** A node's hash is computed from its children's `Ref`s, and `inst_rec` calls `mk` as soon as the last child returns, so the hash exists no sooner. The last child's `Ref` comes out of its own lookup, so the misses form a dependent chain: child lookup, then the parent's hash, then the parent's lookup. A hash of content rather than `Ref`s doesn't help either, since computing one for a child not yet built means walking it.
- **Placing nodes by recency would not help (counting probe on 3e5c74b, reverted, no patch kept).** The idea was to put the bucket of a node near the buckets of nodes built just before it, so lookups touch a warm part of the table. A probe counted `proof_cost_split`'s 10.1 M region builds by how many builds ago the node's newest region child was made:

  | newest region child made | region hit | new node |
  |---|---|---|
  | no region child | 786,287 | 510 |
  | 1 build ago | 0 | 2,591,264 |
  | 2-16 | 200,877 | 121,482 |
  | 17-256 | 225,224 | 105,782 |
  | 257-4K | 641,273 | 201,982 |
  | 4K-64K | 1,629,312 | 273,976 |
  | over 64K | 3,167,735 | 153,845 |

  - The new nodes total 3,448,841, the region's size; no build hit the persistent space.
  - Hits are mostly over old children (3.2 M over 64K builds ago), so recency gives them no locality. Recent children are mostly new nodes, which the next point handles without the table. Dropped.
- **Skipping the lookup that must miss: adopted (2026-10-14).** A node whose region child has no parent yet cannot already exist. `parents` is raised only when a node is pushed, and persistent nodes have no region children. 2,591,264 builds (26% of all, 75% of the new nodes) fall in the "1 build ago" row, where that holds by construction; more may fall in other rows. So `Spaces::build` skips `region.find` for them, which is safe for Invariant I. A debug assertion that such a node really is absent holds in all kernel unit tests. The insert still touches the same control group, but nothing waits on it, since the new `Ref` is the array length.
  - `proof_cost_split`, skip on against off in the same binary (`cpu_ab.ps1`, two rounds of 8 alternating pairs, RTP off):

    | round | load | CPU median, off / on | build median | skip won |
    |---|---|---|---|---|
    | 1 | 33% at the start, 45% at the end | 2.84 / 2.64 s (−7%) | 1,954 / 1,797 ms (−8%) | 6 of 8 |
    | 2 | 28% at the start, 33% at the end | 2.84 / 2.65 s (−7%) | 1,935 / 1,830 ms (−5%) | 7 of 8 |
  - **Full salt-1 sweeps: no detectable effect (2026-10-15).** Twelve sweeps of the same binary in job objects, `SKIP` off and on alternating (two sets of 3 pairs, load 16-39%, RTP off). Job CPU median 51.5 s off against 52.2 s on (+1.5%); the skip won 2 of 6 pairs. Identical sweeps vary about ±10% (46.7-55.7 s off, 49.5-58.8 s on), so the sweep cannot resolve a few percent. It likely spends less of its CPU in large regions than `proof_cost_split`, though that is not measured. Kept: it is sound, and it wins on the kernel-bound benchmark.

**mimalloc against the system heap, after the id-arena port (2026-10-14; probe reverted, no patch kept).** The question was whether to drop mimalloc and do its useful parts directly, now that the kernel keeps its nodes in a few large arrays instead of one block each. Two test binaries were built from 193a1a5. One is as committed. The other has the test crate's `#[global_allocator]` removed, and `machine::large_pages_option` made to return false, since it calls into mimalloc. `MIMALLOC_VERBOSE=1` printed 50 lines from the first and none from the second. RTP off.

| run | mimalloc | system heap | system's cost |
|---|---|---|---|
| `proof_cost_split`, mimalloc on large pages (8 pairs, load 10%) | CPU median 2.26 s, build 1,552 ms | 2.81 s, 1,834 ms | +24% CPU; mimalloc won 8 of 8 |
| `proof_cost_split`, mimalloc on normal pages (8 pairs, load 11%) | 2.22 s | 2.47 s | +11%; mimalloc won 7 of 8 |
| full salt-1 sweep (3 pairs, load 3-25%) | job CPU 43.9 / 46.5 / 58.9 s, wall 32.7-41.4 s | 67.9 / 72.6 / 81.0 s, wall 43.7-50.2 s | +38% to +65%; mimalloc won 3 of 3 |
| sweep memory | peak process 285-295 MB, job 487-550 MB | 208-209 MB, 299-302 MB | mimalloc uses 40% / 70-80% more |

- **Most of mimalloc's value is outside the kernel.** The sweep, which also mines, scores and builds proofs, gains far more than `proof_cost_split`'s check. Those parts allocate many small, short-lived objects, which is what mimalloc is fast at. Replacing it means writing a general allocator, so dropping it is ruled out.
- The two `proof_cost_split` runs are not comparable with each other (they ran one after the other, not interleaved), so they say nothing new about large pages.
- The system heap faults more (1.79 M against 1.25 M per sweep) but peaks lower. mimalloc keeps freed memory for reuse instead of returning it.
- **Still open:** moving the id arena's own arrays and table onto reserved address space, committed as they grow, so they never move and can use large pages on their own (option 1 of the allocator question). mimalloc stays the global allocator either way. Its upper bound was then measured and found to be zero; see the next entry.

**Arrays that never grow: no measurable gain, so reserved storage for the id arena is parked (2026-10-14; probe reverted, no patch kept).** This spike bounds what storage that never moves could buy. A probe on ef75b36 reserved the region's five arrays and its table for `PRESIZE` nodes when `Spaces::open` runs, so nothing grew or was copied. `proof_cost_split` has one region, which ends at 3,448,841 nodes; it grows to capacity 4,194,304 and 4,194,304 table buckets. `PRESIZE=3500000` was compared against the same binary without it (`cpu_ab.ps1`, two rounds of 8 alternating pairs, RTP off).

| round | load | CPU median, growing / presized | build median | presized won |
|---|---|---|---|---|
| 1 | 20% at the start, 53% at the end | 2.57 / 2.47 s (−3.7%) | 1,799 / 1,641 ms | 6 of 8 |
| 2 | 10% at the start, 36% at the end | 2.36 / 2.55 s (+8%) | 1,602 / 1,732 ms | 2 of 8 |

- Over the 16 pairs presizing won 8, and the two rounds disagree in sign by more than either effect. The cost of growth (about 22 doublings, each copying the arrays and rehashing the table once) is below this benchmark's noise, about ±5% here.
- Reserved storage could also give the arena large pages of its own. That is not measured by this probe, but mimalloc already serves these arrays from large pages in `proof_cost_split`, so there is little left to gain.
- **Parked:** option 1 of the allocator question. Revisit only if a profile shows growth (`reserve_rehash`, `memcpy` from `Vec` growth) as a visible share of the build.

**Where a sweep spends its time: the miner's boxed `Term`s, not the kernel (2026-10-15; probe reverted, profile not kept).** samply recorded one salt-1 sweep on 744b31d, all 178 processes, through a throwaway wrapper test that set the sweep's environment. The binary was built with debug info, and frames were named with `llvm-symbolizer`. The run had 48,478 busy samples (wait leaves dropped); load was 11% at the start.

| inclusive share of busy samples | |
|---|---|
| `rewrite::rewrite` (the miner's rewriting, mostly under `rule_miner`'s scoring) | 50.3% |
| mimalloc (`mi_malloc_aligned`, `mi_free`, ...) | 20.6% |
| `machine::tree_encoding` | 13.5% |
| `Term` clone | 13.3% |
| SipHash (`std` `DefaultHasher`, hashing `Term`s) | 11.9% |
| the kernel (`tatic::kernel`) | 10.9% |
| `Term::interp` | 9.3% |
| `rule_set_kernel_check` | 8.0% |
| `Term` drop | 6.9% |
| `inst_rec` (`Spaces::build` is inlined; `Space::push` 1.7%) | 4.1% |

- **This is why kernel changes don't show in a sweep.** The kernel is 11% of it, so the must-miss skip's 7% on `proof_cost_split` is under 1% of a sweep.
- **`Term` is a tree of `Box`es with derived `Hash`/`Clone`.** Cloning, dropping and SipHashing it are O(size) each time, and their allocations are most of mimalloc's share.
- **Call sites (the nearest `church_bv` frame, with inlining):**
  - **Copying the rewrite memo between candidates.** `RewriteMemo::filtered` clones and rehashes every entry it keeps. `absorb` (search.rs, `score_rule`) re-inserts all of `grown`, seed entries included. About 3.0% of busy samples hash and 2.9% clone there (the `HashMap` collect and extend sites), before drops and frees.
  - **Memo lookups in `rewrite_memo`.** The key's `t.clone()`, the trace copies and the result clone are about 2.4%; hashing 0.9%.
  - `rewrite::terms` (building candidate terms) clones 3.6%; `rewrite`'s path push 0.9%; `match_pat` 0.8%.
- **Two directions were open:** hash-cons `Term` (as the kernel did with `Expr`), or, narrower, seed each scoring with a read-through view of the worker's memo instead of a filtered copy. Hash-consing covers the memo copying too, so it was built first.
- **Hash-consed `Term`: adopted (2026-10-15, branch `term-hashcons`).** A sweep cuts its CPU by 30%, and its outputs are unchanged.
  - **Few distinct terms (probe, reverted).** A fingerprint of every `Op` node dropped, over a salt-1 sweep: at most 57,272 distinct per process (the driver), 32,086 in the largest miner (`lib_cmp3d`) against 64.8 M node drops, 1.26 M over the sweep's 171 processes. So terms are shared about 2,000 times, and never freeing a node costs a couple of MB per process.
  - **Design.** `Term` is `Copy`, a `&'static Node`. Leaves are statics; `Op` nodes are interned in a 16-shard `Mutex<hashbrown::HashTable>` with an unseeded hash of the operator and the child addresses, and leaked. Equality and `Hash` take the address; `Ord` is structural, the old derived order (pinned by a test). Spec and plan: `docs/superpowers/` (local).
  - **A latent underflow surfaced.** search.rs's straggler candidates renumbered `V(i)` to `V(i - 4)` before checking that no variable was below 4, so release builds wrapped and then dropped the term. `Term::v` asserts its index, so the check now comes first; the candidates are the same.
  - **Outputs identical.** Salt-1 and salt-2 sweeps (`SWEEP="mines own cold pooled"`, `hc_seq.sh`): `cold.tsv` and `mines.tsv` equal apart from seconds, every log equal apart from timings and the test harness's filtered count, `LEMMA_CACHE` lines included.
  - **Twelve full salt-1 sweeps, old and new alternating** (`hc_rounds.ps1`, sweep_job.ps1; load 2-11% except 42% at the first start, RTP off): job CPU median 39.4 s old against 27.7 s new (-30%), wall 30.3 s against 24.6 s (-19%); new won all 6 pairs.
  - **The new profile** (same method, 26,010 busy samples against 48,478): `Term` clone and drop are gone, SipHash 7.4% (the miner's own maps), mimalloc 17.3%, the kernel 15.6%. The top self functions are now `Term::interp` 15.5% and `Term::max_var` 8.3%, both O(size) walks a node could cache, then `Term::op` (interning) 5.5%. `rewrite_memo` is 44.7% inclusive.
- **Per-node size and variable set: adopted for the simpler code, about 3% of sweep CPU (2026-10-15, branch `term-attrs`).** Each interned node carries its size and a 64-bit mask of its variables, made once from its children; `size`, `max_var` and `has_var` read them instead of walking the tree (a test checks them against a walk). Salt-1 and salt-2 sweeps give identical outputs. Twelve alternating salt-1 sweeps against the hash-consed build (load 4-25%, RTP off): job CPU median 28.7 s against 27.75 s (-3%), new won 5 of 6 pairs; wall unchanged (25.0 s against 25.25 s). The profile's 8.3% for `max_var` promised more than this; why was not checked (no new profile).
- **Profile at 932b561 (2026-10-15; samply of a salt-1 sweep, debug-info build, 22,756 busy samples, profile not kept):** `Term::interp` 16.7% self, 18.3% inclusive, all of it under `counterexample_in`. Of that, 14.2% comes from `tree_encoding`'s `plausibly_equals` screen and 3.4% from `refute`. `tree_step` screens one `t1` against about 50 candidates, and each screen evaluates both sides on the same 204 tuples, so `t1` is evaluated about 50 times over. Next: `Term::op` 7.2% self, 5.8% of it from `terms(k, false)`, which `tree_step` rebuilds on every call. Then `SigMemo::id` 7.5% (it walks the whole term and hashes a structural key with SipHash before it looks anything up), mimalloc about 12%, and SipHash about 3%. `max_var` no longer shows. No frame is named `RewriteMemo::filtered` or `absorb`. They may be inlined, and hashbrown iteration and `(…) -> Rc` inserts take 2.7% and 1.9% inclusive, so memo copying is at most a few percent.
- **`ValueMemo`: adopted, -16% sweep CPU (2026-10-15, branch `value-memo`).** A term's values on a fixed list of inputs are memoized per interned `Term`, each vector built from its children's. There are two input lists. The screen's is the corners plus 202 pseudo-random tuples per `(n, k)`, stored as `u128`. The exhaustive one replaces `SigMemo` and is stored as `u8`. `counterexample_in` compares two stored vectors, so `tree_step` no longer evaluates its fixed side once per candidate. `terms` is built once per thread for each set of arguments. A test checks the screen against the old per-tuple screen and the exhaustive values against `interp`. Salt-1 and salt-2 sweeps give identical outputs. A probe (reverted) counted at most 4,096 to 8,191 screen vectors per process, over 6 to 8 `(n, k)` keys, so at most about 27 MB. Twelve alternating salt-1 sweeps against 932b561 (load 14-36% from other work, RTP off): job CPU median 38.45 s old against 32.15 s new (-16%), new won 6 of 6 pairs; wall 32.45 s against 28.3 s (-13%). Page faults rose from about 1.20 M to 1.53 M per sweep, and peak process memory moved within noise (263-316 MB for both).
- **Profile at 891e9a9 (2026-10-15; samply of a salt-1 sweep, debug-info build, 25,361 busy samples, load 21% from other work, so sample counts don't compare with the run at 932b561; profile not kept):** the screen under `tree_step` is still 17.3% inclusive (`tree_step` 20.4%). Its parts:
  - `ValueMemo::fill` 9.3%: new `t1` terms get all 204 values, 5.8% of it spent building the vectors through mimalloc's zeroed, 16-byte-aligned path.
  - `counterexample_in`'s own frame 4.4%: hash lookups. `fill` checks `contains_key` and then indexes, and `first_difference` indexes both sides again.
  - About 3%: the failing input vector that `counterexample_in` builds, which `plausibly_equals` (the `tree_encoding` path) then discards.
  
  By phase: the rule miner is 71% inclusive (its `closure$32` 39.8%), `rewrite_uncached` 40.7%, `add_tree_law` 17.1%, `prove_rule` 15.2%, `pool_conjectures` 2.8%. mimalloc is about 11% self, SipHash 1.6%. `ValueMemo` under the rule miner and `pool_conjectures` is 4.3%.
- **`ValueMemo` arena and `differs_in` (2026-10-15, branch `screen-tune`): -7% CPU, but +35% peak job memory.** `ValueMemo` keeps every vector end to end in one `Vec`, with a `Term` to index map: a new term allocates nothing of its own, and a known one costs one lookup instead of up to four. `differs_in` answers the screen without building the failing tuple; `plausibly_equals`, `is_law` and `machine_fallback`'s scoring screen use it. The `u64` idea was dropped: the arena already takes the screen off per-term 16-byte-aligned allocation, and `u64` would need a branch on the width. Salt-1 and salt-2 sweeps give identical outputs. Twelve alternating salt-1 sweeps against 891e9a9 (load 14-43%, RTP off): job CPU median 29.65 s old against 27.6 s new (-7%), new won 5 of 6 pairs and tied the sixth; wall 26.15 s against 25.45 s (-3%). Peak job memory rose from 374-449 MB to 577-602 MB, and page faults from about 1.53 M to 1.94 M per sweep. The likely cause is the arena `Vec` doubling: its capacity can be twice what is in use, and each grow briefly holds both copies. The exhaustive memos are the big ones: `pool_conjectures` over three variables stores 2^(3n) bytes per term.
- **`ValueMemo` in fixed 64 KB blocks (2026-10-15, branch `screen-tune`, adopted): -9.5% CPU against 037813f, memory back to before.** The vectors sit end to end in blocks that are never grown or copied. Four timings of twelve alternating salt-1 sweeps each (RTP off):
  - Blocks with the op loop indexing `blocks[b][i]` per element (607e6f7) against 037813f (load 0-8%): job CPU median 19.1 s against 19.35 s, 3 pairs each. Memory was back (peak job 397-455 MB against 393-449 MB), but the gain was gone.
  - The flat arena (bc080e7) against those blocks (load 0-5%): 17.55 s against 18.55 s, flat won 5 of 6. So the layout cost about 5%, not the load.
  - The op loop over slices instead (`split_at_mut`, one zipped loop) against the flat arena (load 6-10%): 21.95 s against 21.15 s (-3.6%), blocks won 5 of 6; peak job 394-459 MB against 541-603 MB, faults 1.50 M against 1.93 M.
  - That build against 037813f (load 6-13%): job CPU median 23.1 s against 20.9 s (-9.5%), new won all 6 pairs; wall 22.1 s against 21.3 s; peak job 428-454 MB against 404-456 MB. Salt-1 and salt-2 sweeps give identical outputs.
  - The machine's speed drifted between timings (the same build ran 18-23 s), so only the within-timing comparisons count.
- **Profile at bc080e7 (samply of a salt-1 sweep, 26,836 busy samples, load 28%, profile not kept):**
  - The rule miner's `closure$32` (35.2% inclusive) is `score_laws` (search.rs): `rewrite_plan` for every law under each candidate's rule set, 29.5% of it.
    - Inside that: `rule_step_in` 14.7%, `tree_step` 11.3% (its screen 9.6%).
    - `ValueMemo::fill` is 18.2% inclusive overall: screens 10.6%, `pool_conjectures` 4.2%, the miner's pool index 3.4%. It includes 2.4% in `Vec` growth (`finish_grow`, aligned realloc).
  - `add_tree_law` 18.3% and `prove_rule` 16.4% sit outside the scoring. They are mostly `tree_proof`'s `shared_lemma`, about 11% of it in kernel checking (`ck`, `check_in`, `conv`, `whnf`).
- **The miner's trace records which rule fired (2026-10-15, branch `trace-fired`): -5.4% CPU, identical outputs.** The Open item below said `score_laws` re-rewrites every law per candidate. It does not: a candidate re-rewrites only the laws whose trace has a term its left side matches (`affected`), about 6% of (law, candidate) pairs, and seeds them with the memo entries it cannot change. The lever was the test itself.
  - `RULE_TRACE` now holds, for each term `rule_step` was asked about, the first rule that fired on it (`Fired`: none, a built-in rule, or a run-time rule). A candidate can only change a term it matches where it comes before that rule in run-time order. That order is most specific first (`set_extra_rules`, `run_order`), so a candidate is not tried last. A preference naming the candidate as a winner falls back to the old test. Memo entries computed with the candidate in force keep the old test, since the candidate may be what fired there.
  - First try, unsound: a yes/no "a rule fired" flag, assuming the candidate is tried last. It changed the mined rules on every cold run. A throwaway check that re-scored every law from scratch under each candidate found 222 laws it wrongly kept, all with a term where a less specific mined rule fired before the candidate. It would have cut the affected pairs to 69%; the sound test cuts them to 80% (175,183 of 218,360, same states).
  - The same check found that `lib_cmp3d`'s `mine_ref` keeps a memo-seeded evaluation of law 168 that differs from a fresh one (51 times), with or without this change; cause and fix in the next entry.
  - Salt-1 and salt-2 sweeps against a2dca77 give the same rules and outputs (only the miner's counters and timings differ): candidates scored 24,778 to 22,396 (the bound is tighter), law re-evaluations 393,684 to 321,499.
  - Timing, twelve alternating salt-1 sweeps against a2dca77 (load 0-4%, RTP off): job CPU median 17.7 s against 16.75 s (-5.4%), new won all 6 pairs; wall 18.7 s against 18.6 s. A first version that compared `run_order` keys (two `show()` strings each) per traced term lost all 6 pairs (19.65 s against 20.4 s). Ranking the rules once per round, and matching before comparing, fixed it.
- **Memo replays that a fresh rewrite would cut (2026-10-15, branch `memo-path`): fixed, identical outputs, CPU a tie.** Law 168 in `lib_cmp3d`'s `mine_ref`: its memo-seeded evaluation under the chosen rules was (fixed) where a fresh one was (not fixed).
    - Cause, on main 4385c7f (a throwaway probe redid every memo hit without the memo and compared, salt-1 sweep, then reverted): 40 hits differ, all in `cmp3d` mines (`lib_cmp3d/mine_ref` 18, `cold_cmp3d_{1,2,3}` 7, 2, 13), all on `lt` terms, and every one is a cycle cut. An entry is stored only when its own call made no cut, but whether a call cuts depends on `REWRITE_PATH`, the terms being rewritten further out. An entry made where the path was short is replayed inside a call whose own term is now on the path; a fresh rewrite cuts there and stops (fewer steps: 1-6 against 2-11), the replay keeps going. No mismatch came from the budget, fallbacks or the rules. So the memo makes `rewrite` depend on which context first computed a term, and the memo-seeded and fresh evaluations of law 168 differ for that reason.
    - Fixes: any cut against the path (an exact repeat as well as an embedding) has this dependence, so changing the cut test does not help. A path-free cut needs termination by a term order, which is `PERM_ORDER=lpo` ("Cycle cut; lpo and a cycling penalty are negative results"), so not reopened. The fix taken: entries record the terms their call rewrote, and a hit is replayed only where the current path cuts none of them.
    - Check: the same probe on the fix found 0 mismatches in 2,287,007 hits (salt 1). Test `memo_hits_match_fresh_rewrites_under_cycling_rules` (an entry made alone, replayed under a path that cuts it) fails without the fix.
    - Outputs: identical to 4385c7f on salts 1 and 2 (416 files each), so the 40 bad hits never changed a mined rule.
    - Reach: a throwaway counter on the fix (reverted) printed each hit the check turns away, over every stage and family (`mines:sbo3,add3,mix3,cmp3d,u3 own cold cross pooled mixed`), salts 1 and 2. Turned away: salt 1 `lib_cmp3d` 31, `lib_u3` 12, `cold_cmp3d_{1,2,3}` 8, 3, 13; salt 2 104, 2, 5, 5, 3. All on `lt` terms, only in mines run under the cmp3d or u3 laws (u3 has `lt` laws too); none in add3, sbo3, mix3 or any own, cross, pooled or mixed loop. So far only `lt` chains reach it, the kind the growth cut was built for ("Growth cut" under "Miner speedups").
    - Effect: a second throwaway probe (reverted) compared each turned-away replay with the fresh rewrite done in its place, over `mines:cmp3d,u3 cold:cmp3d`. Salt 1: 64 of 66 would have returned a different term; salt 2: 55 of 115 (`lib_cmp3d` 40 of 100, the rest only a cut of an already normal term). So most bad replays changed the normal form, and law 168's flip shows they reached law evaluations, but the mined rules came out the same on both salts. The counts per stream differ a little from the full-sweep counter's (salt 2 `lib_cmp3d` 100 against 104, `lib_u3` salt 1 10 against 12) for the same mines.
    - Why the counts drift: the same sweep run twice (`mines:cmp3d,u3`, salt 2) turned away 102 and 98 hits in `lib_cmp3d`, while every output file matched byte for byte (counter lines and timings aside); `mines` alone gave 102 and 104. The sweep scores candidates on 6 workers (`threads: 6` in `sweep`), each with its own `RewriteMemo` for the round, fed from one queue, so what a worker's memo holds depends on thread timing. With replays exact that changes only hit rates; before the fix it could in principle have changed outputs from run to run.
    - Guard: in debug builds (`cargo test` without `--release`) `check_replay` redoes every memo hit without the memo, under the same path and budget, and asserts the same term, steps and fallbacks. With the path check in `fits` disabled it fails at once on `memo_hits_match_fresh_rewrites_under_cycling_rules`. `filtered_memo_entries_hold_under_an_extra_rule` used to replay a stale memo on purpose to show the filter matters; it now compares the base rules' results with the fresh ones instead, which is what that replay returned. Release builds are unchanged; the debug church_bv suite takes 30 s.
    - Timing, twelve alternating salt-1 sweeps against 4385c7f (load 3-55%, RTP off): job CPU median 23.45 s against 22.65 s, new won 3 of 6 pairs; a tie within the noise. Peak job memory 375-450 MB against 397-452 MB. A rerun of 24 (two sets of twelve, RTP off): in the quieter set (load 8-14%) job CPU median 22.55 s against 22.4 s (-0.7%), new won 4 of 6 pairs; in the noisier one (load 9-63%) 3 of 6; 7 of 12 in all. The check costs nothing measurable.
- **Profile at f447a57 (2026-10-15; samply of a salt-1 sweep through a throwaway wrapper test, debug-info build, 19,579 busy samples against 25,361 at 891e9a9, load 10% at the start, RTP off; profile not kept):** the miner is no longer most of it.
  - The kernel (`tatic::kernel`) is 24.9% inclusive, up from 11-16%: `rule_set_kernel_check` 10.3%, `inst_rec` 9.5%, `Space::push` 4.3%. Kernel speedups now show in a sweep.
  - `rule_step_in` is 15.9% inclusive, and its per-rule closure 13.5%. Most of that is overhead around the match, not the match: allocation 4.7% (the rule list `all`, each rule's `sub` vector, the instance's substitution), `rule_permutative` recomputed on every match 2.6% (`rule_order_ok`, `rule_tied`, `rule_weight`; a property of the rule), the closure's own frame 3.3% (`ablated` compares strings for every rule tried). `match_pat` is 1.9%.
  - SipHash 4.6% (`hash_one` and `write`; 9.2% with every frame under `DefaultHasher`): std `HashMap`s and `HashSet`s keyed on `Term`, whose `Hash` is already the node address. Sites: the rule miner's scoring closure 2.7%, `rewrite_memo`'s map 2.1%, `closure$32` 1.7%.
  - `ValueMemo::fill` 7.4% self (two widths), `tree_step` 12.1% inclusive, mimalloc 16.8%, OS kernel 15.9% leaf (`NtFreeVirtualMemory` about 2% of busy, process and thread creation about 1.3%).
  - Levers, by size: (1) one precompiled rule table per rule set, made in `set_extra_rules` with the fixed rules: ablation and permutativity decided once, rules bucketed by root operator, the substitution on the stack, which covers the allocation, `ablated` and `rule_permutative` shares (at most about 10%); (2) an address hasher (hashbrown's default, already a dependency) for the miner's `Term`-keyed maps (at most about 5%); (3) the kernel's `inst_rec`.
- **Rule table (2026-10-15, branch `rule-table`): lever (1), identical outputs, job CPU -10%.** `set_extra_rules` builds a `RuleTable` (`RULE_TABLE` replaces `EXTRA_RULES` and `RuleRef`): every rule with its variable count and permutativity decided once, and for each root operator, and for leaves, the indices of the rules not ablated whose left side can match such a term (a bare-variable left side goes in every bucket), in rule order. `rule_step` tries only that bucket, with the substitution in an 8-slot array on the stack (`rule_weight` already caps rules at 8 variables; the table asserts it). Preferences and `RULE_CONFLICTS` walk the same bucket, which holds every rule that can fire; the preference hop bound still counts all rules.
    - Outputs: identical to 883f50d on salts 1 and 2 (416 files each) but for two stderr lines (`LEMMA_CACHE starts empty`) swapped in salt 2's `lib_sbo3/mine_ref.log`, thread interleaving.
    - Timing, twelve alternating salt-1 sweeps against 883f50d (load 11-15%, RTP off): job CPU median 20.45 s against 22.75 s (-10.1%), wall 21.9 s against 23.1 s (-5.2%); new won all 6 pairs and every new sweep beat every old one. That is about the whole share the profile gave this lever.
- **Address hasher (2026-10-15, branch `rule-table`): lever (2), identical outputs, job CPU about -3%.** Every std `HashMap` and `HashSet` in church_bv keyed on `Term`s (or tuples or vectors of them) now uses hashbrown's default hasher (foldhash) instead of SipHash: `RewriteMemo`'s map, the miner's dedup sets (`seen`, `seen_pat`), `rivals`, `rank`, `picks`, `finished`, `TREE_LAWS`, `TREE_ENCS`, the machine parser's node map, `RULE_PREFS`, `RULE_CONFLICTS`, and the cold file readers. None is iterated in an order that reaches an output (`RULE_PREFS` is filtered into a set of winners, `RULE_CONFLICTS` is sorted before printing). Maps keyed on strings, byte vectors and `usize` kept std's hasher here (moved later: "The rest of church_bv's maps off SipHash"); `GenMemo` keeps its `Fx`.
    - Outputs: identical to the rule table on salts 1 and 2 (416 files each) but for one stdout/stderr line pair swapped in salt 2's `lib_sbo3/mine_ref.log`.
    - Timing, twelve alternating salt-1 sweeps against the rule table (load 6-16%, RTP off): job CPU median 19.15 s against 19.95 s (-4.0%), new won all 6 pairs; two old sweeps took 25.4-25.6 s against 19.3-20.0 s for the other four, likely outside load, and without them the medians are 19.15 s against 19.75 s (-3.0%). Wall 21.4 s against 21.5 s. Within the profile's 4.6% SipHash share.
- **Profile at a7b0719 (2026-10-15; samply of a salt-1 sweep, `SWEEP="mines own cold pooled"`, debug-info build, run through a small env-setting launcher instead of a wrapper test, so no repo change; 17,114 busy samples against 19,579 at f447a57, load 10% at the start, RTP off; profile not kept):** the rule table and the hasher did what the f447a57 profile said.
  - `rule_step_in` 4.3% inclusive (736 samples, from 3,113): `match_pat` 1.6%, `subst_pat` 0.6%, `Term::op` 0.5%. `set_extra_rules`, which now builds the table, is 1.1%.
  - SipHash 1.9% (from 9.2%, same bucket), spread thin: `rule_miner` 0.4%, `pool_conjectures` 0.3%, the lemma cache 0.7%, `moore_encoding` 0.2%. The next entry moves the maps among these off it too; the lemma cache's `exe_identity` (0.2%) keeps SipHash on purpose, since it hashes the exe once per process into a key other processes must reproduce, and hashbrown's default hasher is seeded per process.
  - `rewrite_memo` 22.3% inclusive (from 31.5%).
  - The kernel is 28.4% (4,860 samples, unchanged in absolute terms): `inst_rec` 10.9%, `rule_set_kernel_check` 10.6% (of it `law_proof` 5.6%, `check_laws` 1.8%), `Space::push` 2.7% self.
  - `ValueMemo::fill` 16.8% inclusive, 8.6% self, by nearest caller: `tree_encoding` 6.1%, the miner 5.6%, `pool_conjectures` 3.4%, `check_laws` 1.5%. `first_difference` is 11.2% inclusive (9.3% of it in `fill`), called from `tree_encoding` 7.8%, the miner 1.5%, `check_laws` 1.5%. `tree_encoding` is 12.5% inclusive.
  - hashbrown `reserve_rehash` 5.2% inclusive (3.4% self): `Space::push` 1.2%, the miner 1.5%, `rewrite_memo` 0.6%. Maps growing, not hashing.
  - OS kernel 18.9% of busy as leaf (`ntkrnlmp`), mimalloc 12.7%.
  - Where the kernel time comes from (follow-up on the same profile): `shared_lemma` is 17.2% inclusive, of which `ck` of new lemma proofs is 11.2% of busy, all from `tree_proof`. Every one is a first check: over the salt-1 sweep's 72 processes that report a lemma cache, 1,716 lemmas were built and 1,710 newly saved (2,288 hits), so neither worker threads nor loops check a lemma twice (the sweep already shares one lemma file, "One lemma file per sweep"). About 1.1 ms of CPU per lemma check (11.2% of 17,114 one-millisecond samples over about 1,716 lemmas). `inst_rec` (10.9%) has no single hot spot: it is `instantiate_n` under `hnf_rc` (6.4%) and `closed_prefix_spine` (3.5%), spread over `mk`, `Space::push`, `uses`, `inst_get` and rehashing, 0.5-1.6% each; `resolve` does not show, so Stage 3's parked raw-`Ref` walks are still not called for.
  - `ValueMemo::fill` (follow-up): the vectors are already memoized per term, so the cost is new terms, each 204 `u128` values made through `OP_INFO[o].word`, a function pointer called per element (`call_once` 4.3% under `fill`, `fill` 8.6% self). The per-element indirect call keeps the loop from inlining or vectorizing; one loop per operator (a `match` on `o` outside the loop) would. `tree_encoding` runs the screen (`plausibly_equals`) uncached on purpose, but its fills are memoized like any other.
  - Levers, by size: (1) the kernel (`inst_rec`, then `law_proof`'s checks); (2) `ValueMemo::fill`, most of it reached through `first_difference` from `tree_encoding`; (3) the OS share (process start-up and freeing memory across the sweep's 178 processes); (4) presizing the maps that rehash as they grow.
- **The rest of church_bv's maps off SipHash (2026-10-15, branch `hash-rest`): identical outputs, CPU a tie, kept for uniformity.** The std maps keyed on byte vectors, strings and integers (the miner's value index, `pool_conjectures`' groups, the machine's step and node maps, the lemma cache, `CLOSED`) use hashbrown's default too, so church_bv has no std `HashMap` or `HashSet` left but `GenMemo`'s `Fx` map, and no rule about which maps get which hasher. None is iterated in an order that reaches an output (`groups` is sorted after collecting, the lemma cache writes in its own order list).
    - Outputs: identical to a7b0719 on salts 1 and 2 (416 files each, no difference at all).
    - Timing, twelve alternating salt-1 sweeps against a7b0719 (load 0-7%, RTP off): job CPU median 14.3 s against 14.35 s, new won 3 pairs, lost 2, one even; one old sweep took 17.2 s, likely outside load. A tie, as the 1.9% the profile left on SipHash predicted. With the machine this quiet a whole sweep takes 14 s of CPU against 19-20 s at 11-16% load in the two runs before, so compare these changes only within a set.
- **Open:**
  - The other exhaustive `interp` loops (`eq_pos` in `prove_eq`, `conjecture_miner`, the shift check in machine.rs) are cold and still evaluate per tuple.

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

### cmp3d's library lost its general rules to the round cap (2026-10-11)
After the growth cut, cmp3d's ref mine (salt 1, 400 laws, 8 rounds) no longer picks `sub(sub(x, y), z) -> sub(x, add(y, z))` or
`add(sub(x, y), z) -> add(sub(z, y), x)`. Both are still candidates. After the four big rules (+32, +41, +34, +20 fixed) they are
worth little on cmp3d's own laws, and the 8-round cap ends the mine first: rounds 5-8 fix +6, +3, +3, +1. With 16 rounds they
come back in rounds 10 (+1) and 12 (+3). Rounds 13-16 fix nothing and only shrink terms. Seeding loops with that 16-rule library
(salt 1, total M; `driver::loop_stream` with `LOOP_MODE=ref ROUNDS=16`, then `driver::sweep` stages `cross:add3,sbo3 own:cmp3d`):

| seeded loop | 8-round cmp3d library | 16-round |
|---|---|---|
| add3 | 147 | 57 |
| sbo3 | 95 | 59 |
| cmp3d (own) | 68 | 60 |

The loops seeded from add3's and sbo3's libraries reproduced exactly (48, 46). A rule worth +1 on its own family can be worth
dozens of laws on another, so a family's mine can't judge transfer, and a round cap set for one family's laws trims general rules.
`driver::sweep` now runs every ref mine with 16 rounds (loops still mine 8 per batch). Rerun at salt 1 (stages `mines own cross
pooled:mix3`; cold loops don't use a library): add3's and mix3's mines stop by themselves at 8 and 2 rules (libraries unchanged),
sbo3's at 10 (two `or` rules added; own loop 35 to 31), and cmp3d's reaches the cap (mine 83 to 109 s). Every seeded total is
equal or lower; the changed ones are those above and sbo3's own.

**No cap (kept).** Uncapped, cmp3d's ref mine stops by itself at the same 16 rules (it stops once no candidate fixes a law or
shrinks the terms), so every library is identical. The cap still cut 8 of the loops' per-batch mines at 8 rules. Removing it
everywhere (`RULEMINER_ROUNDS` and the driver's `ROUNDS` now default to no cap) left every seeded total equal or lower (sbo3 from
add3's and cmp3d's libraries 48 to 47 and 59 to 58) and cut cmp3d's cold loops from 180 to 167. A stop rule such as "two rounds
without a fixed law" was not needed. The full sweep (`mines own cold cross cold:mix3 pooled:mix3`) took 638 s.

**Scoring on other families' laws (mixed result).** The direct way to score a candidate on laws outside its family is to mine on
their union: `mines:u3` (stride 11, B=100, K=4, uncapped) stopped by itself at 17 rules (70 s), then stage `mixed` seeds the
loops with it. Salt 1, total M, cold / own / pooled / u3: cmp3d 167 / 60 / 60 / 42, add3 183 / 60 / 42 / 57, sbo3 123 / 31 / 32 /
41, mix3 (held out) 60 / - / 10 / 17. The u3 library is the best one for cmp3d but worse than the pooled one elsewhere, mix3
included. It takes add3's `sub` chain orientation (`sub(x, add(y, z)) -> sub(sub(x, y), z)`, `sub(sub(x, y), z) -> sub(sub(x, z),
y)`), the one that conflicts with sbo3's and that the pooled library drops (see "Why add3 did better"). Scoring on more laws does
not fix an orientation choice, so the union mine does not replace pooling. Salt 2 agrees (u3 best only for cmp3d: README table).

**Down-weighted foreign stragglers (negative, reverted).** A prototype `RULEMINER_FOREIGN=<family>:<stride>:<laws>,..` also scored
the stragglers among the other families' phase-0 laws (each ref mine's window; disjoint from the loops' phases 1-3), each fix
worth 250 against 1000 for an own law, with candidates still drawn from the family's own stragglers only. The general `sub` rules
then win the first rounds (on sbo3, +25 to +52 foreign fixes each). But the uncapped miner already picks them, so the libraries
barely change: sbo3's only reorders, add3's adds one rule, cmp3d's mostly reorders (one comparison rule swapped for two others).
Salt 1, total M, baseline / foreign: own add3 60 / 57, cmp3d 60 / 58, sbo3 31 / 31; add3 from cmp3d's library 57 / 64; pooled
add3 42 / 47, sbo3 32 / 37, cmp3d 60 / 58, mix3 10 / 10; other cross cells within 1. Ref mines took 1.6-2x longer (cmp3d 118 to
187 s). Mixed at best and costlier, so reverted. The pooled cells moving with a reorder alone (sbo3's library holds the same
rules) means rule order affects serving, which no experiment here controls.

### Rule order (2026-10-11)
`rule_step` applies the first rule whose left side matches, so overlapping rules give different normal forms in different list
orders. Serving the salt-1 pooled library (no mining, phases 1-3, total M) in its mined order and five shuffles: add3 53 and 47-62,
sbo3 43 and 38-52, cmp3d 63 and 63-70. A spread of up to 15 laws from order alone is as large as many differences in the tables
above (and explains the pooled cells that moved with a reordered library in the foreign-straggler test).

**Fix (kept):** `set_extra_rules` installs the run-time rules most specific first (larger left side first, ties by text), and every
write to the rule table (`RULE_TABLE`) goes through it, so any order of the same rules serves identically (test `rule_order_does_not_change_rewriting`,
which fails without the sort). Ordering by text alone gave the same totals on this library; specificity was kept because a
specific rule is usually an exception to a general one. Served in all six orders: cmp3d 63, add3 47, sbo3 45 every time. The miner
scores candidates in the same order, so mining and serving still agree, and its memo argument holds (a rule that matches no traced
term changes nothing wherever it sits).

Re-baselined with the full sweep (`mines mines:u3 own cold cross pooled mixed cold:mix3 pooled:mix3 mixed:mix3`, salts 1 and 2;
README table). Ref mines reach far lower M with more rules (salt 1: sbo3 1 with 18 rules, was 10 with 10; add3 8 with 16, was 18
with 8; cmp3d 13 with 31, was 24 with 16; u3 5 with 35, was 16 with 17), and the loops seeded with a family's own or the pooled
library roughly halve (salt 1 / 2: add3 own 30 / 33, was 60 / 46; cmp3d own 33 / 40, was 60 / 61; sbo3 own 27 / 40, was 31 / 48;
pooled add3 27 / 33, sbo3 24 / 38, cmp3d 36 / 43, mix3 7 / 17). One regression: cmp3d's 31-rule library seeds other families
much worse (add3 108 / 100, was 57 / 87; sbo3 91 / 105, was 58 / 82), though still far below cold. cmp3d's ref mine takes 206 s
(was 118 s).

**The regression is one lost general rule.** cmp3d's new library gained 22 specific `lt` rules and lost 7, among them `add(sub(x, y),
z) -> add(sub(z, y), x)`. Appending that one rule (salt 1 loops) takes add3 from 108 to 65 and sbo3 from 91 to 58, leaves cmp3d's
own loop at 33, and leaves the control cells (add3 from sbo3's library 38, sbo3 from add3's 51) unchanged. As with the round cap,
a rule worth little on its own family (here the specific `lt` rules already cover those laws) is dropped, though it is what
transfers. The pooled library carries add3's and sbo3's general rules, so it is unaffected.

**Specific first is not an arbitrary choice.** Serving the salt-1 pooled library (no mining, phases 1-3) under three orders, total
M cmp3d / add3 / sbo3: specific first 43 / 34 / 29 (sum 106), general first (smallest left side first) 68 / 53 / 48 (169), mined
list order 68 / 50 / 45 (163). That library was mined under specific-first, which favors it, but the older pooled library mined in
list order also served better under it (155 vs 159). Order matters this much, so options for later (parked): learn a priority
per rule in the miner (fits the order to the batch, and pooling reopens it), learn which rule wins at each overlapping pair
(needs a critical-pair finder), or complete overlapping pairs Knuth-Bendix style so the order stops mattering (most work; the
step budget and cycle cuts would bound it).

**How many pairs overlap.** `rewrite::rule_overlaps` (syntactic unification, variables renamed apart) lists every pair whose
left sides unify, the second at a non-variable position of the first; `OVERLAP_RULES=<file>` with the ignored test
`rule_overlap_report` prints them. In the salt-1 pooled library (56 rules) all 56 rules overlap something: 1035 ordered pairs,
of which 817 are below the root (the inner rule rewrites a subterm the outer one would match; rule order does not decide these,
the traversal does), 100 are at the root with one left side an instance of the other (specific first settles these), and 118 at
the root otherwise (59 unordered pairs; there specific first is only a size-then-text tie-break). Most of the 118 are comparison
rules (`lt(x, sub(y, z))` against a dozen `lt(.., sub(y, add(..)))` rules); the rest are the `sub`/`add` chain orientations, e.g.
`sub(x, sub(y, z)) -> add(sub(x, y), z)` against `sub(sub(x, y), z) -> sub(x, add(y, z))`. So learning a winner per overlapping
pair means about 60 decisions at the root, and completion would face about 1000 critical pairs: per-pair learning is a modest job,
completion a large one.

**Keeping general rules by a tie-break: no-op.** The miner's candidates are already sorted by left side size (one per left side,
`search.rs`), and a round's winner breaks gain ties toward the earlier candidate, so ties already go to the smaller left side.
The lost cmp3d rule was not tied: under specific first, the specific `lt` rules already cover its laws, so it gains nothing on
cmp3d. Keeping it needs a gain from laws outside the family (the union mine and foreign scoring above), or a library made by
pooling.

**Children first is right (outermost is a negative result).** `rewrite` normalizes a node's children before trying rules at the
node, so an inner overlap goes to the inner rule. A switch that tried the library rules on a node before its children (removed)
served the salt-1 pooled library at cmp3d / add3 / sbo3 205 / 71 / 34, against 43 / 34 / 29.

**Conflicts that happen.** `RULE_CONFLICTS=1` makes serving (`search::rule_set_kernel_check`) count, per term rewritten, each later
rule that would also have rewritten it, and print `CONFLICT <terms> <winner>  OVER  <loser>`. Serving the salt-1 pooled library
hits 63 distinct pairs on phase 0 and 62 on phases 1-3, some with built-in and promoted rules (the static count covers only the
library's own rules).
The most frequent (252 terms on phases 1-3) is between two pooled rules with the same left side, `sub(x, sub(y, z))` rewritten to
`add(sub(x, y), z)` or to `add(sub(z, y), x)`: pooling concatenates libraries, so it can keep two orientations of one left side,
and then only the text tie-break picks.

**Learned preferences.** Lines `winner  OVER  loser` in a library (`rules.txt`; first a `RULE_PREFER=<file>` switch): where both
rules would rewrite a term, the winner does, whatever the order. `scripts/prefer_flips.sh` learns them for a library: it collects the
conflicts on phase 0, serves each flipped pair alone on phases 0-3, and keeps the flips that lower phase 0's M (about 20 min with 3
workers). Total M over cmp3d, add3 and sbo3, train (phase 0) and test (phases 1-3):

| pooled library | conflicts | kept | train | test |
|---|---|---|---|---|
| salt 1 | 63 | 4 | 26 to 20 | 106 to 89 (cmp3d 43 to 40, add3 34 to 26, sbo3 29 to 23) |
| salt 2 | 42 | 3 | 28 to 27 | 142 to 137 |

Phase 0 predicts the rest: at salt 1, every flip that lowered phase 0 lowered phases 1-3, and the worst flips on phase 0 were the
worst on phases 1-3. The salt-1 winners let a `sub(x, sub(y, z))` rule beat `sub(sub(x, y), z) -> sub(x, add(y, z))` (-13 test
alone): the specific-first order is wrong there. Preferences are per library: the salt-1 file on the salt-2 library gives 142 to
136. At salt 2, three flips each give -4 train and -11 or -8 test alone, but kept together only -1 and -5: two of them demote the same
rule in favor of different winners. Keeping flips one at a time and rescoring the rest after each (greedy, like the miner's rounds)
should recover that. The serving runs use no mining (`LOOP_MODE=none`), so these are serving gains on a fixed library. Learning them
inside the miner is measured below: a family's own mine hardly ever has conflicts to learn from.

### Ablating the fixed rewriter and prover parts (2026-10-11)
`ABLATE=<names>` switches off one hand-written part. Serving only (`LOOP_MODE=none`, `CHECK_FAST=1`) on phases 1-3, salt 1, total
M over cmp3d, add3 and sbo3, with the salt-1 pooled library and with no library:

| ablated | pooled library | no library |
|---|---|---|
| nothing | 106 | 828 |
| `zero`, `not`, `chain`, `fold`; in `prove_eq`: `eq_pos`, `eq_cong`, `eq_bitcong`, `shrmask`, `generalize` | 106 | 828 |
| `eq_truth` (truth table over atoms) | 110 | 832 |
| `collapse` | 185 | |
| `promoted` (the 35 promoted rules) | 234 | |
| the 21 built-in `rules()` | 257 | |
| `tree` | 318 | |
| `assoc` | 373 | |
| `comm` | 880 | |

Nine parts never decide a law on these streams, with or without mined rules; all names are wired (`eq_truth` and the others move
M). With no library they also change nothing on mix3, cmp3, u3 and u3w (111, 5, 299, 327). But the unit tests need two of them for
`shr1` laws, which these streams never send through them: without `eq_pos` the built-in `shrnot` rule's laws need a machine
proof (`shrnot_rule_is_provable_and_closes_the_shr_not_laws`), and without `shrmask` that test and
`shr_mask_proves_root_shift_laws_over_arithmetic_and_rejects_false_ones` fail. The other seven (`zero`, `not`, `chain`, `fold`,
`eq_cong`, `eq_bitcong`, `generalize`) can each be off with every unit test passing. The two-variable families (shl, shr, lt,
mul) were not served.

**Deleted (2026-10-11): six of them.** Switching all seven off at once raised M (pooled 106 to 123, no library 828 to 870):
`zero` (`x + 0`) and `chain` (sums a constant carry reduces, `x + 0` among them) cover each other, so each alone looked
redundant. With either one back, all seven families and both libraries give the numbers above exactly. `chain` stayed, as the
general case; `zero`, `not`, `fold`, both congruences and `generalize` (with `shared_subterm` and `GENERALIZE_ABOVE`) are
gone. The tests of folding and of large shared sums still pass, now by the remaining steps. One-at-a-time ablation misses
parts that back each other up; check a deletion set together before deleting. `comm` (sorting operands) matters most: the mined rules are learned on top of a canonical operand order. The library was mined
with every part present, so a large rise means the library relies on that part, not that it could not be learned.

### Preferences and rival orientations in the miner (2026-10-11)
Two greedy extensions of the miner, A/B'd with `driver::sweep` (`mines own cold pooled`) at salts 1 and 2:
- **Preferences** (`RULEMINER_PREFS=1`; on during the A/B, now off by default and used only on pooled libraries, below): after
  the rounds, collect the conflicts on the scored laws and flip the pair with the largest gain, rescoring after each flip, until
  no flip gains; the flips are written into `rules.txt` as `winner  OVER  loser` lines, which serving and later mines read.
- **Rivals** (a switch during the A/B, now always on): after a round's winner is chosen, score the other right sides of its left
  side on the same laws; one with a larger gain replaces it, if proved.

Total M (own, cold and pooled loops on phases 1-3; mines is the four ref mines on phase 0):

| | mines s1 | own s1 | cold s1 | pooled s1 | mines s2 | own s2 | cold s2 | pooled s2 |
|---|---|---|---|---|---|---|---|---|
| baseline | 29 | 90 | 447 | 87 | 24 | 113 | 451 | 114 |
| preferences | 29 | 88 | 446 | 87 | 23 | 112 | 450 | 112 |
| rivals | 23 | 74 | 472 | 75 | 21 | 104 | 450 | 158 |
| both | 23 | 72 | 472 | 75 | 21 | 103 | 452 | 151 |

Preferences barely help. The ref mines learned one preference in all, since a family's own rules are chosen one at a time on
top of each other and rarely conflict. The loops' mines learned 13, 8 of them in pooled loops, where conflicts come from
pooling, but the pooled loops' M hardly moved: a batch's mine already adds rules for the laws a conflict breaks, while
`prefer_flips.sh` measured serving a fixed library (106 to 89). The phase also roughly doubled mine times (wall times are rough:
an orphaned sweep shared the machine for the first ~20 min).
Rivals replace 3-4 winners per add3 mine and one per sbo3 mine, all `sub`/`add` chain orientations: add3's own loops drop from
30 to 14 (salt 1) and 33 to 22 (salt 2), and salt 1's pooled loops from 87 to 75. But salt 2's pooled add3 rises from 33 to 71,
and salt 1's cold cmp3d from 163 to 181. Pooling drops two hand-picked add3 orientations that conflict with sbo3's
(`driver::sweep`); the rivals change add3's orientations, so the drop list no longer matches them.

**Preferences learned on the pooled library (kept).** The pooled stage now keeps every library's rules (no hand-picked drop
list) and has each family learn preferences on it: a mine on the family's phase-0 stream (its ref mine's settings) with no rule
rounds, only the preference phase, on the pooled library; that family's pooled loops start from the result
(`pooled_<family>/rules.txt`). It takes 12-68 s per family and learns 0-5 preferences. Pooled loops, total M on phases 1-3,
from the libraries mined with rivals:

| pooled library | salt 1 | salt 2 |
|---|---|---|
| baseline (no rivals, drop list) | 87 | 114 (add3 33) |
| rivals, drop list | 75 | 158 (add3 71) |
| rivals, everything pooled | 67 | 165 (add3 79) |
| rivals, everything pooled, learned preferences | **60** | 129 (add3 43) |

The learned preferences win back most of salt 2's loss, but salt 2's add3 stays 10 above the baseline. The top preference at
salt 2 (+7000 on add3's phase 0) lets add3's own `sub(xor(x, -1), y) -> sub(-1, add(x, y))` beat `sub(x, sub(y, z)) ->
add(sub(x, y), z)` (in all three libraries) on terms both match, against the specific-first order.
Over own, cold and pooled loops and both salts, the kept setup (rivals; preferences only on pooled libraries) totals 1289 against
the baseline's 1302: own and pooled gain, and salt 1's cold loops lose 25 (447 to 472).

**The cold loss is a greedy path loss, not the orientation.** Most of it is cmp3d phase 3 (56 to 69), whose second batch goes
from 6 to 20 after the first batch's mine; every new straggler is an `lt` law. Serving that batch under the first mine's rules:
the base set gives 6, and with only the rival orientation swapped in still 6; the rivals run's set gives 20, and with its winner
swapped back 22. What differs is the rest of the set. The base mine chose the general `lt(x, sub(y, z)) -> lt(x, add(sub(x, y),
z))` (+11 in-sample; without it the base set gives 24). In the rivals run the rival's larger round gain (+14 against +10) won
round 2, the general rule never led a later round, and specific `lt` rules took the rest. Adding the general
rule to the rivals set gives 17, not 6, since the specific rules fire first. The rivals set is worse on the mined batch too, not
only on the next one: its mine covers 38 of the 43 stragglers against the base mine's 42, and serving the mined batch gives M 5
against 1 (14 with the general rule added). So the larger one-round gain led to a worse finished set: greedy myopia, not
overfitting. Salt 2's cold loops do not lose (451 to 450). Lookahead (below) fixes it.

*Held-out scoring (negative, reverted).* Rank each round's candidates by the smaller of their gains on the even- and odd-indexed
stragglers (guard laws in both), then by the full gain. On this loop it changes nothing (69 both ways): most gains are +1, so the
smaller half is 0 for nearly every candidate and the ranking falls back to the full gain; it only swapped the order of the first
two `sub` rules. It targets overfitting, which this loss is not.

**Lookahead on rival swaps (kept).** When a rival would replace a round's winner, the mine finishes the rest of its rounds both
ways (greedily, rivals taken, no further lookahead) and keeps the choice whose finished set has the larger value (the gain's
measure as a total; ties to the rival). On the loop above it keeps the winner and reproduces the base run (56; 42 of 43 covered).
Sweeps (`mines own cold pooled`), total M:

| | mines s1 | own s1 | cold s1 | pooled s1 | mines s2 | own s2 | cold s2 | pooled s2 |
|---|---|---|---|---|---|---|---|---|
| rivals | 23 | 74 | 472 | 60 | 21 | 102 | 450 | 129 |
| rivals + lookahead | 23 | 74 | **451** | 60 | 21 | 102 | 450 | 129 |

It overrode 6 of 33 swaps, all in cold loops' mines (cmp3d, add3, sbo3); the ref mines' swaps all held, so own and pooled are
unchanged. All loops now total 1266, against 1302 without rivals. Cost: ref mines 1.8-3.5x slower where swaps occur (add3 42 to
102 s and 49 to 173 s), sweeps 27-29% longer (883 to 1120 s, 988 to 1272 s; two sweeps at a time).

*Lookahead over runners-up too (negative, removed).* Each round's alternatives also took the next best proved candidate (k = 2:
winner's rival, winner, runner-up), each finished greedily. On the cmp3d loop above it changed nothing (56); the sweeps lost
everywhere but salt 2's cold loops: own 74 to 84 and 102 to 117, cold 451 to 467 and 450 to 450, pooled 60 to 65 and 129 to 165
(all loops 1266 to 1348); the ref mines' own M 23 to 21 and 21 to 23, 2-3x slower. A guess, untested: at a rival swap both
sides are the same left side, scored on the same laws, while a runner-up is a different rule, and picking among different rules by
their finished in-sample value fits the mined batch more closely than the greedy choice does.

*Runners-up chosen held out (negative, reverted, 2026-10-12).* A test of that guess: the same three alternatives (rival,
winner, runner-up), each finished greedily on the even-indexed stragglers and valued on the odd-indexed ones, and the other way
round, summed (2-fold; guard laws in both folds; the rounds still choose on every straggler; ties to the earlier alternative).
Sweeps against HEAD (with the rival-scoring fix, same rows):

| | mines | own | cold | pooled | loops |
|---|---|---|---|---|---|
| HEAD | 23 / 21 | 74 / 102 | 451 / 450 | 58 / 99 | 583 / 651 |
| held-out runners-up | 21 / 20 | 85 / 103 | 435 / 454 | 66 / 91 | 586 / 648 |

All loops 1234 both ways: the in-sample version's loss is gone (so the guess holds in part, the in-sample choice overfit), but
nothing is gained. It moves M between families rather than lowering it: cmp3d own 33 to 46 and pooled 31 to 41 on salt 1;
add3 cold 166 to 150 (salt 1), sbo3 pooled 40 to 32 (salt 2). cmp3d's ref mines were 3.5-4.5x slower (266 to 923 s, 170 to
763 s) and the sweeps about 2.3x longer (shared machine). Patch kept out of the repo; the greedy choice stays.

*Lookahead cache (kept, exact).* A round depends only on the set of rules chosen so far (`set_extra_rules` sorts them), and the
alternatives' greedy paths often reach the same set in another order, so the miner keeps each set's pick and finished value; the
kept alternative's path is also the next rounds' own. Same choices on the cmp3d loop; picks 47 to 36, and 467 to 180 with three
alternatives a round (316 to 137 s). Full sweeps reproduce every own, cold and pooled
row; sweeps 1120 to 747 s and 1272 to 732 s (two at a time), ref mines 472 to 293 s and 435 to 233 s, so the rival lookahead now
costs less than it added.

*Rule-set evaluations reuse the last one's memo (kept, exact).* Each evaluation of a chosen set (`state`) is seeded with the
previous evaluation's rewrite memo, minus the entries whose trace has a term matched by a rule added or removed since
(`RewriteMemo::filtered`). On the cmp3d cold loop, same choices and M 56; time in these evaluations 9.4 to 2.1 s and 1.1 to 0.3 s
per mine, loop wall time best 46 to 38 s (two runs each, alternated, the machine at ~50% load from other work). Full sweeps
reproduce every own, cold and pooled row at both salts (times not comparable: CPU at start 27% against 14%). Keeping the
candidate scorers' memos across picks too would need worker threads that live for the whole mine (the memos hold thread-interned
expressions); not done, since scoring already reuses 87% of law evaluations across rounds (89868 of 103100 on cmp3d).

**Salt 2's pooled add3 loss is two chain normal forms meeting.** With rivals, add3's own loops at salt 2 gain (33 to 22) but its
pooled loops lose (33 to 43), and sbo3's pooled loops too (38 to 46, own 40); at salt 1 pooling costs nothing (add3 14 own, 13
pooled). Serving add3's salt-2 phases 1-3 (no mining) under: its own library 32; the pooled library with its learned preferences
44, without them 85; add3's plus cmp3d's library 56; add3's plus sbo3's 85, the same on every phase as the whole pool. Leaving one
of sbo3's 12 other rules out of add3 + sbo3 gives at best 71; leaving out its four `sub`/`add` chain orientations together
(`sub(add(x, y), z) -> add(sub(x, z), y)`, `sub(x, sub(y, z)) -> add(sub(z, y), x)`, `add(sub(x, y), z) -> add(sub(z, y), x)`,
`add(x, sub(y, z)) -> sub(x, sub(z, y))`) gives 28, and those four alone added to add3's library give 87. Before rivals, add3
chose three of them itself; with rivals it drops them and orients the chains toward other forms (`add(sub(x, y), z) -> sub(add(x, z), y)`,
`sub(x, sub(y, z)) -> add(x, sub(z, y))`, `sub(sub(x, y), z) -> sub(x, add(y, z))`). Each family's chain rules make a consistent
normal form; mixed, a term can be pulled toward both. The learned preferences flip one pair at a time and win back 85 to 44, but
the four rules matter only together.

*Dropping whole libraries (net zero, reverted).* The pooled library written in per-library sections, and the preference phase
also tried dropping each section whole as a move (the same gain). Pooled loops: salt 1 60 to 73, salt 2 129 to 116. At salt 2
add3 dropped its own library (+14000 on phase 0; pooled add3 43 to 37, against 28 with only sbo3's four chain rules gone) and
cmp3d dropped sbo3's. At salt 1 sbo3 dropped add3's library for +1000, one phase-0 law, and its pooled loops went from 14 to 27.
A library is too coarse a unit: it removes rules that transfer along with the conflicting ones, on little evidence. A finer
unit would be the rules that interact (overlap) with the conflicting ones (`rewrite::rule_overlaps`); tried next.

*Drop units where two libraries' normal forms meet (kept).* Overlap groups as such are useless: all 26 rules of add3 + sbo3 lie in
one overlap web (372 pairs), and groups over root overlaps only split by head operator (a `sub` group, an `add` group), each
mixing both libraries' chain rules. With provenance it works: for libraries A and B, the unit is B's rules (not also A's) whose
left side overlaps one of A's at the root (`rewrite::drop_units`; the pooled file is written in `# library` sections,
`library_sections`). For salt 2's add3 + sbo3 that is 7 of sbo3's rules (the four chain rules among them); serving add3 without
them gives 32 (its own library 32; without only the four, 28). The preference phase tries dropping each unit as a move, beside the
flips; the driver takes the dropped rules out of the family's library.

| pooled loops M | salt 1 | salt 2 |
|---|---|---|
| preferences only | 60 | 129 (cmp3d 40, add3 43, sbo3 46) |
| + drop units | 73 (sbo3 14 to 27) | 103 (37, 22, 44) |
| + drop units, a drop needs gain >= 2000 (kept) | 60 (same rows) | 103 |

At salt 2 add3 drops exactly the 7 rules (+16000) and is back to its own 22; cmp3d (+3483) and sbo3 (+6000, 12 rules in two units)
drop too. At salt 1 sbo3 dropped add3's `sub` chain rules for +1000 (one phase-0 law, 0 of 2 stragglers covered) and lost 13 on
phases 1-3, the same overfit as the whole-library drop there; cmp3d dropped the same unit for +1083 at no cost. A drop removes
many rules at once, so it now needs two laws' worth of gain; the 2000 is set by hand on these runs (salt 1's drops 1000 and 1083,
salt 2's 3483 to 16000). Salt 1 with the floor reproduces every row, so the sectioned file changes nothing by itself. Cost: a
preference round with 5 units takes ~20% longer at salt 1 (cmp3d 7.1 to 8.9 s over two rounds); at salt 2 the drops end the phase
sooner (add3 6 rounds 45 s to 2 rounds 13.5 s). Remaining pooled cost against own libraries at salt 2: cmp3d 37 vs 40
own (better), add3 22 vs 22, sbo3 44 vs 40.

Options for the drop mechanism surveyed after this (2026-10-12; only (a) is built):

| | Option | What it fixes | Cost / risk |
|---|---|---|---|
| a | Evidence floor: a drop must gain >= 2000 (kept, above) | the one-law drop at salt 1 | a hand-set threshold that separates these runs' gains, not a principled one |
| b | Held-out gain for drops: split the phase-0 laws in halves and require a gain on both | the same overfit with no threshold (a one-law gain is 0 on one half) | tried, negative (below) |
| c | Joinability units (Knuth-Bendix): only B's rules whose critical pairs with A's rules do not join under the union | a finer unit than root overlap; for add3 perhaps only the four chain rules (28 by hand vs 32) | tried, kept (below); the units came out larger, not finer |
| d | Unit preference instead of drop: put all of B's unit under A's rules at once | keeps B's rules where A's do not apply | likely fails: the four chain rules alone cost add3 32 to 87 on terms add3's rules do not match; cheap to falsify by serving |
| e | Re-mine after drops (`rounds > 0` in the pooled preference mine) | recovers coverage a drop removed | each pooled preference mine becomes a full mine; treats the symptom, not the overfit |

Ranking at the survey: b (removes the threshold), then c if a family still trails its own library, d only as a quick
falsification. b lost (below).

*Held-out gain for drops (negative, reverted).* A drop qualified when its gain was positive on both halves of the stragglers (even
and odd index, guard laws in both), in place of the floor. Pooled loops 60 and 106 against the floor's 60 and 103. Salt 1 is
unchanged (sbo3's one-law drop is 0 on one half; cmp3d now drops a 5-rule unit for +1083, both halves positive through size, at
no cost). At salt 2 cmp3d's +3483 drop has -715 on one half and is refused, and its pooled loops go 37 to 40: a drop that
transfers can still lose on half the phase-0 laws, so the halves are too strict.

*Full sweeps with drop units (root units, floor).* Every mines, own and cold row at both salts and salt 1's pooled rows match the
sweeps before drops; salt 2's pooled stage 129 to 103. Times not comparable (CPU at start 21-24% against 13-14%).

*Joinability units (kept).* Two rules meet when one of their critical pairs (`rewrite::critical_pairs`: every position of either
left side where the other's unifies, at the root or inside, both ways) does not join: rewritten under the whole pooled base and its
preferences, its two sides reach different normal forms. A unit is B's rules (not also A's) that meet a rule of A's; the floor
stays. Pooled loops, against root units:

| pooled loops M | salt 1 | salt 2 |
|---|---|---|
| root units, floor | 60 (cmp3d 33, add3 13, sbo3 14) | 103 (37, 22, 44) |
| joinability units, floor | 58 (31, 13, 14) | 99 (37, 22, 40) |

Salt 2's sbo3 reaches its own library's 40, so at salt 2 every family is at or below its own library (cmp3d 37 vs 40, add3 22 vs
22). The units are larger, not finer: 7 to 25 rules (salt 1) and 12 to 17 (salt 2) against root units' 1 to 12, since inner
overlaps count and the rewriter's built-in steps do not join every root pair; what makes them better is that they hold the
rules that actually split normal forms. Cost: building the units took ~20 s of the first preference round in each family's
mine (critical pairs rewritten one by one); a pooled stage went from ~120 to ~210 s. The units depend only on the pooled library
(and its preferences, none), so the driver now builds them once (`rewrite::joinability_units`, written to `pooled.units`, read by
the mines through `RULEMINER_UNITS`): same rows at both salts, pooled stage 212 to 142 s and 207 to 152 s.

*Critical pairs at the root only (negative, removed).* Units of 1 to 11 rules instead of 7 to 25; pooled loops 60 and 105 against
58 and 99 (salt 1 cmp3d 31 to 33, salt 2 sbo3 40 to 46). The pairs inside a left side matter.

*The floor is still needed with joinability units.* Without it, pooled loops 71 and 99 against 58 and 99: salt 1's sbo3 again
drops a unit for +1000 (one phase-0 law) and goes 14 to 27; every other drop gains 3215 or more and is the same either way.

*Full sweeps at d19c654 against 6ca89b3, run side by side* (same load; CPU at start 10-12% for salt 1, 27-28% for salt 2, no
quiet window). Every mines, own and cold row matches; pooled 60 to 58 and 129 to 99, the rows of the pooled-stage runs above.
Times, 6ca89b3 to d19c654: sweeps 819 to 745 s and 797 to 671 s; mines 321 to 290 and 255 to 224 s; cold loops 269 to 220 and
251 to 209 s; pooled loops 65 to 54 and 85 to 63 s (their libraries are smaller after drops; the preference mines are not in
these rows). The mines and cold gains are likely the memo reuse ("Rule-set evaluations reuse..."), the only change those stages
run; not separated further.

*A third salt keeps the floor* (salt 3, mines/own/pooled at d19c654, then the pooled stage with the floor at 0 on the same
libraries). Own loops M: cmp3d 29, add3 24, sbo3 27 (80). Pooled with the floor: 23, 24, 27 (74); without it: 29, 24, 27 (80).
Without the floor cmp3d also drops add3's whole unit for +1033 and lands exactly on its own library; every other drop gains
13000 or more and is the same either way. Across three salts the drops that hurt gain 1000-1033 and the ones that help 3215 or
more, so any floor between those gives the same rows; 2000 separates the classes, not tuned to two salts. Salts 4 and 5 (same
pair of runs) never reach it: their smallest drops gain 5149 and 6099, and with or without the floor the rows match (own 75 and
98, pooled 64 and 98). Five salts, no drop between 1033 and 3215.

### Operand order: `show()` wins, also with the promoted rules re-learned under each order; comm is not mined back (2026-10-12)
Learning operand order (learned-vs-fixed.md, candidate 1) is only worth it if the order matters and the current one is not
already good. A temporary switch put one term order behind the three places that use it (the bitwise operand sort with constants
last, `add` comm and left-comm, and the instance check of permutative rules) and ran full sweeps (mines, own, cold, pooled) with
the `show()` order, its reverse, and size first (then `show()`), plus `ABLATE=comm` under the `show()` order. A default-order run
reproduced salt 1's HEAD rows exactly. Total M (salt 1 / salt 2):

| | mines | own | cold | pooled |
|---|---|---|---|---|
| `show()` (current) | 23 / 21 | 74 / 102 | 451 / 450 | 58 / 99 |
| reversed | 29 / 29 | 132 / 147 | 500 / 486 | 106 / 89 |
| size first | 20 / 17 | 98 / 117 | 478 / 457 | 76 / 117 |
| `ABLATE=comm` | 86 / 79 | 177 / 222 | 799 / 798 | 161 / 248 |

The order matters (own loops up to 1.8x), and the current one wins 13 of the 16 pairwise comparisons (each stage and salt against each other order); the exceptions are size first's mines and
reversed salt 2 pooled. Per family the picture is a little more mixed (size first: salt 1 pooled sbo3 11 against 14, salt 2 own
sbo3 39 against 40), but no other order wins a family on both salts. Without the built-in comm the miner does not mine it back
usefully (cold loops 451 to 799, 450 to 798), though each library holds one or more `add` swap rules. The 35 promoted rules were
mined under the `show()` order, which biases the test toward it. Without them (`ABLATE=promoted`, same three orders, the probe's
build), the ranking turns over:

| `ABLATE=promoted` | mines | own | cold | pooled |
|---|---|---|---|---|
| `show()` | 33 / 29 | 139 / 164 | 542 / 497 | 125 / 160 |
| reversed | 31 / 34 | 160 / 142 | 524 / 515 | 143 / 124 |
| size first | **19 / 19** | **120 / 118** | **498** / 510 | **88 / 101** |

Size first wins 7 of 8 cells (all but salt 2's cold loops), and `show()` is last or second in every other. Per family the best
order varies: own loops, add3 26 / 28 best under `show()` / reversed (salt 1 / 2), sbo3 31 / 34 under size first, cmp3d 43 /
46 under `show()` / reversed. This suggested the earlier verdict came from the promoted rules, which are worth far more than the order (the
`show()` order with them, own 74 / 102, beats every order without them).

The fair comparison re-promotes under each order by one procedure (below) and sweeps with that set in place of PROMOTED:

| re-promoted under its own order | mines | own | cold | pooled |
|---|---|---|---|---|
| `show()` | 23 / 21 | 74 / 102 | 451 / 450 | 58 / 99 |
| size first | 30 / **15** | 106 / 129 | 475 / 454 | 79 / 124 |

`show()` reproduces HEAD's rows exactly, though its set differs from PROMOTED in 4 rules (below). Size first wins 1 of 8 cells
(salt 2's mines). By family the loss is cmp3d (own 33 / 40 under `show()`, 55 / 68 under size first) and add3 (14 / 22 against 22
/ 36); sbo3 does better under size first on salt 2 (own 40 to 25, pooled 40 to 24) and salt 1's pooled loops (14 to 10). So the
`ABLATE=promoted` reversal came from the missing rules, not from the order: with the promoted rules re-learned under each order,
`show()` wins. Learning one global order is parked (no better order found); the only remaining signal is per family (sbo3 under
size first), which would need the order learned per family together with that family's promoted rules. The switch is removed.

Where PROMOTED came from (design spec part 2, section 60): `rule_miner` on the older mul, shl, lt and shr families (none a sweep
family), on 2026-10-02's miner (before rivals, lookahead, preferences and the growth cut); 20 rules of the first round, then 15
of shr's second-round 17 ("useful", a filter not written down). Their left sides are literal patterns over normal forms in the
`show()` order, so under another order many cannot match. The fair test above re-promotes under each order by one procedure,
with no promoted rules in force: round 1 mines mul (`MULMINER_MAX=5`), shl (300 laws) and lt (150 laws); round 2 mines those and
shr (`RULEMINER_DEEP=1 MINER_SUB=1 RULEMINER_STRIDE=3`, 900 laws) with round 1's rules in force; every chosen rule is promoted.
Each order gives 35 distinct rules. Under `show()` the set is PROMOTED but for 4 rules: it lacks `xor(shl1(-1, 0),
shl1(shl1(-1, 0), 0)) -> shl1(sub(0, -1), 0)` and `sub(-1, sub(x, -1)) -> sub(shl1(-1, 0), x)`, adds `sub(x, xor(x, -1)) ->
sub(shl1(x, 0), -1)` and `shr1(sub(0, -1), 0) -> shr1(0, 0)`, and orients `sub(x, add(y, x))` to `add(0, sub(0, y))`; so the
undocumented "useful" filter changed about two rules. Under size first the set is the same but for 3 rules mirrored in operand
order. Each mine takes 20-100 s.

### Drops of the mine's own rules (negative, removed, 2026-10-12)
Learned-vs-fixed candidate 2 (the miner's greedy search): a chosen rule that later rules make redundant, or that shadows a later
rule, stays, since the preference phase drops only a pooled base's units. A temporary switch made each rule the mine chose a drop
unit of its own (same move, same 2000 floor) and logged every candidate's gain; full sweeps with preferences on in every mine,
with and without it. The two are identical on every stage (salt 1: mines 23, own 72, cold 450, pooled 56; salt 2: 21, 102, 452,
98). Of 642 own-rule drop candidates over both salts, none gains: 6 are 0 and 636 lose. So greedy mines leave no rule whose
removal helps in-sample, even below the floor, and backward elimination has nothing to work on; the greedy loss documented
above ("The cold loss is a greedy path loss") is a path the greedy never took, not a rule it should not have kept. Preferences in
every mine against HEAD: own 74 to 72 (salt 1), cold 451/450 to 450/452, pooled 58/99 to 56/98; mine times not comparable (the
runs shared the machine with other sweeps).

### Rivals scored by counting only (fix, 2026-10-12)
With the promoted rules out (`ABLATE=promoted`), `rule_miner` on shl panicked ("rule mined is not provable") on the rival
`sub(x, shl1(x, 0)) -> sub(shr1(0, 0), x)`: rivals are scored before they are proved, and scoring built each firing rule's proof,
which `add_tree_law` cannot do with `shr1`. Rivals are now scored with `SCORE_ONLY` (counting only; the rewritten terms do not
depend on the proofs), and `score_laws` keeps a caller's `SCORE_ONLY` instead of resetting it. Full sweeps reproduce HEAD's mines,
own, cold and pooled rows on both salts (23/74/451/58, 21/102/450/99).

### Promotion as an iterated sweep: one iteration pays a little, the second does not (2026-10-12)
Aim: move the promoted rules from "learned once" to "learned in the run" (learned-vs-fixed.md). Three framings:
- *Re-run the section-60 procedure inside the sweep* (rejected as a first step): bookkeeping only. Under `show()` it reproduces
  HEAD's rows exactly ("Operand order"), so it moves no number; worth doing only once the iteration below pays.
- *Promote from the sweep families' union* (rejected): already measured as the union mine (`mines:u3`) and as down-weighted
  foreign stragglers, both mixed, with pooling better ("Scoring on other families' laws", "Down-weighted foreign stragglers").
- *Iterate the sweep* (run): a sweep's output is the next sweep's starting base, the cycle's "proved laws compiled into rules
  that make later work cheaper". Today every ref mine starts from the built-in and promoted rules alone. In iteration k+1 the ref
  mine of family F starts from iteration k's pooled library for F (`pooled_<F>/rules.txt`: the three libraries with F's learned
  preferences and drops) and mines its phase-0 stream on top of it.

**Mechanism (kept):** `MINES_WARM=<sweep dir>` seeds each ref mine with `<dir>/pooled_<fam>/rules.txt` through `LoopCfg.warm`,
as the pooled loops are seeded; a family with no pooled library (mix3) mines cold. Iteration 0 is a HEAD sweep (`mines pooled`);
iteration k+1 runs `mines own` with `MINES_WARM` on iteration k, then the existing pooled stage on its libraries. Iteration 1's own
loops against iteration 0's pooled loops isolate what the ref mine adds on phase 0: both serve phases 1-3 from F's pooled base and
mine each batch on top. No leakage: every base is mined on phase 0, the loops serve phases 1-3. Total M (salt 1 / salt 2):

| | ref mines | own | pooled | pooled text lines (with repeats) |
|---|---|---|---|---|
| iteration 0 (= HEAD) | 23 / 21 | 74 / 102 | 58 / 99 | 60 / 47 |
| iteration 1 | 16 / 15 | **55** / 90 | 57 / **85** | 176 / 105 |
| iteration 2 | 14 / 15 | 58 / 85 | 65 / 85 | 529 / 267 |

(Ref mines' M is in-sample, on the phase 0 the base was fitted to.) The falsifier passes: iteration 1's own loops are lower on
both salts (58 to 55, 99 to 90). Best loops: 157 (iteration 0 pooled) to 142 (iteration 1 pooled; 145 own). By family, salt 1
own: cmp3d 31 to 24, add3 13 to 10, sbo3 14 to 21; salt 2 every family at or below. Iteration 2 adds nothing: own 58 / 85, and
its pooled loops lose on salt 1 (65; add3 10 to 16) while the libraries keep growing (salt 1 cmp3d 31, 48, 61 rules). The pooled
text repeats each base once per library (60 to 529 lines), the duplication the per-family pooled text was meant to remove; it
starts to cost at iteration 2 (pooled 65 against own 58, pooled stage 284 to 922 s), but since own loops also stop improving
there, removing it would at best reach iteration 1's rows, so it was not built. The pooled preference mines' phase-0 M (cmp3d
13 / 11 at iteration 0, 7 / 9 after) shows where the room was: cmp3d. Cost of an iteration: about 220-240 s of ref mines and own
loops, plus 260-280 s of pooled stage, two sweeps at a time.

**From `ABLATE=promoted`: the iterations do not recover PROMOTED (negative, 2026-10-12).** The same procedure (`mines own
pooled` per iteration, `MINES_WARM` on the previous one) with the promoted rules out, iterations 0-3, both salts in parallel
(`docs/runs/2026-10-12/scripts/iterate_np.sh`, rows `npit<k>_<salt>`). Total M (salt 1 / salt 2):

| | ref mines | own | pooled | pooled cmp3d text lines | sweep s |
|---|---|---|---|---|---|
| iteration 0 (no promoted) | 33 / 29 | 139 / 164 | 125 / 160 | 60 / 48 | 640 / 916 |
| iteration 1 | 24 / 18 | 115 / 144 | 120 / 140 | 181 / 138 | 389 / 466 |
| iteration 2 | 24 / 18 | 119 / 140 | 108 / 140 | 495 / 387 | 850 / 923 |
| iteration 3 | 23 / 18 | 107 / 140 | 107 / 140 | 1393 / 1102 | 5040 / 2808 |
| HEAD (promoted, iteration 0) | 23 / 21 | 74 / 102 | 58 / 99 | 60 / 47 | |

Salt 2 stops at 140 from iteration 2; salt 1 creeps down (125 to 107) while the sweep slows 8x, the text roughly tripling each
iteration (each warm base is repeated in every library the next pooling concatenates). By family, iteration 3's pooled loops
against HEAD's: salt 1 sbo3 58 against 14, cmp3d 37 against 31, add3 12 against 13; salt 2 add3 47 against 22, cmp3d 54 against
37, sbo3 39 against 40. So PROMOTED stays "learned once": it was mined on the older mul, shl, lt and shr families (above, "Where
PROMOTED came from"), whose patterns these sweep families' phase-0 streams do not supply, and the iterated sweep (which helps on
top of PROMOTED, 157 to 142) is not a substitute for it.

Not run: pooled loops on the held-out mix3 across iterations (`pooled:mix3`). Not tested by any of this: the promoted rules' precedence (they are tried before
the run-time rules, which a warm base is).

### Learned and fixed parts
Which parts are learned and which are fixed by hand, with the measured evidence per part, is kept in
[learned-vs-fixed.md](learned-vs-fixed.md) (surveyed 2026-10-11, updated as parts move).

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
