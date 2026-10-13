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
28 s). Undecided: trust loaded lemmas, re-check them, or avoid the repeat without a file (fewer processes).

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
write to `EXTRA_RULES` goes through it, so any order of the same rules serves identically (test `rule_order_does_not_change_rewriting`,
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
