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
counts the children through a job object. Speed claims in this file should come from runs like this, now `runs time` (`tools/runs`, which replaced `quiet_ab`), not ad hoc ABAB. The sweeps (formerly local `transfer_mines.sh`, `cross_run.sh` and per-experiment wrappers) are now
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
- `nf_cached`/`fingerprint`: only the ignored `conjecture_miner` probe; it also hashes `Debug` text (both since removed).

Nothing else on the rewrite path reads a term: `rule_step` gets its lemmas through `shared_lemma` (placeholders when counting, at the time),
winner proofs run outside scoring, and the integer screens (`plausibly_equals`, `refute`) already use `Term::interp`. Plan:
first decide at these sites by plain evaluation (a `bool` `Term::bit`, a `bool` implementation of `Gates` for `raw_table`, so
`GoodOps` is built only for proofs); rows must stay identical, since the Church gates compute the same Boolean functions. Then the
proof plans. Also left: `add_tree_law`'s `guarded` formats its lemma key eagerly (`LEMMA_HITS`, which read it first, was removed 2026-10-21), so counting still builds
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
`driver::run_loop`, deleted when the loop starts and ends; `crates/church-bv/src/lemma_cache.rs`), and a later process binds it
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
attractive rules through `RULEMINER_EXTRA`): it rolls back at round 0, and its chosen rules equal 514b7a2's. Since 2026-10-27
the test `miner::a_false_winner_rolls_the_rounds_back` is the rollback check (in process, one false rule; `RULEMINER_EXTRA` is
gone, cleanup CU4a). Pair sweep against
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

