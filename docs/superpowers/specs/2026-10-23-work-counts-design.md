---
status: done
---

# Work counts: a load-independent cost signal for the gate

## Why

The gate (`scripts/streams_ab.sh`) decides with three numbers: M, held-out M and job CPU. M and held-out M are
deterministic. In the A/A they were identical in both arms on every salt
(`docs/tier-cycle.md`, "The gate on the streams and its A/A baseline"). Job CPU is not: its A/A spread is 5.4% per salt,
and a timed run needs a quiet machine. On 2026-10-23 one salt pair of the ablations (plan
`docs/superpowers/plans/2026-10-23-class-table-ablations.md`) was refused 8 times in about 25 minutes while a game held
CPU 8 busy. A count of the work done would give the cost side of a verdict without a quiet machine. This also serves
ROADMAP's second goal: a kernel that improves itself needs a cost it can measure the same way every time.

## What earlier work found (one home: `docs/tier-cycle.md`)

- "Instruction count as a metric" (2026-10-10). The kernel's own counts were per-law node visits by kind, from
  `law_work_report`, built under the `record-defeq` feature with 38 probe sites in `src/kernel.rs`. They ranked
  libraries differently from M, because each use of a rule re-checks the rule's proof. The probes made the build
  about 4x slower, and they were deleted in 306a968 (C10/C11).
- "Kernel cost calibrated against time" (2026-10-10). Raw visits with one weight predicted per-law time with 55%
  held-out error. A non-negative least-squares fit over the per-slot counts got 18%. The decision then was that M
  stays the objective and a fitted cost is a check reported beside it.
- The cost of `mk` (hash-consing) is about three cache misses, not instructions. A count therefore sees how many
  nodes were built, but not what each one cost.

So a count is a proxy. What it can show reliably is that **the work did not change**: equal counts mean equal work,
whatever the load (up to the miner's speculation, a few ppm; § Gate for the counts themselves). It shows an *amount* of cost only after calibration.

## Decisions

1. **What is counted.** *Decided 2026-10-23: (a).*
   - (a, chosen) A few counters at function granularity in the phases that take a sweep's CPU. Which phases,
     and how big each one's share is, come from a profile of one streams arm. The profile and the counters it
     gave are in § Where an arm's CPU goes and § The counters.
   - (b) One count, the number of `mk` calls (every node built, kernel and `Term` alike). Simplest, but it misses
     the walks that build nothing.
   - (c) Bring back the per-site probes (`git revert 306a968`). The most detail, but they were removed for their
     cost and clutter in the trusted kernel.
2. **Always on, or behind a feature.** *Decided 2026-10-23: (a).*
   - (a, chosen) Always on: per-thread counters, summed by `take` when a `WORK` line is printed (§ What changes).
     The overhead is measured (see Gate), not assumed: none measurable once the recursive sites add once per call.
   - (b) A cargo feature. That is two builds, and the timed build is not the counted one, which is the problem
     `record-defeq` had.
3. **How counts are reported.** *Decided 2026-10-23.* A `WORK k=v ...` line per worker task, in its log, as `CLASS_MEMO`
   is (`driver.rs`, `worker`), and one per sweep at its end, for the sweep's own thread and its lanes (plan D4). `streams_ab.sh` sums them per arm and adds `work A <k=n ...> B <k=n ...>`, one total per counter, to each salt line.
4. **What a verdict uses.** *Decided 2026-10-23: (a).*
   - (a, chosen) Counts take the place of job CPU in the cost check, with an A/A spread of their own (expected
     0 where the code is deterministic). Job CPU stays in the output and is compared only on a quiet machine.
   - (b) Counts only beside CPU, for information.
5. **Counts of duplicated work** (see § Determinism risk). *Decided 2026-10-23: (a).*
   - (a, chosen) Count every visit, so a counter reports work done. The A/A of the gate then shows whether the
     race moves counts. If it does, the spread is measured like CPU's.
   - (b) Count `verdict`'s visits into a local and add them only when `insert` reports the key as new. The counter
     then reports work needed, not done. That is one special case at one call site.
6. **How the counters decide "free".** *Decided 2026-10-23: (d).* The counters measure different units (a node
   evaluated, a subterm walked), so they are not summed as they are. They are compared only once M and held-out M
   match on all ten salts (a rise in either already means the part pays). Each counter is summed over the ten salts and
   compared on its own, against a tolerance: the larger of that counter's A/A spread and 1%. The 1% is a size that
   matters, not noise, since the counts repeat to a few ppm; the ablations plan already flags job CPU at 1%.
   - (a) Free when no counter rises past its tolerance. Prior art: gungraun's per-metric limits, which fail on any
     one metric past its limit.
   - (b) One weighted sum, with weights fitted to job CPU on quiet A/A salts. Prior art: KCachegrind's cycle
     estimate; this repo's 2026-10-10 NNLS fit, whose 18% error is over 3x CPU's own A/A spread and whose weights
     were tied to the machine. Rejected for that reason.
   - (c) As (a) with tolerance 0. Rejected: every deletion that moves a few walks would count as a cost.
   - (d, chosen) As (a), with a third outcome from rustc-perf's "mixed" label. The verdict is **free** when no counter
     rises past its tolerance, **costs** when one rises and none falls past its tolerance, and **mixed** when one
     rises and another falls. Costs means the part saves work, so it pays and the driver goes on; free and mixed stop
     the driver, and the session brings them to the user (a free one after one timed pair: the ablations plan's D4).
   - Also surveyed and rejected: one primary counter (rustc-perf and gungraun decide by instructions alone), since
     none of the four counts all the work (`interp`, the largest, is 33% of an arm); a fence over past changes
     (rustc-perf), which has width 0 for counts that repeat exactly and so becomes (c). Sources: gungraun's
     `docs/src/regressions.md`, rustc-perf's `docs/comparison-analysis.md`, both read 2026-10-23.

## Gate for the counts themselves

- **Determinism:** an A/A on salts 1-2 must give equal counts per salt. Shared state across processes and threads
  can make counts depend on scheduling, even where results do not. Examples: `LEMMA_CACHE`, which a sweep's
  processes share and which later tasks read; the class table's lookup memo; the miner's scoped threads. If counts
  differ, either the counted sites move to work that does not depend on those caches, or the spread is measured and
  used the way CPU's is. *Measured 2026-10-24 (`work-aa-s1-2`): they differ, only in the mining tasks: max A/A spread
  interp 3.0 ppm, walk 0, match 8.7 ppm, op 0.02 ppm (job CPU 25% on salt 2). The miner's scoring queue and its proofs
  run alongside the rounds, so how much speculative work is done depends on timing, though the result does not. The
  spread is used the way CPU's is (decision 5(a)), so the 1% floor applies. A second source, found in review: a sweep
  gave each loop to the next free lane, whose worker carries its lemma file and memos into the next loop; since a4eda36
  the lanes are fixed and an A/A loads the same lemmas per loop in both arms (`work-aa-lanes-1-2`).*
- **Proxy quality:** on a quiet machine, counts and job CPU should move together. Per arm over salts 1-10 of the
  A/A and one ablation that changes work, report the ratio of job CPU to each counter. The test passes when two
  things hold. First, on the quiet salts each ratio varies by no more than twice CPU's own A/A spread (11%); a count
  cannot be steadier against CPU than CPU is against itself. Second, the ablation moves CPU and the summed counters
  the same way. If it fails, decision 6(b)'s fitted weights are the fallback, brought back as a decision.
  *Measured 2026-10-24 (`docs/tier-cycle.md`, "Work counts as the gate's cost"): the ablation moved every counter and
  job CPU the same way, but job CPU per count varied 24-46% over salts, and a fitted weighted sum 18.4%. Decided
  2026-10-24: the counts give the direction of a change, not its amount, and decision 6(d) needs only the direction,
  so proxy quality is the co-movement test; a free verdict is checked by one timed pair before it reaches the user.*
- **Overhead:** the counted build against the uncounted build, timed on salts 1-2. Job CPU must stay within the
  A/A's 5.4%. Results (M, held-out M, rules) must be identical.

## Where an arm's CPU goes (run `2026-10-23-streams-prof-s1`)

A samply profile of one cold:streams arm, salt 1, at 103d954 (only docs uncommitted) with debug info: 175 s wall, 429708 busy samples, all
processes. Frames were named with `docs/runs/2026-10-18/scripts/prof_named.py`. Shares of busy samples (inclusive
shares overlap):

| function | inclusive | self |
|---|---|---|
| `miner::Scorer::score_laws` (scoring candidate rules) | 71.8% | |
| `rewrite::prove_eq` | 65.9% | |
| `rewrite::join_search` / `join_walk` | 41.6% / 36.5% | 2.7% |
| `rewrite::Term::interp` (evaluating a term at one input) | 33.0% | 25.9% |
| `search::stream_laws` (stream generation) | 24.0% | |
| `classes::verdict` (the class step's exhaustive check) | 19.8% | |
| `miner::Rounds::play` | 9.5% | |
| `rewrite::Term::op` (building a node) | 7.6% | 2.7% (its closure) |
| `rewrite::match_pat` | 3.8% | 3.6% |

In the sweep, `interp` is reached from two exhaustive checks at widths 1-5: `classes::verdict` (through
`Classes::step`) and `prove_eq`'s per-position step. Its other callers are tests. No other function has more than
4% self.

## The counters (decision 1(a); approved 2026-10-23)

One counter per site, incremented on entry:
- `interp`: each node `Term::interp` visits (it recurses, so this counts nodes, not calls).
- `walk`: each `join_walk` call (it recurses once per subterm it walks).
- `match`: each `match_pat` call.
- `op`: each `Term::op` call (a node built or found).

The four sites sit inside all three big phases (scoring, stream generation, the class step). Whether their counts
track job CPU is not assumed; the proxy-quality gate measures it. Hashing and allocation (about 10% self) are counted
only through the sites that cause them. `interp` is the hottest function (26% self), so its one add per node is the
overhead the gate's overhead check matters most for.

## What changes

- **The counters** (`tests/church_bv/work.rs`): each thread's slot of four atomics, registered in a process-wide
  list; `take` sums every slot and zeroes it, and the `WORK` line prints the sum. Slots are read by `take` rather than
  flushed when their thread ends, since `thread::scope` returns before its threads' thread-local destructors run (plan
  `docs/superpowers/plans/2026-10-23-work-counts.md` D1).
- **The four sites:** `Term::interp` and `match_pat` sum their nodes in a local and add them once per call
  (`count_n`; one add per node cost 7-8% job CPU), `join_walk` and `Term::op` add one per call.
- **`scripts/streams_ab.sh`:** sums each arm's `WORK` lines per salt and prints `work A <k=n ...> B <k=n ...>`; an
  arm with none failed.
- **The ablations driver** (outside the repo; its one home is Task 1 of the ablations plan): the verdict follows
  decision 6 (costs goes on; free and mixed stop it), every pair is untimed, and job CPU is printed but no longer
  decides.

## Determinism risk found in the code

`classes::VERDICTS` is built unlocked (`SharedMemo::get`, then `insert`, in `Classes::step`): two threads may both
build a verdict, and only one inserts it. Its `interp` visits then depend on scheduling. The memos filled through
`SharedMemo::with` build each key once under the lock, so their totals per process do not depend on which thread
built them. Decision 5 settles how the duplicates are counted.

## Out of scope

- Hardware instruction counts (ETW `InstructionRetired` exists on this machine, `xperf -pmcsources`). They need the
  elevated task's flags changed in `~/.claude`, which is the user's file.
- Valgrind and gungraun (Linux only; WSL has `valgrind`). They suit `benches/`, not the gate.
