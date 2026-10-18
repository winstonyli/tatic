---
status: draft
---

# The law generator: a stream-blind source of extra laws for every mine

Date: 2026-10-17. Evidence: `docs/tier-cycle.md`, "A law generator" (runs `2026-10-17-gen-src`, `-gen-cost`, `-gen-salts`)
and "What kind of new law pays most". Roadmap: v0.3 ("Can the kernel itself propose the laws that pay?").

## Why

Extra laws given to a mine cut later machine proofs. Until now the extras that paid came from the test stream itself.
`search::grammar_laws` needs no stream. It grows one leaf of a pool term and keeps the value-equal pairs. On cold sweeps
over salts 1-20 it ties with the stream's own unseen laws: mined-batch M 28 against 44, against 221 with no extras.
Most of that gap is salts 7 and 9; without them the totals are 28 against 30. Its padding-only slice reaches M 27 at 7%
more rules and 1.7-1.9 times the stream arm's loop time. Fewer laws lose part of the gain: at half the counts M is 33, at
a quarter 64.

This passes step 1's test ("does the gain hold at matched cost?") as a tie, not a win. The padding slice costs about
what the stream arm costs and gets the same M without reading the stream.

Today the source is a probe (`driver::extra_laws`, doc comment "LAW SOURCE PROBE"):
- it is gated on three env vars (`MINE_EXTRA`, `MINE_SOURCE`, `GEN_PAD`);
- it takes per-family counts copied from the bucket probe's smallest bucket (add3 60, sbo3 180, cmp3d 350);
- it runs in every loop-mode mine (`cfg.mode == "loop"`), which covers the cold, own, cross, pooled and mixed stages, but it
  was measured on the cold stage only;
- it memoizes in a process-wide static (`MEMO`, listed in `task::PURE`);
- it skips `sphase × n` laws, then filters, then takes n, so it returns fewer than n without a word if the list runs out.

This spec makes it a designed stage.

## Design

### 1. One stage, three regimes

Every mine that adds rules takes generator laws, appended to its law file. That covers three regimes, measured apart:
- **cold loops:** no warm library (stage `cold`); the only regime measured so far;
- **warm loops:** loop mode with a warm library (stages `own`, `cross`, `pooled`, `mixed`); they take extras under today's
  gate, but no run has measured them;
- **ref mines:** the `mines` stage's libraries (`b × k` laws at once, `b` per family from `MINES`, k = 4).

A mine with no rule rounds (`rounds == 0`, the pooled stage's preference mine) takes none. That is one general rule:
extras exist to be mined into rules.

- **Filters only where they can bite:** every generator law has a side outside the pool. Pools are closed under
  renaming, so no generator law twins a stream law or shares the skeleton of one, including the mine's own laws. The
  twin-free and unseen-skeleton filters therefore stay on the stream control arm only, unchanged (phases 1-3). The
  generator path takes its slice as is, and a test checks the argument (Testing).
- **Switch:** on by default, off with `ABLATE=gen`, the same pattern as `ABLATE=join` (read with `rewrite::ablated`). When
  off, sweeps reproduce today's plain numbers exactly. The check diffs the `ABLATE=gen` arm against the `plain_*` folders
  of `2026-10-17-gen-salts` (time columns aside). Being on by default moves every baseline: notes after the change say
  which side of `ABLATE=gen` their numbers are on. Children also receive `ABLATE=gen`; they ignore it.
- **Source:** padding-only grammar laws (`grammar_laws(.., pad: Some(true))`), chosen for cost. The non-padding laws pay
  at least as much per law but cost 14 times the stream arm's time. Nopad and the mixed grammar go from the pipeline (see
  Removed).
- **Stream source:** kept as `GEN_SOURCE=stream`, only as the control arm while v0.3 is open. It reads the test stream,
  so it is no generator. It takes the generator's n per family (its own list is far longer, so the same f would not match
counts), drawn by the same slice rule. Delete it when v0.3 is tagged or answered against,
  whichever comes first.

### 2. One count rule, tied to the generator's own output

The per-family list was an artifact of matching the bucket probe. It is replaced by one fraction `f`: a mine takes
`n = ⌊f × L⌋` extras, where L is the length of the family's generator list (one number per family and sweep; no
filter shortens it, §1). A ratio to the mine's own
law count was considered and rejected. At any one ratio it would give cmp3d (whose extras carry the gain) too few or
add3 and sbo3 (left at M 0-1) many laws they only pay time for.

Padding laws at 20000 terms, from the `GEN_LAWS` lines of `2026-10-17-gen-cost/pad_*`: add3 1546-1645, sbo3 1504-1614,
cmp3d 2520-2662. Today's counts are f ≈ 0.04 for add3, 0.12 for sbo3 and 0.13 for cmp3d. The rule therefore gives add3
about three times its tested count; the f sweep's time column shows whether that costs.

`f` is set by measurement before the default is fixed:
- cold sweeps over salts 1-20 at f ∈ {0.06, 0.12} with fresh slices (§3), and f = 0.12 and 0.25 with the shared slice;
- per arm, the table gives M per family, rules, loop seconds and the salts better, equal or worse than the f = 0.12
  shared arm (a paired count: totals of about 28 move by 3 on one salt);
- the best arm is the one with the lowest total mined-batch M. The default is the cheapest arm (by loop seconds) whose
  paired count against the best arm has no more worse salts than better ones.

### 3. Slices: drawn without replacement, never short

Today both mines of a cold loop get the same extras: the slice depends on the loop's phase only, so `laws_extra_0.txt`
equals `laws_extra_1.txt`, checked on salt 1, cmp3d. The designed stage draws slices from the generator list. The scope
is one (stage, source, family): its 3 loops (phases 1-3) of 2 mines each. Different scopes are independent runs and may
reuse laws. `sweep` hands each loop its first slice index in a new `LoopCfg` field `slice`; a ref mine is a scope of one
mine.
- **fresh:** the scope's mines take consecutive n-law slices, in the order (phase, mine). This needs `6n ≤ L`: f ≤ 1/6;
- **shared:** both mines of a loop take the loop's one slice. This needs `3n ≤ L`: f ≤ 1/3.

A config whose slices do not fit panics with the counts, rather than taking fewer laws. Whether fresh slices beat the
shared slice is measured in the f sweep. If fresh slices lose, the shared slice stays and the doc says so. Every mine gets
n laws in both arms, so at one f the comparison is about variety, not count.

### 4. Generated once per sweep, passed in

`grammar_laws` runs once per family in `driver::sweep`, since salt and deep3 are fixed per sweep. Its laws travel to
`run_loop` through `LoopCfg`, as an `Option<Arc<Vec<(Term, Term)>>>` field next to `warm`. `LoopCfg::from_env` (the
`loop_stream` test) fills it by calling `grammar_laws` itself.

The static `MEMO`, its `PURE` entry (11 entries to 10) and the `GEN_TERMS` env var go. The term budget becomes a
constant beside `grammar_laws` (20000, the value every run used). Generation takes 0.1-0.6 s per family.

### 5. Removed

- **`MINE_EXTRA` and `MINE_SOURCE`:** replaced by `ABLATE=gen`, `GEN_SOURCE=stream` (control only) and the f constant.
- **`GEN_PAD` and the `pad` parameter of `grammar_laws`:** the generator yields padding laws only. Test
  `grammar_pad_splits_the_laws` goes too; `grammar_laws_lie_outside_the_pool` keeps its checks on the padding laws.
- **The no-padding result:** M 9 on salts 1-10 at 14 times the stream's time. It becomes a `decided against` line in
  `PARKED.md`, triggered if mining gets several times cheaper.
- **The "LAW SOURCE PROBE" wording** in the doc comment. The scripts `gen_src.sh` and `gen_cost.sh` stay as the record of
  the runs behind the note. They will no longer run against new builds, and `docs/runs/2026-10-17/README.md` says so.

## Open question carried, not answered here

**Why do padding laws pay?** Each one restates a pool term with one leaf written as a term of equal value, for example
`sub(y, y)` for `0`. Served laws contain no grown terms, so a rule like `sub(x, x) -> 0` has nothing to rewrite in them
directly.

The probe, run after the stage lands:
- on salt 1, list the rules the padding arm's mines keep that plain's do not;
- trace which served laws' proofs use them;
- record the answer in the note.

If the answer names a smaller class (for example "only the laws whose padding is absorbing"), the generator narrows to
it in a later change.

## Testing

- **The slicing is a pure function** `extra_slices(laws: usize, phases: usize, mines: usize, n: usize, fresh: bool)`
  that returns each mine's range or the shortfall. It is written first, against a stub returning today's behaviour
  (`sphase × n` for both mines), so its tests fail on assertions, not on compilation:
  - `extra_slices_are_disjoint_and_full`: fresh slices are disjoint, each exactly n long, and they cover `mines × n`;
  - `extra_slices_refuse_a_short_list`: a list shorter than the slices need returns the shortfall.
- **`generator_laws_pass_the_stream_filters`:** for add3, sbo3 and cmp3d on salt 1, the twin-free and unseen-skeleton
  filters (against phases 1-3 and against the first mine's laws) drop none of the generator list. It guards §1's
  argument and §3's counts. It is a characterization test, expected to pass on its first run: the property holds on
  today's code by construction, and the test is there to catch a future generator that breaks it.
- **Existing tests:**
  - `grammar_laws_lie_outside_the_pool` stays and gains mix3 (the mines stage mines it; `pool3("mix3")` exists, but no
    run has made its laws). Record mix3's law count in the note.
  - `task_state_is_classified` must pass with `MEMO` gone.
- **Suite:** `cargo test --release --test church_bv -j 8`.
- **Sweep checks:**
  - the off path: `ABLATE=gen` against `2026-10-17-gen-salts`'s `plain_*` folders, as in §1;
  - the on path: a temporary `GEN_COUNTS=legacy` reproduces today's counts (60/180/350) and today's slice (skip
    `sphase × n`, both mines alike). Diffed against the `pad_*` folders of `2026-10-17-gen-cost` (salts 1-10) and
    `-gen-salts` (11-20), its M and rule files must match (time columns aside).

## Build order

1. Extras pipeline refactor, tests first:
   - `extra_slices` and its tests;
   - the f rule;
   - laws passed in through `LoopCfg`;
   - the filters confined to the stream arm, and `generator_laws_pass_the_stream_filters`;
   - the `rounds == 0` rule;
   - `ABLATE=gen` and `GEN_SOURCE=stream`;
   - a temporary `GEN_SHARED=1` for the slice A/B, and a temporary `GEN_COUNTS=legacy` for the on-path check;
   - removals.
2. Cold sweeps through `run.ps1`, salts 1-20, padding source:
   - four generator arms (f 0.06 and 0.12 fresh; 0.12 and 0.25 shared);
   - one `ABLATE=gen` arm (the off-path check);
   - one `GEN_COUNTS=legacy` arm (the on-path check, which must match before the other arms count);
   - one `GEN_SOURCE=stream` arm at the f = 0.12 shared arm's counts.

   Expected wall time: 45-90 min sequential. Today's padding arm (f ≈ 0.04-0.13) took 10-37 s per salt, about 20 s on
   average. f = 0.25 may cost several times that if mining is superlinear in its laws.
3. Fix the default f and the slice choice. Delete `GEN_SHARED`, `GEN_COUNTS`, and the fresh-slice code if it lost. Update the note,
   `PARKED.md` and `ROADMAP.md`.
4. Warm loops and ref mines: full sweeps (mines, own, cold, cross, pooled, mixed: every stage the default turns on; mines
   includes mix3, at the f chosen on the loop families), salts 1-10, in three arms: generator on, `ABLATE=gen`,
   and on with ref mines off (a temporary `ABLATE=gen_ref`). Ref mines build the libraries the warm loops start from, so
   the third arm is what separates their effect from the loops'.
   - A plain full sweep takes about 8 s per salt (`2026-10-17-op-cache-ab`). With the generator on, every loop stage
     costs about what the cold stage does, so a 1-salt probe goes first and its time sets the stated estimate (expected
     1-3 min per salt, so 25-60 min for the three arms). `ABLATE=gen_ref` goes after the decision.
   - Measured per regime. A regime whose M gets worse runs with the generator off, and the doc says why. That makes the
     regime, not the family, the unit of the decision.
5. The padding probe above.

## Not in scope

- Deeper growth (two grown leaves, depth-2 terms).
- Enumo-style full enumeration.
- Ranking the generator's laws: that is v0.4's learned proposer, which would take this stage's output as its candidates.
- The sbo3 split. At full counts, every grammar arm left sbo3's mined-batch M at 0 or 1, against 40 plain and 6 for the
  stream. Whether sbo3 has headroom left is a separate question.
