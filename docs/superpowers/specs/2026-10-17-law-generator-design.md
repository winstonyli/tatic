---
status: draft
---

# The law generator: a stream-blind source of extra laws for every mine

Date: 2026-10-17. Evidence: `docs/tier-cycle.md`, "A law generator", "Why padding laws pay", "One filter for every
source" and "Where an extras mine's time goes" (runs `2026-10-17-gen-src`, `-gen-cost`, `-gen-salts`, `-gen-twin`,
`-gen-wide`), and "What kind of new law pays most". Roadmap: v0.3 ("Can the kernel itself propose the laws that pay?").

## Why

Extra laws given to a mine cut later machine proofs. Until now the extras that paid came from the test stream itself.
`search::grammar_laws` needs no stream: it grows one leaf of a pool term into an operator over two leaves and keeps the
value-equal pairs. Unfiltered, on cold sweeps over salts 1-20, its laws tie with the stream's own unseen laws
(mined-batch M 28 against 44, plain 221).

Both sources hide served laws. A law can be a served law with a two-leaf node rewritten as another of equal value
(`sub(y, y)` for `0`, `xor(x, -1)` for `sub(-1, x)`), which the text-level twin filter cannot see. Normalizing every
two-leaf node to its value class's representative, on both sides of both laws, finds such twins in 48% of the stream's
unseen laws, 42% of the padding laws (a grown leaf equal to a leaf), 17% of the mixed grammar's, and 0.1% of the
non-padding laws. Replayed with those twins dropped (salts 1-10):

| source | M, unfiltered | M, filtered | loop seconds, filtered |
|---|---|---|---|
| stream's unseen laws (control) | 31 | 29 | 40 |
| padding laws | 16 | 40 | 51 |
| mixed grammar | 12 | 21 | 359 |
| non-padding laws (22 twins in 17700) | 9 | about 9 (not replayed) | 1373 |

So, filtered alike, a stream-blind source beats the stream: the non-padding laws most, at about 34 times the filtered
stream's loop time. Their mines' time is the join's searches (11 times the stream mine's on salt 6, cmp3d). That cost
decides this spec's count rule and its first sweep.

Today the source is a probe (`driver::extra_laws`, doc comment "LAW SOURCE PROBE"):
- it is gated on three env vars (`MINE_EXTRA`, `MINE_SOURCE`, `GEN_PAD`);
- it takes per-family counts copied from the bucket probe's smallest bucket (add3 60, sbo3 180, cmp3d 350);
- it runs in every loop-mode mine (`cfg.mode == "loop"`), which covers the cold, own, cross, pooled and mixed stages, but it
  was measured on the cold stage only;
- it memoizes in a process-wide static (`MEMO`, listed in `task::PURE`);
- it reads `RULEMINER_DEEP3` with default 0 rather than the sweep's `deep3`;
- it skips `sphase × n` laws, then filters, then takes n, so it returns fewer than n without a word if the list runs out.

This spec makes it a designed stage.

## Decision for review: the source

1. **Non-padding laws (recommended).** Lowest M (9) and almost no twins, so the result needs no filter to be honest;
   costs about 34 times the filtered stream's loop time at today's counts. The count rule (§2) is how the cost is
   managed, and the mining-cost work (`PARKED.md`, "Make the join cheaper") is how it shrinks.
2. **Mixed grammar (padding and non-padding).** M 21 at 9 times the stream's time. Its padding half adds laws that,
   filtered, pay less than the stream's, so it is a diluted option 1, not a cheaper version of it.
3. **Padding laws.** Cheap (51 s), but filtered they lose to the stream (40 against 29, worse on 6 salts of 10). A
   generator that does worse than the stream it replaces does not answer v0.3.

The rest of this spec assumes option 1. Options 2 and 3 become `decided against` lines (§5).

## Design

### 1. One stage, three regimes

Every mine that adds rules takes generator laws, appended to its law file. That covers three regimes, measured apart:
- **cold loops:** no warm library (stage `cold`); the only regime measured so far;
- **warm loops:** loop mode with a warm library (stages `own`, `cross`, `pooled`, `mixed`); they take extras under today's
  gate, but no run has measured them;
- **ref mines:** the `mines` stage's libraries (`b × k` laws at once, `b` per family from `MINES`, k = 4).

A mine with no rule rounds (`rounds == 0`, the pooled stage's preference mine) takes none. That is one general rule:
extras exist to be mined into rules.

- **One twin filter, for every source:** an extra law is kept only if it is no twin (up to renaming variables and
  swapping sides) of a law its scope serves, after both are normalized.
  - *Normalized:* bottom-up, every node over two leaves (`lt` aside: its result is one bit) becomes its value class's
    representative: a leaf if a leaf has its exhaustive width-4 value (`ValueMemo::exhaustive(4, 3)`), else the
    shortest, then least by `show()`, operator-over-two-leaves term with that value. Served laws are normalized the same
    way.
  - *Served laws:* every batch of every loop in the scope (§3), including each mine's own laws, since a loop mines the
    batch it just served.
  - *Scope-level:* the filter depends on the scope, not the mine, so the filtered list and its length L are one per
    scope.
  - *Trivial after normalization:* a law whose sides normalize to the same term is kept. Dropping them from the padding
    laws cost M 40 to 42 and saved 4% of loop time; they are 1.5% of the non-padding laws.

  The per-mine unseen-skeleton filter does not apply to the generator: every leaf slot of the add3, sbo3 and cmp3 pools
  ranges over all of `leaves3()`, so a term with a pool term's skeleton is in the pool, and a grown term is not. The twin
  filter is the check that matters. The skeleton filter stays part of the stream control arm's definition.
- **What the normalization does not see:** a grown node equal in value to a deeper subterm of a pool term. Step 5
  measures it.
- **Switch:** on by default, off with `ABLATE=gen`, the same pattern as `ABLATE=join` (read with `rewrite::ablated`).
  - Being on by default moves every baseline: notes after the change say which side of `ABLATE=gen` their numbers are on.
  - Children also receive `ABLATE=gen`; they ignore it.
- **Source:** the non-padding grammar laws (the decision above).
- **Stream source:** kept as `GEN_SOURCE=stream`, only as the control arm while v0.3 is open. It reads the test stream,
  so it is no generator.
  - It keeps its own filters (text twin-free against phases 1-3, unseen skeleton), then the same class filter, then
    takes the generator's n per family by the same slice rule, sliced after its filters.
  - Delete it when v0.3 is tagged or answered against, whichever comes first.

### 2. One count rule, tied to the filtered list

The per-family list was an artifact of matching the bucket probe. It is replaced by one fraction `f`: a mine takes
`n = ⌊f × L⌋` extras, where L is the scope's filtered list length (§1). A ratio to the mine's own law count was
considered and rejected. At any one ratio it would give cmp3d (whose extras carry the gain) too few laws, or add3 and
sbo3 many laws they only pay time for.

Non-padding laws at 20000 terms (`GEN_LAWS` lines of the `nopad_*` arms): add3 1890-1990, sbo3 1820-1977, cmp3d
4730-4965; the filter keeps over 99%. Today's counts are f ≈ 0.03, 0.10 and 0.07.

Cost grows with n: at today's counts a cold sweep took 100-203 s per salt (`-gen-cost` nopad, wall). `f` is set by
measurement before the default is fixed:
- cold sweeps, two rounds:
  - **round A**, salts 1-10: fresh slices (§3) at f ∈ {0.04, 0.08}, shared slices at f ∈ {0.08, 0.16};
  - **round B**, salts 11-20: the best arm of round A and the cheapest arm that meets the rule below against it;
- per arm, the table gives M per family, rules and loop seconds;
- the best arm has the lowest total mined-batch M. Each other arm gets a paired count against the best (salts better,
  equal, worse), since totals near 10 move by several on one salt;
- the default is the cheapest arm (by loop seconds) with no more worse salts than better ones against the best, over
  all 20 salts.

The arms are not fully crossed: fresh at 0.16 fits (§3) but is left out for cost. So "variety, not count" is measured at
f = 0.08 only.

### 3. Slices: drawn without replacement, never short

Today both mines of a cold loop get the same extras: the slice depends on the loop's phase only, so `laws_extra_0.txt`
equals `laws_extra_1.txt`, checked on salt 1, cmp3d.

The designed stage draws slices from the scope's filtered list.
- **Scope:** one (stage, source, family), that is, its 3 loops (phases 1-3) of 2 mines each, or one ref mine. Different
  scopes are independent runs and may reuse laws.
- **Hand-off:** `sweep` filters once per scope and hands each loop its list and its first slice index, in two new
  `LoopCfg` fields.
- **fresh:** the scope's mines take consecutive n-law slices, in the order (phase, mine). This needs `6n ≤ L`: f ≤ 1/6.
- **shared:** both mines of a loop take the loop's one slice. This needs `3n ≤ L`: f ≤ 1/3.

A config whose slices do not fit panics with the counts, rather than taking fewer laws. Every mine gets n laws in both
arms. If fresh slices lose, the shared slice stays, and the doc says so.

### 4. Generated once per scope family, passed in

`grammar_laws` runs once per family in `driver::sweep`, with the sweep's own salt and `deep3` (not the env default).
`LoopCfg::from_env` (the `loop_stream` test) fills the new fields by calling the same code itself.

The static `MEMO`, its `PURE` entry (11 entries to 10) and the `GEN_TERMS` env var go. The term budget becomes a
constant beside `grammar_laws` (20000, the value every run used). Generation took 0.1-0.6 s per family on the loop
families. The mix3 pool (about 27000 terms, more than the sample) has never been generated, so its L, its time and its
coverage are recorded before step 4.

### 5. Removed

- **`MINE_EXTRA` and `MINE_SOURCE`:** replaced by `ABLATE=gen`, `GEN_SOURCE=stream` (control only) and the f constant.
- **`GEN_PAD`, the `pad` parameter and padding generation in `grammar_laws`:** the generator yields non-padding laws
  only. Test `grammar_pad_splits_the_laws` goes; `grammar_laws_lie_outside_the_pool` keeps its checks.
- **The padding and mixed results:** two `decided against` lines in `PARKED.md`. Padding: filtered M 40 against the
  stream's 29 (run `-gen-wide`). Mixed: M 21, a diluted non-padding source. Trigger for both: none.
- **The "LAW SOURCE PROBE" wording** in the doc comment. The scripts `gen_src.sh`, `gen_cost.sh` and `gen_twin.sh` stay as
  the record of the runs behind the notes. They will no longer run against new builds, and
  `docs/runs/2026-10-17/README.md` says so.

## Testing

- **`normalize_maps_two_leaf_nodes_to_their_class`** (search.rs):
  - `sub(y, y)` normalizes to `0`, `add(x, 0)` to `x`, and `xor(x, -1)` and `sub(-1, x)` to one term;
  - `add(or(z, x), sub(sub(y, y), 0))` normalizes to `add(r, 0)`, with r the representative of `or(z, x)`'s class: the
    outer `add` is over a non-leaf, so it stays (the gap step 5 measures);
  - `lt(x, x)` is kept.

  It fails first on a stub that returns its input.
- **`normalize_finds_the_probes_twins`:** on salt 1, cmp3d phase 1 of the `-gen-cost` padding arm (twins are rare in the
  non-padding laws, so the padding arm exercises the filter), the number of extras the Rust filter drops equals
  `scripts/twin_wide.py`'s class count for that loop. A mismatch means one of the two is wrong; find out which before
  going on.
- **`extra_slices(laws, phases, mines, n, fresh)`**, a pure function returning each mine's range or the shortfall. It is
  written against a stub returning today's behaviour (`sphase × n` for both mines), so its tests fail on assertions:
  - `extra_slices_are_disjoint_and_full`: fresh slices are disjoint, each exactly n long, and they cover `mines × n`;
  - `extra_slices_refuse_a_short_list`: a list shorter than the slices need returns the shortfall.
- **`no_extras_without_rounds`:** a `rounds == 0` config, and any config under `ABLATE=gen`, gets no extras. It fails first
  on today's gate, which looks only at the mode.
- **Existing tests:**
  - `grammar_laws_lie_outside_the_pool` stays and gains mix3;
  - `task_state_is_classified` must pass with `MEMO` gone.
- **Suite:** `cargo test --release --test church_bv -j 8`.
- **Sweep checks** (cold only; the warm and ref paths have the unit tests above and step 4's sweeps):
  - **Off path:** `ABLATE=gen` against the plain arms of `2026-10-17-gen-src` (salts 1-10) and `-gen-salts` (11-20), time
    columns aside. Both were older builds (da775e7 and 4346cda plus the probe), and `-gen-wide` found replays of
    `-gen-src` differ in 2-6 of 90 rule files on b492165. So rebuild b492165's plain arm as the control first; a
    mismatch against it is a refactor bug, one against the older runs alone is build drift.
  - **On path:** a temporary `GEN_COUNTS=legacy` (today's counts, today's slice, no class filter) against `-gen-cost`'s
    `nopad_*` arms (salts 1-10, built on 4346cda, whose padding arm b492165 reproduced exactly). M and rule files must
    match.

## Build order

1. Extras stage, tests first:
   - `normalize` and its tests;
   - `extra_slices` and its tests;
   - the scope-level filter;
   - the f rule;
   - the `LoopCfg` fields;
   - the `rounds == 0` rule;
   - `ABLATE=gen` and `GEN_SOURCE=stream`;
   - temporary `GEN_SHARED=1` and `GEN_COUNTS=legacy`;
   - removals.
2. Cold sweeps through `run.ps1`, non-padding source:
   - round A (salts 1-10): four generator arms, `ABLATE=gen`, `GEN_COUNTS=legacy` (it must match before the other arms
     count), and `GEN_SOURCE=stream` at the fresh 0.08 arm's counts;
   - round B (salts 11-20): the two arms §2 names, `ABLATE=gen` and the stream control.

   Expected wall time, from 100-203 s per salt at today's counts (f ≈ 0.07) and cost taken as linear in n (mining may be
   superlinear, so these are floors): round A about 2.5 h (f 0.04 about 15 min, each 0.08 arm about 25 min, shared 0.16
   about 50 min, legacy about 25 min, the rest a few minutes), round B about 1-1.5 h. A 1-salt probe of the shared 0.16
   arm goes first and its time replaces these estimates.
3. Fix the default f and the slice choice, delete `GEN_SHARED`, `GEN_COUNTS`, and the fresh-slice code if it lost. Update
   the note, `PARKED.md` and `ROADMAP.md`.
4. Warm loops and ref mines: full sweeps (mines, own, cold, cross, pooled, mixed: every stage the default turns on; mines
   includes mix3), salts 1-10, in three arms: generator on, `ABLATE=gen`, and on with ref mines off (a temporary
   `ABLATE=gen_ref`). Ref mines build the libraries the warm loops start from, so the third arm separates their effect
   from the loops'.
   - Ref mines mine 200-400 laws against a loop mine's 100, so the same f gives them a smaller share of extras. A ref
     loss may be that share, not the generator. The table states it, and a ref loss is followed up before the regime
     is turned off.
   - A plain full sweep takes about 8 s per salt (`2026-10-17-op-cache-ab`). A 1-salt probe goes first, and its time
     sets the stated estimate.
   - A regime whose M gets worse runs with the generator off, and the doc says why. `ABLATE=gen_ref` goes after the
     decision.
5. Hidden twins beyond two-leaf nodes: count the generator's laws that twin a served law once any subterm is replaced
   by the least term of equal value up to the pool's depth (which covers `add(t, 0)` over a non-leaf t, and a grown node
   equal to a deeper pool subterm). If the count is material, the filter widens to it.

## Not in scope

- Making mining cheaper (`PARKED.md`, "Make the join cheaper"; the next measurement is a profile of an extras mine).
  It changes this stage's cost, not its design.
- Deeper growth (two grown leaves, depth-2 terms).
- Enumo-style full enumeration.
- Ranking the generator's laws: that is v0.4's learned proposer, which would take this stage's output as its candidates.
- The sbo3 split: at today's counts every grammar arm left sbo3's mined-batch M at 0 or 1 unfiltered, against 40 plain.
  Whether sbo3 has headroom left is a separate question.
