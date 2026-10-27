---
status: done
---

# The law generator: a stream-blind source of extra laws for every mine

Date: 2026-10-17. Evidence: `docs/tier-cycle.md`, "A law generator", "Why padding laws pay", "One filter for every
source" and "Where an extras mine's time goes" (runs `2026-10-17-gen-src`, `-gen-cost`, `-gen-salts`, `-gen-twin`,
`-gen-wide`), and "What kind of new law pays most". Roadmap: v0.3 ("Can the kernel itself propose the laws that pay?"), since 2026-10-22 v0.2 ("Does the law generator pay everywhere it runs?"); the numbers below are the new ones.

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
| non-padding laws (22 twins in 17700) | 9 (`-gen-cost`, another build) | 10 | 1043 |

All rows come from one build (b492165 plus the probe): `-gen-wide`, and `-gen-nopad` for the last row's filtered
replay; the unfiltered 9 is `-gen-cost` (4346cda), whose padding arm b492165 reproduced exactly. So, filtered alike, a
stream-blind source beats the stream on salts 1-10: the non-padding laws most (better than the filtered stream on 6
salts, equal on 4, never worse), with 2478 rules against 895 at 26 times the filtered stream's loop time and about 12
times the unfiltered stream's (86 s). Their mines' time is the join's searches (11 times the stream mine's on salt 6,
cmp3d). That cost decides this spec's count rule and its first sweep. Salts 11-20 have not been run for them; on those
salts the unfiltered mixed grammar tied the stream (16 against 15) where salts 1-10 had it far ahead.

Today the source is a probe (`driver::extra_laws`, doc comment "LAW SOURCE PROBE"):
- it is gated on four env vars (`MINE_EXTRA`, `MINE_SOURCE`, `GEN_PAD`, `GEN_TERMS`);
- it takes per-family counts copied from the bucket probe's smallest bucket (add3 60, sbo3 180, cmp3d 350);
- it runs in every loop-mode mine (`cfg.mode == "loop"`), which covers the cold, own, cross, pooled and mixed stages, but it
  was measured on the cold stage only; ref mines take none;
- it memoizes in a process-wide static (`MEMO`, listed in `task::PURE`), keyed by the mine's env (salt, `deep3`);
- it applies the text twin-free filter (phases 1-3) and the unseen-skeleton filter (the mine's own laws) to both
  sources;
- it skips `sphase × n` laws, then filters, then takes n, so it can return fewer than n, printing only the count
  (`MINE_EXTRA <mine>: k laws`).

This spec makes it a designed stage.

## Decision: the source

Chosen by the user on 2026-10-17: option 1, the non-padding laws.

1. **Non-padding laws (chosen).** Lowest M (9) and almost no twins, so the twin filter barely touches it. Costs
   the most: 1373 loop seconds at today's counts. The count rule (§2) is how the cost is managed, and the mining-cost
   work (`PARKED.md`, "Make the join cheaper") is how it shrinks. A 10-salt result, from another build; round B (§2)
   and the acceptance rule below settle it.
2. **Mixed grammar (padding and non-padding).** M 21 filtered, at 359 s: about 3.8 times cheaper than option 1, for M
   21 against 9. At equal count, half its laws are padding laws, which filtered pay less than the stream's. Option 1
   at a smaller f may reach the same cost with lower M; round A's f 0.04 arm tests that.
3. **Padding laws.** Cheap (51 s), but filtered they lose to the stream (40 against 29, worse on 6 salts of 10). A
   generator that does worse than the stream it replaces does not answer v0.2.

The rest of this spec builds option 1. Option 3 becomes a `decided against` line (§5); option 2 is held until round
A's f 0.04 arm, and becomes `decided against` if that arm costs no more than 359 loop seconds over salts 1-10 at lower M.

**Acceptance:** the stage is on by default only if its chosen arm beats the stream control at the same n, over salts
1-20, paired (more salts better than worse). If it only ties or loses, the default is `ABLATE=gen` and the note says
so: v0.2's answer is then "a stream-blind source matches the stream's unseen laws, at a cost".

## Design

### 1. One stage, three regimes

Every mine that adds rules takes generator laws, appended to its law file. That covers three regimes, measured apart:
- **cold loops:** no warm library (stage `cold`); the only regime measured so far;
- **warm loops:** loop mode with a warm library (stages `own`, `cross`, `pooled`, `mixed`); they take extras under today's
  gate, but no run has measured them;
- **ref mines:** the `mines` stage's libraries (`b × k` laws at once, `b` per family from `MINES`, k = 4).

A mine with no rule rounds (`rounds == 0`, the pooled stage's preference mine) takes none. That is one general rule:
extras exist to be mined into rules.

- **One filter chain, for every source and scope:** an extra law is kept only if, against the laws its scope serves,
  it is (a) no twin after both are normalized and (b) of no served law's skeleton. The same chain filters the generator
  and the stream control, so the two arms differ only in where their laws come from.
  - *Normalized:* bottom-up, every node over two leaves (`lt` aside: it only appears at the root and its result is one
    bit) becomes its width-4 value class's representative (`ValueMemo::exhaustive(4, 3)`). The candidates are the
    leaves `x, y, z, 0, -1` and the terms `op(a, b)` for op in add, sub, xor, and, or over those leaves, plus
    `shl1(a, 0)`; the representative is a leaf if a leaf is in the class (the first in that leaf order), else the
    candidate least by (length of `show()` in characters, then `show()`). This is `scripts/twin_wide.py`'s `REP`.
  - *Twin:* equal keys, where a law's key is the least text, over the six renamings of x, y, z and both side orders, of
    the normalized law. A representative is not preserved by renaming (`sub(or(x, y), x)` and its x/y swap normalize
    apart), so the key renames before normalizing, not after. The probes renamed after, so their counts are lower
    bounds; step 1 gives `twin_wide.py` the same key before its parity test.
  - *Served laws:* the family's phase 1-3 batches the scope's loops serve, including each mine's own laws, since a
    loop mines the batch it just served. A ref mine's library is evaluated on loops of other families too (cross,
    pooled, and u3's in mixed), so a ref mine's served laws are its own batches plus every phase 1-3 batch of every
    loop family the sweep runs (cmp3d, add3 and sbo3 by default). That covers u3 and mix3, which have ref mines but
    no default loops.
  - *Skeleton:* the skeleton filter of today's stream source (`skel`), applied against every served law of the scope
    rather than the mine's own laws. A scope's served laws include each mine's, so this drops at least what today's
    filter drops; step 2's legacy arm against the new arms shows the difference.
  - *Scope-level:* the chain depends on the scope, not the mine, so the filtered list and its length L are one per
    scope.
  - *Trivial after normalization:* a law whose sides normalize to the same term is kept. Dropping them from the padding
    laws cost M 40 to 42 and saved 4% of loop time; they are 1.5% of the non-padding laws.
- **What the normalization does not see:** nodes over a non-leaf (`add(t, 0)` with t not a leaf), and a grown node equal
  in value to a deeper subterm of a pool term. Step 5 measures them.
- **Switch:** on by default, off with `ABLATE=gen`, the same pattern as `ABLATE=join` (read with `rewrite::ablated`).
  - Being on by default moves every baseline: notes after the change say which side of `ABLATE=gen` their numbers are on.
  - Children also receive `ABLATE=gen`; they ignore it.
- **Source:** the non-padding grammar laws (the decision above).
- **Stream source:** kept as `GEN_SOURCE=stream`, only as the control arm while v0.2 is open. It reads the test stream,
  so it is no generator.
  - It goes through the same filter chain (which subsumes today's text twin-free filter), then takes the generator's n
    per family by the same slice rule. Its arm takes n laws, where `-gen-wide`'s filtered stream arm took only the
    survivors of 350, so its M and time will differ from that run's 29 and 40 s.
  - Delete it when v0.2 is tagged or answered against, whichever comes first. Deleted 2026-10-22 with `GEN_N=matched`, once v0.2 was answered.

### 2. One count rule, tied to the filtered list

The per-family list was an artifact of matching the bucket probe. It is replaced by one fraction `f`: a mine takes
`n = ⌊f × L⌋` extras, where L is the scope's filtered list length (§1). A ratio to the mine's own law count was
considered and rejected. At any one ratio it would give cmp3d (whose extras carry the gain) too few laws, or add3 and
sbo3 many laws they only pay time for.

Non-padding laws at 20000 terms (`GEN_LAWS` lines of the `nopad_*` arms): add3 1890-1990, sbo3 1820-1977, cmp3d
4730-4965; the twin check keeps over 99%, and the scope-level skeleton filter's share is first measured in step 2
(so L, and the f values below, may shrink). Against these lists, today's counts are f ≈ 0.03, 0.10 and 0.07.

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

A config whose slices do not fit panics with the counts, rather than taking fewer laws. `sweep` checks every scope's L
against its slices before the first stage runs, so a short list stops the sweep before any work. (Today's slice for
phase 3 is laws `[3n, 4n)` of the list before filtering; the new slices index the filtered list from 0, and the legacy
arm of step 2 keeps today's indexing.) Every mine gets n laws in both
arms. If fresh slices lose, the shared slice stays, and the doc says so.

### 4. Generated once per scope family, passed in

`grammar_laws` runs once per family in `driver::sweep`, with the sweep's salt and `deep3` passed as arguments (today
they arrive through the mine's env, which gives the same values; the change is the hand-off, not the values).
`LoopCfg::from_env` (the `loop_stream` test) fills the new fields by calling the same code itself.

The static `MEMO`, its `PURE` entry (11 entries to 10; `task_state_is_classified` does not check that entries are
used, so the entry is removed by hand) and the `GEN_TERMS` env var go. The term budget becomes a constant beside
`grammar_laws` (20000, the value every run used). Generation took 0.1-0.6 s per family on the loop families. The mix3
pool (23665 distinct terms, "Pool duplicates", cut from `docs/tier-cycle.md` on 2026-10-26:
`git show 00a21d9:docs/tier-cycle.md`) has never been generated; its exhaustive values are heavy for `cargo test`, so its L,
time and coverage are measured in step 4's 1-salt probe, not in the unit test.

### 5. Removed

- **`MINE_EXTRA` and `MINE_SOURCE`:** replaced by `ABLATE=gen`, `GEN_SOURCE=stream` (control only) and the f constant.
- **`GEN_PAD` and the `pad` parameter of `grammar_laws`:** the generator yields non-padding laws only. It keeps today's
  sample (padding and non-padding grown terms drawn together, `search.rs:1870-1885`) and drops the padding laws after
  grouping, as `pad: Some(false)` does today, so the list, its shuffle and L stay those of the `nopad_*` arms. Test
  `grammar_pad_splits_the_laws` becomes a check that no law is a padding law; `grammar_laws_lie_outside_the_pool` keeps
  its checks.
- **The padding result:** a `decided against` line in `PARKED.md` (filtered M 40 against the stream's 29, run
  `-gen-wide`; trigger: none). The mixed result is held as the decision section says.
- **The "LAW SOURCE PROBE" wording** in the doc comment. The scripts `gen_src.sh`, `gen_cost.sh` and `gen_twin.sh` stay as
  the record of the runs behind the notes. They will no longer run against new builds, and
  `docs/runs/2026-10-17/README.md` says so.

## Testing

- **`normalize_maps_two_leaf_nodes_to_their_class`** (search.rs):
  - `sub(y, y)` normalizes to `0`, `add(x, 0)` to `x`, and `xor(x, -1)` and `sub(-1, x)` to one term;
  - `add(or(z, x), sub(sub(y, y), 0))` normalizes to `add(r, 0)`, with r the representative of `or(z, x)`'s class: the
    outer `add` is over a non-leaf, so it stays (the gap step 5 measures);
  - `lt(x, x)` is kept;
  - the keys of `sub(or(x, y), x) = t` and of its x/y swap are equal.

  It fails first on a stub that returns its input.
- **`normalize_finds_the_probes_twins`:** fixtures committed under `docs/runs/2026-10-17/fixtures/` (a run folder can be
  deleted by the retention rule): salt 1 of the `-gen-cost` padding arm, cmp3d, the extras of the phase 1-3 loops (1050) and their
  served files (900 laws; twins are rare in the non-padding laws, so the padding arm exercises the filter). Run over those
  extras, not a scope list, the number of laws the Rust twin check drops (trivial laws not counted) equals
  `scripts/twin_wide.py`'s class count for the loop, once the script has the renaming-first key (§1). A mismatch means
  one of the two is wrong; find out which before going on.
- **`extra_slices(len, loops, mines_per_loop, n, fresh)`**, a pure function returning each mine's range in the filtered
  list, ordered (loop, mine), or the shortfall. It is written against a stub returning today's behaviour (`sphase × n`
  for both mines), so its tests fail on assertions:
  - `extra_slices_are_disjoint_and_full`: fresh slices are disjoint, each exactly n long, and they cover
    `loops × mines_per_loop × n`; shared slices give a loop's mines one range;
  - `extra_slices_refuse_a_short_list`: a list shorter than the slices need returns the shortfall.
- **`takes_extras(cfg, ablated: bool)`**, a pure gate (the `ablated` lookup is cached per task, so a unit test cannot
  toggle `ABLATE` in-process): `no_extras_without_rounds` checks that a `rounds == 0` config, and any config with
  `ablated` true, takes none, and that a ref mine with rounds takes them. It fails first on today's gate, which looks only
  at the mode.
- **Existing tests:**
  - `grammar_laws_lie_outside_the_pool` stays (mix3 is left to step 4's probe, §4);
  - `task_state_is_classified` must pass with `MEMO` gone.
- **Suite:** `cargo test --release --test church_bv -j 8`.
- **Sweep checks** (cold only; the warm and ref paths have the unit tests above and step 4's sweeps):
  - **Off path:** `ABLATE=gen` against the plain arms of `2026-10-17-gen-src` (salts 1-10) and `-gen-salts` (11-20), time
    columns aside. Both were older builds (da775e7 and 4346cda plus the probe), and `-gen-wide` found replays of
    `-gen-src` differ in 2-6 of 90 rule files on b492165. So rebuild b492165's plain arm as the control first; a
    mismatch against it is a refactor bug, one against the older runs alone is build drift.
  - **On path:** a temporary `GEN_COUNTS=legacy` (today's counts, today's skip of `sphase × n`, today's per-mine text
    twin-free and skeleton filters, then take n; no class filter) against `-gen-cost`'s `nopad_*` arms (salts 1-10,
    built on 4346cda, whose padding arm b492165 reproduced exactly). M and rule files must match.

## Build order

1. Extras stage, tests first:
   - `twin_wide.py`'s renaming-first key and the committed fixtures;
   - `normalize` and its tests;
   - `extra_slices` and its tests;
   - the scope-level filter;
   - the f rule;
   - the `LoopCfg` fields;
   - `takes_extras` (the `rounds == 0` rule, ref mines in);
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
4. Warm loops and ref mines: full sweeps with `SWEEP="mines mines:u3 own cold cross pooled mixed"` (the default `mines`
   covers sbo3, add3, mix3 and cmp3d; `mixed` needs `lib_u3`), salts 1-10, in three arms: generator on, `ABLATE=gen`,
   and on with ref mines off (a temporary `ABLATE=gen_ref`). Ref mines build the libraries the warm loops start from, so
   the third arm separates their effect from the loops'. mix3 and u3 enter as ref mines only; their loop stages
   (`cold:mix3` and the like) are not part of the default sweep and stay out. The 1-salt probe records mix3's and
   u3's L and generation time.
   - Ref mines mine 200-400 laws against a loop mine's 100, so the same f gives them a smaller share of extras. A ref
     loss may be that share, not the generator. The table states it, and a ref loss is followed up before the regime
     is turned off.
   - A plain sweep of mines, own, cold and pooled took about 8 s per salt (`2026-10-17-op-cache-ab`, two builds side
     by side), a floor for this sweep, which adds cross, mixed, u3 and the extras. A 1-salt probe goes first, and its
     time sets the stated estimate.
   - A regime whose M gets worse runs with the generator off, and the doc says why. `ABLATE=gen_ref` goes after the
     decision.
   - Done 2026-10-22 (plan `docs/superpowers/plans/2026-10-22-generator-warm-ref.md`, runs `2026-10-22-gen-warm-probe`
     and `-gen-warm`): the third arm came from `LIB=` (ref mines and loops in separate sweeps, a 2×2), so
     `ABLATE=gen_ref` was never written. Every regime pays; the stage stays on (`docs/tier-cycle.md`, "The law
     generator on ref mines and warm loops").
5. Hidden twins beyond two-leaf nodes: count the generator's laws that twin a served law once any subterm is replaced
   by the least term of equal value up to the pool's depth (which covers `add(t, 0)` over a non-leaf t, and a grown node
   equal to a deeper pool subterm). If the count is material, the filter widens to it.
   - Done 2026-10-22 (run `2026-10-22-gen-warm-fix`): `ClassReps` normalizes every node below a law's root over the
     family pool's subterms, or to a child of equal value, and the filter drops trivial laws too. Of step 4's drawn
     extras 11.0% of the loops' and 8.6% of the ref mines' were hidden twins, in every family, and 30% of the loops'
     trivial; the filter widened. M rises with them gone (warm 735 to 754, cold 1451 to 1475), and the generator still
     pays against the generator off but on mixed loops (`docs/tier-cycle.md`, "Hidden twins beyond two-leaf nodes").
     The rise is mostly n halving with L: at f = 0.32 (run `2026-10-22-gen-f32`), about the old n, M is warm 729 and
     cold 1460 and mixed no longer loses ("The generator's n after the wider filter").
     The first attempt (b5e03cd, runs `2026-10-22-hidden-twins` and `-rest`) normalized the root too, so most served
     laws turned trivial and the filter barely filtered; its numbers are void.
   - Since 2026-10-23 the filter's classes are the class table's (`search::twin_key`, spec
     `2026-10-22-class-table-normal-form-design.md` §6); `ClassReps` and its per-family pools are gone
     (`docs/tier-cycle.md`, "The class table as a module ...").

## Not in scope

- Making mining cheaper (`PARKED.md`, "Make the join cheaper"; the next measurement is a profile of an extras mine).
  It changes this stage's cost, not its design.
- Deeper growth (two grown leaves, depth-2 terms).
- Enumo-style full enumeration.
- Ranking the generator's laws: that is v0.3's learned proposer, which would take this stage's output as its candidates.
- The sbo3 split: at today's counts every grammar arm left sbo3's mined-batch M at 0 or 1 unfiltered, against 40 plain.
  Whether sbo3 has headroom left is a separate question.
