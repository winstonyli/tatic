---
status: draft
---

# The law generator: a stream-blind source of extra laws for every mine

Date: 2026-10-17. Evidence: `docs/tier-cycle.md`, "A law generator" and "Why padding laws pay" (runs `2026-10-17-gen-src`,
`-gen-cost`, `-gen-salts`, `-gen-twin`), and "What kind of new law pays most". Roadmap: v0.3 ("Can the kernel itself
propose the laws that pay?").

## Why

Extra laws given to a mine cut later machine proofs. Until now the extras that paid came from the test stream itself.
`search::grammar_laws` needs no stream: it grows one leaf of a pool term and keeps the value-equal pairs. On cold sweeps
over salts 1-20 it ties with the stream's own unseen laws (mined-batch M 28 against 44, plain 221; 28 against 30 without
salts 7 and 9). Its padding-only slice gets 27 at about the stream arm's cost.

But padding hides served laws. A padding law sets a pool term equal to another pool term with one leaf written as a term
of equal value. Stripped of the padding, about a quarter of them are twins of laws the loops serve, which the text-level
twin filter cannot see. Dropping those twins takes the padding arm on salts 1-10 from M 16 to 30, against 14 for
dropping as many other laws. That is a tie with the stream's 29, at 12% fewer rules.

So with the same twin filter on both, the stream-blind generator matches the stream's unseen laws. That is step 1's
answer ("does the gain hold at matched cost?"): a tie, without reading the stream. A fair stage must filter twins up to
equal-valued subterms.

Today the source is a probe (`driver::extra_laws`, doc comment "LAW SOURCE PROBE"):
- it is gated on three env vars (`MINE_EXTRA`, `MINE_SOURCE`, `GEN_PAD`);
- it takes per-family counts copied from the bucket probe's smallest bucket (add3 60, sbo3 180, cmp3d 350);
- it runs in every loop-mode mine (`cfg.mode == "loop"`), which covers the cold, own, cross, pooled and mixed stages, but it
  was measured on the cold stage only;
- it memoizes in a process-wide static (`MEMO`, listed in `task::PURE`);
- it reads `RULEMINER_DEEP3` with default 0 rather than the sweep's `deep3`;
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

- **One filter, through equal-valued subterms:** a generator law is kept only if, once normalized, it is no twin (up to
  renaming variables and swapping sides) of a law its scope serves (§3).
  - *Normalized:* bottom-up, every node over two leaves whose exhaustive width-4 value (`ValueMemo::exhaustive(4, 3)`)
    equals a leaf's becomes that leaf.
  - *Served laws:* every batch of every loop in the scope. These include each mine's own laws, since a loop mines the
    batch it just served.
  - *Scope-level:* the filter depends on the scope, not the mine, so the filtered list and its length L are one per
    scope.
  - *Trivial after normalization:* a law whose sides normalize to the same term (cmp3d: 1678 of 10500) is kept, as the
    probe's `untwin` arm kept it. Whether those pay is untested.

  The per-mine unseen-skeleton filter does not apply to the generator. Before normalization, no generator law shares a
  pool skeleton: every leaf slot of the add3, sbo3 and cmp3 pools ranges over all of `leaves3()`, so a term with a pool
  term's skeleton is in the pool. After normalization, the twin filter is the check that matters. The skeleton filter
  stays the stream control arm's definition. This is the probe's `untwin` arm.
- **What the normalization does not see:** a grown term equal in value to a deeper pool subterm. The probe left that
  untested, so step 5 measures it before the stage is called fair beyond padding.
- **Switch:** on by default, off with `ABLATE=gen`, the same pattern as `ABLATE=join` (read with `rewrite::ablated`).
  - Being on by default moves every baseline: notes after the change say which side of `ABLATE=gen` their numbers are on.
  - Children also receive `ABLATE=gen`; they ignore it.
- **Source:** padding-only grammar laws (`grammar_laws(.., pad: Some(true))`), chosen for cost. The non-padding laws
  have the lowest measured M (9 on salts 1-10), but at 14 times the stream arm's time, and their M is not yet
  twin-checked. The mixed grammar goes too (see Removed).
- **Stream source:** kept as `GEN_SOURCE=stream`, only as the control arm while v0.3 is open. It reads the test stream,
  so it is no generator.
  - It keeps its own filters (text twin-free against phases 1-3, unseen skeleton), then takes the generator's n per
    family by the same slice rule, sliced after its filters.
  - Delete it when v0.3 is tagged or answered against, whichever comes first.

### 2. One count rule, tied to the filtered list

The per-family list was an artifact of matching the bucket probe. It is replaced by one fraction `f`: a mine takes
`n = ⌊f × L⌋` extras, where L is the scope's filtered list length (§1). A ratio to the mine's own law count was
considered and rejected. At any one ratio it would give cmp3d (whose extras carry the gain) too few laws, or add3 and
sbo3 (left at M 0-1) many laws they only pay time for.

Padding laws at 20000 terms (`GEN_LAWS` lines of the `pad_*` arms): add3 1546-1645, sbo3 1504-1660, cmp3d 2520-2662.
The twin filter keeps about 64-76% of them. That gives L of roughly add3 1050, sbo3 1150, cmp3d 1950, and puts today's
counts at f ≈ 0.06, 0.16 and 0.18.

`f` is set by measurement before the default is fixed:
- cold sweeps over salts 1-20, fresh slices (§3) at f ∈ {0.08, 0.16}, shared slices at f ∈ {0.16, 0.30};
- per arm, the table gives M per family, rules and loop seconds;
- the best arm has the lowest total mined-batch M. Each other arm gets a paired count against the best (salts better,
  equal, worse), since totals of about 30 move by 3 on one salt;
- the default is the cheapest arm (by loop seconds) with no more worse salts than better ones against the best.

The arms are not fully crossed: fresh at 0.30 does not fit (§3). So "variety, not count" is measured at f = 0.16 only.

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
- **`GEN_PAD` and the `pad` parameter of `grammar_laws`:** the generator yields padding laws only. Test
  `grammar_pad_splits_the_laws` goes too; `grammar_laws_lie_outside_the_pool` keeps its checks on the padding laws.
- **The no-padding result:** it becomes a `decided against` line in `PARKED.md`: M 9 on salts 1-10 at 14 times the
  stream's time, twins not checked. It is triggered if mining gets several times cheaper.
- **The "LAW SOURCE PROBE" wording** in the doc comment. The scripts `gen_src.sh`, `gen_cost.sh` and `gen_twin.sh` stay as
  the record of the runs behind the notes. They will no longer run against new builds, and
  `docs/runs/2026-10-17/README.md` says so.

## Testing

- **`normalize_strips_leaf_equal_nodes`** (search.rs):
  - `sub(y, y)` normalizes to `0`, and `add(x, 0)` to `x`;
  - `add(or(z, x), sub(sub(y, y), 0))` normalizes to `or(z, x)`;
  - a pool term is unchanged.

  It fails first on a stub that returns its input.
- **`normalize_finds_the_probes_twins`:** on salt 1, cmp3d phase 1, the number of extras of the `-gen-cost` padding arm
  that the Rust filter drops equals the count `scripts/pad_strip.py` gives. The script modelled `shl1` by guess, so a
  mismatch means one of the two is wrong; find out which before going on.
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
    columns aside. Both were older builds (da775e7 and 4346cda plus the probe). If they mismatch, rebuild b492165 as a
    control to tell a build difference from a refactor bug.
  - **On path:** a temporary `GEN_COUNTS=legacy` (today's counts, today's slice, then the new filter) against
    `2026-10-17-gen-twin`'s `untwin_*` arms (salts 1-10). M and rule files must match.

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
2. Cold sweeps through `run.ps1`, salts 1-20, padding source:
   - four generator arms (fresh at 0.08 and 0.16, shared at 0.16 and 0.30);
   - `ABLATE=gen` (the off-path check);
   - `GEN_COUNTS=legacy` (the on-path check, salts 1-10; it must match before the other arms count);
   - `GEN_SOURCE=stream` at the fresh 0.16 arm's counts.

   Expected wall time: 45-90 min sequential. The untwinned padding arm took 8-18 s per salt (85 loop seconds over 10
   salts). f = 0.30 may cost several times that if mining is superlinear in its laws.
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
     sets the stated estimate (expected 1-3 min per salt, so 25-60 min for the three arms).
   - A regime whose M gets worse runs with the generator off, and the doc says why. `ABLATE=gen_ref` goes after the
     decision.
5. Hidden twins beyond padding: for the non-padding laws (which the stage does not use), count twins after normalizing
   grown terms equal in value to any pool subterm, not only to a leaf. If the padding laws' kept share also changes
   under that wider normalization, the stage's filter widens to it.

## Not in scope

- Deeper growth (two grown leaves, depth-2 terms).
- Enumo-style full enumeration.
- Ranking the generator's laws: that is v0.4's learned proposer, which would take this stage's output as its candidates.
- The sbo3 split. At full counts, every grammar arm left sbo3's mined-batch M at 0 or 1, against 40 plain and 6 for the
  stream; untwinned, sbo3 is back to 7. Whether sbo3 has headroom left is a separate question.
