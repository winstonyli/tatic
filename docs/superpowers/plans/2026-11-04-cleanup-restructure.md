---
status: draft
---

# Restructuring cleanup (survey 2026-11-04)

## Intro

Why now: Q2 closed (`f2e6268`), `main` is clean at `67bfbca`, and the layout has outgrown its first shape: 21 flat modules in `src/`, a
19.7k-line `tests/church_bv` driven as a test binary, a 8558-line `docs/tier-cycle.md`, 389 scripts. This is a trial of
`surveying-for-cleanup` on restructuring (folder and module layout) rather than deletion.

Surveys (read-only Sonnet agents, 2026-11-04, `main` at `67bfbca`): src layout and boundaries; tests and benches; scripts and
tools; docs and root markdown; repo root and build layout; architecture (end-state). Run `wf_69f2bdfc-2f7`. Mechanical baseline:
no compiler or linter warning rules out any item below (none of them is dead code). Claims are the surveys' unless marked
(checked). Overlapping findings from different surveys are merged below under one id with "Same as".

Checked by hand, 2026-11-04:
- `scripts/experiments/` is git-ignored with 0 tracked files (372 files on disk): a delete is not recoverable from git.
- `tools/` has 10 tracked files; the 333 MB is the ignored `tools/runs/target`.
- Branches versus `main` (ahead/behind): `env-cache` 0/757, `rule-index` 0/759, `score-no-plans` 0/754, `screen-key` 0/752 (all
  merged); `ring-spikes` 1/677, `score-pool` 1/700, `origin/lazy-view` 2/601. "No path collision" is weak evidence for branches
  this far behind.
- `compile.rs` calls `specialise::specialise` and `specialise.rs` calls `compile::peel`: the `compile <-> specialise` cycle is real.
- `~/.claude/runs/run.ps1` names `docs/runs.md` (global file: moving that path is a proposal to the user, not an item here).
- 74 lines of `PARKED.md` cite `tier-cycle`, by section name.

## Order and decisions

Pending the user's pick. Suggested order (additive and independent first; shared prerequisites before what depends on them):
RB7, SC5, SC4/RB8, DOC3, then the group decisions below. Decisions not yet taken: the target tree (D1), the crate
question (D2), the `tier-cycle.md` split (D3), the fate of `scripts/experiments` (D4).

## Items by area

### Source layout (SR)
- **SR1. Group the 21 flat `src/` modules by layer** (lang / jit / verify / support / testing), keeping `foo.rs + foo/` throughout. IFACE
  (public paths of 9 modules, ~35 `use tatic::` lines, 3 independence allow-lists, ~20 TOUR cites). ~16 files moved, no logic.
- **SR2. Extract term-shape analysis from `compile.rs` into `shape.rs`** (~300 lines: `peel`, `classify`, `Shape`, `free_vars`,
  `infer_closure_arities`, ...). Removes the `compile <-> specialise` cycle and the prover's dependency on the code generator
  (`proof/*` calls `compile::` ~45 times). ~55 call sites. Also AR8 (shared children walk for `Shape`).
- **SR3. Split `kernel.rs` (2198 lines) into role files under `kernel/`** (expr, stack, subst, hc, reduce, check), root re-exports.
  No external path changes. **Conflict:** the architecture survey rejected this ("fewer, larger files are a feature in the trusted
  core"); decision D5.
- **SR4. Kernel as its own workspace crate** so independence is a compile error. IFACE. Same as RB1, AR4. Replaces
  `independence.rs` and its 3 text-scanning tests; ~12 files moved, 150+ import edits.
- **SR5. One test-placement convention** (`foo/tests.rs` for modules with a large test block). Also TB7.
- **SR6. Gather `cfg(test)` support under `testing/`**; take the allocator hack out of `lib.rs`.
- **SR7. Demo as `src/bin/demo.rs`** like the REPL (1 file, 3 doc lines, 1 manifest line).
- **AR9. Fix `proof/` names:** `hardening.rs` holds the universal prover, `universal.rs` two helpers (~400 lines moved).

### church_bv and tests (TB, AR)
- **TB1. `church_bv` from a test binary to a workspace crate** with a real worker/CLI binary (~26-31 files, ~100 doc/script lines).
  IFACE. Same as RB2, AR1. Changes exe names that the gate's arm-cache key hashes (one-time cache invalidation).
- **TB2. Group `church_bv` into core / uniform / studies directories** (~10 files, ~25 doc cites). Additive; makes TB1 a plain move.
- **TB3. Split `rewrite.rs` (4475 lines) and `encoding.rs` by concern.** ~6,500 lines moved. Same as AR5. Collides with
  `origin/lazy-view` (2 ahead, edits `rewrite.rs` by ~196 lines).
- **TB4. Fuse the four fuzz suites into one `tests/fuzz`** (~150 duplicated helper lines). Cheaper stepping stone: a shared
  `tests/common/mod.rs`.
- **TB5. Retire three prototype-era top-level test files** (~270 lines).
- **TB6. Move `class_key.txt` and `held_*.txt` out of the test source directory** (5 files, ~12 path lines, 2 scripts, 1 Rust tool).
- **TB8. `ctx_scorer` reimplements SplitMix64** despite `tatic::rng` (~20 lines).
- **AR2. One module owns pool/extras selection** (`Keep`, `ExtrasKeep`, `POOL`, `EXTRAS_N`, `EXTRAS_SELECT`, `CTX_WEIGHTS`,
  `POOL_DUMP`): two parsers and one validator collapse (~150 lines deleted). The tripwire case: `Keep` grew `Ctx` this session.
- **AR3. One sweep-arm recipe; delete superseded `runs gate` / `cmp` / `time --sweep|--pcs`** (~600 lines out, bash tally to Rust).
- **AR6. Delete the one-case sweep-stage dispatcher in `driver::sweep`** (~40 lines).
- **AR7. Route the remaining direct `std::env` reads through `Setup`**, knobs declared once (~150 lines).

### Scripts and tools (SC, RB)
- **SC1. `scripts/experiments/` (372 untracked files):** delete, or track a curated subset. Unrecoverable from git: needs the
  user's decision (D4). Also DOC8 (stale pointer to it).
- **SC2. Give shared gate/kk/curve scripts a stable home** and stop citing dated run folders as tools (`docs/runs/2026-10-31/scripts/gate.sh`
  is called by every Q2 gate). 3-4 files, ~10 live cites; historical rows stay as written.
- **SC3. Group `scripts/` by role** (gates, checks, tests, probes); breaks `test_gate.sh`, which extracts functions from
  `streams_ab.sh` by `sed`. 11 files, 115+ `runs.md` rows if the gate moves.
- **SC4. `tools/shr_probe.py`:** move out of `tools/` or delete. Same as RB8. **SC5.** Fix the `tools/` description (one crate; the
  333 MB is its ignored target).
- **SC6. Manifest for the 184 dated run scripts** instead of moving them. **RB5.** Move 8 finished-experiment scripts into
  `docs/runs/<date>/scripts`.
- **RB3. Shared crate instead of `#[path]` source sharing** between `church_bv` and `tools/runs`.
- **RB6. 100 tracked `.patch` spike files and the 1163-row `2026-10-12` tree:** one archive convention.
- **RB7. Delete the four merged local branches** (`env-cache`, `rule-index`, `score-no-plans`, `screen-key`; (checked) 0 ahead).

### Docs (DOC)
- **DOC1. Split `RELATED_WORK.md` (6227 lines):** keep the survey, move the 70+ implementation findings out. ~25 files touched.
- **DOC2. Split `docs/tier-cycle.md` (8558 lines) into `docs/tier-cycle/` by H2** (H3 for the two giants), with a checked index;
  ~130 files get a path-prefix sed. Needs DOC3 first. `PARKED.md` cites by section name, which survives a verbatim split.
- **DOC3. One cite checker for every doc-to-doc cite form** (only `TOUR.md` has one today). Prerequisite for DOC1, DOC2, DOC6.
- **DOC4. Collapse the repeated "JIT meets the loop" / belief-layer story** to one home (3 docs, ~60 lines).
- **DOC5. Cut `README.md` to the front door** (~900 lines to `docs/`). **DOC6.** Move `TYPES.md` and the split-out survey off the root
  (~25 one-token edits; same as RB4).
- **DOC7. `docs/superpowers` consistency:** front matter on every file, patches in `spikes/`, stale drafts.

## Considered and rejected

- Moving `docs/runs.md` beside `docs/runs/`: `run.ps1` hardcodes it (global file; propose to the user if wanted).
- Splitting `docs/runs.md`, `PARKED.md`, or reorganizing `docs/runs/<date>/` by kind: wrapper writes rows, retention keeps them, 135 dated-path cites.
- Moving all `docs/runs/*/scripts` into `scripts/`: breaks 330 `runs.md` and 29 `tier-cycle.md` cites.
- Splitting `src/proof` into a crate: inseparable from the JIT (needs `compile`, `eval`, `samples`, `term`).
- `mod.rs` style: the repo is consistent on `foo.rs + foo/`.
- Making `samples.rs` / `rng.rs` test-only: `main.rs`, benches and tests use them.
- Merging the two bench files; renaming top-level tests into a subfolder (Cargo auto-discovery); pruning `target/` (43 GB, disk hygiene, ask first).
