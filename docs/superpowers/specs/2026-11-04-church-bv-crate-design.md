---
status: draft
---

# `church_bv` as a workspace crate (TB1)

Item TB1 of `docs/superpowers/plans/2026-11-04-cleanup-restructure.md`. Facts below are from a read-only look on 2026-11-04
(commit c599226); the plan's first task re-verifies them.

## Intent

`church_bv` (23 `.rs` files, 19.7k lines, 360 `#[test]` attributes; the workspace lists 749 test names in all) is the
repo's research code: bit-vector library, rewriter, provers, miner, drivers. It lives as an integration-test binary of
`tatic`, so it can only be run through `cargo test <exe> driver::x --exact --ignored`, and it re-spawns itself as its own
worker (`driver.rs`, `Worker::spawn`). After TB1 it is a crate of its own, `church-bv`, with a library (the code and its
tests) and a binary (the entry point that drivers, scripts and `tools/runs` call), and `tatic` no longer carries it.

It already depends on nothing but `tatic-kernel`, `tatic-rng`, `hashbrown` and `mimalloc`: no `tatic::` path appears in it.
So the move cuts no coupling; it makes the existing one visible.

## Decided by the user (2026-11-04)

- f1: one crate `crates/church-bv`, lib + bin, flat modules plus `uniform/`. TB2's core/studies directories are decided against.
- g1: two steps. Step 1 is the plain crate move that keeps the 749-name test list. Step 2 is the real bin; its CLI scope is
  settled after step 1 has landed, so this spec fixes step 1 and only frames step 2.
- m1, m3 (2026-11-04): data files in `crates/church-bv/data/`; dead-code lint settled by counting, then one crate-level attribute if needed.
- c1/e1 (SR8): `crates/` layout and hoisted `[workspace.package]` / `[workspace.dependencies]` are in place (c599226).

## Step 1 design

**Layout.** `crates/tatic/tests/church_bv/*.rs` and `uniform/` move (rename only, one commit) to `crates/church-bv/src/`;
`main.rs` becomes `lib.rs`. The data files (`class_key.txt`, `held_{11,13,15,17}.txt`) move to `crates/church-bv/data/`
(decided m1). `crates/church-bv/Cargo.toml`: package
`church-bv` with `version/edition/license.workspace = true`, dependencies `tatic-kernel`, `tatic-rng`, `hashbrown`,
`mimalloc` through `.workspace = true`. Root `members` gains `crates/church-bv`. `tatic` loses the directory and nothing else:
its `tatic-rng` dev-dependency is still used by `compile_fuzz`, `syntax_fuzz`, `ir_fuzz` and `typing`.

**Test names.** The lib is the crate root exactly as `main.rs` was, so module paths, and with them every test name and the
`--exact` filter `driver::worker`, are unchanged. The worker keeps working because it re-runs `current_exe()` with the same
libtest arguments. The exe name stays `church_bv-<hash>.exe` (a lib's unit-test exe is named after the lib), with a new hash.

**Allocator.** `#[cfg(test)] #[global_allocator]` in `lib.rs`, as `tatic`'s own lib does, so the unit-test exe is timed on
mimalloc as before; step 2's bin carries the shipping one. The comment in `crates/tatic/src/lib.rs` that lists
`tests/church_bv/main.rs` is repointed.

**Path edits** (counts from the look; re-grepped by the plan):
- Compile-time: `corpus.rs` two `include_str!` (to `../../../docs/corpora/...`), `machine.rs` `#[path]` to
  `tools/runs/src/state.rs` (to `../../../tools/runs/src/state.rs`), `classes.rs:17` `include_str!("class_key.txt")`
  (to `../data/class_key.txt`); `tools/runs/src/state.rs:3` comment.
- `CARGO_MANIFEST_DIR` joins: `classes.rs:563,612`, `job.rs:696` (`tests/church_bv/...` to `data/...` or `src/...`);
  `corpus.rs`'s `from_repo_root` (`../..`) is unchanged because the package directory is still two levels down.
- Silent if missed: `tools/runs/src/time.rs:87` and its test `:442` (`held_11.txt`); `scripts/streams_ab.sh` (3 lines);
  `scripts/test_gate.sh` (7 lines, a fixture root that mirrors the layout); self-reads `include_str!("symmul.rs")` in
  `uniform/` keep working (relative).
- Commands: `cargo test --test church_bv ...` becomes `cargo test -p church-bv --lib ...` (README 3 lines, `Cargo.toml`
  profile comments, `tools/runs` help text if it says so).
- Docs, repointed with the SR8 method (anchored substitution, then by hand; dated history keeps old paths):
  `docs/TOUR.md` (69 lines, including line 38 "`main.rs` holds only the `mod` lines and the allocator"), `README.md` (8),
  `PARKED.md` (19), `ROADMAP.md` (1), `docs/learned-vs-fixed.md` (1), `docs/tier-cycle.md` (85; only live pointers),
  `CLAUDE.md` unaffected. `bash scripts/tour_check.sh` and `scripts/cite_check.sh` must pass.

**Caches.** The exe hash changes once: the gate's arm cache and the lemma cache (keyed on exe bytes, `lemma_cache.rs:90`)
miss once. Instruction counts across the move are compared by the `church_bv` exe before and after (ICOUNT.md), as in SR8.

**Dead-code lint (decided m3: measure, then one attribute).** In a lib, items used only by tests warn as dead code
in a non-test build, where they did not in a test binary. The plan's first task counts the warnings; if there are many, the
settled answer is one crate-level `#![cfg_attr(not(test), allow(dead_code))]` that step 2 deletes once the bin uses them,
not per-item allows. That attribute is the only expected new line in the code.

## Step 2 frame (not designed here)

A `[[bin]]` that replaces "find the test exe and pass libtest arguments" by subcommands (`loop`, `worker`, the sweeps the
README names). Settled after step 1: which `#[ignore]`d tests become subcommands, whether the worker's protocol keeps
`TATIC_WORKER` and libtest arguments or becomes `church-bv worker`, what `tools/runs` and the scripts call, and the shipping
allocator. Step 2 changes an interface that the gate's cache key and about 100 doc lines name, so it gets its own spec.

## Non-goals

Splitting `rewrite.rs` or `encoding.rs` (TB3); renaming modules; changing any test; the CLI; touching `tatic` beyond the
removed directory and one comment; a version bump or tag.

## Anti-goals

A run that silently reads a different `held_*.txt` or `class_key.txt` (the lemma cache and `CHECK_LAWFILE` hash their
contents); a test list that differs from the 749 names; the lib suite or `church_bv` losing the `[profile.test]` setting
(profiles stay in the root).

## Verification

`cargo check --workspace --all-targets` (no new warnings beyond the two known); the sorted test list equals
`.superpowers/rs/sr8-before.txt`; `cargo test -p church-bv --lib` and the gate script's 0 failures; the full suite through
`run.ps1`; `cargo metadata --locked` differs from the lockfile only by the new package; `tour_check`/`cite_check`;
`church_bv` count before and after within the A/A spread; `tools/runs` tests (45) after the path edits.

## Left to the builder

Substitution commands; where the dead-code attribute goes if needed; commit split inside step 1 (rename-only first).
