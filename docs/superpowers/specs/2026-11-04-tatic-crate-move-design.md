---
status: draft
---

# Move `tatic` to `crates/tatic` (SR8)

Item SR8 of `docs/superpowers/plans/2026-11-04-cleanup-restructure.md`, the follow-up the user chose after SR4. Surveys:
two read-only passes on 2026-11-04 (paths, Cargo mechanics); every count below is theirs and is re-verified by the plan's
first task.

## Intent

After SR4 the workspace is a root package `tatic` plus two crates under `crates/`. That is asymmetric: one crate owns the
repo root, the manifest carries both package and workspace tables, and `src/`, `tests/`, `benches/` sit beside `docs/`,
`scripts/` and `tools/`. After SR8 all three crates are siblings under `crates/` and the root is a virtual workspace: it
holds the workspace manifest, the profiles, the lockfile, and repo-level docs and tooling.

Goals: a symmetric layout; no behaviour change (same 749 test names, same test results, same package names and binaries);
every live path reference repointed in the same series of commits.

Non-goals: moving `docs/`, `scripts/` or `tools/` (decided: they are repo-level); hoisting `[workspace.package]` and
`[workspace.dependencies]` (separate commit, decided e1); renaming the package `tatic`; touching `church_bv` beyond its
path fixes (TB1 is next and moves it again); rewriting dated history.

## Decided by the user (2026-11-04)

- c1: SR8 before TB1.
- d1: virtual root; `docs/`, `scripts/`, `tools/`, `README.md`, `ROADMAP.md`, `PARKED.md`, `TYPES.md`,
  `RELATED_WORK.md`, `CLAUDE.md`, `Cargo.lock`, `.cargo/` and `target/` stay at the repo root.
- e1: the move is pure; hoisting shared package fields and dependencies is a separate commit after it.

## Design

**Layout.** `git mv src tests benches crates/tatic/` (94 tracked files), as one commit with no content edits so every file
is a 100% rename. `crates/tatic/Cargo.toml` takes `[package]` (with `default-run = "demo"`), `[dependencies]`,
`[dev-dependencies]` and both `[[bench]]` tables from the root manifest, with the path dependencies rewritten to
`../tatic-kernel` and `../tatic-rng`. The root keeps only `[workspace]` and the two `[profile.*]` tables.

**Root manifest.** `[profile.sweep]` and `[profile.test]` must stay in the root: Cargo ignores profiles in member manifests,
which would silently turn the lib suite from 2.9 s into 32.5 s and drop fat LTO from sweeps. `[workspace]` gets
`members = ["crates/tatic", "crates/tatic-kernel", "crates/tatic-rng"]`, no `default-members` (a virtual root without it
defaults to all members, the same set as today; `"."` would be a hard error), `exclude = ["tools/runs"]`, and an
explicit `resolver = "3"`: today the root package's edition 2024 implies it, a virtual manifest has no edition and would
fall back to resolver 1 with different feature unification.

**Path edits** (survey counts, to be re-grepped):
- Compile-time: `tests/church_bv/corpus.rs` two `include_str!("../../docs/corpora/...")` and `tests/church_bv/machine.rs`
  `#[path = "../../tools/runs/src/state.rs"]` each gain two `..` levels (the comment at `tools/runs/src/state.rs:3` too).
- Silent if missed: `tools/runs/src/time.rs` (`held_11.txt` under `tests\church_bv`, plus its unit test),
  `scripts/streams_ab.sh` (`ls "$root/tests/church_bv"`), `scripts/test_gate.sh` (a fixture root that mirrors the layout),
  `.gitattributes` (`tests/golden/*.wat`), and the relative `CORPUS=` hint at `tests/church_bv/corpus.rs:66`: `cargo test`
  runs test exes with cwd at the package directory, which is now `crates/tatic`, so a repo-root-relative value no longer
  resolves. Builder's call, provisional: `corpus_report` resolves a relative `CORPUS` and
  `CORPUS_RULES` against the repo root, so the commands in `docs/corpora/*/SOURCE.md` keep working.
- No change: the five `CARGO_MANIFEST_DIR` joins (they move with the package), the self-relative `include_str!("x.rs")`
  sites, `.cargo/config.toml`, `Cargo.lock`, `/target`, `bench_ab.sh` (to be checked once), `tools/runs`'s checkout lookup.

**Docs.** Live path-prefixed cites are repointed with a boundary-anchored substitution (a non-path character before
`src/`, `tests/`, `benches/`, so `crates/tatic-kernel/src/` and `tools/runs/src/` are never hit): `docs/TOUR.md` (about 118
lines), `README.md` (about 17), `PARKED.md` (about 19), `ROADMAP.md`, `docs/learned-vs-fixed.md`, `CLAUDE.md` (the version
field is now `crates/tatic/Cargo.toml`). Dated history keeps its old paths, as in SR4: `docs/tier-cycle.md` dated sections,
`RELATED_WORK.md` finding text (already stale from older moves), done specs and plans, `docs/runs/**`, and the `git show
<sha>^:tests/...` recovery commands. `docs/tier-cycle.md` live "code:" pointers that name a path are repointed; sections
with dates are not. `docs/TOUR.md` is updated in the same commit as the paths and `tour_check.sh` must pass.

**Defaults.** `cargo run` at a virtual root with three members might not pick `demo`; the plan tests it and, if it fails,
documents `cargo run -p tatic` (no `default-members`, which would narrow bare `cargo test`).

**Commits.** Rename-only, then manifests plus path fixes (one commit, so only the rename commit is unbuildable), then docs,
then the `docs/runs.md` rows.

**Caches.** Every test and bench exe gets a new hash suffix and different baked-in paths, so the gate's arm cache and the
lemma cache miss once. Instruction counts taken before the move are not comparable to counts after it by path or exe name;
the check is an A/A on the same revision plus the before/after pair of the `church_bv` test exe (ICOUNT.md).

## Verification

`cargo check --workspace --all-targets`; the test-name list equals `.superpowers/rs/before.txt`'s 749 names; `cargo test
--workspace --lib --bins`, then the integration tests through `run.ps1`; `bash scripts/cite_check.sh`,
`bash scripts/tour_check.sh`, `bash scripts/test_gate.sh`; `cargo run` (demo) and `cargo bench --no-run`; `cargo metadata
--locked` (the lockfile does not change); the profiles take effect (the lib suite stays near 3 s); a count A/B of the
`church_bv` exe; rebuild `tools/runs` and run its tests.

## Left to the builder

The exact substitution commands; whether `crates/*` or explicit paths in `members` (explicit is the SR4 precedent);
ordering of the path-fix commits.
