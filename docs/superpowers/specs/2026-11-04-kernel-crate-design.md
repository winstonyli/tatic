---
status: draft
---

# The kernel as its own workspace crate

Item SR4 of `docs/superpowers/plans/2026-11-04-cleanup-restructure.md` (decision D1). User decisions of 2026-11-04: c1 (kernel
crate only), d1 (`tatic-rng` crate), e1 (crate `tatic-kernel`, every caller rewritten, no re-export shim).

## Why

The kernel (`src/kernel.rs` plus `kernel/{bin,postulates,spaces,tests}.rs`) is the trusted core: what the prover and the
church_bv library rest on. Today "the kernel imports nothing else from tatic" is true by habit; nothing stops a `use
crate::lang::term` from appearing in it. As its own crate with only `hashbrown`, `im` and `stacker` as dependencies, that
becomes a compile error, and the trusted surface has a stated edge: the crate's `pub` items.

A second effect: the kernel's tests and fuzzers (about 1,700 lines) build and run against the kernel alone, so a kernel edit
no longer rebuilds the JIT to test itself. That is an expectation, not a measured gain (a survey builds nothing); the plan
measures it (below).

## Correction to the plan text

The plan said this replaces `independence.rs` and its three text-scanning tests. It does not. Those tests guard the
checkers `decompile`, `spec_check` and `typing` (they share no code with the compiler they check), not the kernel. They stay,
unchanged. SR4 adds a compile-enforced kernel boundary and replaces nothing. The plan item is corrected in the commit that
adds this spec.

## Goals

- `tatic-kernel` is a workspace member whose manifest depends on `hashbrown`, `im`, `stacker` and nothing from tatic.
- `tatic` depends on it; every use of `crate::kernel::…`, `tatic::kernel::…` is rewritten to `tatic_kernel::…`. No `pub use`
  shim in `tatic`, no `kernel` module left in `src/`.
- The SplitMix64 stream has one home, `tatic-rng`, a workspace member with no dependencies, used by `tatic` and by
  `tatic-kernel`'s dev-dependencies.
- Kernel-only tests move into the kernel crate and still run. No test is lost: the full-suite name list after the move equals
  the one before, up to the crate/module path prefix.
- Observable behaviour is unchanged: the same results from the demo and the church_bv sweeps; the same exe-content-keyed caches
  are valid or are invalidated knowingly.

## Non-goals

- No other crates now (term, eval, checkers, church_bv). The three text-scan tests and `testing/independence.rs` stay (c1).
  TB1 (`church_bv` crate) and any checker crates are separate specs.
- No change inside the kernel's logic, its public API shape or its file split (SR3/D5 stay a separate question; with a crate,
  the "one big file" argument gets cheaper to revisit, not forced).
- No re-export shim, no deprecation path (WORKING_STYLE: no compatibility shims).
- No publishing, version bump or tag. Version of every member is `0.6.0`, the workspace's current one.

## Anti-goals

- A move that leaves `cargo test` at the root running fewer tests than before without anyone noticing. (See `default-members`.)
- Splitting the allocator-sensitive kernel timing tests from the allocator they were calibrated under.

## Target layout

```
Cargo.toml                 [package] tatic + [workspace]
crates/tatic-kernel/Cargo.toml   tatic-kernel
crates/tatic-kernel/src/lib.rs   was src/kernel.rs
crates/tatic-kernel/src/{bin,postulates,spaces,tests}.rs   was src/kernel/*.rs   (mod paths unchanged)
crates/tatic-kernel/tests/{kernel_fuzz,kernel_soundness_fuzz,church_encoding,church_lemmas}.rs   moved from tests/
crates/tatic-rng/Cargo.toml      tatic-rng
crates/tatic-rng/src/lib.rs      was src/support/rng.rs
tools/runs                 untouched, excluded from the workspace
```

`git mv` throughout, so renames show at 100% similarity (the files change only in the lines named below).

## Design

### Workspace manifest

The root `Cargo.toml` keeps `[package] tatic` and adds

```toml
[workspace]
members = ["crates/tatic-kernel", "crates/tatic-rng"]
default-members = [".", "crates/tatic-kernel", "crates/tatic-rng"]
exclude = ["tools/runs"]
```

- `exclude = ["tools/runs"]`: `tools/runs` is a standalone crate with its own `Cargo.lock` and `target`; without the
  exclusion cargo refuses `--manifest-path tools/runs/Cargo.toml` as "believes it's in a workspace when it's not".
- `default-members` lists the root and both crates, so a bare `cargo test` / `cargo build` / `cargo check` at the root keeps
  running the kernel's tests. `cargo test --lib`, `--all-targets` and `--bins` still address the root package only unless
  `--workspace` is given; README commands that name those flags gain `--workspace` (list in the plan).
- `[profile.test] opt-level = 1` and `[profile.sweep]` stay in the root manifest: profiles in member manifests are ignored,
  and the root's apply workspace-wide, so the kernel's tests keep opt-level 1.
- `.cargo/config.toml` (mimalloc `CXXFLAGS`) is found by walking up from any member; unchanged.
- One `Cargo.lock` at the root, as now (it gains the two member entries).
- Members inherit nothing: each manifest sets `edition = "2024"` and `version = "0.6.0"` itself (my call: no
  `[workspace.package]` inheritance for two crates; VERSIONING: one version, shared). The `version` fields move together when
  the version is bumped.

### `tatic-rng`

`crates/tatic-rng/src/lib.rs` is `src/support/rng.rs` verbatim (`mix64`, `SplitMix64`, the reference-stream test). `tatic` takes it as
a `[dev-dependencies]` entry (checked: every user is a `cfg(test)` module or an integration test; `typing.rs` uses it below
line 264, its test module), and `tatic-kernel` takes it as a dev-dependency too. `src/support/rng.rs` and its `pub mod rng`
are deleted (`support.rs` keeps `samples`, and its doc line drops "and the PRNG"); `use tatic::support::rng::…`
callers (`syntax_fuzz`, `compile_fuzz`, `church_bv/search.rs`, `kernel_*_fuzz`, `src/testing/ir_fuzz.rs`, `src/verify/typing.rs`)
become `tatic_rng::…`. Seeds name streams in docs; the output per seed must not change (the existing reference test moves with
the file and pins it).

### `tatic-kernel`

- `crates/tatic-kernel/Cargo.toml`: dependencies `hashbrown = "0.16.1"`, `im = "15.1.0"`, `stacker = "0.1.25"` (same versions as the
  root); dev-dependencies `tatic-rng` (path) and `mimalloc = "0.1.52"`.
- Visibility: the kernel has only one `pub(crate)` item its consumers need: `grow` (`src/proof/per_instance.rs`), which becomes
  `pub`. The plan checks, by compiling, that nothing else crosses (`Scope`, `Escape`, `Binder` etc. must already be `pub` since
  `tests/` uses them through `tatic::kernel`). Any further widening is named in the plan, not done silently.
- The doc link at the top of `kernel/bin.rs` (`crate::…`) is rewritten to plain text or an intra-crate link.
- Thread-locals (`SPACES`, `FLOOR`, `SEGMENT_SWITCHES`, `INFER_CACHE`, `EQUAL`) and `#[cfg(test)]` items (`wrap_c_ct_cf`,
  `NatPostulates`, `persistent_len`, `region_capacity`) move with the files untouched. `cfg(test)` is per crate: these are
  compiled when the kernel crate's own tests build, which is where `kernel/tests.rs` uses them. Anything in `tatic`'s own tests
  that used them must be found (grep) and either moved with its test or promoted deliberately; none is expected.

### Which tests move (my call)

Move into the kernel crate, because they use only `tatic::kernel` and `SplitMix64`:

| from | to |
|---|---|
| `src/kernel/tests.rs`, `bin.rs`/`spaces.rs` inline tests | with their files (unit tests of `tatic-kernel`) |
| `tests/kernel_fuzz.rs` | `crates/tatic-kernel/tests/kernel_fuzz.rs` |
| `tests/kernel_soundness_fuzz.rs` | `crates/tatic-kernel/tests/kernel_soundness_fuzz.rs` |
| `tests/church_encoding.rs` | `crates/tatic-kernel/tests/church_encoding.rs` |
| `tests/church_lemmas.rs` | `crates/tatic-kernel/tests/church_lemmas.rs` |

Stay in `tatic`: everything that touches `lang`/`jit`/`proof`/`church_bv`, and every test reading `CARGO_MANIFEST_DIR`
(`church_bv/classes.rs`, `job.rs`, `golden_wat.rs`: their paths are relative to the root package and do not change). Moved
tests change only their `use tatic::kernel::…` lines to `use tatic_kernel::…`.

README and `scripts/` commands that name moved test targets (`--test kernel_fuzz`) become `-p tatic-kernel --test kernel_fuzz`;
the plan lists them by grep.

### Allocator (my call)

`src/lib.rs` installs mimalloc as `#[global_allocator]` under `cfg(test)`, and `src/kernel/tests.rs` has an allocator-sensitive
wall-clock ratio test. The kernel crate's test build must therefore install mimalloc too:
`#[cfg(test)] #[global_allocator] static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;` in `crates/tatic-kernel/src/lib.rs`, and the
moved integration tests (separate binaries) do likewise if they time anything; the plan checks each moved test for timing
assumptions (`kernel_fuzz`/`kernel_soundness_fuzz` declared none). Without it that ratio test would silently measure the system
allocator. The same allocator line in `tatic`'s `lib.rs` stays (SR6 is not this item).

### Dependency fallout in `tatic`

`tatic` keeps `hashbrown`, `im`, `stacker` (used by `lang/term.rs`, `jit/*`, and `src/kernel*`, of which only `kernel*` leaves). The
plan greps each: a dependency used only by the kernel would move out of the root manifest (none expected: `lang/term.rs` and
`jit/*` use all three).

### Documentation and checks

- `docs/TOUR.md`: kernel entries cite `crates/tatic-kernel/src/…` (the cites are `path#symbol`); a short "crates" sentence, since
  the tour is the map. `bash scripts/tour_check.sh` and `bash scripts/cite_check.sh` must pass; `cite_check.sh` and
  `tour_check.sh` are read for hard-coded `src/kernel` paths and fixed if so.
- `README.md` module table and commands; `CLAUDE.md` (`kernel` mentions, if any); `PARKED.md`/`docs/tier-cycle.md` paths to
  `src/kernel*` are live references and are repointed; frozen specs, plans and run rows stay as written.
- `RELATED_WORK.md` finding text mentioning `kernel::grow` stays (frozen).

## Verification

Per the restructuring skill, with its cadence:

1. `cargo check --workspace --all-targets` clean; the two known `church_bv` warnings only.
2. `cargo test --workspace -j 4 -- --list`: names diffed against `.superpowers/rs/before.txt` after stripping the crate and
   module prefix (the baseline is 749 names). No lost, no new.
3. Full suite via `run.ps1 -Kind probe -Affinity CFF -MaxMemGB 12`: lib 361 + 1 ignored in `tatic` as before minus the kernel
   unit tests (which now report under `tatic-kernel`); church_bv 313 + 47 ignored; total passed equals the baseline's.
4. `bash scripts/cite_check.sh`, `bash scripts/tour_check.sh`.
5. `git diff --cached -M --stat`: kernel files and `rng.rs` show as renames; grep of `src/kernel`, `crate::kernel`,
   `tatic::kernel`, `support::rng` returns only frozen history.
6. The compile-time claim: add `use tatic_rng::mix64;` to a throwaway copy of `crates/tatic-kernel/src/lib.rs` non-test code and
   confirm it fails to build (the boundary is real); revert.
7. The build-cost expectation is measured once, not assumed: `touch crates/tatic-kernel/src/kernel_file` rebuild of `cargo test -p
   tatic-kernel --no-run` against the pre-move `cargo test --lib kernel --no-run` equivalent, wall time and the crates rebuilt,
   recorded in the plan outcome (a data point, not a gate).
8. A/A on the exe-keyed arm cache (`scripts/streams_ab.sh` hashes exe contents, not paths): the church_bv test exe is built from
   the same sources, but its contents may differ (linking), so the first post-move arm run rebuilds its cache; recorded, not
   avoided.

## Risks

- **`default-members` is the one silent loss.** Without it a root `cargo test` skips the kernel. Step 3 counts names to catch it.
- **A tool that globs `src/kernel`.** `tools/runs`, `scripts/` and the gate were greped for the old path: none use it (recon
  2026-11-04); the plan repeats the grep at execution.
- **Collision with `origin/lazy-view`.** Earlier recon: that branch touches `rewrite.rs`/`encoding.rs`, not the kernel. The plan
  re-checks `git diff --name-only main...origin/lazy-view` for `src/kernel*` and `tests/kernel*` before moving.
- **Release/profile semantics.** Opt-level and LTO settings are workspace-wide from the root; nothing in a member manifest
  overrides them, so kernel codegen is unchanged. Checked by the `[profile.sweep]` test build still producing a working
  church_bv exe.
- **`stacker`/thread-local behaviour across a crate boundary.** Inlining across crates differs: `#[inline]` functions are
  available cross-crate, non-generic non-inline ones are not (no LTO in dev/test). The kernel's hot paths are called from
  `proof`/`church_bv`; a throughput change is possible in `release` without fat LTO. The `sweep` profile uses fat LTO. The plan
  runs the existing count check (`ICOUNT.md`) on one church_bv sweep before and after; a gap beyond the A/A spread is a finding
  to decide on (add `#[inline]`, or accept), not a blocker silently ignored. This is the main unknown.

## Settled by the builder check (2026-11-04)

- **Benches stay in `tatic`** (`benches/proofs.rs` also uses `proof`, `lang`, `support::samples`); their `kernel::` lines (13)
  become `tatic_kernel::…`. No bench moves; neither bench or `src/bin/*` uses the PRNG (grepped), so `tatic-rng` is a
  dev-dependency only. The bench commands in the README are unchanged.
- **Inlining gate (my call):** the kernel commit is not gated on the count, but a gap beyond the A/A spread stops the work and
  goes to the user as a Decide (add `#[inline]` to named hot kernel functions, or accept); nothing in the kernel is edited for
  it unasked. Workload: the same church_bv sweep exe built twice (before and after), counted on the `sweep` profile (what
  sweeps run) and once on the default test profile (where cross-crate inlining shows).
- **Test-list diff:** `.superpowers/rs/before.txt` (749 lines) is the baseline. Compare the bare test function names (the text
  after the last `::`, with the ` - test` suffix and any binary header dropped), sorted, plus the per-binary counts for the
  kernel tests. A duplicated bare name across binaries would show as a count change.
- **Scripts and gate:** `scripts/`, `tools/runs/src` and `CLAUDE.md` name no kernel path or moved test target (grepped); only
  `README.md` (lines 134-135 `--test kernel_fuzz --test kernel_soundness_fuzz`, and prose names `kernel.rs`) and `docs/TOUR.md`
  do. `cite_check.sh` and `tour_check.sh` carry no `src/` assumption (grepped `tour_check.sh`; the plan re-reads both).
- **Other nested crates:** only `tools/runs` has a `Cargo.toml` besides the root (`git ls-files`).
- **No `[features]`, `[lints]` or `rust-version`** in the root manifest, and no `cfg(feature = …)` in `src/kernel*`.

## Left to the builder

Ordering of the moves inside the plan, the exact README lines, and the commit split (suggested: rng crate, kernel crate, tests
moved, docs), as long as each commit builds and passes the checks that apply to it.

## Decisions marked as mine

Per-member version fields instead of `[workspace.package]`; exactly which tests move; mimalloc in the kernel crate's tests;
`grow` as the only widened item; the cross-crate inlining check.

## Decided by the user (2026-11-04)

- Inlining gate: a count gap beyond the A/A spread stops the work and goes to the user; no `#[inline]` unasked.
- `tatic` stays the root package; new members live in `crates/tatic-kernel` and `crates/tatic-rng` (directory = package name).
- Moving `tatic` itself to `crates/tatic` (a virtual workspace root) is a separate item to follow this one, not part of it.
