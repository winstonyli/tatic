---
status: active
---

# Kernel crate Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** `src/kernel*` becomes the workspace crate `tatic-kernel` (and `src/support/rng.rs` the crate `tatic-rng`), so "the kernel imports nothing from tatic" is a compile error.

**Architecture:** the root `tatic` package stays the root and gains a `[workspace]`; two members under `crates/`. Every `kernel::` / `support::rng::` path is rewritten to `tatic_kernel::` / `tatic_rng::` (no re-export shim). Kernel-only tests move with the crate. Nothing inside the kernel's logic changes.

**Tech Stack:** Rust 2024, cargo workspaces, hashbrown 0.16.1, im 15.1.0, stacker 0.1.25, mimalloc 0.1.52.

**Spec:** `docs/superpowers/specs/2026-11-04-kernel-crate-design.md` (approved 2026-11-04). Item SR4 of `docs/superpowers/plans/2026-11-04-cleanup-restructure.md`.

## Global Constraints

- Layout: `crates/tatic-kernel`, `crates/tatic-rng`; `tatic` stays the root package; `tools/runs` stays outside (`exclude`).
- Every member: `version = "0.6.0"`, `edition = "2024"`, set in its own manifest (no `[workspace.package]`).
- `tatic-kernel` dependencies: `hashbrown = "0.16.1"`, `im = "15.1.0"`, `stacker = "0.1.25"` and nothing from tatic; dev-dependencies `tatic-rng` (path), `mimalloc = "0.1.52"`. `tatic-rng` has no dependencies. `tatic` takes `tatic-kernel` as a dependency and `tatic-rng` as a dev-dependency.
- `default-members = [".", "crates/tatic-kernel", "crates/tatic-rng"]`; `[profile.test]` and `[profile.sweep]` stay in the root manifest.
- No re-export shim; no `#[inline]` or other edit inside the kernel's logic. Only `grow` becomes `pub`, plus any further item the compiler proves is used across the boundary (each named in the task commit).
- `git mv` for every moved file; renames must show at 100% (or the named import lines only) in `git diff --cached -M --stat`.
- Seeds name streams: the `SplitMix64` output for a seed must not change (its reference-stream test moves with it).
- Runs over a minute launch through `~/.claude/runs/run.ps1` (memory-capped, `-Affinity CFF`, `-j 4`); check `(Get-PSDrive C).Free/1GB` before a full build (stop under 5 GB); foreign cargo processes are left alone.
- Never push, tag or bump. Commit trailer: `Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>`.
- Stop and ask (a Decide to the user) if the Task 6 instruction count gap exceeds the A/A spread.

## Review Focus

1. Root `cargo test` silently skipping the kernel tests (`default-members` wrong). Pinned in Task 3 step 6 and Task 6 (name-list diff).
2. A kernel timing test now running on the system allocator. Pinned in Task 4 (the allocator declaration and a check it is the global one).
3. A kernel source file that still reaches into tatic (`crate::lang`, `crate::support`). Pinned in Task 3 (boundary negative check).
4. A `cfg(test)`-only kernel item (`wrap_c_ct_cf`, `NatPostulates`, `persistent_len`, `region_capacity`) needed by a test that stayed in `tatic`, which would no longer compile. Pinned in Task 4 step 1.
5. Cross-crate inlining slowing church_bv sweeps. Pinned in Task 6 (count before/after).

---

### Task 1: Preconditions

**Files:** none changed except the spec's front matter.

**Interfaces:** Produces: `BASE` = the commit this work starts from (record in the ledger); a clean tree.

- [ ] **Step 1: Check the start state.** `git status --short` is empty; `git log --oneline -1` is the commit that holds this plan; `(Get-PSDrive C).Free/1GB` is at least 5 (else stop and report); `Get-Process cargo,rustc -EA 0` lists none of yours.
- [ ] **Step 2: Branch collision.** `git diff --name-only main...origin/lazy-view | grep -E '^(src/kernel|src/support/rng|tests/(kernel|church_enc|church_lem))'` prints nothing. Anything printed is a Decide to the user, not an edit around it. Record the ahead/behind from `git rev-list --left-right --count main...origin/lazy-view` (the evidence is weak when far behind: say so).
- [ ] **Step 3: Regenerate the baseline name list if needed.** `.superpowers/rs/before.txt` (749 lines) must exist; if not, build it from BASE: `cargo test -j 4 -- --list` normalised as in Task 6 step 2.
- [ ] **Step 4: Set the spec `status: active` and this plan `status: active`; commit.**

### Task 2: The `tatic-rng` crate

**Files:**
- Create: `crates/tatic-rng/Cargo.toml`
- Move: `src/support/rng.rs` -> `crates/tatic-rng/src/lib.rs`
- Modify: root `Cargo.toml`; `src/support.rs`; callers of `support::rng`: `src/testing/ir_fuzz.rs`, `src/verify/typing.rs`, `src/kernel/tests.rs` (still in `src` at this point), `tests/syntax_fuzz.rs`, `tests/compile_fuzz.rs`, `tests/kernel_fuzz.rs`, `tests/kernel_soundness_fuzz.rs`, `tests/church_bv/search.rs`.

**Interfaces:** Produces: `tatic_rng::{SplitMix64, mix64}` with the same signatures as `support::rng` (`SplitMix64::new(u64)`, `next_u64`, `below(u32) -> u32`, `i64_range(i64, i64) -> i64`; `mix64(u64) -> u64`).

- [ ] **Step 1: Red check.** `cargo test -p tatic-rng` fails with "package ID specification `tatic-rng` did not match any packages".
- [ ] **Step 2: Create the crate.** `crates/tatic-rng/Cargo.toml`: package `tatic-rng`, `version = "0.6.0"`, `edition = "2024"`, no dependencies. `git mv src/support/rng.rs crates/tatic-rng/src/lib.rs`. Root `Cargo.toml`: add the `[workspace]` of the spec (members both crates, `default-members`, `exclude = ["tools/runs"]`; the kernel member can be listed in Task 3, so for now list only `crates/tatic-rng`) and `tatic-rng = { path = "crates/tatic-rng" }` under `[dev-dependencies]`. Delete `pub mod rng;` from `src/support.rs` and "and the PRNG" from its doc line.
- [ ] **Step 3: Repoint callers.** In the files listed above replace `crate::support::rng::` / `tatic::support::rng::` by `tatic_rng::`. Doc and comment text that names `support::rng` (`grep -rn 'support::rng\|support/rng'` over `src tests benches docs scripts README.md CLAUDE.md`) is repointed when live (TOUR.md line 31 bullet, README module table if listed); frozen specs, plans and run rows stay.
- [ ] **Step 4: Verify.** `cargo check --workspace --all-targets` is clean apart from the two known `church_bv` warnings; `cargo test -p tatic-rng` runs 1 test (`seed_0_gives_the_reference_stream`) and passes; `cargo test --lib -j 4 -- --list | wc -l` shows the lib lost exactly that one test; `bash scripts/cite_check.sh` and `bash scripts/tour_check.sh` pass.
- [ ] **Step 5: Commit** (`git add -A crates src tests Cargo.toml Cargo.lock docs README.md`; `git diff --cached -M --stat` shows `rng.rs` as a rename): `rng: SplitMix64 as the workspace crate tatic-rng`.

### Task 3: The `tatic-kernel` crate

**Files:**
- Create: `crates/tatic-kernel/Cargo.toml`
- Move: `src/kernel.rs` -> `crates/tatic-kernel/src/lib.rs`; `src/kernel/{bin,postulates,spaces,tests}.rs` -> `crates/tatic-kernel/src/`
- Modify: root `Cargo.toml` (member, dependency); `src/lib.rs` (delete `pub mod kernel;`); every file listed by `grep -rlE 'kernel::|crate::kernel|tatic::kernel' src tests benches` that is not moved (31 files: `src/jit.rs`, `src/proof.rs`, `src/proof/*.rs`, `benches/proofs.rs`, `tests/church_bv/**`, `tests/compile_fuzz.rs`).

**Interfaces:** Consumes: `tatic_rng::SplitMix64` (Task 2), as a dev-dependency. Produces: crate `tatic_kernel` exposing exactly what `tatic::kernel` did, plus `pub fn grow<R>(f: impl FnOnce() -> R) -> R`.

- [ ] **Step 1: Record the count.** `cargo test --lib -j 4 -- --list | grep -c '^kernel::'` (tests under the old `kernel::` module path); write it in the ledger. Step 6 must find the same number under `tatic-kernel`. (The red/green for the boundary is step 5.)
- [ ] **Step 2: Create the crate.** `git mv` the five files as above (mod declarations inside `lib.rs` keep their names, so `mod bin; mod postulates; mod spaces;` resolve to `src/bin.rs` etc.; `#[cfg(test)] mod tests;` likewise). `crates/tatic-kernel/Cargo.toml` per Global Constraints. Root manifest: add the member and `tatic-kernel = { path = "crates/tatic-kernel" }` under `[dependencies]`.
- [ ] **Step 3: Make it compile standalone.** `cargo check -p tatic-kernel` and fix, in this order: the doc link in `bin.rs:1` (`crate::kernel::scoped` becomes `crate::scoped`); `use crate::support::rng::SplitMix64` in `tests.rs` (5 sites) becomes `tatic_rng::SplitMix64`; `grow` becomes `pub`. Do not widen anything else yet.
- [ ] **Step 4: Rewrite the callers.** In every file of the 31: `crate::kernel::` and `kernel::` (after a `use crate::{... kernel ...}`) become `tatic_kernel::`; `use tatic::kernel::…` becomes `use tatic_kernel::…`; `use crate::kernel::{self, Expr, …}` (e.g. `src/proof.rs:155`) becomes `use tatic_kernel::{self as kernel, …}` only where the file already calls `kernel::x` many times -- otherwise rewrite the call sites (choose per file and keep the diff to import and path lines). Use the Edit tool or a reviewed sed on the exact patterns; never multi-line perl (it corrupted a file once). Delete `pub mod kernel;` from `src/lib.rs`.
- [ ] **Step 5: Verify the build and the boundary.** `cargo check --workspace --all-targets` clean (two known warnings only). Any `pub(crate)` error across the boundary: widen that one item to `pub`, list it in the commit message. Then the negative check: temporarily put `use tatic_rng::mix64;` in non-test code of `crates/tatic-kernel/src/lib.rs`; `cargo check -p tatic-kernel` must fail with "unresolved import" (tatic-rng is only a dev-dependency); revert it, and confirm `git diff` shows no residue.
- [ ] **Step 6: Run what exists.** `cargo test -p tatic-kernel -j 4` runs the kernel unit tests (count them: `-- --list | grep -c ': test'` must equal the number the old `cargo test --lib kernel::` listed, which is read from `.superpowers/rs/before.txt`); `cargo test -j 4 -- --list | wc -l` at the root still lists the same total (749 including the kernel's now under `tatic-kernel`), proving `default-members`.
- [ ] **Step 7: Commit** (`git diff --cached -M --stat`: the five kernel files are renames; other changes are import/path lines only): `kernel: the trusted checker as the workspace crate tatic-kernel`.

### Task 4: Move the kernel-only tests and fix the allocator

**Files:**
- Move: `tests/{kernel_fuzz,kernel_soundness_fuzz,church_encoding,church_lemmas}.rs` -> `crates/tatic-kernel/tests/`
- Modify: `crates/tatic-kernel/src/lib.rs` (allocator), the moved files' imports, `README.md` lines naming `--test kernel_fuzz --test kernel_soundness_fuzz`.

**Interfaces:** Consumes: `tatic_kernel::*`, `tatic_rng::SplitMix64`.

- [ ] **Step 1: Confirm they are kernel-only.** In each of the four files, every `use` is `tatic_kernel` or `tatic_rng` or std; none reads `CARGO_MANIFEST_DIR`, uses `include_str!`, or names a `tatic::` module other than the kernel. `grep -n 'wrap_c_ct_cf\|NatPostulates\|persistent_len\|region_capacity' tests src benches` shows no use outside `crates/tatic-kernel`. Anything else stays in `tatic` (and is reported).
- [ ] **Step 2: Move and repoint.** `git mv` the four files; their imports become `tatic_kernel::` / `tatic_rng::`.
- [ ] **Step 3: Allocator.** In `crates/tatic-kernel/src/lib.rs` add, with the comment "the allocator the lib's tests are timed under (`tatic/src/lib.rs`); the ratio tests in `tests.rs` measure against it":
  `#[cfg(test)] #[global_allocator] static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;`.
  Integration tests are their own binaries: if one of the four times anything (`Instant`, a wall-clock ratio), declare the same allocator at its top; otherwise add a one-line comment saying why it does not.
- [ ] **Step 4: Verify.** `cargo test -p tatic-kernel -j 4` passes, including the old kernel ratio test and the `assert_scales` thread test; the output lists the 4 moved binaries; `cargo test -j 4 -- --list | wc -l` is still 749.
- [ ] **Step 5: README.** The command at `README.md:134-135` becomes `cargo test --release -p tatic-kernel --test kernel_fuzz --test kernel_soundness_fuzz` plus the `tatic` targets (`--test compile_fuzz --test syntax_fuzz`) as a separate line. `cargo test --lib --bins` (README:132) and `cargo build --all-targets`/`cargo clippy --all-targets` (131, 133) gain `--workspace`.
- [ ] **Step 6: Commit:** `kernel: its fuzzers and Church tests move into the crate`.

### Task 5: Docs and checks

**Files:** `docs/TOUR.md`, `README.md`, `PARKED.md`, `docs/tier-cycle.md`, `scripts/cite_check.sh` and `scripts/tour_check.sh` (only if they assume `src/`), the cleanup plan, the spec.

- [ ] **Step 1: Census.** `grep -rnE 'src/kernel|kernel\.rs|crate::kernel|tatic::kernel|support/rng|support::rng'` over the living docs and scripts, split into live and frozen (frozen: other specs and plans, `RELATED_WORK.md` finding text, `docs/runs.md` rows, `docs/runs/`). List the counts in the commit message.
- [ ] **Step 2: Fix live references.** TOUR cites become `crates/tatic-kernel/src/lib.rs#symbol` (and `.../postulates.rs`, etc.); the tour gets a sentence that the kernel and the PRNG are workspace crates, and the layer sentence says `src/` holds the `tatic` package. README module table and commands updated; `CLAUDE.md` unchanged unless the census shows a hit.
- [ ] **Step 3: Verify.** `bash scripts/cite_check.sh` (51 section cites + the TOUR cites) and `bash scripts/tour_check.sh` pass; a grep of the old paths returns only frozen history.
- [ ] **Step 4: Plan outcomes.** Append "Done 2026-11-04 (commits)" to SR4 in the cleanup plan with actual sizes against estimate; state that the plan's SR8 follows.
- [ ] **Step 5: Commit:** `docs: kernel and rng are workspace crates`.

### Task 6: Whole-suite proof and the cost checks

**Files:** none changed except plan/spec outcome text, `docs/runs.md` rows via the wrapper.

- [ ] **Step 1: Warnings.** `cargo check --workspace --all-targets` and `cargo clippy --workspace --all-targets -- -D warnings` are no worse than BASE (compare with a BASE worktree run if clippy had findings before; record).
- [ ] **Step 2: Name diff.** From `cargo test -j 4 -- --list` (default members) take each `<name>: test` line, keep the text after the last `::`, sort; do the same to `.superpowers/rs/before.txt`; `diff` shows nothing. (Strip prefixes first, then sort.)
- [ ] **Step 3: Full suite.** `run.ps1 -Kind probe -Name kernel-crate-suite -Affinity CFF -MaxMemGB 12 -Detach -Command "cargo test -j 4"` with a bounded watcher on `run.json`. Expected: exit 0; `tatic` lib 361 minus the moved kernel and rng tests, `tatic-kernel` the rest, church_bv 313 passed + 47 ignored, the sum of passed equals BASE's; `peak_commit_mb` recorded.
- [ ] **Step 4: Instruction counts.** Per ICOUNT.md: A/A of 3 runs of the BASE church_bv sweep-profile test exe (built in a `git worktree` of BASE with its own `CARGO_TARGET_DIR`, deleted after), then 3 runs of the new exe, same arguments, `-Cpu 4`; then the same on the default test profile. Report best-of-3 for each and the ratio. If the ratio differs from 1 by more than the A/A (median - best) / best spread, STOP and put the Decide to the user (Global Constraints). Record the run ids.
- [ ] **Step 5: Build cost, once.** `touch` one file in `crates/tatic-kernel/src/` then time `cargo test -p tatic-kernel --no-run`; and, in the BASE worktree, touch `src/kernel.rs` and time `cargo test --lib --no-run`. Record both wall times and the crates rebuilt in the SR4 outcome as a data point.
- [ ] **Step 6: Close.** Spec and this plan `status: done`; leftovers (if any) to `PARKED.md` first; one whole-branch review by a fresh Opus reviewer over `git diff BASE..HEAD` (branches under ~300 changed lines go to Sonnet); then the closing report with the Architecture and Docs checks.
