# tatic

`kind: experiment` (see VERSIONING.md). Version field: `[workspace.package]` in the root `Cargo.toml` (`0.7.0`, tagged `v0.1.0` to `v0.7.0`); no changelog: tag messages are
the history (`git tag -n99`).

- Main goals, in `ROADMAP.md` ("Goals"): a JIT on proved equivalence; a kernel that improves itself (mined rules, its
  own vocabulary); the KR&R tier of a cycle with a GPU model. Check new work and proposals against them.
- Findings and their measurements: `docs/tier-cycle/README.md`. Parked and deferred work: `PARKED.md`; its evidence cites
  findings by section name, not line (override of VERSIONING's `file:line`: that file's lines drift). Milestones: `ROADMAP.md`.
- Specs and plans (`docs/superpowers/`, tracked from 2026-10-17) start with front matter
  `status: draft | active | done | "superseded-by: <file>"`; it overrides any older "Status:" line in the body. `bash scripts/check/front_matter_check.sh` fails on one without it (no allowlist; `front_matter_check_check.sh` tests it).
- `bash scripts/check/cite_check.sh` fails on a section cite that does not resolve and on a mention of either one-file-per-section doc with no section, in every tracked `.md`, or `.rs`, `.sh`, `.toml` comment, outside the history and `scripts/check/` (no allowlist; `cite_check_check.sh` tests it). To point at such a doc as a whole, name its index, `README.md`.
- `docs/TOUR.md` is the map of the codebase and its vocabulary (cites are `path#symbol`). A change that renames, moves,
  adds or removes a module, a stage of the data flow or a glossary term updates the tour in the same commit, and
  `bash scripts/check/tour_check.sh` must pass before committing it. The tour holds concepts and flow only: no measurements,
  dates or results (those live in `docs/tier-cycle/README.md`).
- `bash scripts/check/layout_check.sh` fails on a tracked `.patch` outside `docs/runs/<date>/patches/` and `docs/superpowers/spikes/`, on a sweep recipe (the sweep's output variable set) under `scripts/` or `tools/` outside `scripts/gate/arm_env.sh`, and on a tracked file directly in `scripts/`: scripts live in `check/` (guards and their `*_check_check.sh` tests), `gate/` (the A/B gate, its summaries and tests) or `study/` (one-experiment scripts); `scripts/check/layout_check_check.sh` tests it.
- `bash scripts/check/script_header_check.sh` fails on a tracked script under `docs/runs/*/scripts/` without a header comment or docstring in its first four lines (no allowlist; `script_header_check_check.sh` tests it). That header is the script manifest: there is no separate index.
- `bash scripts/check/size_check.sh` fails on a tracked `.rs` file over 1000 lines that `scripts/check/size_allowlist.txt` does not list, or on a listed one that grew, shrank without its max lowered, or fell under the limit (the list only shrinks; `scripts/check/size_check_check.sh` tests it). Run it before committing a change that adds to a large file.
- Test placement: a module's tests live inline up to 299 lines; a block of 300 or more goes to `foo/tests.rs` (`foo/tests/` once it splits further). `bash scripts/check/test_placement_check.sh` fails on a tracked `.rs` file with a longer top-level `mod tests`/`mod *_tests` block (no allowlist; `scripts/check/test_placement_check_check.sh` tests it). Run it before committing a change that adds tests to a large file.
- A thread that checks or recurses deeply is spawned with `tatic_kernel::CHECK_STACK` (256 MB reserved), where a large `check_in` runs in place. `bash scripts/check/stack_literal_check.sh` fails on that size written as a number in a tracked `.rs` file under `crates/` (no allowlist; `scripts/check/stack_literal_check_check.sh` tests it).
- Long runs launch through `~/.claude/runs/run.ps1` (raw output in `%LOCALAPPDATA%\claude-runs\tatic`, one row each in
  `docs/runs.md`); `runs dir` (and `docs/runs/2026-10-12/scripts/kk.sh`, kept in place as the record the dated scripts source) then write into that run's folder. Curated rows behind the doc's sections are
  in `docs/runs/<date>/`. Pin a recorded run with `run.ps1 -Affinity CFF`, not `start /wait /affinity` in `-Command`;
  rows before 2026-10-30 launched that way (about 130 of them, e.g. `2026-10-29-s1-suite`) can show a false exit 0, so
  read the headline.
