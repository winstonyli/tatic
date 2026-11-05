# tatic

`kind: experiment` (see VERSIONING.md). Version field: `[workspace.package]` in the root `Cargo.toml` (`0.6.0`, tagged `v0.1.0` to `v0.6.0`); no changelog: tag messages are
the history (`git tag -n99`).

- Main goals, in `ROADMAP.md` ("Goals"): a JIT on proved equivalence; a kernel that improves itself (mined rules, its
  own vocabulary); the KR&R tier of a cycle with a GPU model. Check new work and proposals against them.
- Findings and their measurements: `docs/tier-cycle/`. Parked and deferred work: `PARKED.md`; its evidence cites
  `docs/tier-cycle/` by section name, not line (override of VERSIONING's `file:line`: that file's lines drift). Milestones: `ROADMAP.md`.
- Specs and plans (`docs/superpowers/`, tracked from 2026-10-17) start with front matter
  `status: draft | active | done | "superseded-by: <file>"`; it overrides any older "Status:" line in the body.
- `docs/TOUR.md` is the map of the codebase and its vocabulary (cites are `path#symbol`). A change that renames, moves,
  adds or removes a module, a stage of the data flow or a glossary term updates the tour in the same commit, and
  `bash scripts/tour_check.sh` must pass before committing it. The tour holds concepts and flow only: no measurements,
  dates or results (those live in `docs/tier-cycle/`).
- `bash scripts/size_check.sh` fails on a tracked `.rs` file over 1000 lines that `scripts/size_allowlist.txt` does not list, or on a listed one that grew, shrank without its max lowered, or fell under the limit (the list only shrinks; `scripts/size_check_check.sh` tests it). Run it before committing a change that adds to a large file.
- Test placement: a module's tests live inline up to 299 lines; a block of 300 or more goes to `foo/tests.rs` (`foo/tests/` once it splits further). `bash scripts/test_placement_check.sh` fails on a tracked `.rs` file with a longer top-level `mod tests`/`mod *_tests` block (no allowlist; `scripts/test_placement_check_check.sh` tests it). Run it before committing a change that adds tests to a large file.
- Long runs launch through `~/.claude/runs/run.ps1` (raw output in `%LOCALAPPDATA%\claude-runs\tatic`, one row each in
  `docs/runs.md`); `runs dir` (and `docs/runs/2026-10-12/scripts/kk.sh`, kept in place as the record the dated scripts source) then write into that run's folder. Curated rows behind the doc's sections are
  in `docs/runs/<date>/`. Pin a recorded run with `run.ps1 -Affinity CFF`, not `start /wait /affinity` in `-Command`;
  rows before 2026-10-30 launched that way (about 130 of them, e.g. `2026-10-29-s1-suite`) can show a false exit 0, so
  read the headline.
