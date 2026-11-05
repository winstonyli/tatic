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
- Long runs launch through `~/.claude/runs/run.ps1` (raw output in `%LOCALAPPDATA%\claude-runs\tatic`, one row each in
  `docs/runs.md`); `runs dir` and `kk.sh` then write into that run's folder. Curated rows behind the doc's sections are
  in `docs/runs/<date>/`. Pin a recorded run with `run.ps1 -Affinity CFF`, not `start /wait /affinity` in `-Command`;
  rows before 2026-10-30 launched that way (about 130 of them, e.g. `2026-10-29-s1-suite`) can show a false exit 0, so
  read the headline.
