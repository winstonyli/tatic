# tatic

`kind: experiment` (see VERSIONING.md). Version field: `Cargo.toml` (`0.3.0`, tagged `v0.1.0`, `v0.2.0` and `v0.3.0`); no changelog: tag messages are
the history (`git tag -n99`).

- Main goals, in `ROADMAP.md` ("Goals"): a JIT on proved equivalence; a kernel that improves itself (mined rules, its
  own vocabulary); the KR&R tier of a cycle with a GPU model. Check new work and proposals against them.
- Findings and their measurements: `docs/tier-cycle.md`. Parked and deferred work: `PARKED.md`; its evidence cites
  `docs/tier-cycle.md` by section name, not line (override of VERSIONING's `file:line`: that file's lines drift). Milestones: `ROADMAP.md`.
- Specs and plans (`docs/superpowers/`, tracked from 2026-10-17) start with front matter
  `status: draft | active | done | "superseded-by: <file>"`; it overrides any older "Status:" line in the body.
- Long runs launch through `~/.claude/runs/run.ps1` (raw output in `%LOCALAPPDATA%\claude-runs\tatic`, one row each in
  `docs/runs.md`); `runs dir` and `kk.sh` then write into that run's folder. Curated rows behind the doc's sections are
  in `docs/runs/<date>/`.
