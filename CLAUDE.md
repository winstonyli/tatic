# tatic

`kind: experiment` (see VERSIONING.md). Version field: `Cargo.toml` (`0.1.0`, no tags yet); no changelog: tag messages are
the history (`git tag -n99`).

- Findings and their measurements: `docs/tier-cycle.md`. Parked and deferred work: `PARKED.md`. Milestones: `ROADMAP.md`.
- Specs and plans (`docs/superpowers/`, tracked from 2026-10-17) start with front matter
  `status: draft | active | done | "superseded-by: <file>"`; it overrides any older "Status:" line in the body.
- Long runs launch through `~/.claude/runs/run.ps1` (raw output in `%LOCALAPPDATA%\claude-runs\tatic`, one row each in
  `docs/runs.md`); `runs dir` and `kk.sh` then write into that run's folder. Curated rows behind the doc's sections are
  in `docs/runs/<date>/`.
