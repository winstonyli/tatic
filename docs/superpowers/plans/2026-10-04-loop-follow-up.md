---
status: done
---

# Loop follow-up (cumulative pool, carried candidates) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Test whether feeding the batch-by-batch miner a cumulative straggler pool (A) and candidates carried over from earlier rounds, with the rulelm samples added to rather than replacing the mined ones (D), raises the loop's share of the `ref` gain.

**Architecture:** The miner picks rules greedily by how many of the current window's stragglers they fix (`search.rs` gain = fixed*1000 + size drop), from candidates generated out of those same stragglers. A widens the window the driver passes (`RULEMINER_SKIP`/`RULEMINER_LAWS`); D adds an extra candidate file to the miner's own candidates (new env `RULEMINER_EXTRA`) and has the driver accumulate each round's candidates into a pool file. Everything is opt-in; defaults reproduce the existing loop.

**Tech Stack:** Rust test binary (`tests/church_bv/search.rs`, CRLF: edit with the Edit tool), bash driver (`scripts/loop_stream.sh`, LF).

**Spec:** `docs/superpowers/specs/2026-10-04-end-to-end-loop-design.md` (Results sections and the follow-up section at its end).

## Global Constraints

- Defaults unchanged: with none of the new env vars set, `loop_stream.sh` and `rule_miner` behave exactly as before (the stride-7 loop-mined total stays 82).
- Long runs: BelowNormal, `THREADS=6` (at most 12 busy threads), copy the exe to `%TEMP%\bv_loop.exe` before running; never edit a running script; no `tail -F` monitors; report CPU load and Defender state with any timing.
- Do not push or merge; the branch `loop-stream` stays local.
- Commits end with `Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>`.

---

### Task 1: `RULEMINER_EXTRA` in the miner

**Files:**
- Modify: `tests/church_bv/search.rs` (candidate generation, just before the line `// per left side, the smallest right side only`, about line 811)

**Interfaces:**
- Consumes: the `file` proposer's line format in `pilot_candidates` (`lhs -> rhs` in `Term::show` syntax, blank lines and `#` comments skipped; reuse its parsing, do not write a second parser).
- Produces: env `RULEMINER_EXTRA=<path>`: when set and `RULEMINER_PROPOSER` is `mined` (the default), the file's candidates are appended to `cands` before the "one per left side" sort and dedup, and `RULEMINER N extra candidates from <path>` is printed.

- [ ] **Step 1:** Factor the `file` branch's line parsing in `pilot_candidates` into a function `read_rule_file(path: &str) -> Vec<(Term, Term)>` (behaviour unchanged for `file`).
- [ ] **Step 2:** Add a small ignored-free unit test `extra_candidates_are_merged` that writes two lines to a temp file, calls `read_rule_file`, and asserts the two parsed rules (run: `cargo test --test church_bv extra_candidates -- --nocapture` at BelowNormal with `-j 4`).
- [ ] **Step 3:** In `rule_miner`, before the sort at the marked line, read `RULEMINER_EXTRA` (if set and the proposer is `mined`) and `cands.extend(read_rule_file(&path))`; print the count line.
- [ ] **Step 4:** Build the test exe, copy it to `%TEMP%\bv_follow.exe`, and run `rule_miner` on a small window (`RULEMINER_LAWS=20`, deep add3 stride 7) once without and once with `RULEMINER_EXTRA` pointing at a file holding one known-useful rule (for example `add(sub(x, y), z) -> add(sub(z, y), x)`); expect the extra-candidates line only in the second run and the same chosen rules otherwise.
- [ ] **Step 5:** Commit.

### Task 2: driver options WINDOW, POOL, MODEL

**Files:**
- Modify: `scripts/loop_stream.sh`

**Interfaces:**
- Consumes: Task 1's `RULEMINER_EXTRA`; the miner prints `RULEMINER candidate: l -> r` lines only with `RULEMINER_SHOW=1`.
- Produces: env options (all default off): `WINDOW=cum` (round r mines laws OFFSET .. OFFSET+(r+1)*B instead of the last batch only); `POOL=1` (set `RULEMINER_SHOW=1`, after each mine append its `RULEMINER candidate:` lines, text after the colon, to `$out/pool.txt` with `sort -u`, and pass `RULEMINER_EXTRA=$out/pool.txt` to later mines); `MODEL=1` (as `PROPOSER=file` does, run `$PROPOSER_FILE_CMD name` into `$out/cand_<name>.txt`, but keep `PROPOSER=mined` and add those lines to the extra file instead of replacing the mined candidates).

- [ ] **Step 1:** Implement the three options in `mine()`: build the extra file (`pool.txt` and, with MODEL, the round's `cand_*.txt`) into `$out/extra_<name>.txt`, and set `RULEMINER_EXTRA` only when it is non-empty. WINDOW=cum changes the `skip`/`laws` arguments passed to `mine` in the round loop (skip stays OFFSET, laws becomes `$B*(r+1)`).
- [ ] **Step 2:** Smoke on the non-deep tiny case (`B=3 K=2`, as in Task 2 of the first plan) for each option alone and all three together; confirm default behaviour is byte-identical (same `m.tsv` and `rules.txt` as before the change) and that `pool.txt` appears with POOL=1.
- [ ] **Step 3:** Commit.

### Task 3: run the four configurations on the three streams

**Files:**
- Create: `scripts/experiments/follow_run.sh`; logs `scripts/experiments/logs/follow_s<stride>_<cfg>.tsv`, `follow_summary.txt`; Results in the loop spec; a README row.

**Interfaces:**
- Consumes: the options from Task 2; the existing configs' totals as the baseline (loop-mined: stride 7 = 82, stride 5 = 98, stride 3 = 125; ref with the cap of 8: 26, 29, 54; ref16 from `ref_cap.sh` when it has finished).
- Produces: totals for configs `A` (WINDOW=cum), `D` (POOL=1), `AD` (both), `ADM` (both plus MODEL=1) on strides 7 (K=4), 5 (K=2) and 3 (K=3), B=150, OFFSET=0, DEEP3=1, THREADS=6, ROUNDS=8, resumable like `loop_run2.sh`, launched detached at BelowNormal.

- [ ] **Step 1:** Write `follow_run.sh` modelled on `loop_run2.sh`, gated on `%TEMP%\ref_cap.done` and on no other `bv_loop`/`bv_follow` run, using `%TEMP%\bv_follow.exe`.
- [ ] **Step 2:** Pre-flight (CPU load, Defender, orphans, GPU leases for the `ADM` model sampling), launch detached, verify the first row appears.
- [ ] **Step 3:** When it finishes, compute for each config and stream the total M and the share of the ref(16) gain on the batches after the first (as in the loop spec), and write a Results section with the table, stating whether any config beats loop-mined by a margin larger than the run-to-run noise (M counts are deterministic here, so any difference is real but may be single-stream).
- [ ] **Step 4:** Add the README row, update `2026-10-04-research-state.md`, commit.
