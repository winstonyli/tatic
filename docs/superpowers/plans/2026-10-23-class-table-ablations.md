---
status: done
---

# Class-table ablations (spec step 7) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: use superpowers:executing-plans (inline). Steps use checkbox (`- [ ]`)
> syntax for tracking.

**Goal:** Find out which fixed rewriter and prover parts the class table makes redundant, measured on the streams gate,
and delete each part whose removal costs nothing.

**Architecture:** There is no new code in the kernel. Arm B of each comparison is arm A's exe plus a `<exe>.env` file
holding `ABLATE=<switch>`. `Setup` reads that file (`job.rs`, `exe_env`), so the sweep workers and the held-out check
see the switch too. A driver (`scripts/ablations.sh`) runs `scripts/streams_ab.sh` once per switch, salts 1-10, through
`run.ps1` (untimed; D3), prints one verdict per switch, and stops at every "free" or "mixed" verdict. A deletion is a code change that
gets its own approval. A deletion check then shows the deleted build matches the ablated one, and the driver resumes
from the deleted build.

**Tech Stack:** bash, `scripts/streams_ab.sh`, `~/.claude/runs/run.ps1`, the `church_bv` test exe.

**Spec:** `docs/superpowers/specs/2026-10-22-class-table-normal-form-design.md`, §5, the last two paragraphs (the
order and "costs nothing"), and decision 9.

## Decisions (assumed: presented 2026-10-23 with these recommendations, not answered explicitly)

- **D1, the verdict is one-sided.** A part *pays* when its ablation raises M or held-out M on any salt. Otherwise the
  work counts decide, each summed over salts 1-10 against its tolerance (spec
  `docs/superpowers/specs/2026-10-23-work-counts-design.md`, decision 6(d); amended 2026-10-24, replacing job CPU's
  5.4%): *costs* when some counter rises and none falls (the part saves work: it pays, and the driver goes on), *free*
  when none rises, *mixed* when some rise and some fall. A drop in M counts as free and is reported. M and held-out M were identical in both arms of the A/A on every salt
  (`docs/tier-cycle.md`, "The gate on the streams and its A/A baseline"). A rise on any one salt therefore already
  decides "pays", and the driver names every salt that shows one.
- **D2, deletion check.** The deleted build (A) runs against the ablated build (B = the previous A plus `.env`) on
  salts 1-2. M and held-out M must be equal per salt, and the rules the same in 6 of 6 loops. Job CPU is not compared.
- **D3, one driver** runs the switches in order. Every gate run goes through `run.ps1` untimed, pinned to CFF at
  below-normal priority: no verdict reads job CPU (amended 2026-10-24, plan
  `docs/superpowers/plans/2026-10-23-work-counts.md` D2; timed pairs had been refused for load again and again, runs
  `2026-10-23-ablations-1` and `2026-10-24-ablations-4`).
  `streams_ab.sh` runs 4 arms at a time and keeps each finished arm in `arm-cache` (amended 2026-10-24: A runs once
  per build, and a relaunch reuses every arm a stopped run finished; `RESUME_FROM` and the salt pairs were deleted;
  4 arms at once cost about 50% more job CPU per arm and gave about 1.8x throughput, run `2026-10-24-work-aa-jobs4-1-4`).
  The driver stops a gate at the first salt whose B rises, read from the salt lines `streams_ab.sh` prints as each salt finishes: one rise settles "pays" (amended 2026-10-24; free, costs and
  mixed still read all 10 salts). The cache key hashes the exe by its long name: by the 8.3 short name the driver passes,
  `B_collapse.exe.env` was not found, so `collapse`'s B arms were copied from A (run `2026-10-24-abl-collapse`, its verdict
  void; fixed in `streams_ab.sh`). The driver exits at a free or mixed verdict, an error, or the end of its list. The session arms a Monitor on the driver's log and
  sends a notification per verdict line.
- **D4, ask before cutting.** A part that pays gets a row in `docs/learned-vs-fixed.md` and the driver goes on. When a
  part is free, the session first runs one timed pair, salts 1-2 (`run.ps1 -Timed`), A against B, since some cost is
  invisible to the counters (hash-consing's cache misses, kernel proofs; `docs/tier-cycle.md`, "Work counts as the
  gate's cost"). It then brings that pair's job CPU and the deletion's scope (what goes, every caller, tests and docs)
  to the user and waits. A mixed verdict goes to the user the same way.
- **D5, where the driver lives:** `scripts/ablations.sh`, checked by `scripts/test_gate.sh` (amended 2026-10-24,
  the final review's I2: outside the repo it had no tests and its one home was a code block in this plan). It launches
  `run.ps1` by path (the first repo script to; CLAUDE.md routes long runs through it); lease and load checks stay in `~/.claude/runs`. It first copies itself
  into its run folder and runs from there, so an edit or a checkout mid-run cannot change it.

## Global Constraints

- Order (spec §5): `promoted`; `assoc`, `tree`, `chain`; `comm`; `collapse`; `eq_truth`, `eq_pos`; `eq_classes`.
  Each switch is measured against the state the previous ones left.
- `ABLATE` must not be set in the driver's environment: `merge_env` lets process env win over `<exe>.env`, so it
  would reach both arms. The driver refuses to start if it is set.
- Exes are copies outside `target\`, in the driver's run folder, so a rebuild cannot change an arm mid-run.
- Python never reads stdin (`python -P f.py < /dev/null`). No fixed sleeps, no `tail -F`. cargo `-j 4`.
- Never stop or deprioritize another session's job. Lease and load logic stays in `~/.claude/runs`.
- Work on branch `ablations`; merging, pushing and tagging only on request.

## Evidence before launch: which switches take effect

The quick check ran held-out M with no mined rules: bands 11 and 13, `CHECK_FAST`, M = p − f + n, summed. It used
build 80f024a, with each switch in its copy's `.env`. Run record: `docs/runs.md`, row
`2026-10-23-ablate-switch-check`.

| ABLATE | held-out M | vs none |
|---|---|---|
| none | 545 | |
| promoted | 618 | +73 |
| assoc | 573 | +28 |
| tree | 545 | 0 |
| chain | 545 | 0 |
| comm | 552 | +7 |
| collapse | 545 | 0 |
| eq_truth | 659 | +114 |
| eq_pos | 608 | +63 |
| eq_classes | 545 | 0 |
| classes | 626 | +81 |
| classes,tree | 690 | (+64 on classes) |
| classes,chain | 626 | (0) |
| classes,collapse | 627 | (+1) |
| classes,eq_classes | 668 | (+42) |
| classes,assoc / classes,assoc,chain | 686 / 686 | (chain 0) |
| tree,chain / classes,tree,chain | 545 / 690 | (chain 0) |
| eq_truth,eq_pos / eq_truth,eq_pos,eq_classes | 765 / 765 | (0) |

What this shows:
- The `.env` mechanism works: eight of the nine switches change held-out M in some setting.
- `tree`, `collapse` and `eq_classes` take effect only once the class step is off. The table covers for them on these
  laws.
- `chain` changed nothing in any setting tried. Its only caller is the `add` step list (`rewrite.rs`, after
  `rule_step`), and no held-out law reaches it. The loops' own M may still use it, and the gate decides.
- With no mined rules, `promoted`, `assoc`, `comm`, `eq_truth` and `eq_pos` raise held-out M, so they will probably
  pay. Expected (before the arm cache): about 5 pays (one pair each, 13-20 min) and 4 free verdicts (5 pairs plus a deletion check, about
  105 min each), so about 8 h of runs. Wait time for deletion approvals comes on top.

---

### Task 1: The driver

**Files:**
- Create: `scripts/ablations.sh` (first at `%LOCALAPPDATA%\claude-runs\tatic\ablations\driver.sh`; D5)

**Interfaces:**
- Produces: `ablations.sh <A exe> ablate <switch>...` and `ablations.sh <deleted exe> check <ablated-from exe> <switch>`.
  It runs in the current directory, which must be the repo root. Its log is stdout. Each verdict is one line,
  starting `VERDICT <switch> pays|costs|mixed|free|error` or `VERDICT <switch> check identical|differs|error`. Exit 0 on a verdict
  that ends the run (free, mixed, a check, or the end of the list), 1 on an error, 2 on a refused start.

- [x] **Step 1: Write the driver**

The driver is `scripts/ablations.sh` (moved into the repo 2026-10-24, D5), its checks `scripts/test_gate.sh`.

- [x] **Step 2: Check the parser on the A/A's logs (A/A means free on every count)**

Write `$TEMP/aa_check.sh`. It runs `cols` (copied from the driver) and the verdict arithmetic over the five A/A
`out.log` files (`%LOCALAPPDATA%\claude-runs\tatic\2026-10-23-streams-aa-{1-2-3,3-4,5-6,7-8,9-10-2}`). Then run it.

Expected: 10 rows; `M A 1718 B 1718; held A 8721 B 8721; jobcpu A 5865 B 5842 (-0.4%)`; no rise; cpu `within`.
(Checked while writing this plan, 2026-10-23.)

- [x] **Step 3: Check the parser's "pays" path.** Feed one A/A file through `sed 's/M A 176 B 176/M A 176 B 177/'`.

Expected: the rise is found at salt 1. (Checked while writing this plan.)

- [x] **Step 4: Check the refusals.** Start it with `ABLATE=x` in the environment, from `tests/`, and with no
  `RUN_DIR`.

Expected: exit 2 each time, each with its own message.

### Task 2: Build A and launch

- [x] **Step 1:** `git switch -c ablations`. Run `cargo test --release -j 4`; the suite must be green before
  anything is ablated. Build the arms' exe with the sweep profile (fat LTO, what README prescribes for sweeps and
  timing): `cargo test --profile sweep -j 4 --test church_bv --no-run`, then take the path from cargo's "Executable"
  line (`target\sweep\build\tatic\<hash>\out\church_bv-<hash>.exe`). Check that `tools/runs/target/release/runs.exe` exists
  (`streams_ab.sh` needs it).
- [x] **Step 2:** Check for live CPU leases and others' load. Then launch the driver detached, through the wrapper
  as its own non-timed row:
  `cmd //c start "" //b powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind sweep -Name ablations-1 -Command "bash scripts/ablations.sh <A exe short path> ablate promoted assoc tree chain comm collapse eq_truth eq_pos eq_classes"`.
  Annotate its `docs/runs.md` row.
- [x] **Step 3:** Arm a Monitor on the driver's `out.log`, with an exiting loop that ends when `run.json` has an
  `exit`. It prints each `VERDICT` and `DRIVER` line. Send a push notification per verdict.

### Task 3: Per verdict

- **pays:** add the measurement to `docs/learned-vs-fixed.md` (the row that names the part: rewrite strategy for
  `promoted`, `assoc`, `tree`, `chain`, `comm`, `collapse`; the prover row for `eq_truth`, `eq_pos`, `eq_classes`) and
  to `docs/tier-cycle.md`'s section for step 7. Commit both. The driver has already moved on.
- **free:** (the driver has exited.) List what deleting the part removes: the switch's `ablated` guard and the code
  only it reaches, every caller (grep), tests that only test it, `ABLATE` names in docs, and stale doc claims.
  Bring the list to the user and wait (D4). On approval:
  1. delete, build, and run `cargo test --release -j 4 --test church_bv`; the suite must be green;
  2. commit;
  3. build the deleted exe (sweep profile), then run `scripts/ablations.sh <deleted exe> check <previous A> <switch>` through
     the wrapper (row `ablations-check-<switch>`). `<previous A>` is `A.exe` in the last driver run's folder;
  4. on `identical`, relaunch the driver (row `ablations-<n+1>`) with the deleted exe as A and the switches after
     this one;
  5. on `differs`, stop and report: the switch removed more than the deleted code, or the deletion removed more
     than the switch.
- **error:** read the gate run's `out.log` and `err.log` and report. Relaunch only after the cause is known, with
  the same command: the arm cache skips every arm that finished.

### Task 4: Close

- [x] `docs/tier-cycle.md`: a step-7 section with each verdict, the numbers, and the run ids.
- [x] Spec §5: note what was deleted. The spec's status stays as it is: step 8 (§6, `ClassReps` moves onto the
  table) comes next and has its own plan.
- [x] Fix stale claims that name deleted switches or parts: `ROADMAP.md`, `PARKED.md`, `README.md`,
  `docs/learned-vs-fixed.md`, and `CLAUDE.md` if it names a deleted part.
- [x] Set this plan's front matter to `status: done`. Leftovers go to `PARKED.md` first.

## Review Focus

1. The driver killed mid-run. Its gate run has no `.txt`, and the verdict must come out `error`, never "free"; a
   relaunch reuses the arms that finished (arm cache). The driver only reaches "free" when all 20 arms pass.
2. (Deleted 2026-10-24: job CPU no longer decides a verdict.)
3. A deleted part whose code other switches' paths also use (`tree_step` is reached from the `sub` branch too). The
   deletion check (D2) catches a difference only on salts 1-2.
4. A failed arm: an over-8 GB stop, a non-zero exit, or `held` printing `x` for a loop. `streams_ab.sh` counts
   each of these as a failed arm (checked: `arm` writes 1 to its `failed` file on `x`). The driver's
   `0 of N arms failed` grep then turns the run into an `error`, so a B arm that breaks never reads as "free".
5. Midnight: run folders are named `<date>-<name>`, so the driver looks them up by `*-<name>`, never by date.
6. A stale cached arm. The cache key hashes the exe, its `.exe.env` and `streams_ab.sh`, so a rebuild or a script
   edit misses, and a failed arm is never stored (fixtures: an env change misses, the cache off runs both arms).
