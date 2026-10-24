---
status: active
---

# Class-table ablations (spec step 7) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: use superpowers:executing-plans (inline). Steps use checkbox (`- [ ]`)
> syntax for tracking.

**Goal:** Find out which fixed rewriter and prover parts the class table makes redundant, measured on the streams gate,
and delete each part whose removal costs nothing.

**Architecture:** There is no new code in the kernel. Arm B of each comparison is arm A's exe plus a `<exe>.env` file
holding `ABLATE=<switch>`. `Setup` reads that file (`job.rs`, `exe_env`), so the sweep workers and the held-out check
see the switch too. A driver outside the repo runs `scripts/streams_ab.sh` in salt pairs through
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
  decides "pays", and the driver stops that switch at the first pair that shows one.
- **D2, deletion check.** The deleted build (A) runs against the ablated build (B = the previous A plus `.env`) on
  salts 1-2. M and held-out M must be equal per salt, and the rules the same in 6 of 6 loops. Job CPU is not compared.
- **D3, one driver** runs the switches in order. Every salt pair goes through `run.ps1` untimed, pinned to CFF at
  below-normal priority: no verdict reads job CPU (amended 2026-10-24, plan
  `docs/superpowers/plans/2026-10-23-work-counts.md` D2; timed pairs had been refused for load again and again, runs
  `2026-10-23-ablations-1` and `2026-10-24-ablations-4`). A relaunch with
  `RESUME_FROM=<the earlier driver run folder>` reuses that run's finished pairs. The driver
  exits at a free or mixed verdict, an error, or the end of its list. The session arms a Monitor on the driver's log and
  sends a notification per verdict line.
- **D4, ask before cutting.** A part that pays gets a row in `docs/learned-vs-fixed.md` and the driver goes on. When a
  part is free, the session first runs one timed pair, salts 1-2 (`run.ps1 -Timed`), A against B, since some cost is
  invisible to the counters (hash-consing's cache misses, kernel proofs; `docs/tier-cycle.md`, "Work counts as the
  gate's cost"). It then brings that pair's job CPU and the deletion's scope (what goes, every caller, tests and docs)
  to the user and waits. A mixed verdict goes to the user the same way.
- **D5 (new), where the driver lives:** outside the repo, at
  `%LOCALAPPDATA%\claude-runs\tatic\ablations\driver.sh`. Its full text is in Task 1 below, and that is its one
  home. It calls `run.ps1`, which is outside repo code (lease checks stay in `~/.claude/runs`). The alternative,
  `scripts/ablate.sh`, would put a `~/.claude` path into the repo.

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
  pay. Expected: about 5 pays (one pair each, 13-20 min) and 4 free verdicts (5 pairs plus a deletion check, about
  105 min each), so about 8 h of runs. Wait time for deletion approvals comes on top.

---

### Task 1: The driver

**Files:**
- Create: `%LOCALAPPDATA%\claude-runs\tatic\ablations\driver.sh` (outside the repo)

**Interfaces:**
- Produces: `driver.sh <A exe> ablate <switch>...` and `driver.sh <deleted exe> check <ablated-from exe> <switch>`.
  It runs in the current directory, which must be the repo root. Its log is stdout. Each verdict is one line,
  starting `VERDICT <switch> pays|costs|mixed|free|error` or `VERDICT <switch> check identical|differs|error`. Exit 0 on a verdict
  that ends the run (free, mixed, a check, or the end of the list), 1 on an error, 2 on a refused start.

- [ ] **Step 1: Write the driver**

```bash
#!/bin/bash
# The class-table ablations (docs/superpowers/plans/2026-10-23-class-table-ablations.md). Run from the repo root.
#   driver.sh <A exe> ablate <switch>...   per switch: B = A + B.exe.env ABLATE=<switch>; salt pairs 1-2 .. 9-10 of
#                                          scripts/streams_ab.sh; stops a switch at the first M or held-out rise (pays);
#                                          else by the work counts: costs goes on to the next switch, mixed and free exit
#   driver.sh <deleted exe> check <ablated-from exe> <switch>   salts 1-2, deleted against ablated: identical or differs
# Every pair runs untimed through run.ps1, pinned to CFF at below-normal priority: no verdict reads job CPU.
# RESUME_FROM=<an earlier driver run folder>: reuse its finished pairs (same A exe build only)
set -u
[ -z "${ABLATE:-}" ] || { echo "driver: ABLATE=$ABLATE is set in the environment; it would reach both arms"; exit 2; }
[ -f scripts/streams_ab.sh ] || { echo "driver: run from the repo root"; exit 2; }
runs_root="$(cygpath "$LOCALAPPDATA")/claude-runs/tatic"
wrap="$(cygpath -w "$USERPROFILE/.claude/runs/run.ps1")"
[ -n "${RUN_DIR:-}" ] || { echo "driver: launch through run.ps1 (no RUN_DIR)"; exit 2; }
here=$(cygpath "$RUN_DIR")
cp "$1" "$here/A.exe" || exit 2
mode=$2; shift 2
salt_pairs=("1 2" "3 4" "5 6" "7 8" "9 10")

pair() { # <name> <A exe> <B exe> <salt> <salt>: the "salt N:" and streams_ab lines in $here/<name>.txt; 0 ok, 1 failed
  local name=$1 a b rc dir
  # a pair a killed or failed driver run already finished (RESUME_FROM: that run's folder) is reused, not rerun
  if [ -n "${RESUME_FROM:-}" ] && grep -q ' 0 of 4 arms failed' "$(cygpath "$RESUME_FROM")/$name.txt" 2>/dev/null; then
    cp "$(cygpath "$RESUME_FROM")/$name.txt" "$here/$name.txt"; echo "pair $name: reused from $RESUME_FROM"; cat "$here/$name.txt"; return 0
  fi
  a=$(cygpath -d "$2"); b=$(cygpath -d "$3")
  powershell -NoProfile -File "$wrap" -Kind gate -Name "$name" \
    -Command "start /b /wait /belownormal /affinity CFF bash scripts/streams_ab.sh $a $b $4 $5" < /dev/null > /dev/null 2>&1
  rc=$?
  # the newest folder of this name: run.ps1 appends -2, -3 to a name an earlier driver run already used
  dir=$(ls -dt "$runs_root"/*-"$name" "$runs_root"/*-"$name"-[0-9]* 2>/dev/null | head -1)
  echo "pair $name: exit $rc, $dir"
  grep -E '^salt [0-9]+:|^streams_ab' "$dir/out.log" > "$here/$name.txt" 2>/dev/null
  cat "$here/$name.txt"
  [ $rc = 0 ] && grep -q ' 0 of 4 arms failed' "$here/$name.txt"
}
# per salt line, one row per counter: salt name A B
wcols() { sed -nE 's/^salt ([0-9]+): .*; work A (.*) B (.*)$/\1|\2|\3/p' "$@" | awk -F'|' '{na = split($2, x, " "); split($3, y, " "); for (i = 1; i <= na; i++) {split(x[i], p, "="); split(y[i], q, "="); print $1, p[1], p[2], q[2]}}'; }
# each counter's tolerance: max(its A/A spread, 1%); the spreads are a few ppm (docs/tier-cycle.md, "Work counts as the
# gate's cost")
tols="interp=0.01 walk=0.01 match=0.01 op=0.01"
# columns of "salt N: M A a B b; held A a B b; jobcpu A a B b": salt mA mB hA hB cA cB
cols() { sed -nE 's/^salt ([0-9]+): M A ([0-9]+) B ([0-9]+); held A ([0-9x]+) B ([0-9x]+); jobcpu A ([0-9.]+) B ([0-9.]+).*/\1 \2 \3 \4 \5 \6 \7/p' "$@"; }

if [ "$mode" = check ]; then
  sw=$2; cp "$1" "$here/B.exe" || exit 2; echo "ABLATE=$sw" > "$here/B.exe.env"
  pair "check-$sw" "$here/A.exe" "$here/B.exe" 1 2 || { echo "VERDICT $sw check error"; exit 1; }
  same=$(cols "$here/check-$sw.txt" | awk '$2 != $3 || $4 != $5 {d++} END {print d + 0}')
  if [ "$same" = 0 ] && grep -q 'rules same in 6 of 6 loops' "$here/check-$sw.txt"; then echo "VERDICT $sw check identical"
  else echo "VERDICT $sw check differs"; fi
  exit 0
fi

for sw in "$@"; do
  cp "$here/A.exe" "$here/B_$sw.exe"; echo "ABLATE=$sw" > "$here/B_$sw.exe.env"
  done_pairs=()
  for p in "${salt_pairs[@]}"; do
    set -- $p
    pair "abl-$sw-s$1-$2" "$here/A.exe" "$here/B_$sw.exe" $1 $2 || { echo "VERDICT $sw error at salts $p"; exit 1; }
    done_pairs+=("$here/abl-$sw-s$1-$2.txt")
    rise=$(cols "${done_pairs[@]}" | awk '$3 > $2 || $5 > $4 {print "salt " $1}' | head -1)
    [ -n "$rise" ] && break
  done
  sum=$(cols "${done_pairs[@]}" | awk '{mA+=$2; mB+=$3; hA+=$4; hB+=$5; cA+=$6; cB+=$7} END {printf "M A %d B %d; held A %d B %d; jobcpu A %.0f B %.0f (%+.1f%%)", mA, mB, hA, hB, cA, cB, 100*(cB-cA)/cA}')
  last=$(cols "${done_pairs[@]}" | tail -1 | cut -d' ' -f1)
  if [ -n "$rise" ]; then echo "VERDICT $sw pays ($rise first): $sum, salts 1-$last"; continue; fi
  # the counters (spec docs/superpowers/specs/2026-10-23-work-counts-design.md, decision 6(d)): each summed over the
  # salts, against its tolerance
  v=$(wcols "${done_pairs[@]}" | awk -v tols="$tols" 'BEGIN {n = split(tols, t, " "); for (i = 1; i <= n; i++) {split(t[i], kv, "="); tol[kv[1]] = kv[2]}}
      {if (!($2 in a)) o[++k] = $2; a[$2] += $3; b[$2] += $4}
      END {for (i = 1; i <= k; i++) {c = o[i]; d = a[c] ? (b[c] - a[c]) / a[c] : (b[c] ? 1 : 0); s = s sprintf(" %s %+.2f%%", c, 100 * d)
           if (d > tol[c]) up = 1; else if (d < -tol[c]) dn = 1}
           print (up ? (dn ? "mixed" : "costs") : "free") ":" s}')
  echo "VERDICT $sw ${v%%:*}: $sum; work${v#*:}, salts 1-10"
  case "${v%%:*}" in costs) continue ;; *) exit 0 ;; esac
done
echo "DRIVER done: no switch left"
```

- [ ] **Step 2: Check the parser on the A/A's logs (A/A means free on every count)**

Write `$TEMP/aa_check.sh`. It runs `cols` (copied from the driver) and the verdict arithmetic over the five A/A
`out.log` files (`%LOCALAPPDATA%\claude-runs\tatic\2026-10-23-streams-aa-{1-2-3,3-4,5-6,7-8,9-10-2}`). Then run it.

Expected: 10 rows; `M A 1718 B 1718; held A 8721 B 8721; jobcpu A 5865 B 5842 (-0.4%)`; no rise; cpu `within`.
(Checked while writing this plan, 2026-10-23.)

- [ ] **Step 3: Check the parser's "pays" path.** Feed one A/A file through `sed 's/M A 176 B 176/M A 176 B 177/'`.

Expected: the rise is found at salt 1. (Checked while writing this plan.)

- [ ] **Step 4: Check the refusals.** Start it with `ABLATE=x` in the environment, from `tests/`, and with no
  `RUN_DIR`.

Expected: exit 2 each time, each with its own message.

### Task 2: Build A and launch

- [ ] **Step 1:** `git switch -c ablations`. Run `cargo test --release -j 4`; the suite must be green before
  anything is ablated. Build the arms' exe with the sweep profile (fat LTO, what README prescribes for sweeps and
  timing): `cargo test --profile sweep -j 4 --test church_bv --no-run`, then take the path from cargo's "Executable"
  line (`target\sweep\build\tatic\<hash>\out\church_bv-<hash>.exe`). Check that `tools/runs/target/release/runs.exe` exists
  (`streams_ab.sh` needs it).
- [ ] **Step 2:** Check for live CPU leases and others' load. Then launch the driver detached, through the wrapper
  as its own non-timed row:
  `cmd //c start "" //b powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind sweep -Name ablations-1 -Command "bash <driver.sh short path> <A exe short path> ablate promoted assoc tree chain comm collapse eq_truth eq_pos eq_classes"`.
  Annotate its `docs/runs.md` row.
- [ ] **Step 3:** Arm a Monitor on the driver's `out.log`, with an exiting loop that ends when `run.json` has an
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
  3. build the deleted exe (sweep profile), then run `driver.sh <deleted exe> check <previous A> <switch>` through
     the wrapper (row `ablations-check-<switch>`). `<previous A>` is `A.exe` in the last driver run's folder;
  4. on `identical`, relaunch the driver (row `ablations-<n+1>`) with the deleted exe as A and the switches after
     this one;
  5. on `differs`, stop and report: the switch removed more than the deleted code, or the deletion removed more
     than the switch.
- **error:** read the pair's `out.log` and `err.log` and report. Relaunch only after the cause is known, with
  `RESUME_FROM` set to the failed driver run's folder (same A exe) so its finished pairs are not rerun.

### Task 4: Close

- [ ] `docs/tier-cycle.md`: a step-7 section with each verdict, the numbers, and the run ids.
- [ ] Spec §5: note what was deleted. The spec's status stays as it is: step 8 (§6, `ClassReps` moves onto the
  table) comes next and has its own plan.
- [ ] Fix stale claims that name deleted switches or parts: `ROADMAP.md`, `PARKED.md`, `README.md`,
  `docs/learned-vs-fixed.md`, and `CLAUDE.md` if it names a deleted part.
- [ ] Set this plan's front matter to `status: done`. Leftovers go to `PARKED.md` first.

## Review Focus

1. The driver killed mid-pair. That pair has no `.txt`, and its verdict must come out `error`, never "free" from the
   pairs that did finish. The driver only reaches "free" after all five pairs pass.
2. (Deleted 2026-10-24: job CPU no longer decides a verdict.)
3. A deleted part whose code other switches' paths also use (`tree_step` is reached from the `sub` branch too). The
   deletion check (D2) catches a difference only on salts 1-2.
4. A failed arm: an over-8 GB stop, a non-zero exit, or `held` printing `x` for a loop. `streams_ab.sh` counts
   each of these as a failed arm (checked: its `held` loop adds 1 to `failed` on `x`). The driver's
   `0 of 4 arms failed` grep then turns the pair into an `error`, so a B arm that breaks never reads as "free".
5. Midnight: run folders are named `<date>-<name>`, so the driver looks them up by `*-<name>`, never by date.
