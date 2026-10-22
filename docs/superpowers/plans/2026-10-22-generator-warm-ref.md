---
status: draft
---

# Law generator on warm loops and ref mines (v0.2, step 4) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Measure whether the law generator's extras pay on ref mines and warm loops (the regimes that take them today,
unmeasured), and set each regime's default from the result.

**Architecture:** No change to the miner or the driver. One script runs, per salt, two mine sweeps (generator on and
`ABLATE=gen`) and four loop sweeps that read those libraries through `LIB=`: a full 2×2 of {ref mines with extras or
not} × {warm loops with extras or not}. The spec's third arm ("on with ref mines off", a temporary `ABLATE=gen_ref`) is
one cell of that grid, so the switch is never written. A 1-salt probe sets the time estimate, then salts 1-10 run.

**Tech Stack:** bash scripts under `docs/runs/2026-10-22/scripts/`, the `church_bv` sweep exe (`driver::sweep`),
`tools/runs` (`runs run`: wall and job CPU), `~/.claude/runs/run.ps1`.

**Spec:** `docs/superpowers/specs/2026-10-17-law-generator-design.md`, "Build order" step 4 (and §1, "One stage, three
regimes"). Roadmap: v0.2 ("Does the law generator pay everywhere it runs?"). Parked entry: `PARKED.md`, "Law generator
on warm loops and ref mines".

## Global Constraints

- Salts 1-10; stages `mines mines:u3 own cold cross pooled mixed` (spec step 4). mix3 and u3 enter as ref mines only.
- The default `mines` stage covers sbo3, add3, mix3 and cmp3d; `mixed` needs `lib_u3` (spec step 4).
- A 1-salt probe goes first; its time sets the stated estimate, and it records mix3's and u3's L and generation time.
- Ref mines mine 200-400 laws against a loop mine's 100, so the same f gives them a smaller share of extras: the table
  states it, and a ref loss is followed up before the regime is turned off (spec step 4).
- A regime whose M gets worse runs with the generator off, and the doc says why (spec step 4).
- Long runs go through `~/.claude/runs/run.ps1` (`-Kind probe` / `sweep`), raw output in `%LOCALAPPDATA%\claude-runs\tatic`,
  a row in `docs/runs.md`; the exe is a copy outside `target`. At most 12 busy threads: `SWEEP_LANES` stays at 2 (2 × 6
  scoring workers).
- Report CPU load and Defender real-time protection with every timing (`run.ps1` records both).
- Never fixed sleeps: wait on a condition with a deadline. No `python` reading stdin.

## Review Focus

1. **An arm that fails counts as M 0.** A sweep that panics (a short extras list, a missing library) leaves an empty or
   partial tsv; the summary must print `FAILED` and count it, never sum it as 0. Task 1's smoke breaks one arm on purpose.
2. **A loop sweep reading the wrong library.** `LIB=` must point at that salt's own mine sweep; a wrong salt or a missing
   `lib_u3` gives plausible numbers. Task 1 checks the split sweep against one combined sweep (rules files equal).
3. **mix3's or u3's extras list too short, or its generation too heavy.** mix3's pool (23665 terms) has never been
   generated; the sweep stops before any work if a list is short (`scope_extras`), and the 8 GB watchdog stops a runaway.
   Task 2's probe records both.
4. **Comparing gen-on loop time across lanes and contention.** Loop seconds run in 2 lanes on a shared machine; M is the
   decision metric, times are reported with the CPU load and only as a cost estimate.
5. **The ref effect read off the ref mines' own M alone.** A library exists to be served: the ref regime is judged by the
   warm loops it seeds (on_* against off_*), its own M second (Task 3's table has both).

---

### Task 1: The arms script, checked on a small sweep

**Files:**
- Create: `docs/runs/2026-10-22/scripts/gen_warm.sh`

**Interfaces:**
- Consumes: the sweep exe's env (`SWEEP`, `SWEEP_OUT`, `SALT`, `LIB`, `ABLATE=gen`, `MACHINE_STATE=0`), `<stage>.tsv`
  columns (loops: family, stride-phase, from_src, total M, batch Ms comma-separated, rules, secs, exhausted, joined,
  reached; mines: family, secs, total M, rules, exhausted, joined, reached), `kk.sh`, `runs.exe`.
- Produces: per salt `mon_<s>`, `moff_<s>`, `on_on_<s>`, `off_on_<s>`, `on_off_<s>`, `off_off_<s>` under the run
  directory; one summary line per sweep; a last line `gen_warm: N of M sweeps failed`; exit 1 if any failed. Env
  overrides `MINES_SWEEP`, `LOOP_SWEEP`, `COLD_SWEEP`, `ARMS` for the smoke check.

- [ ] **Step 1: Write the script**

```bash
# gen_warm.sh <exe> <salt>...: the law generator on ref mines and warm loops (law-generator spec step 4; plan
# docs/superpowers/plans/2026-10-22-generator-warm-ref.md). Per salt, into kk.sh's directory ($RUN_DIR under run.ps1):
# mon_<s> and moff_<s>, the ref mines (SWEEP=$MINES_SWEEP) with the generator on and with ABLATE=gen; then the loops
# (SWEEP=$LOOP_SWEEP) as <lib>_<gen>_<s>: lib on/off reads mon_<s>/moff_<s> through LIB=, gen on/off is the loops' own
# extras (off: ABLATE=gen). Cold loops read no library, so only on_on and off_off add $COLD_SWEEP. ARMS picks the loop
# arms (default all four). Each sweep is a `runs run` (wall, job CPU); a watchdog stops the exe past 8 GB. Prints one line
# per sweep: ref mines' M per family, or per stage total M and mined-batch M (batches 2-3); a sweep with a non-zero exit
# or a missing tsv prints FAILED and counts. Last line: sweeps failed; exits 1 if any did.
exe=$1; shift
d=$(bash "$(dirname "$0")/../../2026-10-12/scripts/kk.sh")
runs="$(dirname "$0")/../../../../tools/runs/target/release/runs.exe"
[ -x "$runs" ] || { echo "gen_warm: $runs not built (cargo build --release in tools/runs)"; exit 1; }
name=$(basename "$exe" | sed 's/\.[Ee][Xx][Ee]$//')
mines=${MINES_SWEEP:-mines mines:u3}
loops=${LOOP_SWEEP:-own cross pooled mixed}
cold=${COLD_SWEEP-cold}
failed=0; total=0
# sweep <dir> <SWEEP> [VAR=value...]: one sweep of salt $s into <dir>
sweep() {
  local o=$1 sw=$2; shift 2
  mkdir -p "$o"; rm -f "$o/exit"
  ( "$runs" run "$(cygpath -w "$o")" -- MACHINE_STATE=0 SALT=$s "SWEEP=$sw" "SWEEP_OUT=$(cygpath -w "$o")" "$@" "$exe" driver::sweep --exact --ignored --nocapture < /dev/null > "$o/result.txt" 2>&1; echo $? > "$o/exit" ) &
  while [ ! -f "$o/exit" ]; do
    mb=$(powershell -NoProfile -Command "[int]((Get-Process $name -EA 0 | Measure-Object WorkingSet64 -Sum).Sum/1MB)" < /dev/null | tr -d '\r')
    [ "${mb:-0}" -gt 8192 ] && { echo "$o: over 8 GB ($mb MB), stopped"; taskkill //F //IM "$name.exe" > /dev/null; }
    ping -n 6 127.0.0.1 > /dev/null
  done
  wait
  total=$((total + 1))
  local line="" ok=1 st f
  for st in $sw; do
    f="$o/${st//:/_}.tsv"
    if [ ! -s "$f" ]; then ok=0; line="$line $st MISSING;"; continue; fi
    if [ "${st%%:*}" = mines ]; then
      line="$line $(awk -F'\t' '$3 !~ /^[0-9]+$/ {bad=1} {printf "%s M %s rules %s secs %s, ", $1, $3, $4, $2} END {if (bad) printf "BAD "}' "$f")"
    else
      line="$line $st $(awk -F'\t' '$4 !~ /^[0-9]+$/ {bad=1} {split($5,m,","); t+=$4; mb+=m[2]+m[3]; r+=$6; c+=$7} END {printf "M %d mined %d rules %d loop secs %d%s;", t, mb, r, c, bad ? " BAD" : ""}' "$f")"
    fi
  done
  case "$line" in *MISSING*|*BAD*) ok=0 ;; esac
  [ "$(cat "$o/exit")" = 0 ] || ok=0
  [ $ok = 1 ] || { failed=$((failed + 1)); line="FAILED (exit $(cat "$o/exit"))$line"; }
  echo "salt $s $(basename "$o"):$line $(grep -oE '(wall|jobcpu)=[0-9.]+' "$o/result.txt" | tr '\n' ' ')"
}
for s in "$@"; do
  sweep "$d/mon_$s" "$mines"
  sweep "$d/moff_$s" "$mines" ABLATE=gen
  for arm in ${ARMS:-on_on off_on on_off off_off}; do
    lib=${arm%_*}; gen=${arm#*_}
    sw=$loops; [ "$arm" = on_on ] || [ "$arm" = off_off ] && sw="$loops $cold"
    vars=("LIB=$(cygpath -w "$d/m${lib}_$s")"); [ "$gen" = off ] && vars+=(ABLATE=gen)
    sweep "$d/${arm}_$s" "$sw" "${vars[@]}"
  done
done
echo "gen_warm: $failed of $total sweeps failed"
[ $failed = 0 ]
```

- [ ] **Step 2: Build and copy the exe**

Run (bash, repo root):
```bash
cargo test --profile sweep --test church_bv --no-run -j 8 2>&1 | tail -1
cp "$(ls -t target/sweep/build/tatic/*/out/church_bv-*.exe | head -1)" "$TEMP/bv_v02.exe"
```
Expected: `Finished`; the copy exists. (If the newest exe is under `target/sweep/deps/` instead, copy that one; check
the timestamp is from this build.)

- [ ] **Step 3: Smoke run, split sweeps (the script under test)**

Run:
```bash
RUN_DIR= MINES_SWEEP="mines:add3" LOOP_SWEEP="own:add3" COLD_SWEEP="" ARMS="on_on off_off" bash docs/runs/2026-10-22/scripts/gen_warm.sh "$TEMP/bv_v02.exe" 1 | tee "$TEMP/gw_smoke.txt"
```
Expected: four summary lines (mon_1, moff_1, on_on_1, off_off_1), numeric M on each, last line
`gen_warm: 0 of 4 sweeps failed`. The run directory is kk.sh's `$TEMP/tatic-runs/tatic`.

- [ ] **Step 4: Combined sweep, the control for `LIB=`**

Run:
```bash
d="$TEMP/tatic-runs/tatic/combined_1"; mkdir -p "$d"
MACHINE_STATE=0 SALT=1 SWEEP="mines:add3 own:add3" SWEEP_OUT="$(cygpath -w "$d")" "$TEMP/bv_v02.exe" driver::sweep --exact --ignored --nocapture < /dev/null > "$d/log.txt" 2>&1; echo exit $?
for p in 1 2 3; do cmp -s "$d/own_add3_add3_${p}_add3/rules.txt" "$TEMP/tatic-runs/tatic/on_on_1/own_add3_add3_${p}_add3/rules.txt" && echo "loop $p same" || echo "loop $p DIFFER"; done
cmp "$d/own_add3.tsv" "$TEMP/tatic-runs/tatic/on_on_1/own_add3.tsv" | head -1; cut -f1-5 "$d/own_add3.tsv"; cut -f1-5 "$TEMP/tatic-runs/tatic/on_on_1/own_add3.tsv"
```
Expected: `exit 0`, `loop 1 same`, `loop 2 same`, `loop 3 same`, and equal M columns (the secs column may differ, so
`cmp` may report a difference; compare the printed columns 1-5). Check the loop directory names with `ls` first: they are
`<stage>_<fam>_<phase>_<src>` with `:` in the stage replaced by `_` (`driver.rs`, `loop_cfgs`). A difference means the
split does not reproduce one sweep: stop and find out why before Task 2.

- [ ] **Step 5: The failure path**

Run:
```bash
RUN_DIR= MINES_SWEEP="mines:add3" LOOP_SWEEP="own:nosuchfamily" COLD_SWEEP="" ARMS="off_off" bash docs/runs/2026-10-22/scripts/gen_warm.sh "$TEMP/bv_v02.exe" 1 | tail -2; echo "script exit $?"
```
Expected: the `off_off_1` line starts `FAILED`, the last line says `1 of 3 sweeps failed`. (`$?` after the pipe is
`tail`'s; the count line is the check.)

- [ ] **Step 6: Clean up and commit**

Delete `$TEMP/tatic-runs/tatic/{mon_1,moff_1,on_on_1,off_off_1,combined_1}` (this session's smoke output only).
```bash
git add docs/runs/2026-10-22/scripts/gen_warm.sh
git commit -q -F "$TEMP/msg.txt"   # "gen_warm.sh: the generator on ref mines and warm loops, a 2x2 of libraries and loops"
```

### Task 2: The 1-salt probe

**Files:**
- Modify: `docs/runs.md` (the row `run.ps1` writes)

**Interfaces:**
- Consumes: `gen_warm.sh`, `$TEMP/bv_v02.exe`.
- Produces: the run `2026-10-22-gen-warm-probe` (or the date it runs), its summary lines, the mix3/u3 `GEN_LAWS` and
  `GEN ... L n` lines, whether the 8 GB watchdog fired, and the estimate for Task 3.

- [ ] **Step 1: Check the machine**

Look for live runs (`docs/runs.md` rows with no `end`, `Get-Process church_bv*`). Note CPU load and Defender RTP; do not
change Defender.

- [ ] **Step 2: Launch**

```bash
cmd //c start "" //b powershell -NoProfile -File "C:/Users/Winston Li/.claude/runs/run.ps1" -Kind probe -Name gen-warm-probe -Command "bash docs/runs/2026-10-22/scripts/gen_warm.sh 'C:\Users\WINSTO~1\AppData\Local\Temp\bv_v02.exe' 1"
```
Wait on `"exit": *[-0-9]` in `run.json` with a deadline loop (no fixed sleep), checking the `out.log` tail every few
minutes and stating elapsed time if asked.
Expected: exit 0, `gen_warm: 0 of 6 sweeps failed`.

- [ ] **Step 3: Read the probe**

```bash
r="$LOCALAPPDATA/claude-runs/tatic/<date>-gen-warm-probe"
grep -h "GEN_LAWS\|^GEN " "$r"/mon_1/result.txt | sort -u
cat "$r/out.log"
```
Record: mix3's and u3's L and generation seconds; each sweep's wall and job CPU; whether the watchdog fired. Estimate
Task 3 as 9 × the probe's wall (salts vary: say so). If the estimate is over 12 h, or a sweep failed, stop and report
before Task 3.

- [ ] **Step 4: Commit the run row** (`docs/runs.md`).

### Task 3: Salts 1-10

**Files:**
- Modify: `docs/runs.md`

- [ ] **Step 1: Launch** salts 2-10 the same way (`-Kind sweep -Name gen-warm`, salts `2 3 4 5 6 7 8 9 10`); salt 1
  comes from the probe (same exe, same script). Wait on `run.json` as in Task 2.
  Expected: `gen_warm: 0 of 54 sweeps failed`.

- [ ] **Step 2: Tabulate.** Write `docs/runs/2026-10-22/scripts/gen_warm_table.sh <dir>...` against the probe's real output (its code is not fixed here: it parses the summary lines and tsvs Task 2 shows). It reads the run folders'
  tsvs and prints, over salts 1-10:
  - ref mines, mon against moff: per family M, rules, secs, and the extras share (n over the mine's laws, from the
    `GEN ... L n` lines and `MINES`' b × k);
  - per warm stage (own, cross, pooled, mixed), per arm: total M and mined-batch M; and the three paired comparisons,
    salts better / equal / worse on total M:
    - loop extras: off_on against off_off (and on_on against on_off);
    - ref extras on warm loops: on_off against off_off (and on_on against off_on);
    - both: on_on against off_off;
  - cold, on_on against off_off: a check that the cold result (s16 against off) still holds on this build.
  Commit it with the run row.

### Task 4: Decide and record

**Files:**
- Modify: `docs/tier-cycle.md` (a new section after "The law generator as a stage"), `PARKED.md`, `ROADMAP.md`,
  `tests/church_bv/driver.rs:19-23` (module doc), the spec's step 4 (a "Done" line with the run ids), this plan's front
  matter.

- [ ] **Step 1: The rule, per regime** (from the spec): a regime whose M gets worse runs with the generator off.
  "Worse" is the round rule of the spec's §2: more salts worse than better on total M against the off arm, over salts
  1-10. The ref regime is judged on the warm loops it seeds first, its own M second; a ref loss is followed up (the share,
  spec step 4) before the regime is turned off.
- [ ] **Step 2: If every regime pays or ties,** the stage stays on everywhere: the module doc's "unmeasured ... run with
  ABLATE=gen" sentence goes, `PARKED.md`'s step-4 entry is deleted, and step 5 ("Hidden twins") has its trigger.
- [ ] **Step 3: If a regime loses,** turning it off is a change to `takes_extras` (a gate per regime). That is a design
  decision: stop and bring the options to the user before writing it.
- [ ] **Step 4: Docs and commit.** The tier-cycle section (table, runs, CPU and Defender state, the decision), ROADMAP's
  v0.2 line (step 4's result), the spec's step 4 line, plan `status: done`.
