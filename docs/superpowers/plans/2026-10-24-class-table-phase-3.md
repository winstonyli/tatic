---
status: done
---

# The class table, build step 8 (phase 3: the frontier) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Give the gate the frontier of spec §7: held-out bands 15 and 17 beside 11 and 13, and per arm each band's
free share and M under the loops' rules and under the table alone, then record a baseline.

**Architecture:** `stream_sequence` takes the growth count, so `regenerate_held` builds each band from the fewest
growths that reach it (`held_levels`), which leaves `held_11.txt` and `held_13.txt` byte for byte as they are.
`HELD_BANDS` stays the one list of bands; the gate reads the `held_*.txt` files, and a test keeps the files and the
list equal. Each arm writes one line per (rule set, band) to `held_bands.txt`, its three loops plus `none` (no mined
rules); the gate's summary pools them into one `bands` line per arm. The salt line keeps its format (the ablations
driver parses it). `tools/runs`' timing arms keep `held_11.txt` (`time.rs:88`), unaffected.

**Tech Stack:** Rust tests in `tests/church_bv` (cargo, `-j 4`); bash (`scripts/streams_ab.sh`,
`scripts/test_gate.sh`, LF endings); `~/.claude/runs/run.ps1` for the regeneration and the baseline.

**Spec:** `docs/superpowers/specs/2026-10-22-class-table-normal-form-design.md` §7 and build-order step 8, with
decisions D1-D3 (approved 2026-10-24, below). Evidence: `docs/tier-cycle.md`, "The frontier past the loops' sizes".

## Decisions (approved 2026-10-24)

- **D1:** `held_11.txt` and `held_13.txt` stay unchanged; `held_15.txt` and `held_17.txt` are added, generated at three
  and four growths.
- **D2:** the headline is each band's free share and mining's gain per band (loops' rules against the table alone). No
  50% threshold: the probe put the line past 17 for every arm.
- **D3:** per arm, held-out M and free share per band for the loops and for the table alone. The band list comes from
  the held files; `HELD_BANDS` is its one home.

## Rulings this plan makes (flagged for review)

- **R1, the growth count per band:** `held_levels(band) = max(STREAM_LEVELS, ceil((band - SIZE) / 2))`, the fewest
  growths (two nodes each over the table's size 9) whose laws reach the band: 2, 2, 3, 4. It reproduces D1 as a rule,
  not a per-band table. Cost if wrong: bands 15 at three growths and 17 at four differ from "all at four" by at most 1
  point (probe), so nothing measured moves.
- **R2, the held total covers all bands:** `held.txt` and the salt line's `held` become the loops' M over all four
  bands. The history of that number breaks (old rows are bands 11+13); the `bands` line gives each band's M, so old
  totals stay comparable band by band. The ablations driver's "held-out rise" test then also guards bands 15 and 17,
  which is the point of measuring them. Cost if wrong: one number's history; the alternative (keep 11+13 in the total)
  is a special case of two bands.
- **R3, the table alone runs inside each arm:** an empty rules file through the same `held`, per salt. Its result
  does not depend on the salt, so it repeats 10 times per gate (about 4 checks x 1.3 s per arm), but it is cached with
  the arm and needs no second code path. Cost if wrong: about 1 min of CPU per 10-salt gate.

## Global Constraints

- Never let python read stdin; no python is needed in this plan.
- No fixed sleeps; never `tail -F`. Cargo with `-j 4`.
- Before a heavy run, check `%LOCALAPPDATA%\cpu-leases\*.json` for a live exclusive lease and wait for it, or run on
  affinity `CFF`. Never stop or deprioritize another session's job.
- Runs whose output is cited go through `powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1"`; annotate
  each `docs/runs.md` row after "wrapper pid X, child pid Y" with " ; notes".
- `.sh` files stay LF. Commit on the branch, never on `main`; never push, merge or tag.
- Leave alone: `.claude/worktrees/*`, untracked `tests/ring_spike.rs`, `tests/ring_loop_spike.rs`,
  `.superpowers/sdd/2026-10-17-law-generator/`, untracked `Microsoft/`.
- The salt line `salt N: M A a B b; held A a B b; jobcpu A a B b; work ...` keeps its format (`scripts/ablations.sh:71`).

## Review Focus

1. **A stray or missing band file** (a `held_19.txt` left by hand, or `held_15.txt` deleted): the gate reads whatever
   files exist, so they must be `HELD_BANDS` exactly. Pinned by `held_files_are_the_bands` (Task 1).
2. **Band order past two digits** (a future `held_9.txt` or `held_21.txt`): the gate orders bands numerically, not by
   glob. Pinned by the `held()` fake-exe case with bands 9 and 11 (Task 2).
3. **The table-alone check on an empty rules file**: must print a `CHECKED` line like any other (the probe ran it
   this way). Pinned by the baseline's `none` lines (Task 3, Expected) and the fake-exe case (Task 2).
4. **An arm cached before this plan** (no `held_bands.txt`): its key hashes the held files, which change here, so it
   misses; a hand-made one must not break the summary. Pinned by the "an arm with no band lines" case (Task 2).
5. **A failed band check** (no `CHECKED` line): the arm fails as before (`held` returns `x`). Pinned by the existing
   "no ARM_CACHE: both arms run (and fail)" case, which runs `held` on a fake exe with no output.

---

### Task 1: Bands 15 and 17 (Rust and the held files)

**Files:**
- Modify: `tests/church_bv/search.rs` (`stream_sequence`, about lines 921-941; `stream_sequence_cost`, about 951-955)
- Modify: `tests/church_bv/driver.rs:578`, `:649` (callers)
- Modify: `tests/church_bv/classes.rs:570-638` (`HELD_BANDS`, `held_levels`, `regenerate_held`), tests after line 663
- Create: `tests/church_bv/held_15.txt`, `tests/church_bv/held_17.txt` (written by `regenerate_held`)

**Interfaces:**
- Produces: `pub fn stream_sequence(salt: usize, levels: usize) -> std::sync::Arc<Vec<(Term, Term)>>`;
  `pub const HELD_BANDS: [usize; 4] = [11, 13, 15, 17]`; `pub fn held_levels(band: usize) -> usize`;
  files `tests/church_bv/held_{11,13,15,17}.txt` (Task 2's gate reads `held_*.txt`).

- [ ] **Step 1: Write the failing tests** (in `classes.rs`, after `held_files_match_the_key`)

```rust
/// R1: each band comes from the fewest growths of the table's representatives (two nodes each) that reach it, and
/// never fewer than the loops' own (`STREAM_LEVELS`), so bands 11 and 13 are the loops' sequence.
#[test]
fn held_bands_take_the_fewest_growths() {
    assert_eq!(HELD_BANDS.map(held_levels), [2, 2, 3, 4]);
}

/// Review Focus 1: the held-out files present are `HELD_BANDS`' exactly; the gate reads whatever `held_*.txt` exist.
#[test]
fn held_files_are_the_bands() {
    let dir = held_path(HELD_BANDS[0]).parent().unwrap().to_path_buf();
    let mut found: Vec<usize> = std::fs::read_dir(&dir)
        .unwrap()
        .filter_map(|e| e.ok()?.file_name().to_str()?.strip_prefix("held_")?.strip_suffix(".txt")?.parse().ok())
        .collect();
    found.sort();
    assert_eq!(found, HELD_BANDS.to_vec(), "held_*.txt in {}: regenerate ({REGENERATE_HELD})", dir.display());
}
```

- [ ] **Step 2: Run them to see them fail**

Run: `cargo test -j 4 --test church_bv classes::held_ 2>&1 | tail -20`
Expected: compile error, `held_levels` not found (the RED for both: neither builds).

- [ ] **Step 3: Implement**

`search.rs`, replace `stream_sequence`'s doc, signature, memo, `stream_laws` call and print:

```rust
/// The law sequence for `salt` with the table's representatives grown `levels` times (spec §9; the loops use
/// `STREAM_LEVELS`): the 56 streams (`stream_sets`, `STREAM_BUDGET`) interleaved round-robin, a law kept at its first
/// appearance. Built once per process, salt and growth count.
pub fn stream_sequence(salt: usize, levels: usize) -> std::sync::Arc<Vec<(Term, Term)>> {
    static MEMO: crate::task::SharedMemo<(usize, usize), std::sync::Arc<Vec<(Term, Term)>>> = crate::task::SharedMemo::new();
    let build = || {
        let t0 = std::time::Instant::now();
        let streams: Vec<Vec<(Term, Term)>> = stream_sets().iter().map(|ops| stream_laws(ops, salt, STREAM_BUDGET, levels)).collect();
        // (interleave unchanged)
        println!("STREAMS salt {salt}, {levels} growths: {} laws from {} streams in {:.1}s", seq.len(), streams.len(), t0.elapsed().as_secs_f64());
        std::sync::Arc::new(seq)
    };
    MEMO.with((salt, levels), build, |s| s.clone())
}
```

`stream_sequence_cost`: `let seq = stream_sequence(salt, STREAM_LEVELS);`. `driver.rs:578`:
`stream_sequence(num(get, "RULEMINER_SHUFFLE", 0), STREAM_LEVELS)`; `driver.rs:649`:
`residue(&stream_sequence(salt, STREAM_LEVELS), 0, 0, STREAM_EXTRAS)` (import `STREAM_LEVELS` where `stream_sequence`
is imported). Nothing parses the `STREAMS salt` line (grep of scripts, tools and tests, 2026-10-24).

`classes.rs`:

```rust
/// The held-out set's size bands (a law's band: its larger side's size), its laws per band, and its salt, which no
/// sweep salt or draw shift reaches (spec decision 10, plan R6). Bands 15 and 17 lie past the loops' sizes (class-table
/// phase 3 plan, D1); the gate reads the files, `held_files_are_the_bands` keeps them equal to this list.
pub const HELD_BANDS: [usize; 4] = [11, 13, 15, 17];

/// The growths of the table's representatives (size `SIZE`, two nodes per growth) a band's laws come from: the fewest
/// that reach it, and at least the loops' `STREAM_LEVELS` (phase 3 plan, R1).
pub fn held_levels(band: usize) -> usize {
    crate::search::STREAM_LEVELS.max(band.saturating_sub(SIZE).div_ceil(2))
}
```

`regenerate_held`: doc's first line becomes "Regenerates the `held_<band>.txt` files (spec decision 10): each band
from the stream sequence at `HELD_SALT` grown `held_levels(band)` times, laws salt 1's loops serve dropped ..." and the
body:

```rust
    let s1 = crate::search::stream_sequence(1, crate::search::STREAM_LEVELS);
    let served: hashbrown::HashSet<(Term, Term)> = (1..=3).flat_map(|p| crate::search::residue(&s1, p, 0, 300)).collect();
    for band in HELD_BANDS {
        let seq = crate::search::stream_sequence(HELD_SALT, held_levels(band));
        let all: Vec<(Term, Term)> = seq.iter().filter(|(a, b)| a.size().max(b.size()) == band).cloned().collect();
        // (overlap, laws, assert, write, println unchanged; println gains `from {} growths`, held_levels(band))
    }
```

- [ ] **Step 4: Run the fast tests**

Run: `cargo test -j 4 --test church_bv classes::held_ 2>&1 | tail -20`
Expected: `held_bands_take_the_fewest_growths` passes; `held_files_are_the_bands` and `held_files_match_the_key` fail
(no `held_15.txt`, `held_17.txt`).

- [ ] **Step 5: Regenerate, through the wrapper, with a memory cap**

About 9-10 min (four sequences: about 110 s each at two growths for `HELD_SALT` and salt 1, 137 s at three, 212 s at
four; peak commit about 3.3 GB at four, under 6 GB with all four memoized). Build once (`cargo test --profile sweep -j 4 --test church_bv --no-run`, the path from cargo's "Executable" line),
copy the exe to `$LOCALAPPDATA/claude-runs/tatic/regen-exe/R.exe` (outside `target`), then launch detached:

```bash
powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind probe -Name held-15-17 -Command "start /b /wait /belownormal /affinity CFF <R.exe, Windows path> classes::regenerate_held --exact --ignored --nocapture"
```

with a watcher loop beside it (exits once the run folder's `run.json` has a non-null `"end"`, deadline 30 min) that samples
`scripts/tree_mem.ps1 -Match classes::regenerate_held` every 2 s and passes `-Kill` past 12 GB, printing the peak.
Expected: four `HELD <band>: 1000 of N laws in the band` lines; bands 15 and 17 show 0 served (salt 1's loops never
reach them).

- [ ] **Step 6: Check D1 and run the tests**

Run: `git diff --stat tests/church_bv/held_11.txt tests/church_bv/held_13.txt` then
`cargo test -j 4 --test church_bv classes:: 2>&1 | tail -20`
Expected: no diff for 11 and 13 (byte-identical, D1); all `classes::` tests pass. Cross-check against the probe, which
drew the same bands from the same salt and growths with nothing to drop:
`p="$LOCALAPPDATA/claude-runs/tatic/2026-10-24-frontier-probe"; cmp "$p/levels_3/held_15.txt" tests/church_bv/held_15.txt && cmp "$p/levels_4/held_17.txt" tests/church_bv/held_17.txt && echo same`
prints `same` (both files LF from `std::fs::write`). Then the whole non-ignored suite,
`cargo test -j 4 --test church_bv 2>&1 | tail -5`: passes (count the tests that iterate `HELD_BANDS`; only
`held_files_match_the_key` is not ignored, and it parses four files).

- [ ] **Step 7: Commit** (annotate the runs.md row: peak, wall, laws per band)

```bash
git add tests/church_bv/search.rs tests/church_bv/driver.rs tests/church_bv/classes.rs tests/church_bv/held_15.txt tests/church_bv/held_17.txt docs/runs.md
git diff --cached --stat
git commit -q -F "$TEMP/msg.txt"   # "held-out bands 15 and 17: each band from the fewest growths that reach it; 11 and 13 unchanged"
```

### Task 2: The gate's bands (streams_ab.sh, test_gate.sh)

**Files:**
- Modify: `scripts/streams_ab.sh` (header comment, `held()` lines 18-30, `arm()` cache key line 110 and held loop
  lines 127-128, the summary loop lines 146-155)
- Modify: `scripts/test_gate.sh` (lines 16, 19, `mkarm`, new cases after the cache-hit cases)

**Interfaces:**
- Consumes: `tests/church_bv/held_*.txt` (Task 1).
- Produces: per arm `held_bands.txt`, lines `<rules> <band> <laws> <free> <M>` (`rules` = 1, 2, 3 or `none`);
  `held.txt` = the loops' M over all bands (R2); a summary line per arm,
  `bands <arm>: <band> free <f> table <f> M <m> table <m>; ...` (free share = free / laws pooled over salts, M per
  1000 laws), printed after `total <arm>`; the salt line unchanged.

- [ ] **Step 1: Write the failing cases** (`test_gate.sh`)

Line 16 becomes four fake bands; `key()` hashes them as the gate will (sorted numerically); `mkarm` gains a band file:

```bash
for b in 11 13 15 17; do echo $b > "$T/root/tests/church_bv/held_$b.txt"; done
# the held-out files in band order, as streams_ab.sh's `bands` lists them
hfiles() { local b; for b in $(ls "$T/root/tests/church_bv" | sed -nE 's/^held_([0-9]+)\.txt$/\1/p' | sort -n); do echo "$T/root/tests/church_bv/held_$b.txt"; done; }
key() { { cat "$1" "$1.env" "$T/root/scripts/streams_ab.sh" "$T/root/tools/runs/target/release/runs.exe"; hfiles | while read -r f; do cat "$f"; done; } 2>/dev/null | sha256sum | cut -c1-16; }
```

In `mkarm`, after `held.txt`: `printf '%s\n' "1 11 1000 900 100" "none 11 1000 800 200" > "$1/held_bands.txt"`.

New cases, after "cache hit: the last line":

```bash
ok "cache hit: the bands line" "$(echo "$out" | grep '^bands A:')" "bands A: 11 free .900 table .800 M 100.0 table 200.0"
# a fake exe that prints a CHECKED line from its CHECK_LAWFILE's band and its rules file (empty: the table alone)
printf '#!/bin/bash\nb=$(head -1 "$(cygpath -u "$CHECK_LAWFILE")"); [ -s "$(cygpath -u "$CHECK_RULES")" ] && f=$((b * 10)) || f=$b\necho "CHECKED 990 laws kernel-checked ($f with no whole-term machine proof), 10 not proved, 0 used up the rule budget"\n' > "$T/F.exe"
mv "$T/root/tests/church_bv/held_13.txt" "$T/root/tests/church_bv/held_9.txt"; echo 9 > "$T/root/tests/church_bv/held_9.txt"
# the loops' rules files, which the failed sweep (fake runs.exe) never writes and the arm does not delete
for l in 1 2 3; do mkdir -p "$T/fake/s1_B/cold_streams_streams_${l}_none"; echo "rule $l" > "$T/fake/s1_B/cold_streams_streams_${l}_none/rules.txt"; done
gate fake "$(cygpath -w "$T/F.exe")" 1 > /dev/null
ok "held: a line per rule set and band, bands in numeric order" "$(cat "$T/fake/s1_B/held_bands.txt" | paste -sd'|')" \
  "1 9 1000 90 910|1 11 1000 110 890|1 15 1000 150 850|1 17 1000 170 830|2 9 1000 90 910|2 11 1000 110 890|2 15 1000 150 850|2 17 1000 170 830|3 9 1000 90 910|3 11 1000 110 890|3 15 1000 150 850|3 17 1000 170 830|none 9 1000 9 991|none 11 1000 11 989|none 15 1000 15 985|none 17 1000 17 983"
ok "held: the total is the loops' M" "$(cat "$T/fake/s1_B/held.txt")" $((3 * (910 + 890 + 850 + 830)))
mv "$T/root/tests/church_bv/held_9.txt" "$T/root/tests/church_bv/held_13.txt"; echo 13 > "$T/root/tests/church_bv/held_13.txt"
# Review Focus 4: an arm with no band lines (cached before the bands) leaves the summary readable
rm "$T/cache/$(key "$T/A.exe")/s1/held_bands.txt"
ok "an arm with no band lines" "$(ARM_CACHE=$(cygpath -w "$T/cache") gate nobands "$B" 1 | grep '^bands A:')" "bands A: no band lines"
mkarm "$T/cache/$(key "$T/A.exe")/s1" 100 500 10 "arm A"
```

(The arm runs `held` even when its sweep failed, `streams_ab.sh:127`, so the fake gate reaches the checks; a shell
script named `.exe` runs from a Windows path under msys bash, checked 2026-10-24.)

- [ ] **Step 2: Run to see them fail**

Run: `bash scripts/test_gate.sh 2>&1 | grep -E '^(FAIL|PASS)' | head -40`
Expected: FAIL for the cache-hit cases and the cases that expect a reuse ("cache hit: ...", "a variable its .exe.env
sets counts"): the test's `key()` now hashes four held files and the gate still two, so no arm is found; FAIL for both
"held:" cases and "an arm with no band lines". The miss cases ("a changed variable misses", ...) may pass or fail
(they grep for a line a miss no longer prints); they must all pass after Step 3.

- [ ] **Step 3: Implement** (`streams_ab.sh`)

```bash
# the held-out files in band order (tests/church_bv/held_<band>.txt, HELD_BANDS in classes.rs)
bands() { local b; for b in $(ls "$root/tests/church_bv" | sed -nE 's/^held_([0-9]+)\.txt$/\1/p' | sort -n); do echo "$root/tests/church_bv/held_$b.txt"; done; }
held() { # <exe> <rules file> <arm dir> <label>: held-out M over every band; per band `<label> <band> <laws> <free> <M>` to <arm dir>/held_bands.txt, the check's ABLATED and ENV lines to <arm dir>/held_lines.txt
  local m=0 hf band out line p f n e
  while read -r hf; do
    band=${hf##*held_}; band=${band%.txt}
    mapfile -t e < <(held_env "$(cygpath -w "$2")" "$(cygpath -w "$hf")")
    out=$(env "${e[@]}" "$1" search::rule_set_kernel_check --exact --ignored --nocapture < /dev/null 2>&1)
    grep -E '^(ABLATED|ENV) ' <<< "$out" >> "$3/held_lines.txt"; line=$(grep '^CHECKED ' <<< "$out")
    [ -n "$line" ] || { echo "held: no CHECKED line for $2 band $band" >&2; echo x; return; }
    p=$(echo "$line" | sed -E 's/^CHECKED ([0-9]+) .*/\1/'); f=$(echo "$line" | sed -E 's/.*\(([0-9]+) with.*/\1/'); n=$(echo "$line" | sed -E 's/.*\), ([0-9]+) not proved.*/\1/')
    echo "$4 $band $((p + n)) $f $((p - f + n))" >> "$3/held_bands.txt"; m=$((m + p - f + n))
  done < <(bands)
  echo $m
}
```

(The `[ -n "$line" ]` check moves before the `sed`s, which is where it belonged.) In `arm()`: the cache key replaces
`"$root"/tests/church_bv/held_{11,13}.txt` with `$(bands)` read into an array (`mapfile -t hf < <(bands)` then
`"${hf[@]}"`; the paths have a space); `rm -f` gains `"$o/held_bands.txt"`; the held loop becomes

```bash
  h=0
  for l in 1 2 3; do v=$(held "$exe" "$o/cold_streams_streams_${l}_none/rules.txt" "$o" $l); [ "$v" = x ] && f=1 || h=$((h + v)); done
  : > "$o/no_rules.txt"; [ "$(held "$exe" "$o/no_rules.txt" "$o" none)" = x ] && f=1   # the table alone (R3)
  echo $h > "$o/held.txt"
```

After the `total $arm` echo in the summary loop:

```bash
  echo "bands $arm: $(cat "$RUN_DIR"/s*_$arm/held_bands.txt 2>/dev/null | awk '
    function r(a, b, fmt) { return b ? sprintf(fmt, a / b) : "-" }
    {k = ($1 == "none") ? "t" : "l"; if (!($2 in seen)) {seen[$2]; o[++n] = $2}; laws[k, $2] += $3; free[k, $2] += $4; m[k, $2] += $5}
    END {if (!n) {printf "no band lines"; exit}
      for (i = 1; i <= n; i++) {b = o[i]; printf "%s%s free %s table %s M %s table %s", (i > 1 ? "; " : ""), b,
        r(free["l", b], laws["l", b], "%.3f"), r(free["t", b], laws["t", b], "%.3f"), r(1000 * m["l", b], laws["l", b], "%.1f"), r(1000 * m["t", b], laws["t", b], "%.1f")}}' | sed 's/ 0\./ ./g')"
```

Band order in the line is first appearance, which is the files' numeric order (each arm writes bands in that order).
A side with no lines for a band (its checks failed, so the arm failed) prints `-`, not a division by zero. Header
comment: "Then per loop the held-out M under the loop's final rules (`tests/church_bv/held_<band>.txt`, every band,
`HELD_BANDS`; CHECK_FAST ...)", and add "and under no mined rules (the table alone); per arm the pooled free share and
M per 1000 laws per band (`bands`)".

- [ ] **Step 4: Run the checks**

Run: `bash scripts/test_gate.sh 2>&1 | tail -3` and `file scripts/streams_ab.sh scripts/test_gate.sh`
Expected: no FAIL lines, exit 0; both files LF (no "CRLF").

- [ ] **Step 5: Commit**

```bash
git add scripts/streams_ab.sh scripts/test_gate.sh
git diff --cached --stat
git commit -q -F "$TEMP/msg.txt"   # "streams_ab: held-out M and free share per band, for the loops and the table alone"
```

### Task 3: The baseline and the docs

**Files:**
- Modify: `docs/tier-cycle.md` (new section after "The frontier past the loops' sizes"), `docs/runs.md` (row),
  `ROADMAP.md:40-48` (v0.5), the spec (§7, build order, `status: done`), `docs/learned-vs-fixed.md` (if a row names
  the held-out set), this plan (`status: done`)

- [ ] **Step 1: The baseline gate, an A/A of `main`'s branch head**

Build the release-mode test exe once, copy it to `$LOCALAPPDATA/claude-runs/tatic/phase3-exe/A.exe`, no `ARM_CACHE`
(an A/A must run both arms), `JOBS=2`, untimed, affinity `CFF` (no lease: the verdict is counts, not times):

```bash
JOBS=2 powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind gate -Name phase3-baseline -Command "start /b /wait /belownormal /affinity CFF bash scripts/streams_ab.sh <A.exe> <A.exe> 1 2 3 4 5 6 7 8 9 10"
```

About 30 min (salt 6 alone: 2.5 min per arm at `JOBS=1`; 20 arms, 2 at a time, plus 16 band checks per arm at about
1.3 s). Expected: `0 of 20 arms failed`, rules same in 30 of 30 loops, each arm's `held_bands.txt` has 16 lines,
`none` lines identical across salts (the table alone does not depend on the salt), and the A and B `bands` lines
equal. Against the probe (same files for 15 and 17, Task 1 Step 6): the `none` lines for 15 and 17 equal its
`levels 3 band 15 rules none` and `levels 4 band 17 rules none` M (both in the probe's `out.log`); salt 6's loop lines for 15 and 17 equal its `rules 1-3` lines if salt 6's `rules.txt` files equal
`cache-check-1`'s (`cmp` first; the probe used those rules).

- [ ] **Step 2: Record it**

`docs/tier-cycle.md`, a section "*The frontier on the gate (2026-10-2x; run `<id>`)*": the `bands` line as a table
(band, loops' free share, table's, gain in points, M per 1000 laws each), the held total's new scope (R2: four bands,
loops only; the old total is bands 11+13), and a sentence that `none` repeats across salts. Annotate the runs.md row.

- [ ] **Step 3: The docs that name the old state**

- `ROADMAP.md` v0.5: replace "and the largest size still above a threshold" and the last sentence ("The 50% line lies
  beyond size 13, so the metric needs laws grown three or more times (`PARKED.md` ...)") with the measured form: the
  frontier is the free share per band 11-17 against the table alone, printed by the gate (link to the tier-cycle
  section); no threshold (D2).
- `PARKED.md` stays: "Proposer targets beyond ranking" (a) is the proposer model's target past 5 nodes, not the held-out
  set; the ROADMAP line linked it only as the source of "grown three or more times", and the rewrite drops that link.
- The spec, §9 (about line 253, "writes `tests/church_bv/held_11.txt` and `held_13.txt`"): add "(bands 15 and 17
  from phase 3, §7)".
- The spec: §7 gains "Built (plan `docs/superpowers/plans/2026-10-24-class-table-phase-3.md`): bands 15 and 17, the
  gate's `bands` line"; build order "Steps 1-8 are done"; front matter `status: done` (leftovers to `PARKED.md` first).
- `docs/learned-vs-fixed.md`: grep for `held`; update only a row that states the held-out set's bands.
- `docs/tier-cycle.md`, the gate's description (grep `held_11.txt` and `held_13.txt`, about line 5582): "every band of
  `HELD_BANDS`".
- This plan: `status: done`.

- [ ] **Step 4: Commit**

```bash
git add docs/tier-cycle.md docs/runs.md ROADMAP.md docs/learned-vs-fixed.md docs/superpowers/specs/2026-10-22-class-table-normal-form-design.md docs/superpowers/plans/2026-10-24-class-table-phase-3.md
git diff --cached --stat
git commit -q -F "$TEMP/msg.txt"   # "tier-cycle: the frontier on the gate (baseline A/A, salts 1-10); spec step 8 done"
```
