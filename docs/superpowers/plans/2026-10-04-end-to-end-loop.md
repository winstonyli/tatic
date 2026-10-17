---
status: done
---

# End-to-end lemma loop Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Measure, on one family (deep add3), how many whole-term machine proofs a stream of laws needs when rules are mined as the stream arrives, against fixed rules and against rules mined with hindsight.

**Architecture:** No new miner. The existing `rule_miner` (rounds, `RULEMINER_BASE` = rules in force) mines each round's batch; the existing `rule_set_kernel_check` serves a batch under the rules so far and counts machine proofs. One new env var, `RULEMINER_SKIP`, makes both read a window of the law sequence. A bash driver runs rounds: serve batch r with the rules so far (count M_r), then mine batch r to extend the rules. A second proposer mode feeds `rulelm` samples to the miner's `file` proposer.

**Tech Stack:** Rust integration tests (`tests/church_bv/search.rs`), bash on Git Bash, PowerShell for load checks, `tools/rulelm` (separate crate, existing checkpoint `%TEMP%/ck_B.ckpt`).

**Spec:** `docs/superpowers/specs/2026-10-04-end-to-end-loop-design.md` (decisions section: stream C, no subsumption in the first build).

## Global Constraints

- Long runs: BelowNormal (`cmd //c start "" //b //belownormal ...`), at most 12 threads (use `RULEMINER_THREADS=6`), copy the test exe to `%TEMP%` before running. Check `Get-Process bv_*`, CPU (`\Processor(_Total)\% Processor Time`) and `(Get-MpComputerStatus).RealTimeProtectionEnabled` first; record all three with every result. Never stop other sessions' jobs; never change Defender.
- `RULESET=none` panics: leave `RULESET` unset.
- Commits end with `Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>`. Do not push.
- Soundness must not depend on the proposer: every rule is proved by `prove_rule` and every served law is `ck`-checked (already true; do not bypass).
- Decide on machine-proof counts M; timings are reported with load, not used to decide.
- Files in `tests/church_bv/*.rs` may have CRLF line endings: edit with the Edit tool or a Python script that preserves them.

## File Structure

- Modify: `tests/church_bv/search.rs` (`family_laws`: `RULEMINER_SKIP` for the `add3` and `mix3` branches; one new unit test).
- Create: `scripts/loop_stream.sh` (the round driver, modes `none`, `ref`, `loop`).
- Create: `scripts/loop_candidates.sh` (per-round model candidates).
- Create: `scripts/experiments/loop_run.sh` (the recorded experiment) and `scripts/experiments/logs/loop_*.tsv`.
- Modify: `docs/superpowers/specs/2026-10-04-end-to-end-loop-design.md` (results), `docs/superpowers/specs/2026-10-04-research-state.md` (one paragraph), `scripts/experiments/README.md` (rows).

---

### Task 1: Law windows (`RULEMINER_SKIP`)

**Files:**
- Modify: `tests/church_bv/search.rs` (`family_laws`, the `add3` and `mix3` branches; add a test after `family_laws`)

**Interfaces:**
- Consumes: `family_laws(family: &str, env: &dyn Fn(&str, usize) -> usize, n: usize, nv: usize, max: u32) -> Vec<(String, Term, Term)>` (existing).
- Produces: `family_laws` honours `env("RULEMINER_SKIP", 0)` for families `add3` and `mix3`: the laws after the all-variables filter and `step_by(RULEMINER_STRIDE)`, with the first SKIP dropped, then `take(RULEMINER_LAWS)`. Windows `(skip=0,laws=a)` followed by `(skip=a,laws=b)` equal `(skip=0,laws=a+b)`.

- [ ] **Step 1: Write the failing test** (insert after the closing brace of `family_laws`)

```rust
/// `RULEMINER_SKIP` windows: consecutive windows tile the law sequence, and a window past the end is empty.
#[test]
pub fn family_law_windows_tile_the_sequence() {
    let laws = |skip: usize, take: usize| {
        let env = move |k: &str, d: usize| match k {
            "RULEMINER_SKIP" => skip,
            "RULEMINER_LAWS" => take,
            "RULEMINER_STRIDE" => 5,
            _ => d,
        };
        family_laws("add3", &env, 4, 3, 7).into_iter().map(|(name, _, _)| name).collect::<Vec<_>>()
    };
    let whole = laws(0, 12);
    assert_eq!(whole.len(), 12);
    let mut tiled = laws(0, 5);
    tiled.extend(laws(5, 7));
    assert_eq!(tiled, whole);
    assert!(laws(usize::MAX / 2, 5).is_empty());
}
```

- [ ] **Step 2: Run it to verify it fails**

Run: `cargo test --release --test church_bv family_law_windows_tile_the_sequence -j 6`
Expected: FAIL (`tiled != whole`, because SKIP is ignored and both windows return the first laws).

- [ ] **Step 3: Implement.** In the `add3` and `mix3` branches of `family_laws`, change

```rust
            .step_by(env("RULEMINER_STRIDE", 1))
            .take(env("RULEMINER_LAWS", 250))
```

to

```rust
            .step_by(env("RULEMINER_STRIDE", 1))
            .skip(env("RULEMINER_SKIP", 0))
            .take(env("RULEMINER_LAWS", 250))
```

in those two branches only (the `shr` branch also has this pair; leave it unchanged).

- [ ] **Step 4: Run to verify it passes**, and that the existing suite for this file still passes

Run: `cargo test --release --test church_bv family_law_windows_tile_the_sequence -j 6` then `cargo test --release --test church_bv -j 6` (ignored tests stay ignored).
Expected: PASS, and the full run reports 0 failed.

- [ ] **Step 5: Commit**

```bash
git add tests/church_bv/search.rs
git commit -m "family_laws: RULEMINER_SKIP windows for add3 and mix3" -m "Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>"
```

---

### Task 2: Round driver with the `mined` proposer

**Files:**
- Create: `scripts/loop_stream.sh`

**Interfaces:**
- Consumes: Task 1's `RULEMINER_SKIP`; `rule_miner` (prints `RULEMINER chosen (+a fixed, -b size): l -> r`); `rule_set_kernel_check` (prints `CHECKED p laws kernel-checked (f with no whole-term machine proof), u not proved`; env `CHECK_FAMILY`, `CHECK_RULES`).
- Produces: `scripts/loop_stream.sh MODE OUTDIR` where MODE is `none` (no rules at all), `ref` (rules mined once on the whole stream, then every batch served under them), or `loop` (rules mined batch by batch). Env: `EXE` (test exe path, required), `B` (batch size, default 150), `K` (batches, default 4), `OFFSET` (law offset of the stream, default 0), `DEEP3` (default 1), `ROUNDS` (miner rounds per mining run, default 8), `THREADS` (default 6), `PROPOSER` (`mined` default, or `file`), `PROPOSER_FILE_CMD` (a command taking the round name and printing candidate rules; see Task 3). Writes `OUTDIR/rules.txt` (final rules) and `OUTDIR/m.tsv` with one line per batch: `round<TAB>M<TAB>laws<TAB>rules_in_force<TAB>seconds`, where M = `p - f + u` from `CHECKED`. Prints a final line `mode=... total_M=<sum> rules=<n>`.

- [ ] **Step 1: Write the script**

```bash
#!/usr/bin/env bash
# Round driver for the end-to-end loop (docs/superpowers/specs/2026-10-04-end-to-end-loop-design.md).
#   EXE=<church_bv test exe> [B=150 K=4 OFFSET=0 PROPOSER=mined] scripts/loop_stream.sh none|ref|loop OUTDIR
# Batch r is the laws OFFSET+r*B .. OFFSET+(r+1)*B of the add3 sequence (stride 7). It is served under the rules in force
# *before* it is mined, so M is what the stream costs when rules arrive as it does.
set -euo pipefail
mode=$1; out=$2; mkdir -p "$out"
B=${B:-150}; K=${K:-4}; OFFSET=${OFFSET:-0}; PROPOSER=${PROPOSER:-mined}
: "${EXE:?set EXE}"
rules="$out/rules.txt"; : > "$rules"; : > "$out/m.tsv"
win="RULEMINER_FAMILY=add3 CHECK_FAMILY=add3 RULEMINER_DEEP3=${DEEP3:-1} RULEMINER_STRIDE=7"
mc="RULEMINER_PERM=1 RULEMINER_STEPS=40 RULEMINER_THREADS=${THREADS:-6} RULEMINER_ROUNDS=${ROUNDS:-8}"

mine() { # name skip laws -> appends the chosen rules to $rules
  local file_env=""
  if [ "$PROPOSER" = file ]; then
    $PROPOSER_FILE_CMD "$1" > "$out/cand_$1.txt"
    file_env="RULEMINER_PROPOSER=file RULEMINER_PROPOSER_FILE=$out/cand_$1.txt"
  fi
  env $win $mc $file_env RULEMINER_SKIP=$2 RULEMINER_LAWS=$3 RULEMINER_BASE="$rules" "$EXE" search::rule_miner --ignored --nocapture 2>&1 \
    | tee "$out/mine_$1.log" | grep -E "RULEMINER chosen" | grep -- " -> " | sed 's/.*size): //' >> "$rules" || true
}
serve() { # skip -> prints "M laws"
  local line
  line=$(env $win RULEMINER_SKIP=$1 RULEMINER_LAWS=$B CHECK_RULES="$rules" "$EXE" search::rule_set_kernel_check --ignored --nocapture 2>&1 | grep -E "^CHECKED")
  echo "$line" | sed -E 's/CHECKED ([0-9]+) laws kernel-checked \(([0-9]+) with no whole-term machine proof\), ([0-9]+) not proved/\1 \2 \3/' | awk '{print $1-$2+$3, $1+$3}'
}

if [ "$mode" = ref ]; then mine ref "$OFFSET" $((B * K)); fi
total=0
for ((r = 0; r < K; r++)); do
  skip=$((OFFSET + r * B)); t0=$(date +%s)
  read -r m laws < <(serve "$skip")
  printf '%s\t%s\t%s\t%s\t%s\n' "$r" "$m" "$laws" "$(wc -l < "$rules")" "$(( $(date +%s) - t0 ))" >> "$out/m.tsv"
  total=$((total + m))
  if [ "$mode" = loop ]; then mine "$r" "$skip" "$B"; fi
done
echo "mode=$mode proposer=$PROPOSER B=$B K=$K offset=$OFFSET total_M=$total rules=$(wc -l < "$rules")"
```

In `mine`, the later `RULEMINER_LAWS=$3` overrides nothing in `$win` (which sets no LAWS); `ref` mode passes `B*K` as the window length.

- [ ] **Step 2: Build the exe and copy it**

Run: `cargo test --release --test church_bv --no-run -j 6`, then copy the printed `church_bv-*.exe` to `%TEMP%/bv_loop.exe`.

- [ ] **Step 3: Smoke check (the test).** Tiny stream, non-deep pool so it is fast, at BelowNormal:

```bash
E="$(cygpath -m $TEMP)"; EXE="$E/bv_loop.exe" B=10 K=2 DEEP3=0 ROUNDS=2 cmd //c start //wait //b //belownormal bash scripts/loop_stream.sh none "$E/loop_smoke_none"
cat "$TEMP/loop_smoke_none/m.tsv"
```
Expected: two lines `0 <M> 10 0 <s>` and `1 <M> 10 0 <s>` (rules_in_force stays 0, laws is 10 per batch) and a final `mode=none ... total_M=<sum>`. Then run `loop` with the same settings: round 0's M equals the `none` run's round 0 (same rules, none), and `rules_in_force` is non-decreasing. An empty window (`OFFSET=1000000000 B=10 K=1`) must print `total_M=0`.

If `rule_set_kernel_check` prints no `CHECKED` line, the script exits non-zero (`set -e` with the failed grep): fix the pattern against the actual output rather than loosening it.

- [ ] **Step 4: Commit**

```bash
git add scripts/loop_stream.sh
git commit -m "scripts/loop_stream.sh: round driver (none, ref, loop) for the end-to-end loop" -m "Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>"
```

---

### Task 3: Model proposer per round

**Files:**
- Create: `scripts/loop_candidates.sh`

**Interfaces:**
- Consumes: `tools/rulelm/target/release/rulelm.exe`, checkpoint `%TEMP%/ck_B.ckpt` (a **char-mode** model trained with `RULELM_X=1 RULELM_D=64 RULELM_LAYERS=2`, per `exp.sh`; train and sample env must agree; it samples infix directly, so no `from_prefix`; corrected after Task 3 found the original words-mode claim wrong), and `scripts/filter_candidates.py` (reads a file, prints to stdout; see `scripts/experiments/exp.sh`).
- Produces: `scripts/loop_candidates.sh ROUND` prints candidate rules in infix `lhs -> rhs` form, one per line (sorted, unique), sampled with seed `100 + ROUND` (ROUND is numeric; the driver's `ref` name is never used with `PROPOSER=file`); usable as `PROPOSER_FILE_CMD="bash scripts/loop_candidates.sh"`.

- [ ] **Step 1: Reproduce the existing pipeline by hand once.** Run the sampling lines of `exp.sh` for checkpoint `ck_B` (words mode, 4000 samples at temperature 0.8) and confirm the output after `from_prefix` and `filter_candidates.py` is a non-empty file of `lhs -> rhs` lines. If `ck_B.ckpt` is missing from `%TEMP%`, stop and ask: retraining is out of scope for this plan.

- [ ] **Step 2: Write the script**

```bash
#!/usr/bin/env bash
# Candidate rules for round $1: samples from the rulelm checkpoint, converted to infix and filtered (scripts/experiments/exp.sh).
set -euo pipefail
cd "$(dirname "$0")/.."
T="${TEMP:-/tmp}"; r=${1:?round}
raw=$(mktemp)
RULELM_WORDS=1 tools/rulelm/target/release/rulelm.exe sample "$T/ck_B.ckpt" 4000 0.8 $((100 + r)) > "$raw" 2>/dev/null
python scripts/rule_notation.py from_prefix "$raw" > "$raw.infix"
python scripts/filter_candidates.py "$raw.infix" 2>/dev/null | sort -u
rm -f "$raw" "$raw.infix"
```

- [ ] **Step 3: Verify.** `bash scripts/loop_candidates.sh 0 | wc -l` is greater than 0 and every line contains ` -> `; the outputs for rounds 0 and 1 differ (different seeds). Run the smoke loop of Task 2 with `PROPOSER=file PROPOSER_FILE_CMD="bash scripts/loop_candidates.sh"` and confirm `mine_0.log` contains a `proposer file:` line.

- [ ] **Step 4: Commit**

```bash
git add scripts/loop_candidates.sh
git commit -m "scripts/loop_candidates.sh: per-round model candidates for the loop driver" -m "Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>"
```

---

### Task 4: Run the experiment and record it

**Files:**
- Create: `scripts/experiments/loop_run.sh`, `scripts/experiments/logs/loop_*.tsv`, `scripts/experiments/logs/loop_summary.txt`
- Modify: `docs/superpowers/specs/2026-10-04-end-to-end-loop-design.md`, `docs/superpowers/specs/2026-10-04-research-state.md`, `scripts/experiments/README.md`

**Interfaces:**
- Consumes: Tasks 1-3.
- Produces: for stream offsets 0, 1000 and 2000 (three streams; B=150, K=4, deep add3, stride 7): total M under `none`, `ref`, `loop` with `mined`, and `loop` with `file` (model). A table in a new "Results" section of the spec.

- [ ] **Step 1: Pre-flight (record the output).** `Get-Process bv_*`, CPU, Defender RTP, free memory. If CPU is above about 60% from other sessions, run anyway and say so; counts decide, not time.

- [ ] **Step 2: Write `scripts/experiments/loop_run.sh`** looping over `OFFSET in 0 1000 2000` and the four configurations, each in its own `%TEMP%/loop_<offset>_<config>` dir, copying `m.tsv` to `scripts/experiments/logs/loop_<offset>_<config>.tsv` and appending each run's final `total_M=` line to `scripts/experiments/logs/loop_summary.txt`. Launch with `cmd //c start "" //b //belownormal bash scripts/experiments/loop_run.sh`; wait on a `.done` file with `timeout N bash -c 'until [ -f ... ]; do sleep 15; done'` (not `tail -F`; it leaves orphans). Record command, PID, start time, expected duration and log path in the README row before waiting. Run the `file` configuration last so a missing checkpoint does not waste the other runs.

- [ ] **Step 3: Evaluate against the spec's metric.** For each offset: M(none), M(ref), M(loop-mined), M(loop-file). The spec's success rule: M(loop-mined) within 10% of M(ref) and below M(none) by at least the miner's batch gain on this family, and M(loop-file) below M(loop-mined) on at least one offset. Read the spec and state how you read "at least the miner's batch gain" (suggested: M(none) - M(loop-mined) at least 0.5 * (M(none) - M(ref))). Report all four numbers per offset whatever the outcome.

- [ ] **Step 4: Write up.** Add a "Results" section to the loop spec (table plus the verdict, with load and Defender state), one paragraph to `2026-10-04-research-state.md`, and the README rows. A negative result is written up the same way.

- [ ] **Step 5: Commit**

```bash
git add scripts/experiments docs/superpowers
git commit -m "End-to-end loop: first measurements on deep add3" -m "Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>"
```

---

## Self-review (done)

- **Spec coverage:** stream C's first half (the family's own laws; the held-out corpus-generator stream is not built, and Task 4's write-up must say so), M over a fixed stream and the three modes (Tasks 2, 4), model proposer (Task 3), no subsumption (none built), the empty-stream check (Task 2 Step 3), three seeds (as three stream offsets). Not covered, deliberately: the two-process concurrent mode and retraining on accepted rules (spec step 4 and feedback).
- **Placeholders:** none; Task 4 Step 3 asks the implementer to read the spec for one threshold and gives a suggested reading.
- **Type consistency:** `RULEMINER_SKIP`, `RULEMINER_LAWS`, `RULEMINER_BASE`, `CHECK_RULES`, `CHECK_FAMILY`, `PROPOSER_FILE_CMD`, `EXE`, `B`, `K`, `OFFSET`, `DEEP3`, `ROUNDS`, `THREADS` are used the same way in every task.
