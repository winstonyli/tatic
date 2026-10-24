---
status: draft
---

# Work counts Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: use superpowers:executing-plans (inline). Steps use checkbox (`- [ ]`)
> syntax for tracking.

**Goal:** Give the streams gate a cost signal that does not depend on machine load: four work counters per arm, printed
by every sweep process, summed by `scripts/streams_ab.sh`, gated for determinism, proxy quality and overhead, and then
used by the ablations driver in place of job CPU.

**Architecture:** A new module `tests/church_bv/work.rs` holds one counter slot per thread (four `AtomicU64`s that only
their own thread writes) and a process-wide list of the slots. Four sites call `work::count`. A worker task's thread
and a sweep's main thread print `work::line(work::take())` when their work is done. `streams_ab.sh` sums the `WORK`
lines of each arm per salt. The driver (outside the repo) decides by the counts once the gate has passed.

**Tech Stack:** Rust (the `church_bv` test exe), bash, `~/.claude/runs/run.ps1`.

**Spec:** `docs/superpowers/specs/2026-10-23-work-counts-design.md` (approved 2026-10-23).

## Decisions (new; for approval with this plan)

- **D1, counters are summed by `take`, not flushed at thread end** (amends the spec's decision 2 and "What changes").
  The spec says thread-local counters are added into process-wide atomics when their thread ends. That loses the
  scoring workers' counts: `std::thread::scope` returns before the scoped threads' thread-local destructors run. A
  probe (scratchpad `tlsprobe.rs`, 2026-10-23: four scoped threads whose destructor sleeps 20 ms) saw the scope return
  first in 50 of 50 tries. The miner's scoring workers are scoped threads (`miner.rs`, `thread::scope` at the scorer and
  the provers). Instead, each thread registers its own slot (`Arc<[AtomicU64; 4]>`) in a process-wide list on first
  use, and adds to it with a relaxed load and store (no shared cache line, no lock). `take` sums every slot, sets them
  to 0, and drops the slots of threads that have ended. It is called only when no other thread is counting.
  Alternatives: (b) one process-wide atomic per counter, `fetch_add` at each site; rejected, since six scoring threads
  would contend on one cache line at `interp`, the hottest function. (c) flush explicitly at the end of each spawned
  closure; rejected, since every spawn site (seven in `miner.rs` and `driver.rs`) would need it, and a new one would
  silently miss counts.
- **D2, ablation pairs run untimed once the gate passes.** Decision 4(a) takes job CPU out of the verdict, so a pair
  no longer needs a quiet machine. The driver runs every pair the way the deletion check runs now: no `-Timed`,
  pinned to CFF at below-normal priority. Its `-Timed` branch, the eight retries and `wait_quiet` exist only for load
  refusals, so they are deleted.
- **D3, the spec's "Mixed stops the driver as pays and costs do" is corrected** to what the ablations plan's D4 says:
  pays (an M rise) and costs (a counter rises) record and go on; free and mixed stop the driver and come to the user.
  Fixed in the spec in Task 5.
- **D4, a `WORK` line per worker task and one per sweep main thread**, not one per process at exit. A worker process
  runs many tasks, and its stdout is the task's log only while the task runs (`driver.rs`, `worker`). The sweep's main
  thread prints its own line into `out.txt` (it builds the stream sequence, `scope_extras`). `streams_ab.sh` sums all
  of them under the arm's folder, which covers both.

## Global Constraints

- Counters: `interp` per node `Term::interp` visits, `walk` per `join_walk` call, `match` per `match_pat` call, `op` per
  `Term::op` call (spec, "The counters"). Line format: `WORK interp=<n> walk=<n> match=<n> op=<n>`.
- Salt line: `salt N: M A a B b; held A a B b; jobcpu A a B b; work A interp=.. walk=.. match=.. op=.. B interp=.. ...`.
- Verdict (spec decision 6(d)): counters are compared only once M and held-out M match on all ten salts; each counter
  summed over salts 1-10, tolerance max(its A/A spread, 1%); free / costs / mixed.
- Gate (spec, "Gate for the counts themselves"): determinism (A/A salts 1-2, equal counts per salt); proxy quality (each
  CPU/count ratio varies at most 11% over the quiet salts of the A/A and one ablation, and the ablation moves CPU and the
  summed counters the same way); overhead (counted against uncounted, timed, salts 1-2, job CPU within 5.4%, results
  identical).
- `scripts/streams_ab.sh` and `driver.sh` are read by bash while they run: edit either only when no run of it is live
  (check `docs/runs.md` for rows with no `end`, and the wrapper pid).
- Python never reads stdin (`python -P f.py < /dev/null`). No fixed sleeps, no `tail -F`. cargo `-j 4`.
- Never stop or deprioritize another session's job. Lease and load logic stays in `~/.claude/runs`.
- Work on branch `ablations`; merging, pushing and tagging only on request.

## Review Focus

1. Counts made on scoped threads must reach `take` (D1). Pinned by `work::take_sees_scoped_threads` (Task 1).
2. A worker task's line must hold that task's work only, not an earlier task's. Pinned by `worker_runs_tasks`'s new
   assertion that every ok task's log has exactly one `WORK` line (Task 2), and by the A/A's equal counts (Task 4).
3. A failed arm (no `WORK` lines) must not read as zero work and so as "free". `streams_ab.sh` counts an arm with
   no `WORK` line as failed (Task 3, Step 3 checks it).
4. A counter whose A total is 0 (a switch that removes all of one kind of work in A's own arm cannot happen, but a
   broken site can). The driver treats a 0 in A with a nonzero B as a rise, and 0 in both as no change (Task 5 fixture).
5. Overhead: `interp` gains one thread-local access per node. The overhead gate (Task 4) decides; if it fails, stop and
   report rather than moving the counter.

---

### Task 1: The counters and their four sites

**Files:**
- Create: `tests/church_bv/work.rs`
- Modify: `tests/church_bv/main.rs` (add `mod work;`)
- Modify: `tests/church_bv/rewrite.rs` (`Term::op`, `Term::interp`, `match_pat`, `join_walk`: one call each)
- Modify: `tests/church_bv/job.rs` (`hidden_state_is_classified`: two entries, its doc)

**Interfaces:**
- Produces: `work::Site { Interp, Walk, Match, Op }`, `work::count(Site)`, `work::take() -> [u64; 4]`,
  `work::line([u64; 4]) -> String`.

- [ ] **Step 1: Write the module and its test, sites not yet counted.** `tests/church_bv/work.rs`:

```rust
//! Counts of the work a process does at four sites, the gate's cost signal: the same on a busy machine as on a quiet one
//! (docs/superpowers/specs/2026-10-23-work-counts-design.md).
use std::sync::atomic::{AtomicU64, Ordering::Relaxed};
use std::sync::{Arc, Mutex};

/// The counted sites, in the order of `NAMES`.
#[derive(Clone, Copy)]
pub enum Site {
    Interp,
    Walk,
    Match,
    Op,
}
pub const NAMES: [&str; 4] = ["interp", "walk", "match", "op"];

/// The counter slot of every thread that has counted, until `take` finds its thread gone. A thread writes only its own
/// slot. Slots are read by `take`, not added up when their thread ends: `thread::scope` returns before its threads'
/// thread-local destructors run (50 of 50 tries, 2026-10-23, plan docs/superpowers/plans/2026-10-23-work-counts.md D1).
static SLOTS: Mutex<Vec<Arc<[AtomicU64; 4]>>> = Mutex::new(Vec::new());
thread_local! {
    static SLOT: Arc<[AtomicU64; 4]> = {
        let s: Arc<[AtomicU64; 4]> = Arc::new(Default::default());
        SLOTS.lock().unwrap().push(s.clone());
        s
    };
}

/// One unit of work at `site`, on this thread.
#[inline]
pub fn count(site: Site) {
    let _ = SLOT.try_with(|s| {
        let c = &s[site as usize];
        c.store(c.load(Relaxed) + 1, Relaxed);
    });
}

/// The work counted since the last `take`, summed over this process's threads, with every counter set back to 0. Call it
/// only when no other thread is counting (after a task's threads are joined): a count made during the call may be lost.
pub fn take() -> [u64; 4] {
    let mut slots = SLOTS.lock().unwrap();
    let mut out = [0; 4];
    for s in slots.iter() {
        for (o, c) in out.iter_mut().zip(s.iter()) {
            *o += c.swap(0, Relaxed);
        }
    }
    // a slot that only this list holds belongs to a thread that has ended
    slots.retain(|s| Arc::strong_count(s) > 1);
    out
}

/// The `WORK` line of `counts`: `WORK interp=<n> walk=<n> match=<n> op=<n>`.
pub fn line(counts: [u64; 4]) -> String {
    let kv: Vec<String> = NAMES.iter().zip(counts).map(|(n, c)| format!("{n}={c}")).collect();
    format!("WORK {}", kv.join(" "))
}

/// Counts made on threads a `thread::scope` ran reach `take` as soon as the scope returns, and `take` starts the counters
/// again from 0. It runs `probe` in a child process, so no other test's threads count into it.
#[test]
fn take_sees_scoped_threads() {
    let out = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["work::probe", "--exact", "--ignored", "--nocapture"])
        .env("WORK_PROBE", "1")
        .stdin(std::process::Stdio::null())
        .output()
        .unwrap();
    let text = String::from_utf8_lossy(&out.stdout);
    let lines: Vec<&str> = text.lines().filter(|l| l.starts_with("WORK ")).collect();
    assert_eq!(lines, ["WORK interp=9 walk=0 match=9 op=3", "WORK interp=0 walk=0 match=0 op=0"], "{text}");
}

/// `take_sees_scoped_threads`' child: three scoped threads each build `add(x, y)` (1 op), evaluate it (3 nodes) and match
/// it against itself (3 calls); then two `WORK` lines.
#[test]
#[ignore]
fn probe() {
    if std::env::var_os("WORK_PROBE").is_none() {
        return;
    }
    use crate::rewrite::{matches, Term, ADD};
    std::thread::scope(|s| {
        for _ in 0..3 {
            s.spawn(|| {
                let t = Term::op(ADD, Term::v(0), Term::v(1));
                assert_eq!(t.interp(4, &[1, 2]), 3);
                assert!(matches(&t, &t));
            });
        }
    });
    println!("{}", line(take()));
    println!("{}", line(take()));
}
```

Add `mod work;` after `mod task;` in `tests/church_bv/main.rs`.

- [ ] **Step 2: Run the tests to see them fail.**

Run: `cargo test --release -j 4 --test church_bv -- work:: job::hidden_state_is_classified 2>&1 | tail -15`
Expected: `take_sees_scoped_threads` FAILS with `left: ["WORK interp=0 walk=0 match=0 op=0", ...]`;
`hidden_state_is_classified` FAILS naming `work.rs:… ThreadLocal("SLOT")` and `work.rs:… ProcessWide("SLOTS")`.

- [ ] **Step 3: Count the four sites.** In `tests/church_bv/rewrite.rs`, add the first line of each body:
  - `pub fn op(o: usize, a: Term, b: Term) -> Term {` gets `crate::work::count(crate::work::Site::Op);`
  - `pub fn interp(&self, n: usize, vals: &[u128]) -> u128 {` gets `crate::work::count(crate::work::Site::Interp);`
  - `pub fn match_pat(p: &Term, t: &Term, sub: &mut [Option<Term>]) -> bool {` gets
    `crate::work::count(crate::work::Site::Match);`
  - `fn join_walk(...) -> bool {` gets `crate::work::count(crate::work::Site::Walk);` before `if let Some(x) = examined`.

  In `tests/church_bv/job.rs`, `hidden_state_is_classified`: `THREAD_LOCAL` goes from 7 to 8 entries with
  `("work.rs", "SLOT", "this thread's work counts: no task reads them, the worker prints them after it")`, and
  `PROCESS_WIDE` from 6 to 7 with `("work.rs", "SLOTS", "every thread's work counts, read only by take")`. Its doc's
  first sentence becomes: "a thread-local is a pure memo on `THREAD_LOCAL` (D3 of
  docs/superpowers/plans/2026-10-21-rewrite-context.md) or the work counts, which no task reads".

- [ ] **Step 4: Run the tests to see them pass, then the suite.**

Run: `cargo test --release -j 4 --test church_bv -- work:: job::hidden_state_is_classified 2>&1 | tail -5`
Expected: both PASS.
Run: `cargo test --release -j 4 --test church_bv 2>&1 | tail -3` and `cargo build --release -j 4 2>&1 | grep -c warning`
Expected: `146 passed` (145 before plus `take_sees_scoped_threads`), 0 failed; no warnings.

- [ ] **Step 5: Commit.** `git add tests/church_bv/work.rs tests/church_bv/main.rs tests/church_bv/rewrite.rs
  tests/church_bv/job.rs`; message `work counts: work.rs (per-thread slots summed by take, D1) and the four sites`.

### Task 2: `WORK` lines from worker tasks and the sweep

**Files:**
- Modify: `tests/church_bv/driver.rs` (`worker`, `sweep`, `worker_runs_tasks`)

**Interfaces:**
- Consumes: `work::take`, `work::line` (Task 1).
- Produces: one `WORK ...` line per worker task in its log, after `CLASS_MEMO`; one at the end of `sweep`'s stdout.

- [ ] **Step 1: Write the failing assertion.** In `worker_runs_tasks`, replace the loop at its end:

```rust
    for i in [1, 2, 4, 7, 8, 9] {
        let lines: Vec<&str> = text(i).lines().filter(|l| !l.starts_with("ECHO ")).collect();
        assert_eq!(lines, ["WORK interp=0 walk=0 match=0 op=0"], "{i}.log holds its task's lines and one WORK line: {}", text(i));
    }
```

and in `echoes`, also drop `WORK ` lines: `.filter(|l| !l.starts_with("ECHO nonce=") && !l.starts_with("WORK "))`.

- [ ] **Step 2: Run it to see it fail.**

Run: `cargo test --release -j 4 --test church_bv driver::worker_runs_tasks -- --exact --ignored --nocapture 2>&1 | tail -8`
Expected: FAIL at the new assertion, `left: []`. (If, after Step 3, an `env_echo` log shows nonzero counts, find
which call counted before changing the expectation: `env_echo` evaluates no term.)

- [ ] **Step 3: Print the lines.** In `worker`, after the `CLASS_MEMO` block and before the flush:

```rust
                println!("{}", crate::work::line(crate::work::take()));
```

At the end of `sweep`, after `machine_state("end", ...)`:

```rust
    // this thread's own work (the stream sequence, the extras lists) and the lanes' (their tasks' lines are in their logs)
    println!("{}", crate::work::line(crate::work::take()));
```

- [ ] **Step 4: Run it to see it pass, then the suite.** Same command as Step 2: PASS. Then
  `cargo test --release -j 4 --test church_bv 2>&1 | tail -3`: 146 passed.

- [ ] **Step 5: Commit.** `git add tests/church_bv/driver.rs`; message `work counts: a WORK line per worker task and
  one per sweep`.

### Task 3: `streams_ab.sh` sums the counts

**Files:**
- Modify: `scripts/streams_ab.sh`
- Modify: `%LOCALAPPDATA%\claude-runs\tatic\ablations\driver.sh` and the ablations plan's Task 1 block (the `cols`
  regex only; both synced)

**Interfaces:**
- Consumes: the `WORK` lines (Task 2).
- Produces: the salt line of Global Constraints; `total A: ... ; work interp=.. ...`; an arm with no `WORK` line
  counts as failed.

- [ ] **Step 1: Check no run of either script is live** (`docs/runs.md` rows with no `end`; the wrapper pid alive).

- [ ] **Step 2: Edit `streams_ab.sh`.** Add after `c() { ... }`:

```bash
  w() { grep -rh '^WORK ' "$RUN_DIR/s${s}_$1" 2>/dev/null | awk '{for (i = 2; i <= NF; i++) {split($i, kv, "="); if (!(kv[1] in t)) o[++n] = kv[1]; t[kv[1]] += kv[2]}} END {for (i = 1; i <= n; i++) printf "%s%s=%.0f", (i > 1 ? " " : ""), o[i], t[o[i]]}'; }
```

  End the salt line with `; work A $(w A) B $(w B)`. After each arm's `held` loop, count an arm without a `WORK` line
  as failed: `grep -rqs '^WORK ' "$o" || failed=$((failed + 1))`. In the per-arm `total` loop, sum the same way over
  `"$RUN_DIR"/s*_$arm` and add `; work <k=n ...>` to the `total` line. Update the header comment: per salt also each
  arm's work counts (the summed `WORK` lines, spec docs/superpowers/specs/2026-10-23-work-counts-design.md), and an
  arm with none failed.

  In `driver.sh` (and the plan block), drop the `$` at the end of `cols`' regex, so it still parses a salt line that
  goes on with `; work ...`.

- [ ] **Step 3: Check the parsing on a fixture.** Make `$TEMP/wfix/s1_A/x/a.log` with `WORK interp=5 walk=1 match=2 op=3`
  and `$TEMP/wfix/s1_A/out.txt` with `WORK interp=7 walk=0 match=0 op=1`; run the `w` function on it from a script
  file (`RUN_DIR=$TEMP/wfix s=1`).
Expected: `interp=12 walk=1 match=2 op=4`. An empty `s1_B` gives the empty string.
  Feed the driver's `cols` a salt line with a work tail.
Expected: the seven columns, as before.

- [ ] **Step 4: End to end, untimed, salt 1, A/A with Task 2's exe.** Build the sweep profile
  (`cargo test --profile sweep -j 4 --test church_bv --no-run`, path from the "Executable" line), copy it to the run
  folder, and run through the wrapper:
  `powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind gate -Name work-aa-s1 -Command "start /b /wait /belownormal /affinity CFF bash scripts/streams_ab.sh <exe> <exe> 1"`
  (about 8 minutes).
Expected: `salt 1: ... ; work A interp=<n> walk=<n> match=<n> op=<n> B <the same four numbers>`, all four nonzero;
  `0 of 2 arms failed`. Annotate the `docs/runs.md` row.

- [ ] **Step 5: Commit.** `git add scripts/streams_ab.sh docs/superpowers/plans/2026-10-23-class-table-ablations.md docs/runs.md`;
  message `streams_ab: per salt and per arm, the summed WORK counts; an arm with none failed`.

### Task 4: The counts' gate

**Files:**
- Modify: `docs/tier-cycle.md` (new section "Work counts as the gate's cost", after "Ablations of the class table")
- Modify: `docs/runs.md` (the rows' notes)

Each run goes through the wrapper as its own row; timed ones with `-Timed`. Pairs of salts, as the driver runs them,
so a lease is held at most ~15 minutes. The uncounted exe is the build at f0390df (the `exe_env` fix and the promoted
rules restored), `%LOCALAPPDATA%\claude-runs\tatic\2026-10-24-ablations-4\A.exe`. The counted exe is Task 3's.

Commands (exe paths as 8.3 short paths, `cygpath -d`, as the driver passes them; an arm B with a switch is a copy of
the exe with `<exe>.env` holding `ABLATE=<switch>`):
- untimed: `powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind gate -Name <name> -Command "start /b /wait /belownormal /affinity CFF bash scripts/streams_ab.sh <A> <B> <salt> <salt>"`
- timed: `powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind gate -Name <name> -Timed -WaitSec 1800 -HoldMin 40 -Command "bash scripts/streams_ab.sh <A> <B> <salt> <salt>"`;
  on exit 3 (refused), run it again. A pair takes about 15 minutes; Step 3 is ten pairs, about 2.5 hours of quiet machine.

- [ ] **Step 1: Determinism.** Salts 1-2, counted A/A, untimed (row `work-aa-s1-2`). Expected: equal counts per salt in
  both arms. If any counter differs: stop and report the spread per counter
  (decision 5(a): the spread is then measured like CPU's, over salts 1-10, in Step 3's A/A).
- [ ] **Step 2: Overhead.** Salt pair 1-2, uncounted (A) against counted (B), `-Timed`. Expected: M, held-out M and
  rules identical; B's job CPU at most 5.4% above A's per salt. If it is over: stop and report (Review Focus 5).
- [ ] **Step 3: Proxy quality.** Salts 1-10, counted A/A, `-Timed`, five pairs; then salts 1-10, counted A against
  counted A + `ABLATE=assoc` (the next switch on the ablations list), `-Timed`. All these salts passed `-Timed`'s load
  check, so all count as quiet. For each arm and salt, compute job CPU ÷ each counter with a script file
  (`python -P f.py < /dev/null`) kept in `docs/runs/<date>/scripts/`. The ratio is compared across salts, whose
  workloads differ; within one A/A salt the counts are equal, so the ratio would only repeat CPU's own noise.
  Expected: per counter, the ratio varies at most 11% (max ÷ min − 1) over the 40 arm-salts; summed over salts 1-10,
  the ablation's counters (each, and their sum) and its job CPU move the same way. If `assoc`'s counters and job CPU both move less
  than 1%, it does not test co-movement: run the next switch (`tree`) the same way. These ablation runs also give the
  switch's verdict under both rules; record it.
- [ ] **Step 4: Record.** The section in `docs/tier-cycle.md`: the four counters' totals per arm, the A/A spread per
  counter (the tolerances: max(spread, 1%)), the overhead, the ratios' spread and the co-movement, each with run ids.
  Annotate the `docs/runs.md` rows. If any part of the gate failed, stop here and report: decision 6(b)'s fitted
  weights come back as a decision for the user (spec, "Proxy quality").
- [ ] **Step 5: Commit.** `git add docs/tier-cycle.md docs/runs.md docs/runs/<date>/scripts/`; message
  `work counts: the gate (determinism, overhead, proxy quality)`.

### Task 5: The driver decides by counts

**Files:**
- Modify: `%LOCALAPPDATA%\claude-runs\tatic\ablations\driver.sh` and the ablations plan's Task 1 block (synced)
- Modify: `docs/superpowers/plans/2026-10-23-class-table-ablations.md` (D1, D3: the verdict and untimed pairs)
- Modify: `docs/superpowers/specs/2026-10-23-work-counts-design.md` (D1 and D3 of this plan; status)

- [ ] **Step 1: Check no driver run is live.**
- [ ] **Step 2: Write the fixtures.** In `$TEMP/dfix/`, five pair files `abl-x-s1-2.txt` .. `abl-x-s9-10.txt`, each two
  salt lines `salt N: M A 176 B 176; held A 900 B 900; jobcpu A 430.0 B 431.0; work A interp=1000 walk=100 match=50 op=10 B interp=1000 walk=100 match=50 op=10`
  and `streams_ab: rules same in 6 of 6 loops; 0 of 4 arms failed`. Variants, each its own folder: `free` (as is);
  `costs` (salt 1's B `interp=1300`: +3% summed); `mixed` (that, and every B `walk=80`); `pays` (salt 3's B `M ... B 177`);
  `zero` (every A and B `op=0`: free).
- [ ] **Step 3: Run the old driver on them** (`RESUME_FROM=<fixture>`, `RUN_DIR` a temp folder, `ablate x`).
Expected: `free` for free, costs, mixed and zero (the old driver ignores counts), and pays at salt 3 for pays. This
  is the RED.
- [ ] **Step 4: Change the driver.** Replace the free/job-CPU verdict at the end of the switch loop:

```bash
  # the counters (spec docs/superpowers/specs/2026-10-23-work-counts-design.md, decision 6(d)): each summed over the
  # salts, against max(its A/A spread, 1%) (docs/tier-cycle.md, "Work counts as the gate's cost")
  v=$(wcols "${done_pairs[@]}" | awk -v tols="$tols" 'BEGIN {n = split(tols, t, " "); for (i = 1; i <= n; i++) {split(t[i], kv, "="); tol[kv[1]] = kv[2]}}
      {if (!($2 in a)) o[++k] = $2; a[$2] += $3; b[$2] += $4}
      END {for (i = 1; i <= k; i++) {c = o[i]; d = a[c] ? (b[c] - a[c]) / a[c] : (b[c] ? 1 : 0); s = s sprintf(" %s %+.2f%%", c, 100 * d)
           if (d > tol[c]) up = 1; else if (d < -tol[c]) dn = 1}
           print (up ? (dn ? "mixed" : "costs") : "free") ":" s}')
  echo "VERDICT $sw ${v%%:*}: $sum; work${v#*:}, salts 1-10"
  case "${v%%:*}" in costs) continue ;; *) exit 0 ;; esac
```

  with, above `cols`:

```bash
# per salt line, one row per counter: salt name A B
wcols() { sed -nE 's/^salt ([0-9]+): .*; work A (.*) B (.*)$/\1|\2|\3/p' "$@" | awk -F'|' '{na = split($2, x, " "); split($3, y, " "); for (i = 1; i <= na; i++) {split(x[i], p, "="); split(y[i], q, "="); print $1, p[1], p[2], q[2]}}'; }
# each counter's tolerance: max(its A/A spread, 1%), from Task 4 of docs/superpowers/plans/2026-10-23-work-counts.md
tols="interp=0.01 walk=0.01 match=0.01 op=0.01"
```

  (`tols` takes Task 4's measured spreads where any is over 1%.) Delete the job-CPU check (`cpu=...`, its `over`
  verdict). D2: `pair` always runs untimed and pinned; delete the `timed` variable, its `-Timed` flags, the retry loop,
  the exit-3 branch and `wait_quiet`; the `untimed` argument goes too. Update the header comment: ablate mode now
  prints pays (M or held-out rise), costs, mixed or free; costs goes on to the next switch; mixed and free exit.

- [ ] **Step 5: Run the fixtures again.**
Expected: free, costs (goes on: `DRIVER done: no switch left`), mixed (exits), pays at salt 3, free for zero. Then
  sync the plan block (`diff` against the file: identical).
- [ ] **Step 6: Docs.** Ablations plan D1 and D3: the verdict by counts (link the spec's decision 6) and untimed pairs
  (this plan's D2). Its Review Focus item 1 keeps the killed-mid-pair case and drops the refusals; item 2 (CPU
  leniency) goes, as job CPU no longer decides. Spec: decision 2 and "What changes" say the slots are summed by `take`
  (D1); decision 3 says a line per worker task and per sweep (D4); decision 6's "mixed" sentence follows D3;
  `status: done`. This plan's status: `done`.
- [ ] **Step 7: Commit.** `git add docs/superpowers/plans/2026-10-23-class-table-ablations.md
  docs/superpowers/specs/2026-10-23-work-counts-design.md docs/superpowers/plans/2026-10-23-work-counts.md`; message
  `ablations driver: decides by work counts (free, costs, mixed), pairs untimed`. Then relaunch the ablations from
  `assoc` (or the switch after the ones Task 4 already measured), as the ablations plan's Task 3 says.
