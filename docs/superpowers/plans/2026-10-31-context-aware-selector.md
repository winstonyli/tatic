---
status: done
---

# v0.6, second try: select the extras by the kernel's straggler verdicts (implementation plan)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Find out whether filling a mine's n extras slots with laws the kernel marks as stragglers (from a `POOL` times larger candidate list) moves the frontier beyond a random draw at matched mining CPU.

**Architecture:** The driver appends `POOL x n` extras per mine to the lawfile and tells the miner where they start (`RULEMINER_EXTRAS_FROM`), how many to keep (`RULEMINER_EXTRAS_KEEP`) and by what (`RULEMINER_EXTRAS_BY`: `first` or `straggler`). In the miner, `laws_of` splits into `classify` (a verdict per law under the mine's base rules) and `assemble` (stragglers, guard sample); a pure `kept_indices` chooses which pool laws survive between the two. `first` truncates before classifying, so it is exactly today's mine and is the control.

**Tech Stack:** Rust (the `church_bv` test crate, no new dependency), bash, `~/.claude/runs/run.ps1` for recorded runs, `scripts/streams_ab.sh` for the gate.

**Spec:** `docs/superpowers/specs/2026-10-31-context-aware-selector-design.md` (approved 2026-10-31).

## Global Constraints

- `kind: experiment`; no compatibility shims; no new Cargo dependency.
- Selection only decides which laws a mine reads; every law and rule still passes the kernel.
- Unset `EXTRAS_SELECT` leaves the driver and miner behaving exactly as today.
- Judge on gate salts 1-3, held-out M summed, sigma = 76 (the stage 1 redraw spread; re-derived in Task 5 if `r319` does not reproduce held-out M 5166).
- Long runs launch through `~/.claude/runs/run.ps1` (`-Kind gate -Affinity CFF -Detach`, paths in 8.3 form via `cygpath -d`), one row each in `docs/runs.md`, a watcher on `run.json`'s `"end"` (deadline stated per run). Untimed gate wrapper: `docs/runs/2026-10-31/scripts/gate.sh` (JOBS=3, ARM_CACHE). Check for orphan processes, live CPU leases and free disk (`LONG_RUNS.md`) before each run; report Defender real-time state with results.
- Commit after each task with the trailer `Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>`; never push, tag or bump.
- Thresholds in Task 5 are set here, before any data.

## Review Focus

1. `RULEMINER_EXTRAS_FROM` past the end of the lawfile, or `KEEP` larger than the pool: no panic; the mine keeps what exists (test in Task 2).
2. A pool with fewer than n stragglers: the shortfall is filled with the other pool laws in order, so n laws are kept whenever the pool has n (test in Task 2).
3. `KEEP=0`: the served laws are untouched and no extra is read (test in Task 2).
4. A pool law that is not a law or is over the carry cap (outcome `Skipped`): it takes a slot under `first` (as today), is chosen last under `straggler`, and never reaches `assemble` as a straggler or guard (tests in Tasks 1 and 2).
5. `EXTRAS_SELECT` set to an unknown word, or together with `SCORER`: an error naming the variable, not a silent fallback (test in Task 3).
6. `by=first` reproduces today's mine rule for rule, and a straggler-first mine on `served + [clean, straggler]` with `KEEP=1` equals the mine on `served + [straggler]` (tests in Task 2).

## File Structure

- `tests/church_bv/miner.rs`: `Outcome`, `classify`, `assemble`, `laws_of` as their composition, `Keep`, `kept_indices`, config fields, `laws()` wiring, tests.
- `tests/church_bv/driver.rs`: `EXTRAS_SELECT` in `scope_extras` and the `mine` closure of `run_loop`, the `GEN` print, tests.
- `docs/runs/2026-10-31/scripts/`: `gate.sh`, `curve.sh` (exist); no new script.
- Docs: `docs/tier-cycle.md` (result), `ROADMAP.md`, `PARKED.md`, `docs/learned-vs-fixed.md` if a row changes, `docs/TOUR.md` (glossary: Straggler-first selection; `bash scripts/tour_check.sh`), spec and this plan `status:`.

---

### Task 1: Split `laws_of` into `classify` and `assemble` (no behavior change)

**Files:**
- Modify: `tests/church_bv/miner.rs` (`laws_of`, around line 144)
- Modify: `docs/superpowers/specs/2026-10-31-context-aware-selector-design.md`, this plan (`status: active`)

**Interfaces:**
- Produces: `enum Outcome { Skipped, Clean(String, Term, Term), Straggler(Scored) }` (derive `Clone`; `Scored` is the existing tuple `(name, t1, t2, normal, fell, took)`); `fn classify(job: &mut Job, laws: &[(String, Term, Term)], budget: i64, fast: bool, loud: bool) -> Vec<Outcome>` (one outcome per input law, same order; prints the per-straggler `RULEMINER straggler` lines when `loud`); `fn assemble(outcomes: Vec<Outcome>, guard_k: usize, loud: bool, clock: &Clock) -> Laws`.
- `laws_of(job, laws, guard_k, fast, budget, clock, loud) -> Laws` keeps its signature and becomes `assemble(classify(...), ...)` (callers: `laws`, `transfer_labels`, tests).

- [ ] **Step 1: Capture the baseline.** Run `cargo test --release --test church_bv miner:: 2>&1 | tail -20` and keep the pass list (expected: all green).

- [ ] **Step 2: Move the body.** Cut `laws_of`'s loop into `classify` (the `counting` rules wrapper stays inside it; `Skipped` is the `continue` case; `unproved` and the `fell` bump stay as they are). `assemble` takes the stragglers and clean laws out of the outcomes in order, prints the two summary lines (`RULEMINER {} stragglers of {} laws, ...` with `outcomes.len()` as the law count and `unproved` recomputed as stragglers with `fell` from an unproved rewrite: carry it in the `Straggler` payload as it is in `Scored.4`... if `unproved` cannot be recovered from `Scored`, add a `bool` to `Outcome::Straggler(Scored, bool)`), builds the guard sample exactly as before, and returns `Laws { stragglers, scored, guard_w, n, kv }`. `n` and `kv` come from the same constants (`4`, `STREAM_VARS`).

- [ ] **Step 3: Run the baseline again.** Same command; expected: identical pass list. Also a unit test `classify_orders_outcomes_like_the_input` that classifies three laws (one not a law such as two sides with different variable sets or `is_law` false, one `and(x, y) = and(y, x)`, one from `ROLLBACK_LAWS` that is a straggler) and asserts `[Skipped, Clean, Straggler]` by position. Write it first, watch it fail to compile, then make it pass.

- [ ] **Step 4: Flip statuses and commit.** Set `status: active` in the spec and this plan.

```bash
git add tests/church_bv/miner.rs docs/superpowers
git commit -m "church_bv: laws_of is classify then assemble (no behavior change)

Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>"
```

---

### Task 2: `Keep`, `kept_indices` and the mine's extras selection

**Files:**
- Modify: `tests/church_bv/miner.rs` (`MinerConfig`, `laws`, tests)

**Interfaces:**
- Consumes: Task 1's `Outcome`, `classify`, `assemble`.
- Produces: `pub enum Keep { First, Straggler }` with `Keep::parse(&str) -> Result<Keep, String>` (`"first"`, `"straggler"`; anything else `Err("EXTRAS_SELECT: expected first or straggler, got {s}")`); `pub struct ExtrasKeep { pub from: usize, pub n: usize, pub by: Keep }`; `MinerConfig.extras: Option<ExtrasKeep>` read from `RULEMINER_EXTRAS_FROM` (present means on), `RULEMINER_EXTRAS_KEEP` (required with FROM) and `RULEMINER_EXTRAS_BY` (required with FROM); `fn kept_indices(len: usize, from: usize, n: usize, by: Keep, is_straggler: &dyn Fn(usize) -> bool) -> Vec<usize>`.

- [ ] **Step 1: Failing unit tests for `kept_indices`.**

```rust
#[test]
fn kept_indices_keeps_the_served_laws_and_n_of_the_pool() {
    let none = |_: usize| false;
    // 3 served, pool of 6, keep 2
    assert_eq!(kept_indices(9, 3, 2, Keep::First, &none), vec![0, 1, 2, 3, 4]);
    let s = |i: usize| i == 5 || i == 7; // stragglers at pool positions 5 and 7
    assert_eq!(kept_indices(9, 3, 2, Keep::Straggler, &s), vec![0, 1, 2, 5, 7], "stragglers first, in order");
    assert_eq!(kept_indices(9, 3, 3, Keep::Straggler, &s), vec![0, 1, 2, 3, 5, 7], "the shortfall is the first other pool law, kept in index order");
    assert_eq!(kept_indices(9, 3, 0, Keep::Straggler, &s), vec![0, 1, 2], "keep 0 reads no extra");
    assert_eq!(kept_indices(9, 3, 99, Keep::Straggler, &s), (0..9).collect::<Vec<_>>(), "keep past the pool keeps the pool");
    assert_eq!(kept_indices(4, 9, 2, Keep::First, &none), vec![0, 1, 2, 3], "from past the end: all served, no pool");
}
```

Run: `cargo test --release --test church_bv kept_indices` -> FAIL (not defined).

- [ ] **Step 2: Implement `kept_indices`.** Result is ascending. Served `0..min(from, len)`; pool `from..len`. `First`: the first `n` pool indices. `Straggler`: the pool indices where `is_straggler` is true, first `n`; if fewer than `n`, add non-stragglers in index order until `n`; sort the union ascending. Run the test -> PASS.

- [ ] **Step 3: Failing integration tests** (use `ROLLBACK_LAWS` and `mine(&setup, &[])` as `a_false_winner_rolls_the_rounds_back` does; a helper writes a temp lawfile, builds a `Setup::with_env`, runs `mine`, and returns the chosen rule lines):

```rust
// served = ROLLBACK_LAWS lines; `clean` = "and(x, y) = and(y, x)"; `strag` = a straggler of the served file found with
// `classify` (first Outcome::Straggler), written with its two `show()` sides as `lhs = rhs`.
#[test]
fn extras_by_first_is_todays_mine() {
    // served + [clean, strag] with FROM=len(served), KEEP=1, BY=first  ==  served + [clean]  (no extras env)
}
#[test]
fn extras_by_straggler_keeps_the_straggler_over_the_clean_law() {
    // served + [clean, strag], KEEP=1, BY=straggler  ==  served + [strag]
    // and the log-independent check: classify says clean is Clean and strag is Straggler (the test is meaningful)
}
#[test]
fn extras_keep_zero_and_a_from_past_the_end_do_not_panic() {
    // KEEP=0 == served alone; FROM=1000 == the whole file read as served
}
```

Run -> FAIL.

- [ ] **Step 4: Wire `laws`.** In `MinerConfig::new` read the three variables (`s.var("RULEMINER_EXTRAS_FROM")`; if present, `RULEMINER_EXTRAS_KEEP` and `_BY` must also be, else `panic!` naming the missing one; `Keep::parse(..)` errors panic with its message). In `laws()`:

```rust
let mut named = read_named_laws(&cfg.lawfile);
clock.phase("law building");
let Some(x) = &cfg.extras else { return laws_of(job, named, cfg.guard, cfg.fast, budget, clock, true) };
if x.by == Keep::First {
    let keep = kept_indices(named.len(), x.from, x.n, Keep::First, &|_| false);
    named = keep.iter().map(|&i| named[i].clone()).collect(); // truncated before classifying: today's mine, none of the pool's cost
    return laws_of(job, named, cfg.guard, cfg.fast, budget, clock, true);
}
let outcomes = classify(job, &named, budget, cfg.fast, true);
let keep = kept_indices(named.len(), x.from, x.n, Keep::Straggler, &|i| matches!(outcomes[i], Outcome::Straggler(..)));
let pool_stragglers = (x.from.min(named.len())..named.len()).filter(|&i| matches!(outcomes[i], Outcome::Straggler(..))).count();
println!("RULEMINER extras: kept {} of {} pool laws, {pool_stragglers} stragglers in the pool", keep.len() - x.from.min(named.len()), named.len().saturating_sub(x.from));
clock.phase("extras selection");
assemble(keep.into_iter().map(|i| outcomes[i].clone()).collect(), cfg.guard, true, clock)
```

(Note the straggler lines `classify` prints with `loud` include dropped pool laws; the `extras:` line is the one to read for kept counts.)

- [ ] **Step 5: Run.** `cargo test --release --test church_bv miner::` -> all green, including the new tests. Check the Review Focus 4 case with a pool law that is `Skipped` (a law with five variables) in `kept_indices`' straggler test via `is_straggler` returning false for it.

- [ ] **Step 6: Commit.**

```bash
git add tests/church_bv/miner.rs
git commit -m "church_bv: a mine can keep n of a pool of extras by the kernel's straggler verdict (RULEMINER_EXTRAS_*)

Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>"
```

---

### Task 3: The driver passes the pool and the selection

**Files:**
- Modify: `tests/church_bv/driver.rs` (`scope_extras`, `run_loop`'s `mine` closure, tests)

**Interfaces:**
- Consumes: `miner::Keep::parse`.
- Produces: driver variable `EXTRAS_SELECT=first|straggler` (unset = today). With it set, `scope_extras` gives each mine a slice of `POOL x n` laws (the whole pool), requires no `SCORER`, and `run_loop` sets `RULEMINER_EXTRAS_FROM` (the served file's line count), `RULEMINER_EXTRAS_KEEP` (`EXTRAS_N`, default 319) and `RULEMINER_EXTRAS_BY` on that mine's env.

- [ ] **Step 1: Failing test for the parse.** A pure `fn extras_select(select: Option<&str>, scorer: bool) -> Result<Option<Keep>, String>` in `driver.rs`: `None` -> `Ok(None)`; `"first"` -> `Ok(Some(Keep::First))`; `"bogus"` -> `Err` mentioning `EXTRAS_SELECT`; `Some(_)` with `scorer == true` -> `Err` mentioning both `EXTRAS_SELECT` and `SCORER`. Test, watch it fail, implement.

- [ ] **Step 2: `scope_extras`.** Parse `extras_select(setup.var("EXTRAS_SELECT"), setup.var("SCORER").is_some())` (an `Err` returns `Err`). With a selection, call `select_extras(&kept, pool * n, pool * n, None)` (the identity: every mine's slice is its whole pool) and size `at` with `extra_slices(laws.len(), scope.len(), mines, pool * n)`. Add `select {}` to the `GEN` print. `POOL=1` with a selection is allowed (the selection then picks among n and changes nothing).

- [ ] **Step 3: `run_loop`'s `mine` closure.** After `write_laws` and before appending the extras, `let from = std::fs::read_to_string(&lawfile_path).unwrap().lines().count();` (the served laws written so far). If `extras_select(..)` is `Some(by)`: push `("RULEMINER_EXTRAS_FROM", from)`, `("RULEMINER_EXTRAS_KEEP", setup.or("EXTRAS_N", EXTRAS_N))`, `("RULEMINER_EXTRAS_BY", "first"|"straggler")` onto `env` before `worker.run`. The `GEN_EXTRA` print says `laws` already; extend it with `, keep {n}`.

- [ ] **Step 4: Run.** `cargo test --release --test church_bv driver::` and the whole `miner::` set -> green. `cargo test --release --test church_bv --no-run` -> builds; the printed exe path is Task 4's.

- [ ] **Step 5: Commit.**

```bash
git add tests/church_bv/driver.rs
git commit -m "church_bv: EXTRAS_SELECT hands each mine its whole pool and the selection (first or straggler)

Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>"
```

---

### Task 4: Build the arms and smoke-test one mine (a recorded probe)

**Files:**
- Modify: `docs/runs.md` (rows by `run.ps1`)

Expected duration: 10 minutes (one salt, n 80, two arms, JOBS=3). Check for orphans and live leases first.

- [ ] **Step 1: Build and copy.** `cargo test --release --test church_bv --no-run`; copy the printed exe to `$LOCALAPPDATA/claude-runs/tatic/v06-exes/h1.exe` and make these copies (same bytes, only `.exe.env` differs; each env line `NAME=value`):

| exe copy | `.exe.env` lines |
|---|---|
| `h1r80.exe`, `h1r160.exe`, `h1r319.exe` | `EXTRAS_N=80` / `160` / `319` |
| `h1h80.exe`, `h1h160.exe`, `h1h319.exe` | the same `EXTRAS_N`, plus `POOL=4` and `EXTRAS_SELECT=straggler` |
| `h1c319.exe` | `EXTRAS_N=319`, `POOL=4`, `EXTRAS_SELECT=first` (the control) |

- [ ] **Step 2: Smoke gate on salt 1, n 80.**

```bash
A=$(cygpath -m "$(cygpath -d "$LOCALAPPDATA/claude-runs/tatic/v06-exes/h1r80.exe")")
B=$(cygpath -m "$(cygpath -d "$LOCALAPPDATA/claude-runs/tatic/v06-exes/h1h80.exe")")
G=$(cygpath -m "$(cygpath -d "$PWD/docs/runs/2026-10-31/scripts/gate.sh")")
powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind probe -Name v06h-smoke -Affinity CFF -Detach -Command "bash $G $A $B 1"
```

Watcher on `run.json`'s `"end"`, deadline 30 minutes. Read, in the run folder: the `ENV` lines show `EXTRAS_SELECT` and `POOL` on arm B only (and no `changed` flag); the `GEN` line says `select straggler`; each B mine log has `RULEMINER extras: kept 80 of 320 pool laws, <k> stragglers in the pool` with `k` near 0.37 x 320 = 118 (expected 100-140; a very different rate means the classification or the pool is wrong); the `laws and stragglers` and `extras selection` phase times of a B mine give the classification cost (the spec's 0.1 s per mine is the figure to recheck: record the actual); A and B give different rules (selection took effect).

- [ ] **Step 3: Stop here if anything is off.** A missing `extras:` line, `k` far from 118, or identical A and B rules is a bug: debug with `superpowers:systematic-debugging` before Task 5.

- [ ] **Step 4: Commit the record.**

```bash
git add docs/runs.md
git commit -m "docs: v0.6 h1 smoke run v06h-smoke

Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>"
```

---

### Task 5: The gate matrix and the curve verdict (recorded runs)

**Files:**
- Modify: `docs/runs.md`, `docs/tier-cycle.md`, `ROADMAP.md`, `PARKED.md`, `docs/TOUR.md`, `docs/learned-vs-fixed.md` (only if its "Miner" or "Loop and driver" row changes), the spec and this plan

Expected duration: four gate runs on salts 1-3, about 22 minutes at n 319 and less at n 80 and 160, the arm cache reusing the repeated random arm: about 1.5 hours wall. Check orphans, leases, disk and Defender before each.

- [ ] **Step 1: Run four gates** (`run.ps1 -Kind gate -Affinity CFF -Detach`, salts `1 2 3`, a watcher each; names `v06h-g1` ... `v06h-g4`):

| run | A | B | answers |
|---|---|---|---|
| `v06h-g1` | `h1r319` | `h1c319` | the control: pool 4, selection off, must equal `r319` |
| `v06h-g2` | `h1r80` | `h1h80` | the curve at n 80 |
| `v06h-g3` | `h1r160` | `h1h160` | the curve at n 160 |
| `v06h-g4` | `h1r319` | `h1h319` | the curve at n 319 |

Before reading results, check each `out.log`'s `ENV` lines and that no arm has a `changed` flag.

- [ ] **Step 2: Read the curve** with `docs/runs/2026-10-31/scripts/curve.sh <label> <A|B> <run>` (the stage 1 usage; one line per arm summed over salts 1-3: held-out M, loop M, rules, job CPU, work, bands).

**Checks before the verdict.** (a) `h1r319` held-out M is 5166 (the stage 1 `r319`); if it differs, the refactor changed behavior: stop, find it. (b) `h1c319` held-out M is within sigma = 76 of `h1r319` (it should be exactly equal rule for rule: `first` truncates before classifying, so it is today's mine given the same extras; a difference means the pool changes which laws are first, and then the control is the stage 1 `c319`, 5168). (c) Each `h1h` mine's `extras:` line: record the mean kept stragglers and the share of the 80/160/319 kept that are stragglers.

**Verdict rule (set before the data).** A **win** is either (a) `held(h_n) < held(r_n) - 76` for some n with job CPU of `h_n` no more than 1.1x that of `r_n`, or (b) `held(h_n) <= held(r_2n)` with lower job CPU than `r_2n` (`r_2n` is `h1r160` for n 80 and `h1r319` for n 160; for n 319 there is no `r_638` here, so (b) is read against the recorded n 688 figure, held-out M 4622 at about twice the job CPU, `PARKED.md`, the mining-budget entry). Anything else is a **null**; a worse held-out M than random at every n is recorded as **worse**, with the guard-law loss (non-straggler extras dropped) as the first suspect. h1b (marginal selection) is considered only after a **null** here, not a win.

- [ ] **Step 3: Record.** `docs/tier-cycle.md`: a section "Selecting the extras by straggler verdict (v0.6, second try)" with the curve table, the kept-straggler share, the classification cost, the verdict, the run ids. Update `ROADMAP.md` v0.6: a win -> a stage 2 line with its `Done when`; a null or worse -> the result linked and v0.6 stays open (the user decides what follows: h1b, h2/h3, or closing v0.6). `PARKED.md`: the learned-proposer entry's trigger and evidence cite the new result; h1b as its own entry if h1a is null. `docs/TOUR.md`: the glossary entry "Straggler-first selection" and the "Extras"/"Pool" entries, then `bash scripts/tour_check.sh`. Set the spec and this plan `status: done`. Docs check: grep the docs for the old wording ("stage 2 is parked", "a learned model") and fix or list the stale files.

- [ ] **Step 4: Commit.**

```bash
git add docs ROADMAP.md PARKED.md
git commit -m "docs: v0.6 h1 result, straggler-first extras (runs v06h-g1..g4)

Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>"
```

---

## Self-review

- **Spec coverage:** in-mine selection and the pool (Tasks 2, 3); h1a straggler-first with `Skipped` and unproved laws counted as in `laws_of` (Tasks 1, 2); cost at matched CPU over a curve and the classification cost (Tasks 4, 5); success rule and control (Task 5); identity, keep-step unit test, determinism (Tasks 1, 2, 5 check (a)); h1b parked until h1a reads (Task 5 Step 3). Not covered by a task on purpose: the verdict's determinism is a property of the existing step budget (`LAW_STEPS`), confirmed by the gate's rules repeating between the equal arms of `v06h-g1`.
- **Placeholder scan:** Task 1 Step 2 leaves one choice (carry `unproved` in `Outcome::Straggler` as a `bool` if `Scored` cannot give it); the choice is stated, not open.
- **Type consistency:** `Keep`, `ExtrasKeep`, `kept_indices(len, from, n, by, is_straggler)`, `Outcome`, `classify`, `assemble` are used with one signature across Tasks 1-3; the env names `RULEMINER_EXTRAS_FROM/KEEP/BY` and the driver's `EXTRAS_SELECT` match in Tasks 2, 3, 4.
- **Rulings made while planning:** the served/extras split is passed as a line index (`FROM`) over the one lawfile rather than a second file, so the baseline lawfile stays byte-identical; `first` truncates before classifying so the control costs nothing extra; the `Outcome::Skipped` laws take a pool slot under `first` and are filled last under `straggler`.
