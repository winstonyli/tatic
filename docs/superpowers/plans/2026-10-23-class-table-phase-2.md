---
status: draft
---

# The class table as the rewriter's normal form, build steps 4-6 Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make the class table the rewriter's normal form (phase 2), move the loops and their gate onto table-seeded
operator-set streams with a frozen past-domain held-out set, and delete the hand-written families.

**Architecture:** `rewrite_uncached` looks every node up in the table after its children (`Classes::lookup`): a known
node is final, as its own representative or through the proved step to it; others go on to the rules. Laws come from
`search::stream_sequence(salt)`: 56 streams (`stream_laws`, one per operator set of size 2 and 3) interleaved
round-robin, generated once per process and salt; a loop's phase p takes residue class p at stride 4, and the mines'
extras come from phase 0. `classes::regenerate_held` freezes 1000 open laws per size band (11, 13) into
`tests/church_bv/held_{11,13}.txt`, and `scripts/streams_ab.sh` gates on `cold:streams` plus M on those files. Once the
new gate has its A/A baseline, the families and everything only they used are deleted.

**Tech Stack:** Rust (the `church_bv` test binary), the kernel (`tatic::kernel`), bash scripts, `~/.claude/runs/run.ps1`,
`tools/runs` (`runs.exe`, used by the gate scripts; `time.rs` changed in Task 9).

**Spec:** `docs/superpowers/specs/2026-10-22-class-table-normal-form-design.md` (approved 2026-10-23, amended while
planning in `b6dc952`). This plan covers its build steps 4-6. Steps 7 (the ablations, one switch at a time on the new
gate) and 8 (phase 3) need the new gate's A/A spread, which Task 7 measures; they get their own plan afterwards.

## Rulings this plan makes inside the spec

Each is stated once; tasks cite them by number.

- **R1. Phases are residue classes** of `stream_sequence(salt)` at stride `STREAM_STRIDE = 4` (spec §9 as amended):
  phase 0 feeds the mines' extras, phases 1-3 the three loops. The sequence is the 56 streams interleaved round-robin,
  a law kept at its first appearance (two streams can draw one law).
- **R2. The extras** are the first `STREAM_EXTRAS = 1650` laws of phase 0 (the size of cmp3d's generator list on the
  old gate, `docs/tier-cycle.md` "L 1644"), filtered against the scope's served laws as today, `GEN_F` share as today,
  so a mine sees about as many extras as before. `GEN_DRAW=d` shifts the extras' salt by `1000 d` as before. New; to
  confirm at review.
- **R3. Table steps are counted per closed law** through one helper, `Job::steps_if_closed(f)`: the steps taken inside
  `f` are kept only when `f` returns `Some`. `prove_eq`'s phase 1 and the kernel-check task's per-law loop both use it,
  so phase 2's steps on laws left open are not counted (spec decision 2).
- **R4. Tests set switches through `Setup::with_env(pairs)`** (the process's environment with `pairs` over it, no
  result file); `classes::prove_eq_closes_a_residue_law_by_the_table`'s temporary result file goes.
- **R5. The lookup memo's size** is printed by the worker after every task (`CLASS_MEMO <terms>`, from
  `Classes::memo_len()`, which does not build the table), so a gate reads each worker's peak from its logs.
- **R6. The held-out files:** a law's band is its larger side's size; files are written from `stream_sequence(HELD_SALT)`
  with `HELD_SALT = 7_777_777` (no sweep salt or draw shift reaches it); laws salt 1's loops serve (phases 1-3, the
  first 300 laws each) are dropped and counted; each band takes its first 1000 laws in sequence order, which is
  round-robin over the streams. The header is `held laws of size <band>, class key fnv <16 hex digits>, table size 9`,
  the hash FNV-1a 64 over the key file's trimmed lines joined by `\n` (line endings differ between checkouts).
- **R7. The new gate runs in chunks of two salts** (`run.ps1 -Timed -HoldMin 45` each), so no CPU lease is held for
  hours; each chunk is its own `docs/runs.md` row.
- **R8. Temporary `streams` branches.** Task 5 adds `streams` beside the families in `family_vars`, the driver's law
  window, `loop_cfgs` and `Draw::grammar`; Task 8 deletes the family side of each, so no branch stays. This is the
  spec's step 5 before step 6, additive with no rework.
- **R9. `family_laws` names its last family:** `mul` explicitly; any other unknown name panics with
  `family {f}: three-variable laws come from stream law files (RULEMINER_LAWFILE, CHECK_LAWFILE)` instead of silently
  mining `mul`. `CHECK_FAMILY` defaults to `streams`; `CHECK_RULES` becomes optional (unset: no mined rules).
- **R10. `Draw` is deleted in Task 8:** `stream_sequence`'s memo is its cache.
- **R11. The `pad_1` fixture test** (`normalize_finds_the_probes_twins`) is deleted with the families (its counts are
  of cmp3d loops); the fixture directory stays only if a doc cites its path.

## Global Constraints

- Table: size 9, operators `add and or xor sub shl1 shr1 lt`, key file `tests/church_bv/class_key.txt` (unchanged).
- Streams: every set of two and three of `add and or xor sub shl1 shr1` (56), budget 20000 per growth, two growths,
  laws kept when the table leaves them open and they agree on the 4096 width-8 inputs (spec decision 8, §9).
- Switches: `classes` = phase 2 (the normal form in `rewrite`); `eq_classes` = phase 1 (the step in `prove_eq`); no
  table at all = `ABLATE=classes,eq_classes`.
- Held-out set: 1000 laws per band, bands 11 and 13, at a salt no loop uses (decision 10).
- Gate: before Task 7, `docs/runs/2026-10-18/scripts/salts_ab.sh` (cold:cmp3d, salts 1-5); from Task 7 on,
  `scripts/streams_ab.sh` (cold:streams plus held-out M); the A/A baseline on salts 1-10.
- Memory stop: a gate arm whose largest `peakproc` exceeds the baseline's by more than 150 MB stops the plan for a
  decision (`PARKED.md`, "Bound the class table's lookup memo").
- Builds: `cargo ... -j 4`; check `%LOCALAPPDATA%\cpu-leases\*.json` for a live exclusive lease before any build or
  run over 30 s; runs that are cited go through `run.ps1` (RUNS.md) and get a `docs/runs.md` row with notes.
- Never let `python` read stdin; no fixed sleeps; never `tail -F`.
- Commits on `rule-generality` only, message from `$TEMP/msg.txt`, ending `Co-Authored-By: Claude Opus 5.5
  <noreply@anthropic.com>`; never push, tag or merge.
- Leave alone: `.claude/worktrees/*`, untracked `tests/ring_spike.rs` and `tests/ring_loop_spike.rs`,
  `.superpowers/sdd/2026-10-17-law-generator/`. Historical scripts and docs under `docs/runs/` stay as records.

## Review Focus

1. **A node past the table's size whose key values match a stored class** must be replaced only through `step`'s
   verdict, never declared final or replaced unproved. Pinned by Task 2's `rewrite_replaces_a_node_past_the_table_only_with_a_proof`.
2. **The held-out files after a key or line-ending change:** a regenerated key must fail the suite with the
   regeneration message, while a CRLF checkout of the same key must not. Pinned by Task 6's `held_header_ignores_line_endings`
   and `a_held_header_for_another_key_fails`.
3. **A stream generated twice** (the gate's two arms are separate processes) must give the same laws in the same order;
   a `HashMap` iteration leaking into the order would make arms serve different laws. Pinned by Task 4's
   `stream_laws_are_deterministic_and_open` (two direct calls, not the memo).
4. **The extras overlapping the loops' served laws:** phase 0 must share no law with phases 1-3. Pinned by Task 5's
   `stream_phases_are_disjoint_residue_classes`.
5. **Deleting the families must not change `cold:streams`:** the same exe logic before and after Task 8-9 must give the
   same rules in every loop. Pinned by Task 10's A/B (rules same in every loop, M equal).

---

### Task 1: `Setup::with_env` and `Job::steps_if_closed`

**Files:**
- Modify: `tests/church_bv/job.rs` (after `Setup::for_task`, line ~46; `impl Job`; tests near line 333)
- Modify: `tests/church_bv/classes.rs:680-681`

**Interfaces:**
- Produces: `pub fn Setup::with_env(pairs: Vec<(String, String)>) -> Arc<Setup>`;
  `pub fn Job::steps_if_closed<R>(&mut self, f: impl FnOnce(&mut Job) -> Option<R>) -> Option<R>`.

- [ ] **Step 1: Write the failing tests** (in `job.rs`, after `with_rules_puts_the_outer_rules_back`)

```rust
/// A test's switch: `with_env` lays its pairs over the process's environment.
#[test]
fn with_env_sets_a_switch() {
    let s = Setup::with_env(vec![("ABLATE".into(), "classes,eq_classes".into())]);
    assert!(s.ablated("classes") && s.ablated("eq_classes") && !s.ablated("comm"));
}

/// Table steps taken inside `steps_if_closed` are kept only when it returns `Some` (spec decision 2: a closed law's
/// steps), and the steps counted before it stay either way.
#[test]
fn steps_are_kept_only_for_a_closed_law() {
    use crate::rewrite::parse_term;
    let job = &mut Job::new(Setup::process());
    let (p, q) = ((parse_term("x"), parse_term("y")), (parse_term("y"), parse_term("x")));
    job.table_steps.insert(p);
    let open = job.steps_if_closed(|job| {
        job.table_steps.insert(q);
        None::<()>
    });
    assert!(open.is_none() && job.table_steps.len() == 1 && job.table_steps.contains(&p));
    let closed = job.steps_if_closed(|job| {
        job.table_steps.insert(q);
        Some(())
    });
    assert!(closed.is_some() && job.table_steps.contains(&p) && job.table_steps.contains(&q));
}
```

- [ ] **Step 2: Run them to see them fail**

Run: `cargo test --release --test church_bv -j 4 -- job::with_env job::steps_are_kept 2>&1 | grep -E "^error|cannot find|no method" | head -3`
Expected: compile errors naming `with_env` and `steps_if_closed`.

- [ ] **Step 3: Implement**

In `impl Setup`, after `for_task`:

```rust
    /// The process's setup with `pairs` over its environment and no result file: a test's job with a switch set.
    pub fn with_env(pairs: Vec<(String, String)>) -> Arc<Setup> {
        Arc::new(Setup::from_env(merge_env(process_env(), exe_env().as_deref(), &pairs)))
    }
```

In `impl Job` (beside its other methods):

```rust
    /// Runs `f` with the class-table steps it takes counted apart, and keeps them (in `table_steps`) only when `f` returns
    /// `Some`: the replacements a closed law used (spec decision 2), whichever phase took them.
    pub fn steps_if_closed<R>(&mut self, f: impl FnOnce(&mut Job) -> Option<R>) -> Option<R> {
        let kept = std::mem::take(&mut self.table_steps);
        let r = f(self);
        let used = std::mem::replace(&mut self.table_steps, kept);
        if r.is_some() {
            self.table_steps.extend(used);
        }
        r
    }
```

In `classes.rs`, `prove_eq_closes_a_residue_law_by_the_table`: delete the line
`let results = std::fs::File::create(...)` and change the next line to
`let job = &mut Job::new(Setup::with_env(vec![("ABLATE".into(), "classes".into())]));` (Task 2 renames the switch).

- [ ] **Step 4: Run the tests**

Run: `cargo test --release --test church_bv -j 4 -- job:: classes::prove_eq_closes 2>&1 | grep -E "^test result|FAILED|panicked" | head`
Expected: `test result: ok`, 0 failed.

- [ ] **Step 5: Commit**

```bash
git add tests/church_bv/job.rs tests/church_bv/classes.rs
git diff --cached --stat
printf 'job: Setup::with_env for a test'"'"'s switches, and Job::steps_if_closed, the one place a closed law'"'"'s table steps are kept\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n' > "$TEMP/msg.txt"
git commit -q -F "$TEMP/msg.txt"
```

Then build the base exe for Task 3 (phase 2 not yet in):

```bash
cargo test --release --test church_bv --no-run -j 4 2>&1 | tail -1
x="$(ls -t target/release/build/tatic/*/out/church_bv-*.exe target/release/deps/church_bv-*.exe 2>/dev/null | head -1)"
cp "$x" "$TEMP/bv_p2_base.exe"
```

---

### Task 2: Phase 2 in `rewrite` (spec §5)

**Files:**
- Modify: `tests/church_bv/classes.rs:351-366` (`rep` → `lookup`, `rep`, `reps`, `memo_len`), tests near line 680
- Modify: `tests/church_bv/rewrite.rs:2420` (hook), `:2694` and `:2716-2728` (`prove_eq`), the five tests at 3809,
  3828, 3871, 3955, 4237
- Modify: `tests/church_bv/search.rs:1449` (`rule_set_kernel_check_task`'s per-law loop)
- Modify: `tests/church_bv/job.rs:80-81` (the `ablated` doc's switch list)
- Modify: `tests/church_bv/driver.rs` (`worker`, after the task's thread joins)

**Interfaces:**
- Consumes: `Setup::with_env`, `Job::steps_if_closed` (Task 1).
- Produces: `pub fn Classes::lookup(&self, t: &Term) -> Option<Term>`; `pub fn Classes::reps(&self) -> impl Iterator<Item = Term> + '_`;
  `pub fn Classes::memo_len() -> Option<usize>`; switches `classes` (phase 2) and `eq_classes` (phase 1).

- [ ] **Step 1: Write the failing tests** (in `classes.rs`, after `steps_of_a_pair_left_open_are_not_counted`)

```rust
/// `lookup` answers a known class with its representative, the term itself included; `rep` only when it differs; a
/// term over a fourth variable is unknown.
#[test]
fn lookup_includes_the_term_itself() {
    let (c, _) = Classes::build(&Key::parse(KEY_FILE).unwrap(), 5, 0, 0);
    let show = |t: Option<Term>| t.map(|t| t.show());
    let x = parse_term("x");
    assert_eq!(show(c.lookup(&x)), Some("x".to_string()));
    assert_eq!(show(c.rep(&x)), None);
    assert_eq!(show(c.lookup(&parse_term("sub(y, y)"))), Some("0".to_string()));
    assert_eq!(show(c.lookup(&parse_term("add(x, u)"))), None);
}

/// Phase 2 (spec §5): a node the table knows is final in `rewrite`. `sub(add(x, y), y)` rewrites to `x` with no rule
/// tried (the rule trace stays empty) and a table step counted; with `ABLATE=classes,eq_classes` rules are tried and
/// no table step is taken.
#[test]
fn rewrite_takes_the_table_before_any_rule() {
    let t = parse_term("sub(add(x, y), y)");
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        job.rw.trace = Some(vec![]);
        let (r, _) = rewrite(job, &t, 4, 3);
        assert_eq!(r.show(), "x");
        assert_eq!(job.rw.trace.as_ref().unwrap().len(), 0, "a rule was tried");
        assert!(!job.table_steps.is_empty());
    });
    let job = &mut Job::new(Setup::with_env(vec![("ABLATE".into(), "classes,eq_classes".into())]));
    tatic::kernel::scoped(|| {
        job.rw.trace = Some(vec![]);
        rewrite(job, &t, 4, 3);
        assert!(!job.rw.trace.as_ref().unwrap().is_empty(), "no rule was tried");
        assert!(job.table_steps.is_empty());
    });
}

/// A node over a fourth variable is unknown to the table: `sub(add(x, u), u)` goes to the rules (the trace records
/// them) and no table step is taken at a node with `u`.
#[test]
fn rewrite_leaves_a_fourth_variable_to_the_rules() {
    let t = parse_term("sub(add(x, u), u)");
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        job.rw.trace = Some(vec![]);
        let (r, _) = rewrite(job, &t, 4, 4);
        assert_eq!(r.show(), "x");
        assert!(!job.rw.trace.as_ref().unwrap().is_empty());
        assert!(job.table_steps.iter().all(|(u, _)| !u.has_var(3)));
    });
}

/// Review Focus 1: a node past the table's size whose values match a stored class is replaced only through `step`'s
/// verdict. `add(add(add(x, y), z), add(add(x, z), y))` (size 11, children normal) has the class of a term within size
/// 9; it is replaced, and the replacement is a counted (proved) step from a node larger than `SIZE`.
#[test]
fn rewrite_replaces_a_node_past_the_table_only_with_a_proof() {
    let t = parse_term("add(add(add(x, y), z), add(add(x, z), y))");
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let (r, plan) = rewrite(job, &t, 4, 3);
        assert!(r.size() <= SIZE, "{}", r.show());
        assert!(job.table_steps.iter().any(|(u, _)| u.size() > SIZE), "no counted step from a node past the table's size");
        let (p, s) = law_proof(job, 4, 3, &t, &r, &plan);
        job.lemmas.ck("past the table's size", &p, &s);
    });
}
```

`law_proof(job, n, k, t1, t2, plan: &Plan)` is the call `held_out_replacements_prove` makes. If the last test fails only
because `step` finds no verdict for `add(r, r)` (no replacement, `r` unchanged), the table is behaving as required; pick
a size-11 law whose replacement has a `Bitwise` verdict instead (`or(or(and(x, y), z), or(and(x, y), z))`, class
`or(and(x, y), z)`) and ledger the ruling. A replacement without a counted step is a bug.

- [ ] **Step 2: Run them to see them fail**

Run: `cargo test --release --test church_bv -j 4 -- classes::lookup_includes classes::rewrite_ 2>&1 | grep -E "^error|no method|panicked|^test " | head -6`
Expected: a compile error naming `lookup`.

- [ ] **Step 3: `lookup`, `rep`, `reps`, `memo_len`**

Replace `rep` (classes.rs:351-366) with:

```rust
    /// The representative of `t`'s class, `t` itself included, when the table knows the class; `None` otherwise, and for
    /// a term over a variable other than x, y, z. Pure: no proof. One memo holds every term asked (spec §5).
    pub fn lookup(&self, t: &Term) -> Option<Term> {
        if t.max_var() >= 3 {
            return None;
        }
        let (values, reps) = &mut *self.memos.lock().unwrap_or_else(|e| e.into_inner());
        *reps.entry(*t).or_insert_with(|| {
            let mut vals = vec![];
            for m in values.iter_mut() {
                vals.extend_from_slice(m.values(t));
            }
            self.map.get(&class_hash(&vals, matches!(*t.node(), Node::Op(LT, ..)))).copied()
        })
    }

    /// The representative of `t`'s class when the table knows it and it is not `t` (`lookup`, the term itself left out).
    pub fn rep(&self, t: &Term) -> Option<Term> {
        self.lookup(t).filter(|r| r != t)
    }

    /// Every stored representative (the streams' seeds, spec §9).
    pub fn reps(&self) -> impl Iterator<Item = Term> + '_ {
        self.map.values().copied()
    }

    /// Terms in the process's lookup memo, or `None` before the table is built (it is not built here): the worker prints
    /// it after each task, so a gate reads the memo's peak (spec §9).
    pub fn memo_len() -> Option<usize> {
        CLASSES.get().map(|c| c.memos.lock().unwrap_or_else(|e| e.into_inner()).1.len())
    }
```

Update the module doc (classes.rs:4) "`rep` looks a term's class up" to "`lookup` and `rep` look a term's class up".

- [ ] **Step 4: The hook in `rewrite_uncached`** (rewrite.rs, right after `let t1 = Term::op(o, a2, b2);`)

```rust
    // the class table's normal form (docs/superpowers/specs/2026-10-22-class-table-normal-form-design.md §5): a node the
    // table knows is final, as its own representative or through the proved step to it; any other node goes on to the
    // rules (over a fourth variable, a class not stored, or a replacement with no proof)
    if !job.setup().ablated("classes") {
        let c = crate::classes::Classes::get();
        if let Some(r) = c.lookup(&t1) {
            if r == t1 {
                return (t1, cong);
            }
            if let Some((r, p)) = c.step(job, n, k, &t1) {
                return (r, Plan::trans(job, cong, p));
            }
        }
    }
```

- [ ] **Step 5: Phase 1 renamed `eq_classes`, counted through `steps_if_closed`** (rewrite.rs `prove_eq`)

Change the comment `// each step below can be switched off: \`ABLATE=eq_truth,eq_pos,classes,shrmask\`` to
`// each step below can be switched off: \`ABLATE=eq_truth,eq_pos,eq_classes,shrmask\``. Replace the class-table block
(from `// the learned class table` through its closing `}`) with:

```rust
    // the learned class table (docs/superpowers/specs/2026-10-22-class-table-normal-form-design.md §4): both sides
    // normalized by its proved replacements; if they meet, the law is closed with no rule, and only then are its steps
    // counted (`Job::steps_if_closed`)
    if !job.setup().ablated("eq_classes") {
        let c = crate::classes::Classes::get();
        let closed = job.steps_if_closed(|job| {
            let ((na, pa), (nb, pb)) = (c.normalize(job, n, k, a), c.normalize(job, n, k, b));
            (na == nb).then(|| Plan::trans(job, pa, Plan::sym(job, pb)))
        });
        if closed.is_some() {
            return closed;
        }
    }
```

In `job.rs`'s `ablated` doc, change the list to
`(comma list: comm, assoc, chain, tree, collapse, join, promoted, ruleset, a built-in rule's name, the class table's normal form classes, prove_eq's eq_truth, eq_pos, eq_classes, shrmask, and the driver's gen)`.

- [ ] **Step 6: The checker counts per closed law** (search.rs `rule_set_kernel_check_task`)

Change `let (r, plan_spent) = job.spent(|job| rewrite_plan(job, 4, kv, t1, t2));` to
`let (r, plan_spent) = job.spent(|job| job.steps_if_closed(|job| rewrite_plan(job, 4, kv, t1, t2)));`.

- [ ] **Step 7: The worker reports the memo** (driver.rs `worker`)

Right after the `let ok = match task_fn(&name) { ... };` statement (before `std::io::stdout().flush().unwrap();`):

```rust
                if let Some(n) = crate::classes::Classes::memo_len() {
                    println!("CLASS_MEMO {n}");
                }
```

- [ ] **Step 8: Existing tests**

1. `classes::prove_eq_closes_a_residue_law_by_the_table`: the ablated job's pair becomes
   `("ABLATE".into(), "classes,eq_classes".into())`; its doc's `ABLATE=classes` becomes `ABLATE=classes,eq_classes`.
2. `classes::steps_of_a_pair_left_open_are_not_counted`: replace `prove_eq(job, 4, 3, &a, &b);` with
   `assert!(job.steps_if_closed(|job| prove_eq(job, 4, 3, &a, &b)).is_none());` and its doc with
   "A pair whose normal forms differ keeps none of the table steps taken on it (`Job::steps_if_closed`, as the
   kernel-check task counts): `sub(add(x, y), y)` steps to `x`, which does not meet `y`."
3. The five rule-cycle tests (`rewrite_cycles_are_cut`, `growing_rewrite_chains_are_cut`,
   `filtered_memo_entries_hold_under_an_extra_rule`, `trace_index_agrees_with_touched_by`,
   `memo_keeps_rewrites_cut_inside_their_own_call`): change `let job = &mut Job::new(Setup::process());` to
   `let job = &mut Job::new(Setup::with_env(vec![("ABLATE".into(), "classes".into())]));` and add to each doc comment
   the sentence "The table's normal form is off: this tests the rules' cuts and memo, which act only where the table
   does not (spec, Testing)."

- [ ] **Step 9: Run the suite**

Run: `cargo test --release --test church_bv -j 4 2>&1 | grep -E "^test result|FAILED|panicked" | head`
Expected: 0 failed, including the four new tests and `job::hidden_state_is_classified` (phase 2 adds no static).
If `rewrite_leaves_a_fourth_variable_to_the_rules` fails only on `r.show() == "x"` (the rules leave another normal
form), assert instead that `r` has no `u` node below a table step and ledger the ruling; any other failure is a bug.

- [ ] **Step 10: Commit**

```bash
git add tests/church_bv/classes.rs tests/church_bv/rewrite.rs tests/church_bv/search.rs tests/church_bv/job.rs tests/church_bv/driver.rs
git diff --cached --stat
printf 'rewrite: the class table as the normal form (phase 2, ABLATE=classes): a known node is final, as its own representative or through the proved step; phase 1 renamed eq_classes; steps counted per closed law; workers report the lookup memo\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n' > "$TEMP/msg.txt"
git commit -q -F "$TEMP/msg.txt"
```

---

### Task 3: Phase 2 on the old gate, once

**Files:**
- Modify: `docs/runs.md`, `docs/tier-cycle.md`, `docs/learned-vs-fixed.md`, `PARKED.md`

- [ ] **Step 1: Build the arms**

```bash
cargo test --release --test church_bv --no-run -j 4 2>&1 | tail -1
x="$(ls -t target/release/build/tatic/*/out/church_bv-*.exe target/release/deps/church_bv-*.exe 2>/dev/null | head -1)"
cp "$x" "$TEMP/bv_p2.exe"; cp "$x" "$TEMP/bv_p2_off.exe"; printf 'ABLATE=classes\n' > "$TEMP/bv_p2_off.exe.env"
```

- [ ] **Step 2: The restore check, then the gate** (check CPU leases first)

```bash
w() { cygpath -w "$1"; }
powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind gate -Timed -Name p2-restore -Command "bash docs/runs/2026-10-18/scripts/salts_ab.sh '$(w "$TEMP/bv_p2_base.exe")' '$(w "$TEMP/bv_p2_off.exe")' 1"
powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind gate -Timed -Name p2-gate -Command "bash docs/runs/2026-10-18/scripts/salts_ab.sh '$(w "$TEMP/bv_p2_base.exe")' '$(w "$TEMP/bv_p2.exe")' 1 2 3 4 5"
```

Expected: the restore run (about 2 min) ends `rules same in 3 of 3 loops; 0 of 2 arms failed` with equal M per loop;
if not, stop and find why (`ABLATE=classes` must give phase 1 exactly). The gate (about 10 min) ends
`0 of 10 arms failed`, with B's M near the spike's 0 (A about 377 over salts 1-5) and B's job CPU well under A's
(spike: 451 to 26 s). Then from `$RUN_DIR` of the gate:
- `grep -rh "^CLASS_MEMO" "$RUN_DIR"/s*_B | awk '{if ($2 > m) m = $2} END {print m}'`: the memo's peak (spike: under
  50000);
- `grep -rh "^CLASS_UNUSABLE" "$RUN_DIR"/s*_B | sort -u | wc -l`;
- per arm the largest `peakproc` (`grep -h peakproc "$RUN_DIR"/s*_A/result.txt`, `_B`).
If B's largest `peakproc` exceeds A's by more than 150 MB, record and stop for a decision.

- [ ] **Step 3: Record and commit**

Fill in both `docs/runs.md` rows (headline and " ; notes" after the pids). In `docs/tier-cycle.md` add a section
"*Phase 2 in the rewriter (<date>; plan docs/superpowers/plans/2026-10-23-class-table-phase-2.md; runs <restore id>,
<gate id>)*": the restore check; M per salt and per arm, rules agreement, wall and job CPU per arm; the memo's peak;
unusable replacements; the largest `peakproc` per arm; against the spike's numbers ("Phase 2 leaves the miner nothing
to learn on the gate"). In `docs/learned-vs-fixed.md`, candidate 4: one sentence giving phase 2's result with a link to
that section. In `PARKED.md`, "Bound the class table's lookup memo" and "The class table's lookup beyond its domain,
and under one lock": update **evidence** with this gate's numbers (`Classes::lookup` now, not `rep`).

```bash
git add docs/runs.md docs/tier-cycle.md docs/learned-vs-fixed.md PARKED.md
git diff --cached --stat
printf 'runs: phase 2 on the old gate (<gate id>): M <A> -> <B>, job cpu <A> -> <B> s, memo peak <n> terms; restore check same rules\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n' > "$TEMP/msg.txt"
git commit -q -F "$TEMP/msg.txt"
```

---

### Task 4: `stream_laws` and `stream_sequence` (spec decision 8, §9)

**Files:**
- Modify: `tests/church_bv/search.rs` (new items after `grammar_laws_have_no_padding`, about line 1139)

**Interfaces:**
- Consumes: `Classes::reps`, `Classes::normalize` (Task 2 and before).
- Produces (all `pub` in `search`): `fn stream_sets() -> Vec<Vec<usize>>`; `const STREAM_BUDGET: usize = 20000`;
  `const STREAM_LEVELS: usize = 2`; `const STREAM_STRIDE: usize = 4`;
  `fn stream_laws(ops: &[usize], salt: usize, budget: usize, levels: usize) -> Vec<(Term, Term)>`;
  `fn stream_sequence(salt: usize) -> std::sync::Arc<Vec<(Term, Term)>>`;
  `fn residue(seq: &[(Term, Term)], phase: usize, skip: usize, laws: usize) -> Vec<(Term, Term)>`.

- [ ] **Step 1: Write the failing tests**

```rust
/// The rotation (spec decision 8): every set of two and three of the seven bit-vector operators, none with `lt`.
#[test]
pub fn stream_sets_are_the_pairs_and_triples() {
    let sets = stream_sets();
    assert_eq!(sets.len(), 56);
    assert_eq!(sets.iter().filter(|s| s.len() == 2).count(), 21);
    assert!(sets.iter().all(|s| (2..=3).contains(&s.len()) && !s.contains(&LT)));
}

/// Review Focus 3: a stream is the same laws in the same order on every call (two direct calls, not the memo); another
/// salt gives other laws; every law's sides use only the set's operators, the table leaves it open, and it agrees on
/// the 4096 width-8 inputs.
#[test]
pub fn stream_laws_are_deterministic_and_open() {
    let ops = [ADD, SHR1];
    let (a, b) = (stream_laws(&ops, 1, 2000, 2), stream_laws(&ops, 1, 2000, 2));
    assert!(a.len() > 20, "{} laws", a.len());
    assert!(a == b, "same salt, other laws or order");
    assert!(a != stream_laws(&ops, 2, 2000, 2), "another salt, the same laws");
    fn within(t: &Term, ops: &[usize]) -> bool {
        match *t.node() {
            Node::Op(o, x, y) => ops.contains(&o) && within(&x, ops) && within(&y, ops),
            _ => true,
        }
    }
    let c = crate::classes::Classes::get();
    let job = &mut Job::new(Setup::process());
    let mut r8 = width8();
    tatic::kernel::scoped(|| {
        for (x, y) in &a {
            assert!(within(x, &ops) && within(y, &ops), "{} = {}", x.show(), y.show());
            assert!(c.normalize(job, 4, 3, x).0 != c.normalize(job, 4, 3, y).0, "closed: {} = {}", x.show(), y.show());
            let vx = r8.values(x).to_vec();
            assert_eq!(vx, r8.values(y).to_vec(), "{} = {}", x.show(), y.show());
        }
    });
}

/// Phases are residue classes at `STREAM_STRIDE`, windowed by skip and count.
#[test]
pub fn residue_takes_a_phase_window() {
    let seq: Vec<(Term, Term)> = (0..40).map(|i| (Term::v(0), (0..i).fold(Term::v(1), |t, _| Term::op(ADD, t, Term::v(2))))).collect();
    let at = |w: Vec<(Term, Term)>| w.iter().map(|l| seq.iter().position(|s| s == l).unwrap()).collect::<Vec<_>>();
    assert_eq!(at(residue(&seq, 1, 0, 3)), [1, 5, 9]);
    assert_eq!(at(residue(&seq, 2, 1, 2)), [6, 10]);
    assert_eq!(at(residue(&seq, 3, 9, 5)), [39]);
}
```

- [ ] **Step 2: Run them to see them fail**

Run: `cargo test --release --test church_bv -j 4 -- search::stream_ search::residue 2>&1 | grep -E "^error|cannot find" | head -3`
Expected: compile errors naming `stream_sets`, `stream_laws`, `residue`, `width8`.

- [ ] **Step 3: Implement** (search.rs, after `grammar_laws_have_no_padding`)

```rust
/// The streams' operator sets (spec decision 8): every set of two and three of the seven bit-vector operators, in the
/// order of their bit masks over `[ADD, AND, OR, XOR, SUB, SHL1, SHR1]` (as `docs/runs/2026-10-23/scripts/mix_streams.sh`).
pub fn stream_sets() -> Vec<Vec<usize>> {
    let ops = [ADD, AND, OR, XOR, SUB, SHL1, SHR1];
    (1u32..128).filter(|m| matches!(m.count_ones(), 2 | 3)).map(|m| (0..7).filter(|i| m >> i & 1 == 1).map(|i| ops[i]).collect()).collect()
}

/// Terms grown per level of a stream (the probe's budget, docs/tier-cycle.md "Triples match pairs per grown term").
pub const STREAM_BUDGET: usize = 20000;
/// Growth levels of a stream.
pub const STREAM_LEVELS: usize = 2;
/// Phases of the stream sequence: phase 0 feeds the mines' extras, 1-3 the loops (spec §9).
pub const STREAM_STRIDE: usize = 4;

/// The 4096 pseudo-random width-8 inputs an open law must agree on (the probe's): width 4 only conjectured it.
fn width8() -> ValueMemo<u8> {
    let mut seed = 0x6a09_e667_f3bc_c908u128;
    let vars: Vec<Box<[u8]>> = (0..3)
        .map(|_| {
            (0..4096)
                .map(|_| {
                    seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                    (seed >> 40) as u8
                })
                .collect()
        })
        .collect();
    ValueMemo::new(8, 4096, vars)
}

/// One stream (spec §9; the probe `open_law_counts`, `docs/runs/2026-10-23/patches/open_law_counts_table.patch`): seeds
/// are the class table's representatives whose operators lie in `ops`; `levels` times, one leaf of a term is grown into
/// one of the seeds' operators over two leaves (`shl1` and `shr1` over one), padding dropped, about `budget` terms per
/// level drawn by `salt`. Laws are grouped by width-4 values as `pool_conjectures` does, have a grown side, use all three
/// variables, and are shuffled by `salt`; kept when the table leaves them open (normal forms differ) and they agree on
/// `width8`'s inputs. Prints the laws kept and refuted.
pub fn stream_laws(ops: &[usize], salt: usize, budget: usize, levels: usize) -> Vec<(Term, Term)> {
    let c = crate::classes::Classes::get();
    fn within(t: Term, ops: &[usize]) -> bool {
        match *t.node() {
            Node::Op(o, a, b) => ops.contains(&o) && within(a, ops) && within(b, ops),
            _ => true,
        }
    }
    let mut seeds: Vec<Term> = c.reps().filter(|t| within(*t, ops)).collect();
    seeds.sort_by_cached_key(|t| t.show());
    fn ops_of(t: Term, out: &mut std::collections::BTreeSet<usize>) {
        if let Node::Op(o, a, b) = *t.node() {
            out.insert(o);
            ops_of(a, out);
            ops_of(b, out);
        }
    }
    // the leaf positions of a term (a shift's second operand is not one), and the term with leaf `k` replaced by `g`
    fn leaf_count(t: Term) -> usize {
        match *t.node() {
            Node::Op(SHL1 | SHR1, a, _) => leaf_count(a),
            Node::Op(_, a, b) => leaf_count(a) + leaf_count(b),
            _ => 1,
        }
    }
    fn replaced(t: Term, k: &mut Option<usize>, g: Term) -> Term {
        match *t.node() {
            Node::Op(o @ (SHL1 | SHR1), a, b) => Term::op(o, replaced(a, k, g), b),
            Node::Op(o, a, b) => {
                let a = replaced(a, k, g);
                Term::op(o, a, replaced(b, k, g))
            }
            _ => match *k {
                Some(0) => {
                    *k = None;
                    g
                }
                Some(i) => {
                    *k = Some(i - 1);
                    t
                }
                None => t,
            },
        }
    }
    let mut grown_ops = std::collections::BTreeSet::new();
    seeds.iter().for_each(|t| ops_of(*t, &mut grown_ops));
    let leaves = leaves3();
    let mut memo = ValueMemo::exhaustive(4, 3);
    let leaf_values: Vec<Vec<u8>> = leaves.iter().map(|l| memo.values(l).to_vec()).collect();
    let grow: Vec<Term> = grown_ops
        .iter()
        .flat_map(|&o| if o == SHL1 || o == SHR1 { leaves.iter().map(|a| mk(o, a, &Term::ZERO)).collect::<Vec<_>>() } else { leaves.iter().flat_map(|a| leaves.iter().map(move |b| mk(o, a, b))).collect() })
        .filter(|g| !leaf_values.contains(&memo.values(g).to_vec()))
        .collect();
    let mut level: hashbrown::HashMap<Term, usize> = seeds.iter().map(|t| (*t, 0)).collect();
    let (mut base, mut i) = (seeds.clone(), 0u64);
    for l in 1..=levels {
        let total: usize = base.iter().map(|t| leaf_count(*t)).sum::<usize>() * grow.len();
        let mut next = vec![];
        for t in &base {
            for p in 0..leaf_count(*t) {
                for g in &grow {
                    i += 1;
                    if (tatic::rng::mix64(i ^ tatic::rng::mix64(salt as u64 + 13 * l as u64)) % total.max(1) as u64) < budget as u64 {
                        let w = replaced(*t, &mut Some(p), *g);
                        if !level.contains_key(&w) {
                            level.insert(w, l);
                            next.push(w);
                        }
                    }
                }
            }
        }
        base = next;
    }
    // sorted, so the order owes nothing to the map's
    let mut terms: Vec<Term> = level.keys().cloned().collect();
    terms.sort_by_cached_key(|t| (level[t], t.show()));
    let laws: Vec<(Term, Term)> =
        pool_conjectures(terms, 4, 3, 0).into_iter().filter(|(a, b)| level[a].max(level[b]) > 0 && (0..3).all(|v| a.has_var(v) || b.has_var(v))).collect();
    let job = &mut Job::new(Setup::process());
    let mut r8 = width8();
    let (mut out, mut refuted) = (vec![], 0usize);
    tatic::kernel::scoped(|| {
        for (a, b) in shuffled(laws, salt) {
            if c.normalize(job, 4, 3, &a).0 == c.normalize(job, 4, 3, &b).0 {
                continue;
            }
            let va = r8.values(&a).to_vec();
            if va != r8.values(&b) {
                refuted += 1;
                continue;
            }
            out.push((a, b));
        }
    });
    let names: Vec<&str> = ops.iter().map(|o| OP_INFO[*o].name).collect();
    println!("STREAM {} salt {salt}: {} open laws, {refuted} refuted at width 8", names.join(","), out.len());
    out
}

/// The loops' law sequence for `salt` (spec §9): the 56 streams (`stream_sets`, `STREAM_BUDGET`, `STREAM_LEVELS`)
/// interleaved round-robin, a law kept at its first appearance. Built once per process and salt.
pub fn stream_sequence(salt: usize) -> std::sync::Arc<Vec<(Term, Term)>> {
    static MEMO: crate::task::SharedMemo<usize, std::sync::Arc<Vec<(Term, Term)>>> = crate::task::SharedMemo::new();
    let build = || {
        let t0 = std::time::Instant::now();
        let streams: Vec<Vec<(Term, Term)>> = stream_sets().iter().map(|ops| stream_laws(ops, salt, STREAM_BUDGET, STREAM_LEVELS)).collect();
        let (mut seen, mut seq) = (HashSet::new(), vec![]);
        for i in 0..streams.iter().map(Vec::len).max().unwrap_or(0) {
            for s in &streams {
                if let Some(l) = s.get(i) {
                    if seen.insert(*l) {
                        seq.push(*l);
                    }
                }
            }
        }
        println!("STREAMS salt {salt}: {} laws from {} streams in {:.1}s", seq.len(), streams.len(), t0.elapsed().as_secs_f64());
        std::sync::Arc::new(seq)
    };
    MEMO.with(salt, build, |s| s.clone())
}

/// Phase `phase`'s window of a sequence: its residue class at `STREAM_STRIDE`, `laws` of them from `skip`.
pub fn residue(seq: &[(Term, Term)], phase: usize, skip: usize, laws: usize) -> Vec<(Term, Term)> {
    seq.iter().skip(phase).step_by(STREAM_STRIDE).skip(skip).take(laws).cloned().collect()
}
```

`SharedMemo::with(key, init, f)` runs `init` under the memo's lock (`task.rs:23`): a second thread asking for the same
salt waits for the first build instead of repeating it. `pool_conjectures` is `machine::pool_conjectures` (in scope
through `main.rs`'s `use machine::*`); it sorts its pairs by text, so its order does not depend on a map's.

- [ ] **Step 4: Run the tests**

Run: `cargo test --release --test church_bv -j 4 -- search::stream_ search::residue 2>&1 | grep -E "^test |panicked|^test result" | head`
Expected: 3 passed.

- [ ] **Step 5: Time one full sequence** (check CPU leases first)

Add an ignored probe test beside them, kept as the command that measures the sequence:

```rust
/// Builds `stream_sequence(STREAMS_SALT)` (default 1) and prints its size and time: what a sweep pays once (spec §9, Risks).
#[test]
#[ignore]
pub fn stream_sequence_cost() {
    let salt = Setup::process().or("STREAMS_SALT", 1usize);
    let seq = stream_sequence(salt);
    println!("SEQUENCE salt {salt}: {} laws; phase 1 window of 300: {}", seq.len(), residue(&seq, 1, 0, 300).len());
}
```

```bash
cargo test --release --test church_bv --no-run -j 4 2>&1 | tail -1
x="$(ls -t target/release/build/tatic/*/out/church_bv-*.exe target/release/deps/church_bv-*.exe 2>/dev/null | head -1)"; cp "$x" "$TEMP/bv_p2_seq.exe"
powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind probe -Name stream-sequence -Command "'$(cygpath -w "$TEMP/bv_p2_seq.exe")' search::stream_sequence_cost --exact --ignored --nocapture"
```
Expected: about 1.5-2 min (the probe's); `STREAMS salt 1:` with tens of thousands of laws (the probe: about 28900
held laws for the 21 pairs alone; the sequence dedups across streams); 56 `STREAM` lines, none with 0 laws. If it
takes over 5 minutes, record and stop for a decision (the sweep pays it once per salt).

- [ ] **Step 6: Commit**

```bash
git add tests/church_bv/search.rs docs/runs.md
git diff --cached --stat
printf 'search: stream_laws and stream_sequence, the table-seeded operator-set streams (spec decision 8, §9); probe stream-sequence: <n> laws in <s> s\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n' > "$TEMP/msg.txt"
git commit -q -F "$TEMP/msg.txt"
```

---

### Task 5: `cold:streams` in the sweep (R1, R2, R8)

**Files:**
- Modify: `tests/church_bv/search.rs:1251` (`family_vars`)
- Modify: `tests/church_bv/driver.rs` (`write_laws` 547, `stream_laws` 560 renamed `window_laws`, `served_laws` 574,
  `Draw::grammar` 609, `loop_cfgs` in `sweep`, tests)

**Interfaces:**
- Consumes: `search::{stream_sequence, residue, STREAM_STRIDE}`.
- Produces: family name `streams` (three variables); sweep stage `cold:streams` with loop dirs
  `cold_streams_streams_<1|2|3>_none`, `cold_streams.tsv` rows `streams\t4-<p>\tfrom_none\t<M>...`; driver
  `const STREAM_EXTRAS: usize = 1650`; `fn window(setup: &Setup, family: &str, get: &dyn Fn(&str) -> Option<String>) -> Vec<(Term, Term)>`.

- [ ] **Step 1: Write the failing test** (driver.rs, after `extra_slices_refuse_a_short_list`)

```rust
/// Review Focus 4: the stream phases are disjoint residue classes, so phase 0 (the mines' extras) shares no law with
/// the loops' phases 1-3, and their windows tile each class.
#[test]
fn stream_phases_are_disjoint_residue_classes() {
    let seq: Vec<(Term, Term)> = (0..200).map(|i| (Term::v(0), (0..i).fold(Term::v(1), |t, _| Term::op(ADD, t, Term::v(2))))).collect();
    let phase = |p: usize| residue(&seq, p, 0, usize::MAX);
    let all: Vec<_> = (0..STREAM_STRIDE).flat_map(phase).collect();
    assert_eq!(all.len(), seq.len());
    let distinct: hashbrown::HashSet<_> = all.iter().collect();
    assert_eq!(distinct.len(), seq.len(), "a law in two phases");
    assert!(residue(&seq, 1, 0, 10) == phase(1)[..10] && residue(&seq, 1, 10, 10) == phase(1)[10..20]);
    assert_eq!(family_vars("streams"), 3);
}
```

- [ ] **Step 2: Run it to see it fail**

Run: `cargo test --release --test church_bv -j 4 -- driver::stream_phases 2>&1 | grep -E "^error|panicked|^test " | head -3`
Expected: a compile error (`residue` or `STREAM_STRIDE` not in scope) or a panic on `family_vars("streams")`.

- [ ] **Step 3: Implement**

`family_vars` (search.rs): `if family == "streams" || THREE_VAR_FAMILIES.contains(&family) { 3 } else { 2 }` (keep its
current shape otherwise; Task 8 reduces it to `streams`).

driver.rs (`use super::*` already brings `search`'s public items, `main.rs:26`). Add, above `write_laws`:

```rust
/// Laws in a stream mine's extras: the first this many of phase 0, about the size of cmp3d's generator list on the old
/// gate (L 1644, docs/tier-cycle.md), so a mine sees as many extras as it did there (plan R2).
const STREAM_EXTRAS: usize = 1650;

/// The law window `get`'s `RULEMINER_*` variables select from `family`'s sequence: for `streams`, phase
/// `RULEMINER_PHASE`'s residue class of `stream_sequence(RULEMINER_SHUFFLE)` (spec §9, plan R1); otherwise `family_laws`.
fn window(setup: &Setup, family: &str, get: &dyn Fn(&str) -> Option<String>) -> Vec<(Term, Term)> {
    if family == "streams" {
        let seq = stream_sequence(num(get, "RULEMINER_SHUFFLE", 0));
        return residue(&seq, num(get, "RULEMINER_PHASE", 0), num(get, "RULEMINER_SKIP", 0), num(get, "RULEMINER_LAWS", 250));
    }
    family_laws(setup, family, get, 4, family_vars(family), 7).into_iter().map(|(_, a, b)| (a, b)).collect()
}
```

`write_laws` body becomes:

```rust
    let get = |k: &str| env.iter().rev().find(|(kk, _)| kk == k).map_or_else(|| setup.var(k).map(str::to_owned), |(_, v)| Some(v.clone()));
    let laws: Vec<(String, Term, Term)> = window(setup, family, &get).into_iter().map(|(a, b)| (String::new(), a, b)).collect();
    std::fs::write(path, laws_text(&laws)).unwrap();
    (var.to_string(), path.display().to_string())
```

Rename the driver's `fn stream_laws` to `window_laws` (and its caller in `served_laws`), its last line becoming
`window(setup, &cfg.family, &env)`; its doc "The laws a child of `cfg` takes at phase `phase`: `laws` of them from
`skip`, through the variables `run_loop` gives its children."

`Draw::grammar`: the cached value becomes, for `k.0 == "streams"`,
`residue(&stream_sequence(k.2), 0, 0, STREAM_EXTRAS)` and otherwise `grammar_laws(&k.0, k.1, k.2)`; the `GEN_LAWS`
line stays. Doc: "`grammar_laws` for `cfg`'s family, `deep3` and salt (the draw's), or for `streams` the first
`STREAM_EXTRAS` laws of phase 0 at that salt; generated once per sweep."

`sweep`'s `loop_cfgs`, its first line becomes
`let stride = if fam == "streams" { STREAM_STRIDE } else { LOOPS.iter().find(|l| l.0 == fam).unwrap_or_else(|| panic!("no loop stride for {fam}")).1 };`
(the streams' windows ignore `cfg.stride`; it is set only so the child env's `RULEMINER_STRIDE` is not the families').
Loop scopes filter their extras against their own served laws only (`also` is empty for them), so a `cold:streams`
sweep never builds a family sequence.

- [ ] **Step 4: Run the tests**

Run: `cargo test --release --test church_bv -j 4 -- driver:: search:: 2>&1 | grep -E "^test result|FAILED|panicked" | head`
Expected: 0 failed.

- [ ] **Step 5: One `cold:streams` sweep** (check CPU leases first)

```bash
cargo test --release --test church_bv --no-run -j 4 2>&1 | tail -1
x="$(ls -t target/release/build/tatic/*/out/church_bv-*.exe target/release/deps/church_bv-*.exe 2>/dev/null | head -1)"; cp "$x" "$TEMP/bv_p2_streams.exe"
powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind probe -Name cold-streams -Command "env MACHINE_STATE=0 SWEEP=cold:streams SALT=1 'SWEEP_OUT=%RUN_DIR%' '$(cygpath -w "$TEMP/bv_p2_streams.exe")' driver::sweep --exact --ignored --nocapture"
```
Expected: `STREAMS salt 1:` once (one generation, R1), `GEN ...: L <n> n <m>` with n near 0.16 L, three rows in
`$RUN_DIR/cold_streams.tsv` (`streams\t4-1`, `4-2`, `4-3`), every loop's `m.tsv` with 9 columns, a `CLASS_MEMO`
line in each task log. Note M per loop, wall and the generation's share. If the extras are short (`extras lists too
short`), stop: R2's cap needs a decision.

- [ ] **Step 6: Commit**

```bash
git add tests/church_bv/search.rs tests/church_bv/driver.rs docs/runs.md
git diff --cached --stat
printf 'driver: the streams as a loop family (cold:streams): phases are residue classes of one stream sequence per salt, extras from phase 0\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n' > "$TEMP/msg.txt"
git commit -q -F "$TEMP/msg.txt"
```

---

### Task 6: The held-out files (decision 10, R6)

**Files:**
- Modify: `tests/church_bv/classes.rs` (after `regenerate_key`)
- Create: `tests/church_bv/held_11.txt`, `tests/church_bv/held_13.txt` (written by the command)

**Interfaces:**
- Consumes: `search::{stream_sequence, residue}`.
- Produces: `pub const HELD_BANDS: [usize; 2] = [11, 13]`; `pub fn held_path(band: usize) -> std::path::PathBuf`;
  `pub fn parse_held(band: usize, text: &str) -> Result<Vec<(Term, Term)>, String>`;
  `pub fn held_laws(band: usize) -> Vec<(Term, Term)>`; ignored test `classes::regenerate_held`.

- [ ] **Step 1: Write the failing tests**

```rust
/// A held-out file's text reads back as its laws, and its header names this build's key and size.
#[test]
fn held_text_round_trips() {
    let laws = vec![(parse_term("add(x, y)"), parse_term("add(y, x)"))];
    let back = parse_held(11, &held_text(11, &laws)).unwrap();
    assert_eq!(back.len(), 1);
    assert!(back[0] == laws[0]);
}

/// Review Focus 2: a header for another key, size or band fails with the regeneration message.
#[test]
fn a_held_header_for_another_key_fails() {
    let e = parse_held(11, "held laws of size 11, class key fnv 0000000000000000, table size 9\n").unwrap_err();
    assert!(e.contains("regenerate_held"), "{e}");
    assert!(parse_held(13, &held_text(11, &[])).is_err());
}

/// Review Focus 2: the key's hash ignores line endings, so a CRLF checkout of the same key reads the same files.
#[test]
fn held_header_ignores_line_endings() {
    assert_eq!(text_hash(KEY_FILE), text_hash(&KEY_FILE.replace("\r\n", "\n").replace('\n', "\r\n")));
}

/// The committed held-out files match this build's key and size, and hold 1000 laws of their band each.
#[test]
fn held_files_match_the_key() {
    for band in HELD_BANDS {
        let laws = held_laws(band);
        assert_eq!(laws.len(), HELD_PER_BAND, "band {band}");
        assert!(laws.iter().all(|(a, b)| a.size().max(b.size()) == band), "band {band}");
    }
}
```

- [ ] **Step 2: Run them to see them fail**

Run: `cargo test --release --test church_bv -j 4 -- classes::held classes::a_held 2>&1 | grep -E "^error|cannot find" | head -3`
Expected: compile errors naming `parse_held`, `held_text`, `text_hash`.

- [ ] **Step 3: Implement** (classes.rs, after `regenerate_key`)

```rust
/// The held-out set's size bands (a law's band: its larger side's size), its laws per band, and its salt, which no
/// sweep salt or draw shift reaches (spec decision 10, plan R6).
pub const HELD_BANDS: [usize; 2] = [11, 13];
pub const HELD_PER_BAND: usize = 1000;
pub const HELD_SALT: usize = 7_777_777;
const REGENERATE_HELD: &str = "<exe> classes::regenerate_held --exact --ignored --nocapture";

/// FNV-1a 64 of a text's trimmed lines joined by `\n`: the same for any line endings.
fn text_hash(text: &str) -> u64 {
    let mut h = 0xcbf2_9ce4_8422_2325u64;
    for b in text.lines().map(str::trim).collect::<Vec<_>>().join("\n").bytes() {
        h = (h ^ b as u64).wrapping_mul(0x0100_0000_01b3);
    }
    h
}

fn held_header(band: usize) -> String {
    format!("held laws of size {band}, class key fnv {:016x}, table size {SIZE}", text_hash(KEY_FILE))
}

/// A held-out file's text: its header, then `lhs = rhs` lines.
pub fn held_text(band: usize, laws: &[(Term, Term)]) -> String {
    let mut s = held_header(band) + "\n";
    for (a, b) in laws {
        s += &format!("{} = {}\n", a.show(), b.show());
    }
    s
}

/// `tests/church_bv/held_<band>.txt`.
pub fn held_path(band: usize) -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(format!("tests/church_bv/held_{band}.txt"))
}

/// A held-out file's laws; an error when its header is not this build's (another key, size or band).
pub fn parse_held(band: usize, text: &str) -> Result<Vec<(Term, Term)>, String> {
    let mut lines = text.lines().map(str::trim).filter(|l| !l.is_empty());
    let head = lines.next().unwrap_or("");
    if head != held_header(band) {
        return Err(format!("held-out header {head:?} is not {:?}: regenerate the held-out files ({REGENERATE_HELD})", held_header(band)));
    }
    Ok(lines.filter_map(|l| l.split_once(" = ")).map(|(a, b)| (parse_term(a), parse_term(b))).collect())
}

/// The committed held-out laws of `band`; a file for another key fails the process.
pub fn held_laws(band: usize) -> Vec<(Term, Term)> {
    let text = std::fs::read_to_string(held_path(band)).unwrap_or_else(|e| panic!("{}: {e} ({REGENERATE_HELD})", held_path(band).display()));
    parse_held(band, &text).unwrap_or_else(|e| panic!("{e}"))
}

/// Regenerates `held_11.txt` and `held_13.txt` (spec decision 10): the stream sequence at `HELD_SALT`, laws salt 1's
/// loops serve dropped (phases 1-3, their first 300 laws: the gate's first salt; counted), each band's first
/// `HELD_PER_BAND` laws in sequence order (round-robin over the streams). Run when the key or the table's size changes.
#[test]
#[ignore]
fn regenerate_held() {
    let seq = crate::search::stream_sequence(HELD_SALT);
    let s1 = crate::search::stream_sequence(1);
    let served: hashbrown::HashSet<(Term, Term)> = (1..=3).flat_map(|p| crate::search::residue(&s1, p, 0, 300)).collect();
    for band in HELD_BANDS {
        let all: Vec<(Term, Term)> = seq.iter().filter(|(a, b)| a.size().max(b.size()) == band).cloned().collect();
        let overlap = all.iter().filter(|l| served.contains(l)).count();
        let laws: Vec<(Term, Term)> = all.iter().filter(|l| !served.contains(l)).take(HELD_PER_BAND).cloned().collect();
        assert_eq!(laws.len(), HELD_PER_BAND, "band {band}: {} laws in the band", all.len());
        std::fs::write(held_path(band), held_text(band, &laws)).unwrap();
        println!("HELD {band}: {} of {} laws in the band; {overlap} served by salt 1's loops, dropped", laws.len(), all.len());
    }
}
```

- [ ] **Step 4: Run the format tests**

Run: `cargo test --release --test church_bv -j 4 -- classes::held_text classes::a_held classes::held_header 2>&1 | grep -E "^test |panicked" | head`
Expected: 3 passed (`held_files_match_the_key` fails until Step 5 writes the files).

- [ ] **Step 5: Write the files** (check CPU leases first; about 3-4 min: two sequences)

```bash
cargo test --release --test church_bv --no-run -j 4 2>&1 | tail -1
x="$(ls -t target/release/build/tatic/*/out/church_bv-*.exe target/release/deps/church_bv-*.exe 2>/dev/null | head -1)"; cp "$x" "$TEMP/bv_p2_held.exe"
powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind probe -Name held-regen -Command "'$(cygpath -w "$TEMP/bv_p2_held.exe")' classes::regenerate_held --exact --ignored --nocapture"
```
Expected: two `HELD` lines, each `1000 of <n>` with the overlap count. An overlap over 5% of a band is material:
record it and stop for a decision (spec, Risks). Then
`cargo test --release --test church_bv -j 4 -- classes:: 2>&1 | grep -E "^test result|FAILED"`: 0 failed.

- [ ] **Step 6: Commit**

```bash
git add tests/church_bv/classes.rs tests/church_bv/held_11.txt tests/church_bv/held_13.txt docs/runs.md
git diff --cached --stat
printf 'classes: the past-domain held-out files (decision 10): 1000 open laws per band 11 and 13 from the streams at a held-out salt, headers checked against the key; run <id>, overlap <a>/<b>\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n' > "$TEMP/msg.txt"
git commit -q -F "$TEMP/msg.txt"
```

---

### Task 7: The new gate and its A/A baseline (spec §9, R7)

**Files:**
- Create: `scripts/streams_ab.sh`
- Modify: `docs/runs.md`, `docs/tier-cycle.md`, `PARKED.md` (memo entry evidence), `ROADMAP.md` (if it names the old gate)

**Interfaces:**
- Consumes: `cold:streams` (Task 5), `held_11.txt`/`held_13.txt` (Task 6), `CLASS_MEMO` lines (Task 2).
- Produces: `scripts/streams_ab.sh <exe A> <exe B> <salts...>`, whose last line is
  `streams_ab: rules same in <x> of <y> loops; <f> of <n> arms failed`, with per-salt lines
  `salt <s>: M A <a> B <b>; held A <ha> B <hb>; jobcpu A <ca> B <cb>` and per-arm totals.

- [ ] **Step 1: Write the script**

```bash
# streams_ab.sh <exe A> <exe B> <salts...>: the gate on the streams (spec §9). Per salt, SWEEP=cold:streams (extras
# on, 2 lanes, 6 scoring workers) with A and B, A first on odd salts and B first on even ones, each a `runs run` (job
# CPU and wall) into $RUN_DIR/s<salt>_<A|B>; a watchdog stops an exe past 8 GB. Then per loop the held-out M under the
# loop's final rules (tests/church_bv/held_{11,13}.txt, CHECK_FAST: the laws that still need a whole-term machine
# proof). Per salt: M, held-out M and job CPU of each arm, and whether each loop's rules agree; per arm the totals, the
# lookup memo's peak (CLASS_MEMO) and the largest peakproc. Last line: loops with the same rules, and arms that failed
# (non-zero exit or no M); exits 1 if any arm failed. Differing rules are reported, not failed.
a=$1; b=$2; shift 2
root="$(cd "$(dirname "$0")/.." && pwd)"
runs="$root/tools/runs/target/release/runs.exe"
[ -x "$runs" ] || { echo "streams_ab: $runs not built (cargo build --release in tools/runs)"; exit 1; }
failed=0; same_n=0; loops=0
held() { # <exe> <rules file>: held-out M over both bands
  local m=0 band line p f n
  for band in 11 13; do
    line=$(MACHINE_STATE=0 CHECK_FAST=1 CHECK_FAMILY=streams "CHECK_RULES=$(cygpath -w "$2")" "CHECK_LAWFILE=$(cygpath -w "$root/tests/church_bv/held_$band.txt")" "$1" search::rule_set_kernel_check --exact --ignored --nocapture < /dev/null 2>&1 | grep '^CHECKED ')
    p=$(echo "$line" | sed -E 's/^CHECKED ([0-9]+) .*/\1/'); f=$(echo "$line" | sed -E 's/.*\(([0-9]+) with.*/\1/'); n=$(echo "$line" | sed -E 's/.*\), ([0-9]+) not proved.*/\1/')
    [ -n "$line" ] || { echo "held: no CHECKED line for $2 band $band" >&2; echo x; return; }
    m=$((m + p - f + n))
  done
  echo $m
}
for s in "$@"; do
  [ $((s % 2)) = 1 ] && order="A B" || order="B A"
  for arm in $order; do
    [ $arm = A ] && exe=$a || exe=$b
    name=$(basename "$exe" | sed 's/\.[Ee][Xx][Ee]$//'); o="$RUN_DIR/s${s}_$arm"; mkdir -p "$o"; rm -f "$o/exit"
    ( "$runs" run "$(cygpath -w "$o")" -- MACHINE_STATE=0 SWEEP=cold:streams SALT=$s "SWEEP_OUT=$(cygpath -w "$o")" "$exe" driver::sweep --exact --ignored --nocapture < /dev/null > "$o/result.txt" 2>&1; echo $? > "$o/exit" ) &
    while [ ! -f "$o/exit" ]; do
      mb=$(powershell -NoProfile -Command "[int]((Get-Process $name -EA 0 | Measure-Object WorkingSet64 -Sum).Sum/1MB)" < /dev/null | tr -d '\r')
      [ "${mb:-0}" -gt 8192 ] && { echo "salt $s $arm: over 8 GB ($mb MB), stopped"; taskkill //F //IM "$name.exe" > /dev/null; }
      ping -n 6 127.0.0.1 > /dev/null
    done
    echo "salt $s $arm: exit $(cat "$o/exit") $(tail -1 "$o/result.txt")"
    [ "$(cat "$o/exit")" = 0 ] && cut -f4 "$o/cold_streams.tsv" 2>/dev/null | grep -qE '^[0-9]+$' || failed=$((failed + 1))
    h=0
    for l in 1 2 3; do v=$(held "$exe" "$o/cold_streams_streams_${l}_none/rules.txt"); [ "$v" = x ] && failed=$((failed + 1)) || h=$((h + v)); done
    echo $h > "$o/held.txt"
  done
  for l in 1 2 3; do
    f="cold_streams_streams_${l}_none/rules.txt"
    cmp -s "$RUN_DIR/s${s}_A/$f" "$RUN_DIR/s${s}_B/$f" && same_n=$((same_n + 1)) || echo "salt $s loop $l: rules differ"
    loops=$((loops + 1))
  done
  m() { cut -f4 "$RUN_DIR/s${s}_$1/cold_streams.tsv" 2>/dev/null | grep -E '^[0-9]+$' | awk '{s += $1} END {print s + 0}'; }
  c() { grep -oE 'jobcpu=[0-9.]+' "$RUN_DIR/s${s}_$1/result.txt" | cut -d= -f2; }
  echo "salt $s: M A $(m A) B $(m B); held A $(cat "$RUN_DIR/s${s}_A/held.txt") B $(cat "$RUN_DIR/s${s}_B/held.txt"); jobcpu A $(c A) B $(c B)"
done
for arm in A B; do
  m=0; h=0
  for s in "$@"; do
    for v in $(cut -f4 "$RUN_DIR/s${s}_$arm/cold_streams.tsv" 2>/dev/null | grep -E '^[0-9]+$'); do m=$((m + v)); done
    h=$((h + $(cat "$RUN_DIR/s${s}_$arm/held.txt" 2>/dev/null || echo 0)))
  done
  memo=$(grep -rh '^CLASS_MEMO' "$RUN_DIR"/s*_$arm 2>/dev/null | awk '{if ($2 > x) x = $2} END {print x + 0}')
  peak=$(grep -h -oE 'peakproc=[0-9]+' "$RUN_DIR"/s*_$arm/result.txt 2>/dev/null | cut -d= -f2 | sort -n | tail -1)
  echo "total $arm: M $m; held $h; $(cat "$RUN_DIR"/s*_$arm/result.txt | grep -oE '(wall|jobcpu)=[0-9.]+' | awk -F= '{t[$1]+=$2} END {printf "wall %.0f s, job cpu %.0f s", t["wall"], t["jobcpu"]}'); memo peak $memo terms; peakproc max $peak"
done
echo "streams_ab: rules same in $same_n of $loops loops; $failed of $(($# * 2)) arms failed"
[ $failed = 0 ]
```

The patterns match `runs run`'s summary line (`wall=12.3s jobcpu=10.41s ... peakproc=279MB`, `tools/runs/src/main.rs:173`)
and the checker's `CHECKED {proved} laws kernel-checked ({free} with no whole-term machine proof), {none} not proved, ...`
(`search.rs`, `rule_set_kernel_check_task`).

- [ ] **Step 2: Time the held-out M once** (check CPU leases first)

On Task 5's sweep output (`cold_streams_streams_1_none/rules.txt` in its run folder):
```bash
time (MACHINE_STATE=0 CHECK_FAST=1 CHECK_FAMILY=streams "CHECK_RULES=<that rules.txt, Windows path>" "CHECK_LAWFILE=$(cygpath -w tests/church_bv/held_11.txt)" "$TEMP/bv_p2_held.exe" search::rule_set_kernel_check --exact --ignored --nocapture < /dev/null 2>&1 | grep -E '^(CHECKED|JOINED)')
```
Expected: a `CHECKED` line over at most 1000 laws. Note the time: the gate pays it 6 times per arm per salt. If it is
over 2 min, record it and stop for a decision (a smaller held-out sample, or held-out M on fewer loops).

- [ ] **Step 3: Check the script on one salt** (A/A, the Task 6 exe both arms)

```bash
w() { cygpath -w "$1"; }
cp "$TEMP/bv_p2_held.exe" "$TEMP/bv_p2_gate.exe"
powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind gate -Timed -HoldMin 45 -Name streams-gate-check -Command "bash scripts/streams_ab.sh '$(w "$TEMP/bv_p2_held.exe")' '$(w "$TEMP/bv_p2_gate.exe")' 1"
```
Expected: `0 of 2 arms failed`, a `salt 1:` line with numbers in every field, two `total` lines.

- [ ] **Step 4: Commit the script**

```bash
git add scripts/streams_ab.sh docs/runs.md
git diff --cached --stat
printf 'scripts: streams_ab.sh, the gate on the streams (spec §9): cold:streams A/B per salt plus held-out M under each loop'"'"'s rules, memo peak and peakproc\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n' > "$TEMP/msg.txt"
git commit -q -F "$TEMP/msg.txt"
```

- [ ] **Step 5: The A/A baseline on salts 1-10** (five chunks, R7; check leases before each)

Rebuild at this commit and copy to `bv_aa_A.exe` and `bv_aa_B.exe` (same binary), then for each chunk `1 2`, `3 4`,
`5 6`, `7 8`, `9 10`:
```bash
powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind gate -Timed -HoldMin 45 -Name streams-aa-<first>-<last> -Command "bash scripts/streams_ab.sh '$(w "$TEMP/bv_aa_A.exe")' '$(w "$TEMP/bv_aa_B.exe")' <first> <last>"
```
Expected per chunk: `0 of 4 arms failed`. Rules may differ between A and B (the miner's parallel choices); record how
many loops agree.

- [ ] **Step 6: The spread, recorded**

From the five chunks' `salt <s>:` lines, compute per salt the relative difference |B - A| / mean for M, held-out M and
job CPU, and their maximum over salts 1-10: that maximum is the spread decision 9's "costs nothing" uses. Record in
`docs/tier-cycle.md` a section "*The gate on the streams and its A/A baseline (<date>; plan
docs/superpowers/plans/2026-10-23-class-table-phase-2.md; runs <ids>)*": the sequence's size and generation time, held-
out M's cost per loop, M / held-out M / job CPU per salt and arm, the three spreads, the memo's peak and the largest
`peakproc` (against Task 3's), rules agreement, and the overlap Task 6 reported. In `PARKED.md`, "Bound the class
table's lookup memo": add the peak on laws past the domain to its evidence; if the largest `peakproc` exceeds Task 3's
by more than 150 MB, its trigger has fired: stop for a decision. Grep `ROADMAP.md`, `PARKED.md`, `README.md` and the
spec for "salts_ab" or "cold:cmp3d" named as *the* gate and point them at `scripts/streams_ab.sh` (historical rows stay).

```bash
git add docs/tier-cycle.md docs/runs.md PARKED.md
git diff --cached --stat
printf 'runs: the streams gate'"'"'s A/A baseline on salts 1-10 (<ids>): spread M <x>%%, held-out M <y>%%, job cpu <z>%%; memo peak <n>\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n' > "$TEMP/msg.txt"
git commit -q -F "$TEMP/msg.txt"
```
(Add `ROADMAP.md`, `README.md` or the spec if they changed.)

---

### Task 8: The families deleted from the law path (spec §10)

**Files:**
- Modify: `tests/church_bv/search.rs`, `tests/church_bv/driver.rs`, `tests/church_bv/miner.rs`, `tests/church_bv/classes.rs`
- Delete: `docs/runs/2026-10-23/fixtures/held/` (spec §10)

**Interfaces:**
- Consumes: everything from Tasks 4-7.
- Produces: `family_vars(f) = 3` only for `streams`; `family_laws` with branches `shl`, `shr`, `lt`, `mul` and a panic
  for any other name (R9); the driver serving only `cold:streams`; `LoopCfg` without `family`, `stride`, `deep3`, `split`.

Build first with `$TEMP/bv_p2_before.exe` = the exe at Task 7's commit (copy `bv_aa_A.exe`), for Task 10's A/B.

- [ ] **Step 1: `search.rs`, the families' law code**

Delete: `THREE_VAR_FAMILIES`; `pool3`; `add3_pool`, `cmp3_pool`, `depth2_pool`, `depth1` (keep `leaves3` and `mk`:
`stream_laws` uses them); `pool3_sequence`; `shape_part`; `grammar_laws`, `GEN_TERMS`, `grammar_sample`; in
`family_laws` the `u3w` branch and the pool3 branch (`else if let Some(seq) = pool3_sequence(...)`), and make its last
branch explicit:

```rust
    } else if family == "mul" {
        mul_laws(max)
    } else {
        panic!("family {family}: three-variable laws come from stream law files (RULEMINER_LAWFILE, CHECK_LAWFILE)")
    }
```

`family_vars` becomes `if family == "streams" { 3 } else { 2 }` with doc "Variables of a law family: three for the
streams (their laws come through law files), two for `family_laws`' own." `check_laws`: `CHECK_FAMILY` defaults to
`"streams"`; `CHECK_RULES` optional:
`let text = job.setup().var("CHECK_RULES").map(|f| std::fs::read_to_string(f).unwrap()).unwrap_or_default();`
(update its doc: "the `CHECK_RULES` (none when unset)").

Delete the tests: `u3w_window_is_an_equal_mix`, `family_law_windows_tile_the_sequence`, `family_law_shape_halves_partition`
and its helper `shape_halves_partition`, `family_laws_takes_the_shape_salt_from_its_env`, `shape_salt_changes_the_split`,
`family_law_phases_are_disjoint`, `pools_have_no_repeated_terms`, `grammar_laws_lie_outside_the_pool`,
`grammar_laws_have_no_padding`, `normalize_finds_the_probes_twins` (R11), `hidden_twins_in_a_run`.
Rewrite: `shuffle_is_a_fixed_permutation` on laws built in the test, `(0..50).map(|i| (Term::v(0), (0..i).fold(Term::v(1), |t, _| Term::op(ADD, t, Term::v(2)))))`
in place of add3's; `law_windows_survive_a_law_file` on family `lt` only (`RULEMINER_LAWS` 60, no `SKIP`; assert 60
laws if `lt` yields that many, else its count); `show_cmp_is_the_text_order` on the first 2000 of
`Classes::get().reps()` sorted by `show()` in place of `pool3("cmp3d")`.

- [ ] **Step 2: `driver.rs`, one law source**

Delete: `MINES`, `LOOPS`, `served_by_loops` and `ref_mines_filter_against_every_loop_family`, `Draw` (R10), and in
`sweep`: `library`, `mines_warm`, `ref_cfg`, `srcs`, the `mines` and `pooled` stage branches, the ref mines' `also`
list (`loops`). `stage_fams` accepts only `cold` (default fams `streams`) and `cold:streams`, any other stage panicking
`unknown stage {stage}: the sweep runs cold:streams (spec §10)`. `loop_cfgs(stage, fam)` builds three `loop` configs,
phases 1-3, warm `None`, out dir `{stage with ':'->'_'}_streams_{p}_none` (the name Task 7's script reads), and the tsv
row keeps its format (`streams\t4-<p>\tfrom_none\t...`). `scope_extras(setup, scope)`: extras are
`residue(&stream_sequence(salt + 1000 * GEN_DRAW), 0, 0, STREAM_EXTRAS)` with `salt` = the scope's `RULEMINER_SHUFFLE`
(through `cfg_var`), filtered against the scope's served laws.

`LoopCfg`: delete `family`, `stride`, `deep3`, `split`; `from_env` stops reading `FAMILY`, `STRIDE`, `DEEP3`,
`SPLIT`. `window` loses its `family` parameter and its `family_laws` branch (streams only); `write_laws(setup, env,
path, var)`. `run_loop`'s common env: `RULEMINER_FAMILY` and `CHECK_FAMILY` = `streams`; drop `RULEMINER_DEEP3`,
`RULEMINER_STRIDE`, `RULEMINER_SHAPE`; keep `RULEMINER_PHASE` (the parent's window reads it from the child env it
builds). Update the module doc (driver.rs:1-45): stages, `FAMILY`, `MINES_WARM` and the pooled files go; the laws
come from `search::stream_sequence` (spec §9).

- [ ] **Step 3: `miner.rs` and `classes.rs`**

`miner.rs`: the doc lines naming `RULEMINER_SHAPE*` (about line 20) and `RULEMINER_FAMILY`'s families (about line 41):
say three-variable laws come through `RULEMINER_LAWFILE` (family `streams`). `classes.rs`: `held_out_replacements_prove`
reads `held_laws(11)` and `held_laws(13)` in place of the fixture directory; since those laws are open by construction,
it collects the replacements `walk` makes on both sides of every law, and for each pair `(u, r)` with a verdict
compiles the law `u = r` from `step`'s plan to a checked proof (`law_proof(job, 4, 3, &u, &r, &plan)`, then
`job.lemmas.ck`); its output line counts replacements, verdicts by prover and proofs checked. Update its doc. Then:

```bash
git rm -r -q docs/runs/2026-10-23/fixtures/held
grep -rn "fixtures/pad_1" docs README.md | head -3
```
If the grep finds nothing, `git rm -r -q docs/runs/2026-10-17/fixtures/pad_1` too (R11).

- [ ] **Step 4: Compile, then let the dead-code warnings name the rest**

Run: `cargo test --release --test church_bv --no-run -j 4 2>&1 | grep -E "^(error|warning)" -A3 | head -60`
Expected: no errors. For each `never used` warning on an item only the deleted code used (for example `num`'s other
callers, `laws_text`, `pool_conjectures`, `lt_pool`, `shl_conjectures`, `terms`, `twin_key`): keep it if any caller
remains, delete it if none. Any warning outside `search.rs`, `driver.rs`, `miner.rs`, `classes.rs`: report it, do not
delete.

- [ ] **Step 5: Run the suite and the deletion check**

Run: `cargo test --release --test church_bv -j 4 2>&1 | grep -E "^test result|FAILED|panicked" | head`
Expected: 0 failed.
Run: `grep -nE "pool3|THREE_VAR_FAMILIES|grammar_sample|grammar_laws|GEN_TERMS|served_by_loops|MINES_WARM|\bMINES\b|\bLOOPS\b|shape_part|RULEMINER_SHAPE|RULEMINER_DEEP3|u3w|add3|sbo3|mix3|cmp3d" tests/church_bv/*.rs | grep -v "^\S*:\s*//" | head`
Expected: only comments that cite run records or docs (rewrite into present terms where a comment describes code that
is gone).

- [ ] **Step 6: Commit**

```bash
git add -A tests/church_bv docs/runs/2026-10-23/fixtures docs/runs/2026-10-17/fixtures
git diff --cached --stat
printf 'church_bv: the families deleted from the law path (spec §10): pools, family sequences, shape halves, the grammar generator, MINES/LOOPS and ref mines; the sweep serves cold:streams; held_out_replacements_prove on the held-out files\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n' > "$TEMP/msg.txt"
git commit -q -F "$TEMP/msg.txt"
```
Check that `git diff --cached --stat` lists nothing under `.claude/worktrees`, `tests/ring_*` or `.superpowers`.

---

### Task 9: What only the families used: pooled libraries, `RULESET`, yield code, `tools/runs`, README

**Files:**
- Modify: `tests/church_bv/rewrite.rs` (`library_sections` ~1570, `drop_units` ~1645, `joinability_units` ~1661,
  `units_text` ~1674, their test ~1683; `build_rule_set` 1467-1481 and its use at 1517; `law_time` ~4262)
- Modify: `tests/church_bv/miner.rs` (`prefs`/`units` config 53-56 and 80-81, `prefs_phase` ~1039-1076 and its call
  ~136, module doc line 3), `tests/church_bv/job.rs` (`rule_set` field and accessor 25, 92-94; `ablated` doc),
  `tests/church_bv/search.rs` (`proposal_yield` ~1926-1998, `promoted_rule_sets_are_proved` ~1553)
- Delete: `scripts/data/add3_mm_rules.txt`, `mix3_mm_rules.txt`, `add3_nl_rules.txt`, `mix3_nl_rules.txt`,
  `docs/runs/2026-10-12/scripts/cmp3d_own_rules.txt`
- Modify: `tools/runs/src/time.rs` (`sweep_arms` 77, `pcs_arms` 83-92, test ~445), `tools/runs/src/main.rs:132`, `README.md`

**Interfaces:**
- Produces: `tools/runs` `--sweep` arms run `SWEEP=cold:streams`; `--pcs` arms run `proof_cost_split` on
  `tests/church_bv/held_11.txt` with no mined rules (`pcs_arms(root: &Path, ...)`, root = the checkout).

- [ ] **Step 1: Pooled libraries and the preference phase**

Delete `library_sections`, `drop_units`, `joinability_units`, `units_text`, `drop_units_are_the_rules_meeting_another_library`
(rewrite.rs), and in miner.rs the `prefs` and `units` fields, their reads, `prefs_phase` and its call; the module doc
drops "the preference phase (`prefs_phase`)". Preferences themselves (`parse_prefs`, `OVER` lines, `base_prefs`) stay:
they are read from any rules file. If any deleted function has a caller outside the pooled stage and `prefs_phase`,
stop and report it.

- [ ] **Step 2: `RULESET` and the family rule files**

Delete `build_rule_set`, the `all.extend(setup.rule_set()...)` line in `build_fixed_rules` (and "the `RULESET` rules"
in its doc), `Setup::rule_set` and its field and initializer, `promoted_rule_sets_are_proved`, and the four
`scripts/data/*_rules.txt` files (`git rm`). In the `ablated` doc drop `ruleset`. Delete `law_time` (rewrite.rs) and
`docs/runs/2026-10-12/scripts/cmp3d_own_rules.txt` (`git rm`).

- [ ] **Step 3: The yield code**

Delete `proposal_yield`; then let the compiler's dead-code warnings name what only it used (`classify_proposals`,
`mutate_laws`, the n-gram proposer), deleting each only if no caller remains (`proposal_credit_report` may use some).
`proof_cost_split` and `proposal_credit_report` docs: "laws from `CHECK_LAWFILE` (required: the streams' laws come
through files)".

- [ ] **Step 4: `tools/runs`**

`sweep_arms`: `("SWEEP", "cold:streams")`. `pcs_arms(root: &Path, ...)` with base env
`CHECK_FAMILY=streams`, `CHECK_LAWFILE=<root>\tests\church_bv\held_11.txt`, no `CHECK_RULES`, no `RULEMINER_LAWS`;
doc: "`proof_cost_split` on the held-out band 11 (1000 laws) with no mined rules". `main.rs:132` passes `&checkout()?`.
The test `pcs_arms_from_one_exe_or_two`: assert the `CHECK_LAWFILE` pair
(`r"C:\s\tests\church_bv\held_11.txt"`) in place of `CHECK_RULES`.
Run: `cd tools/runs && cargo test --release -j 4 2>&1 | grep -E "^test result|FAILED" | head -3`
Expected: 0 failed.

- [ ] **Step 5: README and docs wording**

`README.md` (about lines 75-160): replace the families and sweep-stage text with the streams (`stream_sequence`,
`cold:streams`, the held-out files, `scripts/streams_ab.sh`), linking the spec §9 rather than restating it. Grep
`ROADMAP.md`, `PARKED.md`, `docs/learned-vs-fixed.md` and `CLAUDE.md` for `pool3`, `u3w`, `mines own cold`,
`MINES_WARM`, `RULESET`, `proposal_yield`: fix text that describes current code (entries about deleted code become
`decided against` or are deleted, per VERSIONING.md); leave run records.

- [ ] **Step 6: Run the suite and commit**

Run: `cargo test --release --test church_bv -j 4 2>&1 | grep -E "^test result|FAILED|panicked" | head`
Expected: 0 failed, no `never used` warning left from these deletions.

```bash
git add -A tests/church_bv scripts/data docs/runs/2026-10-12/scripts tools/runs/src README.md ROADMAP.md PARKED.md docs/learned-vs-fixed.md
git diff --cached --stat
printf 'church_bv: what only the families used, deleted: pooled libraries and the preference phase, RULESET and its rule files, the yield proposers, law_time; tools/runs arms on cold:streams and the held-out file\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n' > "$TEMP/msg.txt"
git commit -q -F "$TEMP/msg.txt"
```

---

### Task 10: The gate after the deletion, and the close-out

**Files:**
- Modify: `docs/runs.md`, `docs/tier-cycle.md`, `docs/learned-vs-fixed.md`, `ROADMAP.md`, `PARKED.md`, this plan,
  the spec

- [ ] **Step 1: A/B before and after the deletion** (Review Focus 5; check leases first)

```bash
cargo test --release --test church_bv --no-run -j 4 2>&1 | tail -1
x="$(ls -t target/release/build/tatic/*/out/church_bv-*.exe target/release/deps/church_bv-*.exe 2>/dev/null | head -1)"; cp "$x" "$TEMP/bv_p2_after.exe"
w() { cygpath -w "$1"; }
powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind gate -Timed -HoldMin 45 -Name streams-deletion-1-2 -Command "bash scripts/streams_ab.sh '$(w "$TEMP/bv_p2_before.exe")' '$(w "$TEMP/bv_p2_after.exe")' 1 2"
```
Expected: `0 of 4 arms failed`; M and held-out M equal per salt, and rules same in as many loops as the A/A agreed on
those salts (Task 7). A loop whose M differs beyond the A/A spread means the deletion changed behavior: find why
before closing (likely the child env Task 8 dropped).

- [ ] **Step 2: Close-out docs**

`docs/runs.md`: the row's headline and notes. `docs/tier-cycle.md`: one paragraph "The families deleted (<date>, run
<id>)" under the gate section of Task 7: what went (link the spec §10), the A/B result. `docs/learned-vs-fixed.md`:
the law source row (hand-written family pools → learned table's representatives grown per operator set). `ROADMAP.md`
v0.5: "the class-table spec's decision 11 moves the loops onto operator-set streams" becomes present tense ("the loops
run on operator-set streams"). `PARKED.md`: entries whose trigger or evidence names a deleted family or stage
("Transfer to families...", anything citing `MINES_WARM`, `u3`, `pooled`): mark `decided against` with "families
deleted (spec decision 11)" or rewrite the trigger onto the streams; add parked items for anything this plan left
(R2's extras cap to revisit; held-out M's cost if Task 7 found it high). Spec: build steps 4-6 marked done in its
Build order ("Steps 1-6 are done (plans ... and docs/superpowers/plans/2026-10-23-class-table-phase-2.md)"); status
stays `active` (steps 7-8 remain). This plan: `status: done`.

```bash
git add docs/runs.md docs/tier-cycle.md docs/learned-vs-fixed.md ROADMAP.md PARKED.md docs/superpowers/plans/2026-10-23-class-table-phase-2.md docs/superpowers/specs/2026-10-22-class-table-normal-form-design.md
git diff --cached --stat
printf 'runs: the families'"'"' deletion gated (<id>): cold:streams unchanged; plan done, spec steps 4-6 done\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n' > "$TEMP/msg.txt"
git commit -q -F "$TEMP/msg.txt"
```

- [ ] **Step 3: Leftovers**

`Get-Process church_bv*, bv_*, python -EA 0`: none of this plan's processes left. `git status --short`: only the
untracked files the constraints name.
