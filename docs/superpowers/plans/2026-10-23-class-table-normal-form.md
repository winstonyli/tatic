---
status: draft
---

# The class table in the rewriter, build steps 1-3 Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build the learned class table as a module of `church_bv` (key file, table, proved replacements), move the
law generator's twin filter onto it, and enter it as a step of `prove_eq` (phase 1), each gated.

**Architecture:** One new module, `tests/church_bv/classes.rs`, holds the key file's format, the table's build from a
key, lookup (`rep`, `canonical`), the replacements' verdicts and proofs (`step`, `normalize`), and the key's
regeneration. The key is baked into the binary (`include_str!`), so the table is a pure function of the source and
each process builds it once (`Classes::get`). `search::ClassReps` is deleted; its twin key moves onto `canonical`.
`prove_eq` gains one step after the per-position step, switched off by `ABLATE=classes`.

**Tech Stack:** Rust (the `church_bv` test binary), mimalloc, the kernel (`tatic::kernel`), bash scripts under
`docs/runs/<date>/scripts/`, `~/.claude/runs/run.ps1`, `tools/runs` (via `salts_ab.sh`).

**Spec:** `docs/superpowers/specs/2026-10-22-class-table-normal-form-design.md` (approved 2026-10-23). This plan covers
its build steps 1-3. Steps 4 (phase 2 in `rewrite`, ablations) and 5 (phase 3, mining on the residue) depend on
phase 1's gate and get their own plan afterwards.

## Rulings this plan makes inside the spec

Each is stated here once; tasks cite them by number.

- **R1. The key file is baked in** with `include_str!("class_key.txt")`: the table is then a pure function of the
  source (`job::hidden_state_is_classified`), a worker cannot read a different key than its build was tested with, and
  regenerating means rebuilding. The spec's "read from the key file" is met at compile time.
- **R2. A verdict's law is over the pair's own variables.** For `u -> r`, `kv = 1 + max(u.max_var(), r.max_var())`;
  each `shr1` node (outermost) becomes `V(kv + i)`, the same on both sides; the law's arguments are `V(0..kv)` then the
  atoms. The verdict memo is keyed by `(n, CARRY_CAP, u, r)` (the spec's `(u, r, n, k)`: `k` is fixed by `u` and `r`;
  `tree_encoding` reads `CARRY_CAP` before its own memo, so the cap is part of the key). A replacement is used only when
  `r.max_var() < k`, the context's variable count (a two-variable family never receives a `z`).
- **R3. The `Bitwise` verdict** for a pair with neither `add`, `sub` nor `lt` is decided as `prove_eq`'s per-position
  step does: agreement on every input at widths 1..=5. One check covers pairs with and without shifts (the truth table
  is its width-1 case). Otherwise the verdict is `Tree` when `tree_encoding` finds an encoding over atoms, else unusable.
- **R4. Lookup uses one `ValueMemo<u8>` per key width**, behind one lock in the table, so `ValueMemo::new` becomes
  `pub`. The build keeps its own flat value rows (all widths end to end), dropped when it returns, as the spec says.
  Both hash the same flat bytes (`class_hash`).
- **R5. Process-wide state:** the table is a `static CLASSES: OnceLock<Classes>`, listed in `hidden_state_is_classified`
  (`PROCESS_WIDE`); the verdicts are a `SharedMemo` (no listing needed).
- **R6. The count of decision 2** is `Job::table_steps`, the distinct `(u, r)` pairs `step` returned with a proof in the
  task. The kernel-check task records it as `classes`, and the driver appends it to `m.tsv` as a ninth column (last, so
  `runs cmp`'s cut of field 5 and older scripts' first eight fields are unchanged).
- **R7. The twin filter** uses `Classes::canonical` (bottom-up `rep`, no proof) through a free function
  `search::twin_key(a, b)` with `ClassReps::key`'s renamings and kept roots; `ClassReps`, `Draw::reps` and the
  per-family pools it built are deleted.
- **R8. The key's refuter** checks, in order: 4096 pseudo-random width-8 inputs, every width-4 input, every width-3
  input (spec §2: new), then the screen's 204 width-8 inputs (`Term::counterexample`).
- **R9. `mi_collect` after a build** is decided by Task 4's measurement: kept (one `extern "C"` call in `Classes::get`)
  only if the commit after a build in a sweep-like process (`MIMALLOC_ALLOW_LARGE_OS_PAGES=0`) drops by at least 50 MB
  with it.

## Global Constraints

- Table: terms over x, y, z, 0 and -1, operators in this order: `add and or xor sub shl1 shr1 lt`; `shl1` and `shr1`
  enumerated only with second operand `0`; size 9 (`SIZE`); `lt` a second sort no operator takes (spec, decisions 3, 4).
- A class's representative is its smallest member `Machine::parse` takes, else its smallest (decision 7).
- Key file `tests/church_bv/class_key.txt`: header `ops add and or xor sub shl1 shr1 lt size 9`, then one input per
  line `<width> <x> <y> <z>`; a header mismatch fails the process with a message naming `classes::regenerate_key`; no
  fallback (spec §2).
- Replacements are used only with a proof at the job's width `n` (4 in the loops); an unusable one is not used and is
  printed once per process as `CLASS_UNUSABLE <u> = <r>`; the key never changes during a run (decision 6).
- M is unchanged in meaning; table replacements are counted apart (decision 2).
- Ablation name `classes` (spec §4).
- No compatibility shims: `ClassReps` is deleted, not kept beside the new filter.
- Builds: `cargo ... -j 8`; one cargo per target dir (if another session is building in `target/`, wait or use
  `CARGO_TARGET_DIR=$LOCALAPPDATA/tatic-target-probe`). At most 12 busy threads.
- Long or cited runs go through `powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1"` (gates with
  `-Timed`); the row's headline (no `|`) and notes are filled in after. Before any run over 30 s, check
  `%LOCALAPPDATA%\cpu-leases\*.json` for a live exclusive lease. Never stop another session's job.
- Never let python read stdin (write the script to a file, run `python -P f.py < /dev/null`); no fixed sleeps; no
  `tail -F`. Never `sed -i` a repo file (CRLF files get rewritten): use the Edit tool, then check `git diff --stat`.
- Commit on `rule-generality` only: `git add` named files, check `git diff --cached --stat`, `git commit -q -F <msg>`,
  message ending `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`. No push, tag or merge.

## Review Focus

1. **A context with fewer than three variables.** Two-variable families run with `k = 2`; a representative over `z`
   must never replace a node there (R2). Task 3's `a_representative_outside_the_context_is_not_used` pins it.
2. **An operator's ignored operand.** Laws contain `shr1(a, b)` and `shl1(a, b)` with `b` not `0`; lookup maps them to
   the `0` form, and the replacement's proof must still check. Task 2's size-5 test (`shr1(x, y)`) and Task 3's
   `steps_compile_to_checked_proofs` pin it.
3. **`ABLATE=classes` restoring the old answers.** With the step off, a phase-1 binary must behave as the one before
   it. Task 6's unit test checks the path; its gate checks rules agree in all loops of salt 1 against Task 5's binary.
4. **A stale key file.** Changing `OPS` or `SIZE` without regenerating must fail loudly, never build a wrong table.
   Task 1's `a_key_with_another_header_names_the_regeneration` pins it.
5. **Lookup memory over a long run.** The lookup memos keep 1 byte per key input for every distinct term looked up, for
   the process's life; a sweep worker's peak commit is about 480 MB today. Task 6's gate reports `peakproc` per arm
   (from `runs run`) and stops for a decision if B's exceeds A's by more than 150 MB.

---

### Task 1: The key file

**Files:**
- Create: `tests/church_bv/classes.rs`
- Create: `tests/church_bv/class_key.txt`
- Modify: `tests/church_bv/main.rs` (module list)
- Modify: `docs/superpowers/specs/2026-10-22-class-table-normal-form-design.md` (front matter only)

**Interfaces:**
- Produces: `classes::OPS: [usize; 8]`, `classes::SIZE: usize`, `classes::KEY_FILE: &str`,
  `classes::Key { pub sets: Vec<(usize, Vec<[u128; 3]>)> }` with `Key::parse(&str) -> Result<Key, String>`,
  `Key::text(&self) -> String`, `Key::push(&mut self, w: usize, x: [u128; 3])`, `Key::start() -> Key`,
  `Key::len(&self) -> usize`.

- [ ] **Step 1: Mark the spec active**

Edit the spec's front matter `status: draft` to `status: active`.

- [ ] **Step 2: Write the failing tests**

Create `tests/church_bv/classes.rs`:

```rust
//! The learned class table (docs/superpowers/specs/2026-10-22-class-table-normal-form-design.md): terms over x, y, z, 0
//! and -1 to size `SIZE`, enumerated from representatives only and keyed by their values on a learned key
//! (`class_key.txt`, baked in) and their sort. A class's representative is its smallest member `Machine::parse` takes,
//! else its smallest (decision 7). `rep` looks a term's class up; `step` and `normalize` use a replacement only with a
//! proof (§3).

use super::*;

/// The operators in enumeration order; `shl1` and `shr1` are unary, enumerated with the second operand `0`.
pub const OPS: [usize; 8] = [ADD, AND, OR, XOR, SUB, SHL1, SHR1, LT];
/// The largest term size the table enumerates (decision 4).
pub const SIZE: usize = 9;
/// The key, learned by `regenerate_key` and baked in, so the table depends only on the source.
pub const KEY_FILE: &str = include_str!("class_key.txt");
const REGENERATE: &str = "<exe> classes::regenerate_key --exact --ignored --nocapture, then rebuild";

/// The table's key: per width, its inputs (x, y, z).
#[derive(Clone, Debug, PartialEq)]
pub struct Key {
    pub sets: Vec<(usize, Vec<[u128; 3]>)>,
}

impl Key {
    /// The header the build expects: its operators in order and its size.
    fn header() -> String {
        format!("ops {} size {SIZE}", OPS.map(|o| OP_INFO[o].name).join(" "))
    }

    /// A key file's inputs; an error when its header is not this build's (it was learned for another table) or a line is
    /// not `<width> <x> <y> <z>` with a width of 1 to 8.
    pub fn parse(text: &str) -> Result<Key, String> {
        let mut lines = text.lines().map(str::trim).filter(|l| !l.is_empty());
        let head = lines.next().unwrap_or("");
        if head != Key::header() {
            return Err(format!("class key header {head:?} is not {:?}: regenerate the key ({REGENERATE})", Key::header()));
        }
        let mut key = Key { sets: vec![] };
        for l in lines {
            let f: Vec<u128> = l.split_whitespace().map(str::parse).collect::<Result<_, _>>().map_err(|e| format!("class key line {l:?}: {e}"))?;
            let &[w, x, y, z] = f.as_slice() else {
                return Err(format!("class key line {l:?}: not `<width> <x> <y> <z>`"));
            };
            if !(1..=8).contains(&w) || [x, y, z].iter().any(|v| *v > low_bits(w as usize)) {
                return Err(format!("class key line {l:?}: width 1 to 8 and values within it"));
            }
            key.push(w as usize, [x, y, z]);
        }
        Ok(key)
    }

    /// The key file's text.
    pub fn text(&self) -> String {
        let mut s = Key::header() + "\n";
        for (w, ins) in &self.sets {
            for x in ins {
                s += &format!("{w} {} {} {}\n", x[0], x[1], x[2]);
            }
        }
        s
    }

    /// Adds an input at width `w`.
    pub fn push(&mut self, w: usize, x: [u128; 3]) {
        match self.sets.iter_mut().find(|s| s.0 == w) {
            Some(s) => s.1.push(x),
            None => self.sets.push((w, vec![x])),
        }
    }

    /// The refinement's start: the 8 tuples of 0s and 1s, at width 8.
    pub fn start() -> Key {
        let mut k = Key { sets: vec![] };
        for i in 0..8u128 {
            k.push(8, [0, 1, 2].map(|v| i >> v & 1));
        }
        k
    }

    /// Inputs over all widths.
    pub fn len(&self) -> usize {
        self.sets.iter().map(|s| s.1.len()).sum()
    }
}

/// A key file's text reads back as the same key, and the baked-in file parses.
#[test]
fn a_key_round_trips_through_its_text() {
    let mut k = Key::start();
    k.push(4, [15, 0, 7]);
    k.push(3, [1, 2, 3]);
    assert_eq!(Key::parse(&k.text()), Ok(k.clone()));
    assert_eq!(k.len(), 10);
    assert!(Key::parse(KEY_FILE).is_ok(), "{:?}", Key::parse(KEY_FILE).err());
}

/// A key learned for another operator set or size, or a malformed line, is refused with the regeneration command.
#[test]
fn a_key_with_another_header_names_the_regeneration() {
    let other_ops = Key::start().text().replacen(" lt size", " size", 1);
    let other_size = Key::start().text().replacen("size 9", "size 11", 1);
    for text in [other_ops, other_size] {
        let e = Key::parse(&text).unwrap_err();
        assert!(e.contains("classes::regenerate_key"), "{e}");
    }
    let head = Key::start().text().lines().next().unwrap().to_string();
    assert!(Key::parse(&format!("{head}\n8 1 2\n")).is_err(), "three fields");
    assert!(Key::parse(&format!("{head}\n4 16 0 0\n")).is_err(), "a value wider than its width");
    assert!(Key::parse(&format!("{head}\n9 0 0 0\n")).is_err(), "width 9");
}
```

Create `tests/church_bv/class_key.txt` (the refinement's start; Task 2 replaces it with the learned key):

```
ops add and or xor sub shl1 shr1 lt size 9
8 0 0 0
8 1 0 0
8 0 1 0
8 1 1 0
8 0 0 1
8 1 0 1
8 0 1 1
8 1 1 1
```

In `tests/church_bv/main.rs`, add `mod classes;` on the line before `mod driver;`.

- [ ] **Step 3: Run the tests**

Run: `cargo test --release --test church_bv -j 8 -- classes:: 2>&1 | tail -6`
Expected: `test result: ok. 2 passed`. (These tests are written with the code: the format has no behaviour to see fail
before it exists; check that removing `lt` from `OPS` makes `a_key_round_trips_through_its_text` fail on the baked
file, then restore it.)

- [ ] **Step 4: Commit**

```bash
git add tests/church_bv/classes.rs tests/church_bv/class_key.txt tests/church_bv/main.rs docs/superpowers/specs/2026-10-22-class-table-normal-form-design.md
git diff --cached --stat
printf 'classes: the class table'"'"'s key file (format, header check, the refinement'"'"'s start); spec active\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n' > "$TEMP/msg.txt"
git commit -q -F "$TEMP/msg.txt"
```

---

### Task 2: The table, lookup, and the learned key

**Files:**
- Modify: `tests/church_bv/classes.rs`
- Modify: `tests/church_bv/rewrite.rs` (`ValueMemo::new` becomes `pub`)
- Modify: `tests/church_bv/job.rs` (`hidden_state_is_classified`: `CLASSES`)
- Modify: `tests/church_bv/class_key.txt` (regenerated)
- Create: `docs/runs/<today>/scripts/class_key.sh`

**Interfaces:**
- Consumes: Task 1's `Key`, `OPS`, `SIZE`, `KEY_FILE`.
- Produces: `classes::Classes` with `Classes::build(key: &Key, size: usize, sample_n: usize, seed: u128) -> (Classes, BuildStats)`,
  `Classes::get() -> &'static Classes`, `Classes::rep(&self, t: &Term) -> Option<Term>`,
  `Classes::canonical(&self, t: &Term) -> Term`, `Classes::len(&self) -> usize`;
  `classes::BuildStats { pub merges: usize, pub sample: Vec<(Term, Term)>, pub displaced: usize, pub lts: usize, pub millis: u128 }`.

- [ ] **Step 1: Write the failing test**

Append to `classes.rs`:

```rust
/// Built from the key file to size 5 (spec "Testing"): padding maps to its leaf, `ClassReps`'s value-equal two-leaf
/// nodes share a representative, a unary operator's ignored operand becomes `0`, and an `lt` whose first member the
/// machine refuses is represented by a later one it takes (decision 7: both size 5, the `shr1` one enumerated first).
#[test]
fn the_size_5_table_maps_terms_to_their_representatives() {
    let (c, _) = Classes::build(&Key::parse(KEY_FILE).unwrap(), 5, 0, 0);
    let n = |s: &str| c.canonical(&parse_term(s)).show();
    assert_eq!(n("sub(y, y)"), "0");
    assert_eq!(n("add(x, 0)"), "x");
    assert_eq!(n("sub(-1, x)"), "xor(x, -1)");
    assert_eq!(n("xor(x, -1)"), "xor(x, -1)");
    assert_eq!(n("shr1(x, y)"), "shr1(x, 0)");
    assert_eq!(n("lt(0, shr1(x, 0))"), "lt(sub(0, -1), x)");
    let rep = |s: &str| c.rep(&parse_term(s)).map(|t| t.show());
    assert_eq!(rep("add(x, 0)").as_deref(), Some("x"));
    assert_eq!(rep("x"), None, "a representative maps to nothing");
    assert_eq!(rep("add(u, 0)"), None, "a fourth variable");
}
```

- [ ] **Step 2: Run it to verify it fails**

Run: `cargo test --release --test church_bv -j 8 -- classes:: 2>&1 | grep -E "^error|cannot find" | head -3`
Expected: compile error, `Classes` not found.

- [ ] **Step 3: Implement the table**

In `rewrite.rs`, change `    fn new(n: usize, len: usize, vars: Vec<Box<[W]>>) -> Self {` (in `impl<W: Word> ValueMemo<W>`) to
`    pub fn new(n: usize, len: usize, vars: Vec<Box<[W]>>) -> Self {`.

In `classes.rs`, below `use super::*;` add:

```rust
use super::rewrite::Node;
use std::sync::{Mutex, OnceLock};
```

and append:

```rust
/// A class's key: a term's values on the key's inputs (all widths end to end) and whether it is an `lt` (a second sort),
/// hashed to 128 bits.
fn class_hash(vals: &[u8], lt: bool) -> (u64, u64) {
    use std::hash::{Hash, Hasher};
    let (mut h1, mut h2) = (std::collections::hash_map::DefaultHasher::new(), std::collections::hash_map::DefaultHasher::new());
    (lt, vals).hash(&mut h1);
    (0xa5u8, vals, lt).hash(&mut h2);
    (h1.finish(), h2.finish())
}

/// The table: each class's key to its representative, and the lookup's value memos (one per key width, in key order).
pub struct Classes {
    map: hashbrown::HashMap<(u64, u64), Term>,
    memos: Mutex<Vec<ValueMemo<u8>>>,
}

/// What a build saw besides the table: the merges the key proposed (a new term whose key a class already has), a uniform
/// sample of them as (member, its class's representative when the build ends), the representatives a later member
/// displaced (decision 7), the `lt` classes, and the build's time.
pub struct BuildStats {
    pub merges: usize,
    pub sample: Vec<(Term, Term)>,
    pub displaced: usize,
    pub lts: usize,
    pub millis: u128,
}

/// The process's table, built on first use from the baked-in key.
static CLASSES: OnceLock<Classes> = OnceLock::new();

impl Classes {
    /// The table to `size` under `key`, from representatives only, with a reservoir sample of `sample_n` merges (`seed`
    /// drives it). The terms' values live only while it builds.
    pub fn build(key: &Key, size: usize, sample_n: usize, mut seed: u128) -> (Classes, BuildStats) {
        let t0 = std::time::Instant::now();
        let (mut masks, mut cols) = (vec![], [vec![], vec![], vec![]]);
        for (w, ins) in &key.sets {
            for x in ins {
                masks.push(low_bits(*w));
                for v in 0..3 {
                    cols[v].push(x[v] as u8);
                }
            }
        }
        let leaf = |t: &Term| -> Vec<u8> {
            match *t.node() {
                Node::V(v) => cols[v].clone(),
                Node::Zero => vec![0; masks.len()],
                _ => masks.iter().map(|m| *m as u8).collect(),
            }
        };
        let zip = |o: usize, a: &[u8], b: &[u8]| -> Vec<u8> {
            let f = OP_INFO[o].word;
            a.iter().zip(b).zip(&masks).map(|((&p, &q), &m)| f(p as u128, q as u128, m) as u8).collect()
        };
        let mut map: hashbrown::HashMap<(u64, u64), Term> = Default::default();
        let mut st = BuildStats { merges: 0, sample: vec![], displaced: 0, lts: 0, millis: 0 };
        // representatives a later member displaced, to the member: the sample's pairs are fixed up from it at the end
        let mut moved: hashbrown::HashMap<Term, Term> = Default::default();
        // per size, the bit-vector representatives and their values (an `lt` is a sort no operator takes)
        let mut reps: Vec<Vec<(Term, Vec<u8>)>> = vec![vec![]; size + 1];
        for t in [Term::v(0), Term::v(1), Term::v(2), Term::ZERO, Term::ONES] {
            let (v, h) = (leaf(&t), class_hash(&leaf(&t), false));
            if !map.contains_key(&h) {
                map.insert(h, t);
                reps[1].push((t, v));
            }
        }
        for s in (3..=size).step_by(2) {
            let (done, rest) = reps.split_at_mut(s);
            let new = &mut rest[0];
            for sa in (1..s - 1).step_by(2) {
                let sb = s - 1 - sa;
                for (ra, va) in &done[sa] {
                    for (rb, vb) in &done[sb] {
                        for o in OPS {
                            if OP_INFO[o].shift && *rb != Term::ZERO {
                                continue;
                            }
                            let v = zip(o, va, vb);
                            let h = class_hash(&v, o == LT);
                            // made only when needed: most candidates are merges, and interned terms are never freed
                            let term = || Term::op(o, *ra, *rb);
                            match map.get_mut(&h) {
                                Some(rep) => {
                                    if Machine::parse(rep).is_none() && Machine::parse(&term()).is_some() {
                                        moved.insert(*rep, term());
                                        *rep = term();
                                        st.displaced += 1;
                                    }
                                    st.merges += 1;
                                    seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                                    let slot = if st.sample.len() < sample_n { Some(st.sample.len()) } else { Some((seed >> 64) as usize % st.merges).filter(|&x| x < sample_n) };
                                    if let Some(x) = slot {
                                        let c = (term(), *rep);
                                        if x == st.sample.len() {
                                            st.sample.push(c);
                                        } else {
                                            st.sample[x] = c;
                                        }
                                    }
                                }
                                None => {
                                    map.insert(h, term());
                                    if o == LT {
                                        st.lts += 1;
                                    } else {
                                        new.push((term(), v));
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        drop(reps);
        // a sampled pair's representative as the build ends: a displaced one is now a member
        for (u, r) in st.sample.iter_mut() {
            if let Some(&n) = moved.get(r) {
                (*u, *r) = if *u == n { (*r, n) } else { (*u, n) };
            }
        }
        let memos = key.sets.iter().map(|(w, ins)| ValueMemo::new(*w, ins.len(), (0..3).map(|v| ins.iter().map(|x| x[v] as u8).collect()).collect())).collect();
        st.millis = t0.elapsed().as_millis();
        (Classes { map, memos: Mutex::new(memos) }, st)
    }

    /// The process's table, built from `KEY_FILE` on first use; a key learned for another table fails the process.
    pub fn get() -> &'static Classes {
        CLASSES.get_or_init(|| {
            let key = Key::parse(KEY_FILE).unwrap_or_else(|e| panic!("{e}"));
            let (c, st) = Classes::build(&key, SIZE, 0, 0);
            println!("CLASSES {} classes ({} lt) to size {SIZE} under {} key inputs, built in {} ms", c.len(), st.lts, key.len(), st.millis);
            c
        })
    }

    /// Classes in the table.
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// The representative of `t`'s class when the table knows it and it is not `t`; `None` otherwise, and for a term over a
    /// variable other than x, y, z. Pure: no proof.
    pub fn rep(&self, t: &Term) -> Option<Term> {
        if t.max_var() >= 3 {
            return None;
        }
        let mut vals = vec![];
        for m in self.memos.lock().unwrap_or_else(|e| e.into_inner()).iter_mut() {
            vals.extend_from_slice(m.values(t));
        }
        let r = *self.map.get(&class_hash(&vals, matches!(*t.node(), Node::Op(LT, ..))))?;
        (r != *t).then_some(r)
    }

    /// `t` with every node, bottom-up, replaced by its class's representative where the table knows it (no proof: the law
    /// generator's twin filter).
    pub fn canonical(&self, t: &Term) -> Term {
        let t1 = match *t.node() {
            Node::Op(o, a, b) => Term::op(o, self.canonical(&a), self.canonical(&b)),
            _ => *t,
        };
        self.rep(&t1).unwrap_or(t1)
    }
}
```

In `job.rs`'s `hidden_state_is_classified`, change `const PROCESS_WIDE: [(&str, &str, &str); 6] = [` to `; 7] = [` and
add the entry `("classes.rs", "CLASSES", "the class table: built once from the baked-in key, pure"),` after the `TABLE`
line.

- [ ] **Step 4: Add the key's refinement**

Append to `classes.rs`:

```rust
/// The key refinement's refuter (R8 of the plan): 4096 pseudo-random width-8 inputs, every width-4 input, every width-3
/// input, then the screen's width-8 inputs.
struct Refuter {
    r8: ValueMemo<u8>,
    e4: ValueMemo<u8>,
    e3: ValueMemo<u8>,
}

impl Refuter {
    const TESTS: usize = 4096;
    fn new() -> Refuter {
        let mut seed = 0x6a09_e667_f3bc_c908u128;
        let tvars: Vec<Box<[u8]>> = (0..3)
            .map(|_| {
                (0..Self::TESTS)
                    .map(|_| {
                        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                        (seed >> 40) as u8
                    })
                    .collect()
            })
            .collect();
        Refuter { r8: ValueMemo::new(8, Self::TESTS, tvars), e4: ValueMemo::exhaustive(4, 3), e3: ValueMemo::exhaustive(3, 3) }
    }

    /// An input on which `a` and `b` differ: (width, tuple).
    fn refute(&mut self, a: &Term, b: &Term) -> Option<(usize, [u128; 3])> {
        let tuple = |v: Vec<u128>| [v[0], v[1], v[2]];
        if let Some(i) = self.r8.first_difference(a, b, Self::TESTS) {
            return Some((8, tuple(self.r8.input(i))));
        }
        if let Some(i) = self.e4.first_difference(a, b, 1 << 12) {
            return Some((4, tuple(self.e4.input(i))));
        }
        if let Some(i) = self.e3.first_difference(a, b, 1 << 9) {
            return Some((3, tuple(self.e3.input(i))));
        }
        a.counterexample(b, 8, 3).map(|x| (8, tuple(x)))
    }
}

/// Regenerates `class_key.txt` (spec §2; run `2026-10-22-key-refine`): from the 8 tuples of 0s and 1s, each round builds
/// the table, refutes a sample of 20000 of its merges, and adds one refuting input per refuted merge that the inputs added
/// this round do not already separate. The file is written only on a round whose sample has no refuted merge; rebuild to
/// use it.
#[test]
#[ignore]
fn regenerate_key() {
    let mut key = Key::start();
    for round in 0..30u128 {
        let (c, st) = Classes::build(&key, SIZE, 20000, 0x51ed_270b_27a3_c1f5 + round);
        // the memos grow with every term refuted, so each thousand pairs starts fresh ones
        let mut refuter = Refuter::new();
        let (mut refuted, mut added) = (0usize, Vec::<(usize, [u128; 3])>::new());
        for (i, (u, r)) in st.sample.iter().enumerate() {
            if i % 1000 == 999 {
                refuter = Refuter::new();
            }
            if let Some(cex) = refuter.refute(u, r) {
                refuted += 1;
                if !added.iter().any(|(w, x)| u.interp(*w, x) != r.interp(*w, x)) {
                    added.push(cex);
                }
            }
        }
        println!(
            "ROUND {round}: key {} inputs, {} classes ({} lt), {} merges, {} displaced, refuted {refuted} of {}, added {}, build {} ms",
            key.len(),
            c.len(),
            st.lts,
            st.merges,
            st.displaced,
            st.sample.len(),
            added.len(),
            st.millis
        );
        if refuted == 0 {
            let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/church_bv/class_key.txt");
            std::fs::write(&path, key.text()).unwrap();
            println!("WROTE {} ({} inputs: {})", path.display(), key.len(), key.sets.iter().map(|(w, i)| format!("{} at width {w}", i.len())).collect::<Vec<_>>().join(", "));
            return;
        }
        for (w, x) in added {
            key.push(w, x);
        }
    }
    panic!("the key did not converge in 30 rounds; class_key.txt is unchanged");
}
```

- [ ] **Step 5: Build and run the regeneration**

Write `docs/runs/<today>/scripts/class_key.sh` (`<today>` is the date the step runs, `date +%F`):

```bash
#!/bin/bash
# class_key.sh <exe>: classes::regenerate_key (plan docs/superpowers/plans/2026-10-23-class-table-normal-form.md, Task 2):
# refines the class table's key from the 8 tuples of 0s and 1s and writes tests/church_bv/class_key.txt on a clean round.
EXE=$1; T="${RUN_DIR:-$TEMP}"
"$EXE" classes::regenerate_key --exact --ignored --nocapture < /dev/null > "$T/class_key.log" 2>&1; rc=$?
grep -E "^(ROUND|WROTE)|panicked" "$T/class_key.log"
grep -E "^WROTE" "$T/class_key.log" | sed 's/^WROTE .* (/key /; s/)$//' > "$T/headline.txt"
exit $rc
```

Run (bash, repo root):
```bash
cargo test --release --test church_bv --no-run -j 8 2>&1 | tail -1
cp "$(ls -t target/release/build/tatic/*/out/church_bv-*.exe target/release/deps/church_bv-*.exe 2>/dev/null | head -1)" "$TEMP/bv_ct2.exe"
powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind probe -Name class-key -Command "bash docs/runs/$(date +%F)/scripts/class_key.sh '$(cygpath -w "$TEMP/bv_ct2.exe")'"
```
Expected: about 16 rounds and under 2 minutes (the probe converged in 16 rounds, 27 s, to 387 inputs; the width-3
check may add a few); the last lines `ROUND <n>: ... refuted 0 of 20000 ...` and `WROTE ...class_key.txt (<about 390>
inputs: ...)`; `git diff --stat tests/church_bv/class_key.txt` shows the file replaced. If it panics with "did not
converge", stop and report: the width-3 check changes the probe's measured behaviour.

Fill in the runs.md row's headline from the `WROTE` line (no `|`).

- [ ] **Step 6: Run the tests**

Run: `cargo test --release --test church_bv -j 8 -- classes:: job::hidden_state_is_classified 2>&1 | tail -8`
Expected: `test result: ok. 4 passed` (the size-5 test passes only under the learned key). If an exact representative
differs (e.g. `sub(-1, x)` maps to another size-3 member), check it is a member of the class and the first parse-able
one in enumeration order before changing the assertion, and say so in the commit message.

- [ ] **Step 7: Commit**

```bash
git add tests/church_bv/classes.rs tests/church_bv/class_key.txt tests/church_bv/rewrite.rs tests/church_bv/job.rs docs/runs/*/scripts/class_key.sh docs/runs.md
git diff --cached --stat
printf 'classes: the table (built from the baked-in key, parse-first representatives), rep and canonical lookup, and regenerate_key; the learned key (run <id>: <inputs> inputs)\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n' > "$TEMP/msg.txt"
git commit -q -F "$TEMP/msg.txt"
```
(Replace `<id>` and `<inputs>` in the message with the run's id and the key's input count.)

---

### Task 3: Verdicts, `step` and `normalize`

**Files:**
- Modify: `tests/church_bv/classes.rs`
- Modify: `tests/church_bv/job.rs` (`Job::table_steps`)

**Interfaces:**
- Consumes: Task 2's `Classes::get`, `Classes::rep`.
- Produces: `Classes::step(&self, job: &mut Job, n: usize, k: usize, t: &Term) -> Option<(Term, PlanRc)>`,
  `Classes::normalize(&self, job: &mut Job, n: usize, k: usize, t: &Term) -> (Term, PlanRc)`,
  `Job::table_steps: hashbrown::HashSet<(Term, Term)>` (pub field).

- [ ] **Step 1: Write the failing tests**

Append to `classes.rs`:

```rust
/// A step's replacement has a plan that compiles to a kernel-checked proof at width 4: an `add` law (`Tree`), a bitwise
/// law (`Bitwise`), one over a `shr1` atom, and `shr1` with a nonzero ignored operand.
#[test]
fn steps_compile_to_checked_proofs() {
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let c = Classes::get();
        for (s, want) in [("sub(add(x, y), y)", "x"), ("and(x, or(x, y))", "x"), ("add(shr1(x, 0), 0)", "shr1(x, 0)"), ("shr1(x, y)", "shr1(x, 0)")] {
            let t = parse_term(s);
            let (r, plan) = c.step(job, 4, 3, &t).unwrap_or_else(|| panic!("{s}: no step"));
            assert_eq!(r.show(), want);
            let (p, st) = law_proof(job, 4, 3, &t, &r, &plan);
            job.lemmas.ck(s, &p, &st);
        }
        assert_eq!(job.table_steps.len(), 4);
    });
}

/// Counting takes the same steps (the verdict is decided the same way, R3) and builds no plan; the law it closes then
/// compiles to a checked proof (spec "Testing": counting and compiling agree).
#[test]
fn counting_and_compiling_agree() {
    let (a, b) = (parse_term("add(sub(add(x, y), y), and(z, or(z, x)))"), parse_term("add(and(x, or(x, y)), z)"));
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let c = Classes::get();
        let rules = job.rules().counting(true);
        let (na, nb, plan) = job.with_rules(rules, |job| {
            let ((na, pa), (nb, _)) = (c.normalize(job, 4, 3, &a), c.normalize(job, 4, 3, &b));
            (na, nb, pa)
        });
        assert!(matches!(*plan, Plan::Counting));
        assert_eq!(na.show(), nb.show(), "the law meets while counting");
        let ((ma, pa), (mb, pb)) = (c.normalize(job, 4, 3, &a), c.normalize(job, 4, 3, &b));
        assert_eq!((ma.show(), mb.show()), (na.show(), nb.show()));
        let plan = Plan::trans(job, pa, Plan::sym(job, pb));
        let (p, s) = law_proof(job, 4, 3, &a, &b, &plan);
        job.lemmas.ck("counted law", &p, &s);
    });
}

/// A representative over a variable the context lacks is not used (R2): `add(y, 0)` steps to `y` with two variables, not
/// with one.
#[test]
fn a_representative_outside_the_context_is_not_used() {
    let job = &mut Job::new(Setup::process());
    let c = Classes::get();
    let t = parse_term("add(y, 0)");
    assert_eq!(c.step(job, 4, 2, &t).map(|(r, _)| r.show()).as_deref(), Some("y"));
    assert!(c.step(job, 4, 1, &t).is_none());
}
```

- [ ] **Step 2: Run them to verify they fail**

Run: `cargo test --release --test church_bv -j 8 -- classes:: 2>&1 | grep -E "^error" | head -3`
Expected: compile errors: no method `step` / `normalize` on `Classes`, no field `table_steps`.

- [ ] **Step 3: Implement**

In `job.rs`, add to `pub struct Job` after the `lemmas` field:

```rust
    /// The distinct class-table replacements `classes::Classes::step` used, each with a proof (spec decision 2: counted
    /// apart from M, as a learning cost).
    pub table_steps: hashbrown::HashSet<(Term, Term)>,
```

and in `Job::new` add `table_steps: Default::default()` after `lemmas: Lemmas::default()`.

In `classes.rs`, below the other `use` lines add `use crate::task::SharedMemo;`, and append:

```rust
/// How a replacement `u -> r` is proved (spec §3, R2, R3): its prover, the law's sides over `V(0..)` and its arguments.
#[derive(Clone)]
struct Verdict {
    kind: LawKind,
    lhs: Term,
    rhs: Term,
    args: Vec<Term>,
}

/// Replacements' verdicts by (width, carry cap, u, r). Pure: a verdict depends only on its key (`tree_encoding` reads the
/// carry cap before its own memo).
static VERDICTS: SharedMemo<(usize, usize, Term, Term), Option<Verdict>> = SharedMemo::new();

/// The verdict on `u -> r` at width `n`: `Bitwise` when neither side has `add`, `sub` or `lt` and they agree at widths
/// 1..=5; else `Tree` when `tree_encoding` finds a carry encoding with each `shr1` node a fresh variable (decision 3);
/// else none (decision 6).
fn verdict(job: &Job, n: usize, u: &Term, r: &Term) -> Option<Verdict> {
    let kv = 1 + u.max_var().max(r.max_var());
    let vars = (0..kv).map(Term::v);
    if u.add_free() && r.add_free() {
        // a position reads only a few neighbours, so these widths hold every case (`prove_eq`'s per-position step)
        let holds = (1..=5usize).all(|w| {
            (0..1u128 << (w * kv)).all(|i| {
                let x: Vec<u128> = (0..kv).map(|v| (i >> (w * v)) & low_bits(w)).collect();
                u.interp(w, &x) == r.interp(w, &x)
            })
        });
        return holds.then(|| Verdict { kind: LawKind::Bitwise, lhs: *u, rhs: *r, args: vars.collect() });
    }
    fn atomize(t: Term, kv: usize, atoms: &mut Vec<Term>) -> Term {
        match *t.node() {
            Node::Op(SHR1, ..) => {
                let i = atoms.iter().position(|a| *a == t).unwrap_or_else(|| {
                    atoms.push(t);
                    atoms.len() - 1
                });
                Term::v(kv + i)
            }
            Node::Op(o, a, b) => Term::op(o, atomize(a, kv, atoms), atomize(b, kv, atoms)),
            _ => t,
        }
    }
    let mut atoms = vec![];
    let (lhs, rhs) = (atomize(*u, kv, &mut atoms), atomize(*r, kv, &mut atoms));
    let args: Vec<Term> = vars.chain(atoms).collect();
    tree_encoding(job, n, args.len(), &lhs, &rhs)?;
    Some(Verdict { kind: LawKind::Tree, lhs, rhs, args })
}

impl Classes {
    /// `rep(t)` when that replacement has a proof at width `n` and its representative is over the context's `k` variables,
    /// with its plan (`Plan::Law`, or the shared `Plan::Counting` while counting); counted in `job.table_steps`.
    pub fn step(&self, job: &mut Job, n: usize, k: usize, t: &Term) -> Option<(Term, PlanRc)> {
        let r = self.rep(t)?;
        if r.max_var() >= k {
            return None;
        }
        let key = (n, carry_cap(job), *t, r);
        let v = match VERDICTS.get(&key) {
            Some(v) => v,
            None => {
                let v = verdict(job, n, t, &r);
                if v.is_none() {
                    println!("CLASS_UNUSABLE {} = {}", t.show(), r.show());
                }
                VERDICTS.insert(key, v.clone());
                v
            }
        }?;
        job.table_steps.insert((*t, r));
        Some((r, Plan::law(job, v.kind, v.lhs, v.rhs, v.args)))
    }

    /// `t` with `step` taken at every node, bottom-up, and its plan: `Cong` per changed node, `Trans` per replacement.
    pub fn normalize(&self, job: &mut Job, n: usize, k: usize, t: &Term) -> (Term, PlanRc) {
        let (t1, p1) = match *t.node() {
            Node::Op(o, a, b) => {
                let ((a1, pa), (b1, pb)) = (self.normalize(job, n, k, &a), self.normalize(job, n, k, &b));
                if (a1, b1) == (a, b) { (*t, Plan::refl(job, t)) } else { (Term::op(o, a1, b1), Plan::cong(job, o, pa, pb)) }
            }
            _ => (*t, Plan::refl(job, t)),
        };
        match self.step(job, n, k, &t1) {
            Some((r, p)) => (r, Plan::trans(job, p1, p)),
            None => (t1, p1),
        }
    }
}
```

- [ ] **Step 4: Run the tests**

Run: `cargo test --release --test church_bv -j 8 -- classes:: 2>&1 | tail -8`
Expected: `test result: ok. 6 passed`. A `Compiler` panic in `steps_compile_to_checked_proofs` on the `shr1(x, y)` case
means `bitwise_law_k` does not take a nonzero ignored operand: report it (Review Focus 2) rather than dropping the
case.

- [ ] **Step 5: Run the whole suite**

Run: `cargo test --release --test church_bv -j 8 2>&1 | grep -E "^test result|FAILED|panicked" | head`
Expected: `test result: ok.` with 0 failed (passed: the count before Task 1 plus 6; the ignored count plus 1).

- [ ] **Step 6: Commit**

```bash
git add tests/church_bv/classes.rs tests/church_bv/job.rs
git diff --cached --stat
printf 'classes: verdicts (bitwise at widths 1-5, else a carry encoding over shr1 atoms), step and normalize with plans; Job::table_steps counts the replacements used\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n' > "$TEMP/msg.txt"
git commit -q -F "$TEMP/msg.txt"
```

---

### Task 4: The held-out proofs and a build's memory

**Files:**
- Create: `docs/runs/2026-10-23/fixtures/held/` (copies of the held-out law files)
- Modify: `tests/church_bv/classes.rs` (ignored test; possibly `mi_collect` in `Classes::get`, R9)
- Create: `docs/runs/<today>/scripts/class_held.sh`, `docs/runs/<today>/scripts/class_commit.sh`,
  `docs/runs/<today>/patches/class_commit.patch`
- Modify: `docs/tier-cycle.md`, `docs/runs.md`

**Interfaces:**
- Consumes: Task 3's `step`, `normalize`, `Job::table_steps`.
- Produces: the fixture directory; a decision on R9.

- [ ] **Step 1: Copy the fixtures**

Run (bash, repo root):
```bash
d=docs/runs/2026-10-23/fixtures/held; mkdir -p "$d"
R="$LOCALAPPDATA/claude-runs/tatic"
cp "$R/2026-10-22-join-residue/join_residue/residue.txt" "$d/join_residue.txt"
for f in "$R"/2026-10-22-size-band/size_band/*/held_size_*.txt; do cp "$f" "$d/$(basename "$(dirname "$f")")_$(basename "$f")"; done
ls "$d" | wc -l; du -sh "$d"
```
Expected: 14 files (`join_residue.txt`, and `held_size_{7,9,11}.txt` for add3, mix3 and sbo3 plus 7-13 for cmp3d,
prefixed by family), about 160 KB; each line one law `<lhs> = <rhs>`.

- [ ] **Step 2: Write the ignored test**

Append to `classes.rs`:

```rust
/// Every replacement the table makes on the held-out laws (spec "Testing", "Proofs"; `docs/runs/2026-10-23/fixtures/held`,
/// from runs `2026-10-22-size-band` and `-join-residue`) has a verdict at width 4, and every law that meets compiles to a
/// kernel-checked proof. Prints the laws met per file, the replacements by prover, and the time in verdicts and in proofs.
#[test]
#[ignore]
fn held_out_replacements_prove() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("docs/runs/2026-10-23/fixtures/held");
    let mut files: Vec<_> = std::fs::read_dir(&dir).unwrap().flatten().map(|e| e.path()).collect();
    files.sort();
    let c = Classes::get();
    // the replacements canonicalizing makes (the table's own choice, before any verdict)
    fn walk(c: &Classes, t: &Term, out: &mut hashbrown::HashSet<(Term, Term)>) -> Term {
        let t1 = match *t.node() {
            Node::Op(o, a, b) => Term::op(o, walk(c, &a, out), walk(c, &b, out)),
            _ => *t,
        };
        match c.rep(&t1) {
            Some(r) => {
                out.insert((t1, r));
                r
            }
            None => t1,
        }
    }
    let mut laws: Vec<(String, Term, Term)> = vec![];
    let mut pairs = hashbrown::HashSet::new();
    for f in &files {
        let (mut n, mut met) = (0, 0);
        for line in std::fs::read_to_string(f).unwrap().lines().filter(|l| l.contains(" = ")) {
            let (l, r) = line.split_once(" = ").unwrap();
            let (a, b) = (parse_term(l.trim()), parse_term(r.trim()));
            n += 1;
            if walk(c, &a, &mut pairs) == walk(c, &b, &mut pairs) {
                met += 1;
                laws.push((line.to_string(), a, b));
            }
        }
        println!("LAWS {}: {met} of {n} meet", f.file_name().unwrap().to_string_lossy());
    }
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let t0 = std::time::Instant::now();
        let mut pairs: Vec<_> = pairs.into_iter().collect();
        pairs.sort_by_cached_key(|(u, r)| (u.show(), r.show()));
        let unusable: Vec<String> = pairs.iter().filter(|(u, _)| c.step(job, 4, 3, u).is_none()).map(|(u, r)| format!("{} = {}", u.show(), r.show())).collect();
        let verdict_ms = t0.elapsed().as_millis();
        // a replacement with no proof leaves `normalize` short of `walk`'s normal form, so a met law would not compile
        assert!(unusable.is_empty(), "{} of {} replacements with no proof: {unusable:?}", unusable.len(), pairs.len());
        let t1 = std::time::Instant::now();
        for (line, a, b) in &laws {
            let ((_, pa), (_, pb)) = (c.normalize(job, 4, 3, a), c.normalize(job, 4, 3, b));
            let plan = Plan::trans(job, pa, Plan::sym(job, pb));
            let (p, s) = law_proof(job, 4, 3, a, b, &plan);
            job.lemmas.ck(line, &p, &s);
        }
        println!("REPLACEMENTS {} made, all with a proof; verdicts {verdict_ms} ms, {} laws compiled and checked in {} ms", pairs.len(), laws.len(), t1.elapsed().as_millis());
    });
}
```

- [ ] **Step 3: Run it**

Write `docs/runs/<today>/scripts/class_held.sh`:

```bash
#!/bin/bash
# class_held.sh <exe>: classes::held_out_replacements_prove (plan 2026-10-23-class-table-normal-form, Task 4): the
# held-out laws met by the table, its replacements' verdicts at width 4, and every met law compiled and kernel-checked.
EXE=$1; T="${RUN_DIR:-$TEMP}"
"$EXE" classes::held_out_replacements_prove --exact --ignored --nocapture < /dev/null > "$T/class_held.log" 2>&1; rc=$?
grep -E "^(CLASSES|LAWS|REPLACEMENTS|CLASS_UNUSABLE)|panicked" "$T/class_held.log"
grep -E "^REPLACEMENTS" "$T/class_held.log" > "$T/headline.txt"
exit $rc
```

Run:
```bash
cargo test --release --test church_bv --no-run -j 8 2>&1 | tail -1
cp "$(ls -t target/release/build/tatic/*/out/church_bv-*.exe target/release/deps/church_bv-*.exe 2>/dev/null | head -1)" "$TEMP/bv_ct4.exe"
powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind probe -Name class-held -Command "bash docs/runs/$(date +%F)/scripts/class_held.sh '$(cygpath -w "$TEMP/bv_ct4.exe")'"
```
Expected: a few minutes (about 3200 replacements, each a verdict and a proof; the probe took about 20 ms each); `LAWS`
per file near the spec's figures ("Why": 189-200 of 200 per family and size, 15 of 15 for `join_residue.txt`);
`REPLACEMENTS` about 3200 made, all with a proof; exit 0. A panic naming replacements with no proof is a finding: stop
and report them with the log (decision 6 drops them in use, but on these laws the probe proved all).

- [ ] **Step 4: Measure a build's commit**

Write `docs/runs/<today>/patches/class_commit.patch` as a patch that appends this ignored test to `classes.rs` (the
measurement stays a patch, as the spec's probes do):

```rust
/// Probe (plan Task 4, R9): the process's commit before the table's build, after it, and after `mi_collect(true)`.
#[test]
#[ignore]
fn build_commit_probe() {
    #[repr(C)]
    #[derive(Default)]
    struct Pmc { cb: u32, faults: u32, peak_ws: usize, ws: usize, qpp_peak: usize, qpp: usize, qnp_peak: usize, qnp: usize, pagefile: usize, peak_pagefile: usize }
    unsafe extern "system" {
        fn GetCurrentProcess() -> isize;
        fn K32GetProcessMemoryInfo(h: isize, p: *mut Pmc, cb: u32) -> i32;
    }
    unsafe extern "C" {
        fn mi_collect(force: bool);
    }
    let mb = || {
        let mut p = Pmc { cb: std::mem::size_of::<Pmc>() as u32, ..Default::default() };
        unsafe { K32GetProcessMemoryInfo(GetCurrentProcess(), &mut p, p.cb) };
        (p.pagefile >> 20, p.peak_pagefile >> 20, p.ws >> 20)
    };
    println!("COMMIT before {:?}", mb());
    let c = Classes::get();
    println!("COMMIT after build {:?} ({} classes)", mb(), c.len());
    unsafe { mi_collect(true) };
    println!("COMMIT after mi_collect {:?}", mb());
}
```

(Make the patch with `git diff > <patch>` after adding the test, then `git checkout tests/church_bv/classes.rs`.)
Write `docs/runs/<today>/scripts/class_commit.sh`:

```bash
#!/bin/bash
# class_commit.sh <exe>: the class table's build commit (MB: commit, peak commit, working set) with mimalloc's large
# OS pages allowed and not (as sweep children run), before and after mi_collect(true) (plan Task 4, R9). The exe is the
# Task 4 build plus patches/class_commit.patch.
EXE=$1; T="${RUN_DIR:-$TEMP}"
for lp in 1 0; do
  MIMALLOC_ALLOW_LARGE_OS_PAGES=$lp "$EXE" classes::build_commit_probe --exact --ignored --nocapture < /dev/null > "$T/commit$lp.log" 2>&1
  echo "== large OS pages $lp: exit $?"; grep -E "^(COMMIT|CLASSES)|panicked" "$T/commit$lp.log"
done
grep -h "after mi_collect" "$T/commit0.log" > "$T/headline.txt"
```

Run: apply the patch, build, copy the exe to `$TEMP/bv_ct4c.exe`, revert the patch (`git checkout
tests/church_bv/classes.rs`; `git status --short` shows only the new patch and scripts), then
`powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind probe -Name class-commit -Command "bash docs/runs/$(date +%F)/scripts/class_commit.sh '$(cygpath -w "$TEMP/bv_ct4c.exe")'"`.
Expected: under a minute; with large pages off, a commit after the build near the probe's 215 MB peak and after
`mi_collect` near 95 MB (spec §1).

- [ ] **Step 5: Apply R9**

If the large-pages-off commit after `mi_collect` is at least 50 MB below the commit after the build, add to
`Classes::get`, after the `println!`:

```rust
            // the build's values go back to the system (spec §1, plan R9: <after build> MB to <after collect> MB in run <id>)
            unsafe extern "C" {
                fn mi_collect(force: bool);
            }
            unsafe { mi_collect(true) };
```

(with the measured numbers and run id in the comment), run `cargo test --release --test church_bv -j 8 -- classes::`
(expected: ok), and say so in the commit. Otherwise add nothing; the doc section records why.

- [ ] **Step 6: Record**

Fill in both runs.md rows' headlines and notes. In `docs/tier-cycle.md`, after the section
"*`shr1` in the class table, its proofs over atoms, and a table's memory ...*", add a section
"*The class table as a module: the learned key, held-out proofs and a build's memory (<date>; runs <class-key id>,
<class-held id>, <class-commit id>)*" stating: the key's rounds, inputs per width and build time (against the probe's
387 inputs and 16 rounds: what the width-3 check changed); classes; laws met per family against the spec's 189-200;
replacements, verdicts by prover if printed, unusable count, verdict and proof times; the commit numbers and R9's
outcome. In `docs/learned-vs-fixed.md`, candidate 4's last sentence becomes: "It is being built as a module
(`tests/church_bv/classes.rs`, plan `docs/superpowers/plans/2026-10-23-class-table-normal-form.md`; tier-cycle.md,
"The class table as a module ...")."

- [ ] **Step 7: Commit**

```bash
git add tests/church_bv/classes.rs docs/runs/2026-10-23/fixtures/held docs/runs/*/scripts/class_held.sh docs/runs/*/scripts/class_commit.sh docs/runs/*/patches/class_commit.patch docs/tier-cycle.md docs/learned-vs-fixed.md docs/runs.md
git diff --cached --stat
printf 'classes: held-out replacements all proved (run <id>: <made> made, <met> laws met and kernel-checked); a build'"'"'s commit measured (run <id>), mi_collect <kept|not kept>\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n' > "$TEMP/msg.txt"
git commit -q -F "$TEMP/msg.txt"
```

---

### Task 5: The twin filter on the table

**Files:**
- Modify: `tests/church_bv/search.rs` (delete `ClassReps`; add `twin_key`; tests; `hidden_twins_in_a_run`)
- Modify: `tests/church_bv/driver.rs` (`Draw`, `filtered`, `scope_extras`, test)
- Modify: `docs/tier-cycle.md`, `docs/runs.md`, `docs/learned-vs-fixed.md` if it names `ClassReps`
- Modify: `docs/superpowers/specs/2026-10-17-law-generator-design.md` only if it states `ClassReps`'s pools as current
  (grep first)

**Interfaces:**
- Consumes: Task 2's `Classes::get`, `Classes::canonical`.
- Produces: `search::twin_key(a: &Term, b: &Term) -> Option<String>`; `driver::filtered(source: &[(Term, Term)], served: &[(Term, Term)]) -> Vec<(Term, Term)>`.

- [ ] **Step 1: Build the baseline exe**

Before any edit: `cp "$TEMP/bv_ct4.exe" "$TEMP/bv_ct4_base.exe"` if `bv_ct4.exe` is Task 4's final commit's build
(rebuild and copy if Step 5 of Task 4 changed `Classes::get`). This is the gate's arm A.

- [ ] **Step 2: Rewrite the tests on the new interface**

In `search.rs`, replace the test `normalize_maps_two_leaf_nodes_to_their_class` (its doc comment included) with:

```rust
/// The twin key is the same for two laws that differ by renaming variables, is `None` for a law whose sides are equal
/// below their roots, keeps each side's root (both sides of `sub(y, y) = and(x, 0)` are `0`), and leaves a law between
/// two members of one class (associativity) nontrivial.
#[test]
pub fn twin_keys_rename_normalize_below_roots_and_keep_them() {
    let p = parse_term;
    let swap = twin_key(&p("sub(or(y, x), y)"), &p("and(y, z)"));
    assert_eq!(twin_key(&p("sub(or(x, y), x)"), &p("and(x, z)")), swap, "renaming x and y");
    assert!(swap.is_some());
    assert_eq!(twin_key(&p("add(sub(y, y), x)"), &p("add(0, x)")), None, "sides equal below their roots");
    assert!(twin_key(&p("sub(y, y)"), &p("and(x, 0)")).is_some(), "a side's root stays");
    assert!(twin_key(&p("add(add(x, y), z)"), &p("add(x, add(y, z))")).is_some(), "a law within one class");
    assert_eq!(twin_key(&p("and(or(x, sub(y, 0)), z)"), &p("z")), twin_key(&p("and(or(x, y), z)"), &p("z")), "padding below the root");
}
```

In `normalize_finds_the_probes_twins`, replace `let mut c = ClassReps::new(&[]);` and the three `c.key(a, b)` uses
with `twin_key(a, b)`, and change its doc comment's first sentence to "On the probe's fixture (...), the extras whose
twin key (on the class table) is a served law's key, and the trivial ones." Keep the `assert_eq!((twins, trivial),
(443, 409));` for now.

In `driver.rs`'s `filtered_drops_twins_skeletons_and_trivial_laws`, change
`filtered(&[twin, skel, trivial, other], &served, &mut ClassReps::new(&[]))` to `filtered(&[twin, skel, trivial, other], &served)`.

- [ ] **Step 3: Run them to verify they fail**

Run: `cargo test --release --test church_bv -j 8 -- twin_keys normalize_finds filtered_drops 2>&1 | grep -E "^error" | head -3`
Expected: compile errors: `twin_key` not found; `filtered` takes 3 arguments.

- [ ] **Step 4: Implement**

In `search.rs`, delete `pub struct ClassReps` and its `impl` (from the doc comment "/// The width-4 value classes of the
leaves, the two-leaf terms and a pool's subterms" through the end of `impl ClassReps`), and add in their place:

```rust
/// A law's twin key (the law generator's twin filter, docs/superpowers/specs/2026-10-17-law-generator-design.md §1; on
/// the class table since docs/superpowers/specs/2026-10-22-class-table-normal-form-design.md §6): the least `a = b` text,
/// over the six renamings of x, y, z and both side orders, of the law renamed and then each side's children made
/// canonical (renaming first, since a representative is not preserved by renaming). A side's root is kept: canonicalizing
/// it too would make every law trivial whose sides are of one class, which every true law within the table's size is.
/// `None` if the sides are then one term (the law is trivial).
pub fn twin_key(a: &Term, b: &Term) -> Option<String> {
    let c = crate::classes::Classes::get();
    let side = |t: Term| match *t.node() {
        Node::Op(o, x, y) => Term::op(o, c.canonical(&x), c.canonical(&y)),
        _ => t,
    };
    if side(*a) == side(*b) {
        return None;
    }
    const PERMS: [[usize; 3]; 6] = [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]];
    fn renamed(t: Term, to: &[usize; 3]) -> Term {
        match *t.node() {
            Node::V(i) => Term::v(to[i]),
            Node::Op(o, a, b) => Term::op(o, renamed(a, to), renamed(b, to)),
            _ => t,
        }
    }
    let mut best: Option<String> = None;
    for p in &PERMS {
        for (l, r) in [(a, b), (b, a)] {
            let s = format!("{} = {}", side(renamed(*l, p)).show(), side(renamed(*r, p)).show());
            if best.as_ref().is_none_or(|k| s < *k) {
                best = Some(s);
            }
        }
    }
    best
}
```

(`renamed` maps `V(i)` with `i < 3`; laws reaching the filter are over x, y, z, as before.)

In `hidden_twins_in_a_run`: delete `let mut reps: std::collections::HashMap<String, ClassReps> = Default::default();`
and the `let c = reps.entry(...)...;` block; replace each `c.key(a, b)` with `twin_key(a, b)`; in its doc comment
change "once every node is normalized over the family's pool" to "once every node below a side's root is made
canonical by the class table".

In `driver.rs`:
- `struct Draw`: delete the `reps` field (and its doc comment if it has one); `Draw::new` becomes
  `Draw { laws: Default::default(), draw }`; delete `fn reps` and its doc comment.
- `filtered`: signature `fn filtered(source: &[(Term, Term)], served: &[(Term, Term)]) -> Vec<(Term, Term)>`; its two
  `reps.key(..)` calls become `twin_key(..)`.
- `scope_extras`: `let laws = filtered(&draw.grammar(&c), &served);`.

Then `grep -n "ClassReps\|\.reps(" tests/church_bv/*.rs` must print nothing.

- [ ] **Step 5: Measure the fixture's counts and pin them**

Run: `cargo test --release --test church_bv -j 8 -- twin_keys normalize_finds filtered_drops 2>&1 | grep -E "^test |left|right" | head`
Expected: `twin_keys...` and `filtered_drops...` ok; `normalize_finds_the_probes_twins` FAILED with `left: (<t>, <v>)`
and `right: (443, 409)`. Put the measured `(t, v)` in the assertion and replace the comment above it with:
"// on the class table (plan 2026-10-23, Task 5): <t> twins and <v> trivial laws; `ClassReps` (two-leaf nodes and a
child of equal value) found 443 and 409". Rerun: ok. If `t` is below 400 or `v` below 350, say so in the commit: the
filter drops fewer laws than before.

- [ ] **Step 6: Run the whole suite**

Run: `cargo test --release --test church_bv -j 8 2>&1 | grep -E "^test result|FAILED|panicked" | head`
Expected: ok, 0 failed (one test replaced, none added: the passed count is Task 3's).

- [ ] **Step 7: Gate the generator stage**

Run (bash, repo root; check CPU leases first):
```bash
cargo test --release --test church_bv --no-run -j 8 2>&1 | tail -1
cp "$(ls -t target/release/build/tatic/*/out/church_bv-*.exe target/release/deps/church_bv-*.exe 2>/dev/null | head -1)" "$TEMP/bv_ct5.exe"
powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind gate -Timed -Name ct-twins-gate -Command "bash docs/runs/2026-10-18/scripts/salts_ab.sh '$(cygpath -w "$TEMP/bv_ct4_base.exe")' '$(cygpath -w "$TEMP/bv_ct5.exe")' 1 2 3 4 5"
```
Expected: about 10 minutes (2026-10-21-t3-gate: 9.3); `0 of 10 arms failed`. Rules will differ (the extras differ);
record per arm total M, wall and job CPU, and each scope's law count (`GEN_LAWS <scope>: <n> laws in <s>s`;
`grep -h "^GEN_LAWS" "$RUN_DIR"/s*_A/result.txt` and `_B`). If B's total M is more than 3% above A's, stop and report
before Task 6: the spec's §6 expects no loss within size 9.

- [ ] **Step 8: Record and commit**

Fill in the runs.md row. In `docs/tier-cycle.md`, under the section added in Task 4, add a paragraph "The twin filter
on the table" with: the fixture counts (old 443/409, new), the gate's M, wall and job CPU per arm, and L per scope.
Grep `docs/` and `PARKED.md` for `ClassReps` and fix any line that states it as current (tier-cycle history sections
stay as written). Then:

```bash
git add tests/church_bv/search.rs tests/church_bv/driver.rs docs/tier-cycle.md docs/runs.md
git diff --cached --stat
printf 'search: the law generator'"'"'s twin filter on the class table (twin_key); ClassReps and the per-family pools it built are gone; gate run <id>: M <A> -> <B>\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n' > "$TEMP/msg.txt"
git commit -q -F "$TEMP/msg.txt"
```
(Add any other doc files the grep fixed.)

---

### Task 6: Phase 1 in `prove_eq`, its count, and the gate

**Files:**
- Modify: `tests/church_bv/rewrite.rs` (`prove_eq`)
- Modify: `tests/church_bv/search.rs` (`rule_set_kernel_check_task`: the `classes` record)
- Modify: `tests/church_bv/driver.rs` (`serve`, `m.tsv`, module doc)
- Modify: `tests/church_bv/classes.rs` (test)
- Modify: `docs/tier-cycle.md`, `docs/learned-vs-fixed.md`, `docs/runs.md`

**Interfaces:**
- Consumes: Task 3's `Classes::normalize`, `Job::table_steps`; Task 5's `bv_ct5.exe`.
- Produces: `prove_eq`'s table step (ablation `classes`); the `classes` task record; `m.tsv`'s ninth column.

- [ ] **Step 1: Write the failing test**

Append to `classes.rs`:

```rust
/// Phase 1 (spec §4): the table closes a law the join left at 20000 visits (run `2026-10-22-join-residue`) with no
/// machine proof, and the proof checks; with `ABLATE=classes` the law takes the old path (a machine proof, or none).
#[test]
fn prove_eq_closes_a_residue_law_by_the_table() {
    let (a, b) = (parse_term("add(and(z, xor(x, -1)), y)"), parse_term("add(xor(x, and(xor(x, -1), z)), sub(y, x))"));
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let plan = prove_eq(job, 4, 3, &a, &b).expect("closed by the table");
        assert_eq!(job.rw.fallbacks, 0);
        assert!(!job.table_steps.is_empty());
        let (p, s) = law_proof(job, 4, 3, &a, &b, &plan);
        job.lemmas.ck("residue law", &p, &s);
    });
    let results = std::fs::File::create(std::env::temp_dir().join("classes_ablated.results")).unwrap();
    let job = &mut Job::new(Setup::for_task(vec![("ABLATE".into(), "classes".into())], results));
    let r = prove_eq(job, 4, 3, &a, &b);
    assert!(job.table_steps.is_empty(), "the ablated path takes no table step");
    assert!(r.is_none() || job.rw.fallbacks > 0, "without the table the law needs the machine or stays open");
}
```

- [ ] **Step 2: Run it to verify it fails**

Run: `cargo test --release --test church_bv -j 8 -- classes::prove_eq_closes 2>&1 | grep -E "panicked|^test " | head -3`
Expected: FAILED, panicking at `assert_eq!(job.rw.fallbacks, 0)` (left 1) or at `closed by the table`.

- [ ] **Step 3: Implement the step**

In `rewrite.rs`'s `prove_eq`, change the comment `// each step below can be switched off: \`ABLATE=eq_truth,eq_pos,shrmask\``
to `// each step below can be switched off: \`ABLATE=eq_truth,eq_pos,classes,shrmask\``, and insert after the
per-position step's closing brace (before the comment "congruence on equal operators ... were removed"):

```rust
    // the learned class table (docs/superpowers/specs/2026-10-22-class-table-normal-form-design.md §4): both sides
    // normalized by its proved replacements; if they meet, the law is closed with no rule
    if !job.setup().ablated("classes") {
        let c = crate::classes::Classes::get();
        let ((na, pa), (nb, pb)) = (c.normalize(job, n, k, a), c.normalize(job, n, k, b));
        if na == nb {
            return Some(Plan::trans(job, pa, Plan::sym(job, pb)));
        }
    }
```

and extend `prove_eq`'s doc comment: "...the per-position law; the class table's normal forms (when both sides meet);
the bit-0 mask reduction; ...".

- [ ] **Step 4: Run the test and the suite**

Run: `cargo test --release --test church_bv -j 8 2>&1 | grep -E "^test result|FAILED|panicked" | head`
Expected: ok, 0 failed. A test elsewhere that pins an exact plan, M or normal form may change because `prove_eq` now
closes more pairs: read each failure; a changed count caused by the table is updated with a comment naming this plan's
Task 6, anything else is a bug to fix.

- [ ] **Step 5: The `classes` record and `m.tsv`'s column**

In `search.rs`'s `rule_set_kernel_check_task`, change
`.chain([("reached", cost.reached)])` to `.chain([("reached", cost.reached), ("classes", job.table_steps.len() as u64)])`.

In `driver.rs`'s `serve` closure: change the comment above it to
`// (M, laws, laws that used up the rule budget, laws joined, terms the join reached, class-table replacements used) of the batch at \`skip\``;
change `let (n, k, p, x, j, r) = (count("proved"), count("free"), count("none"), count("exhausted"), count("joined"), count("reached"));`
to also read `count("classes")` as `cl`, and return `(n - k + p, n + p, x, j, r, cl)`. In the loop below,
`let (m, laws, ex, j, rc) = serve(skip);` becomes `let (m, laws, ex, j, rc, cl) = serve(skip);` and the `m.tsv` line
becomes `&format!("{r}\t{m}\t{laws}\t{}\t{}\t{ex}\t{j}\t{rc}\t{cl}\n", count(), t0.elapsed().as_secs())`. In the
module doc's `m.tsv` description, after "terms the join's searches reached: its cost, which M does not show" add
", and the distinct class-table replacements the batch used, each with a proof (spec decision 2: apart from M)".

Run: `cargo test --release --test church_bv -j 8 2>&1 | grep -E "^test result|FAILED" | head -3`
Expected: ok.

- [ ] **Step 6: Commit the code**

```bash
git add tests/church_bv/rewrite.rs tests/church_bv/search.rs tests/church_bv/driver.rs tests/church_bv/classes.rs
git diff --cached --stat
printf 'prove_eq: the class table'"'"'s normal forms close a pair after the per-position step (ABLATE=classes); the kernel-check task records the replacements used, m.tsv'"'"'s ninth column\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n' > "$TEMP/msg.txt"
git commit -q -F "$TEMP/msg.txt"
```

- [ ] **Step 7: The gate**

Run (bash, repo root; check CPU leases first):
```bash
cargo test --release --test church_bv --no-run -j 8 2>&1 | tail -1
x="$(ls -t target/release/build/tatic/*/out/church_bv-*.exe target/release/deps/church_bv-*.exe 2>/dev/null | head -1)"
cp "$x" "$TEMP/bv_ct6.exe"; cp "$x" "$TEMP/bv_ct6_off.exe"; printf 'ABLATE=classes\n' > "$TEMP/bv_ct6_off.exe.env"
w() { cygpath -w "$1"; }
powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind gate -Timed -Name ct-phase1-restore -Command "bash docs/runs/2026-10-18/scripts/salts_ab.sh '$(w "$TEMP/bv_ct5.exe")' '$(w "$TEMP/bv_ct6_off.exe")' 1"
powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind gate -Timed -Name ct-phase1-gate -Command "bash docs/runs/2026-10-18/scripts/salts_ab.sh '$(w "$TEMP/bv_ct6_off.exe")' '$(w "$TEMP/bv_ct6.exe")' 1 2 3 4 5"
```
Expected: the restore run (about 2 minutes) ends `rules same in 3 of 3 loops; 0 of 2 arms failed` with equal M per
loop (Review Focus 3: the `.env` switch restores the old answers; if not, stop and find why). The gate (about 10
minutes or more: each worker builds the table once, about 1.7 s) ends `0 of 10 arms failed`. Then:
- `find "$RUN_DIR"/s1_B -name m.tsv -exec awk -F'\t' '{print NF}' {} + | sort -u` prints `9`, and the ninth column
  (`find ... -exec cut -f9 {} +`) is nonzero in B and 0 in A;
- `grep -h "^CLASSES " "$RUN_DIR"/s1_B -r | head -2` shows the table's size and build time;
- `grep -rh "^CLASS_UNUSABLE" "$RUN_DIR"/s*_B | sort -u | wc -l` counts the unusable replacements met;
- per arm, total M, wall, job CPU and the largest `peakproc` (`grep -h peakproc "$RUN_DIR"/s*_A/result.txt`, `_B`).
If B's largest `peakproc` exceeds A's by more than 150 MB (Review Focus 5), or B's job CPU exceeds A's by more than
25%, finish recording and stop for a decision before any further work.

- [ ] **Step 8: Record and commit**

Fill in both runs.md rows' headlines and notes. In `docs/tier-cycle.md`, add a section "*The class table in
`prove_eq`: phase 1 (<date>; plan docs/superpowers/plans/2026-10-23-class-table-normal-form.md; runs <restore id>,
<gate id>)*" with: the restore check; M per salt and in total per arm, rules agreement, wall and job CPU per arm; table
replacements per batch (the ninth column: range and total per arm B); unusable replacements met; build time and table
size per worker; the largest `peakproc` per arm; and the verdict: whether phase 1 pays, and what phase 2's plan should
start from. In `docs/learned-vs-fixed.md`, candidate 4: replace "It is being built as a module ..." with one sentence
giving phase 1's result and pointing at that section. If the gate parks anything (cost, memory), add it to `PARKED.md`
with what, why, trigger, evidence (section name) and status. Grep `ROADMAP.md`, `PARKED.md` and the spec for wording
this changes ("Probe only, not wired in", "draft spec") and fix it. The spec stays `active` (steps 4-5 remain); this
plan's front matter becomes `status: done`.

```bash
git add docs/tier-cycle.md docs/learned-vs-fixed.md docs/runs.md docs/superpowers/plans/2026-10-23-class-table-normal-form.md
git diff --cached --stat
printf 'runs: the class table in prove_eq (phase 1), gate <id>: M <A> -> <B>, job cpu <A> -> <B> s, <n> replacements per batch; plan done\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n' > "$TEMP/msg.txt"
git commit -q -F "$TEMP/msg.txt"
```
(Add `PARKED.md`, `ROADMAP.md` or the spec if they changed.)
