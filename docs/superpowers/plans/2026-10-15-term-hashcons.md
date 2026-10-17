---
status: done
---

# Hash-consed `Term` Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make church_bv's `rewrite::Term` a `Copy` pointer to an interned node, so clone, drop, hash and equality are O(1), and measure the sweep.

**Architecture:** `Term(&'static Node)`. Leaves are statics, `Op` nodes are interned in a 16-shard global table and never freed. Equality and hashing use the address; `Ord` is structural and equal to today's derived order. Every use site in rewrite.rs, search.rs and machine.rs moves to `Term::op`/`Term::v`/`Term::ZERO`/`Term::ONES` and `match *t.node()`.

**Tech Stack:** Rust (nightly 1.100), hashbrown 0.16 `HashTable`, PowerShell/bash run scripts, samply.

**Spec:** `docs/superpowers/specs/2026-10-15-term-hashcons-design.md`

## Global Constraints

- Work in a worktree: `git worktree add ../tatic-hc -b term-hashcons main`. Every cargo call there uses `-j 8`. Worktree files are CRLF: change them with the Edit tool, or use `\r?\n` in any regex.
- Never let python read stdin: write the script to a file and run `python -P f.py < /dev/null`.
- Runs: BelowNormal priority, affinity FFF (at most 12 cores). Report load (`\Processor(_Total)\% Processor Time`) and Defender RTP with every timing. Never kill other sessions' processes.
- Signatures keep `&Term`. No `unsafe`. No new dependency.
- Outputs identical: a fixed-salt sweep's `.tsv` files are identical apart from seconds columns; logs differ only in timings and their own path, with every `LEMMA_CACHE` line equal; anything else fails.
- Commit messages end with `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`. No merge into main and no push without the user's go-ahead.

## Execution

Task 2 goes to one Sonnet implementer (a few hundred mechanical edits with small judgment calls); Tasks 1, 3 and 4 run inline. Each task depends on the one before.

---

### Task 1: Worktree, base exe, pinned order

**Files:**
- Create (throwaway, never committed): a test in `../tatic-hc/tests/church_bv/rewrite.rs`

**Interfaces:**
- Produces: `$TEMP/kk/hc_old.exe` (church_bv at main's HEAD); the `PINNED` list for Task 2's test, the sorted `show()` strings.

- [ ] **Step 1:** `git worktree add ../tatic-hc -b term-hashcons main`; check `git -C ../tatic-hc log -1 --oneline` is main's HEAD.
  The worktree's `target/` starts empty, so its first build compiles every dependency (several minutes; wasmtime).
  Record the baseline: `cargo clippy --release --tests -j 8 2>&1 | grep -c "^warning"` there, into `clippy_base.txt`
  in the scratchpad.
- [ ] **Step 2:** In the worktree, append this throwaway test to `tests/church_bv/rewrite.rs`:

```rust
#[test]
fn pin_term_order() {
    let mut ts: Vec<Term> = PIN_SOURCE.iter().map(|s| parse_term(s)).collect();
    ts.sort();
    for t in &ts {
        println!("PIN {}", t.show());
    }
}
const PIN_SOURCE: [&str; 38] = [
    "add(x, add(y, z))", "x", "and(add(x, y), -1)", "-1", "add(y, x)", "q", "xor(x, -1)", "0", "add(x, y)",
    "add(add(x, y), z)", "add(x, x)", "and(x, y)", "or(x, 0)", "sub(-1, x)", "lt(x, y)", "shl1(x, x)", "shr1(y, y)",
    "add(add(x, y), y)", "add(add(x, z), y)", "and(add(x, y), 0)", "xor(and(x, y), or(x, y))", "xor(and(x, y), or(y, x))",
    "or(and(x, y), and(x, z))", "sub(add(x, y), y)", "sub(x, sub(x, y))", "lt(sub(x, y), 0)", "shl1(add(x, y), x)",
    "add(shl1(x, x), 0)", "add(0, x)", "add(-1, x)", "add(u, v)", "add(w, p)", "and(-1, 0)", "y",
    "xor(xor(x, y), xor(z, u))", "xor(xor(x, y), xor(z, v))", "add(add(add(x, y), z), u)", "add(x, add(y, add(z, u)))",
];
```

- [ ] **Step 3:** Run `cargo test --release --test church_bv -j 8 pin_term_order -- --nocapture` in the worktree. Expected: 38 `PIN` lines. Save them (in order) to the scratchpad as `pinned.txt`; Task 2's `PINNED` array is these strings in this order.
- [ ] **Step 4:** Remove the test (`git -C ../tatic-hc checkout -- tests/church_bv/rewrite.rs`; `git status` clean), rebuild with `cargo test --release --test church_bv -j 8 --no-run`, and copy the printed executable to `$TEMP/kk/hc_old.exe`.

### Task 2: The interned `Term` and every use site (one commit)

**Files:**
- Modify: `tests/church_bv/rewrite.rs` (type at lines 1-11, `parse_term` ~1022, unify ~1285-1315, every site)
- Modify: `tests/church_bv/search.rs`, `tests/church_bv/machine.rs` (every `Term` site)
- Test: new tests at the end of `tests/church_bv/rewrite.rs`

**Interfaces:**
- Consumes: `pinned.txt` from Task 1.
- Produces: `Term` (Copy), `Node`, `Term::ZERO`, `Term::ONES`, `Term::v(usize) -> Term`, `Term::op(usize, Term, Term) -> Term`, `Term::node(&self) -> &'static Node`.

- [ ] **Step 1: Write the new tests** at the end of `rewrite.rs` (they fail to compile until Step 3):

```rust
#[test]
fn term_interning() {
    let (x, y) = (Term::v(0), Term::v(1));
    let a = Term::op(ADD, x, Term::op(XOR, y, Term::ONES));
    let b = Term::op(ADD, x, Term::op(XOR, y, Term::ONES));
    assert!(std::ptr::eq(a.node(), b.node()));
    assert!(a != Term::op(ADD, Term::op(XOR, y, Term::ONES), x));
    // built on 8 threads at once: one node per term
    let built: Vec<Vec<Term>> = std::thread::scope(|s| {
        let hs: Vec<_> = (0..8)
            .map(|_| s.spawn(|| (0..200).map(|i| Term::op(i % 8, Term::v(i % 5), Term::op(AND, Term::v(i % 7), Term::ZERO))).collect::<Vec<_>>()))
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    for w in &built[1..] {
        assert!(w.iter().zip(&built[0]).all(|(p, q)| std::ptr::eq(p.node(), q.node())));
    }
    assert_eq!((std::mem::size_of::<Term>(), std::mem::size_of::<Node>()), (8, 32));
}

#[test]
fn term_order_is_the_old_derived_order() {
    let mut ts: Vec<Term> = PIN_SOURCE.iter().map(|s| parse_term(s)).collect();
    ts.sort();
    let got: Vec<String> = ts.iter().map(|t| t.show()).collect();
    assert_eq!(got, PINNED);
    for t in &ts {
        assert!(parse_term(&t.show()) == *t);
    }
    // variables past VARS (renamed apart) sort by index, before every other leaf
    assert!(Term::v(9) < Term::v(10) && Term::v(63) < Term::ZERO && Term::ZERO < Term::ONES);
}
/// Terms in no particular order; `PINNED` is their sort under the old derived `Ord`, captured at main's HEAD.
const PIN_SOURCE: [&str; 38] = [
    "add(x, add(y, z))", "x", "and(add(x, y), -1)", "-1", "add(y, x)", "q", "xor(x, -1)", "0", "add(x, y)",
    "add(add(x, y), z)", "add(x, x)", "and(x, y)", "or(x, 0)", "sub(-1, x)", "lt(x, y)", "shl1(x, x)", "shr1(y, y)",
    "add(add(x, y), y)", "add(add(x, z), y)", "and(add(x, y), 0)", "xor(and(x, y), or(x, y))", "xor(and(x, y), or(y, x))",
    "or(and(x, y), and(x, z))", "sub(add(x, y), y)", "sub(x, sub(x, y))", "lt(sub(x, y), 0)", "shl1(add(x, y), x)",
    "add(shl1(x, x), 0)", "add(0, x)", "add(-1, x)", "add(u, v)", "add(w, p)", "and(-1, 0)", "y",
    "xor(xor(x, y), xor(z, u))", "xor(xor(x, y), xor(z, v))", "add(add(add(x, y), z), u)", "add(x, add(y, add(z, u)))",
];
const PINNED: [&str; 38] = PINNED_FROM_TASK_1;
```

  `PINNED_FROM_TASK_1` is not code: before dispatching this task, the controller replaces it in the brief with the
  literal array `["…", …]` of `pinned.txt`'s 38 strings (the `PIN ` prefix stripped), in file order.

- [ ] **Step 2: Replace the type.** Lines 3-11 of `rewrite.rs` become:

```rust
/// A hash-consed term: a pointer to its one node. Leaves are statics, `Op` nodes are interned (`Term::op`) and never
/// freed, so equal terms are the same pointer: `==` and `Hash` take the address, and clone is a copy.
/// `show()` is for text (files, logs, lemma names) and the text orders. `Ord` is structural (`V < Zero < Ones < Op`,
/// then fields), the order the derived one gave; it only makes canonical keys (a sorted rule set).
#[derive(Clone, Copy)]
pub struct Term(&'static Node);
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Node {
    V(usize),
    Zero,
    Ones,
    Op(usize, Term, Term),
}
static LEAVES: [Node; 64] = {
    let mut a = [Node::Zero; 64];
    let mut i = 0;
    while i < 64 {
        a[i] = Node::V(i);
        i += 1;
    }
    a
};
// The leaf consts name statics: a promoted `&Node::Zero` need not have one address.
static ZERO_NODE: Node = Node::Zero;
static ONES_NODE: Node = Node::Ones;
const SHARDS: usize = 16;
static TABLE: [std::sync::Mutex<hashbrown::HashTable<&'static Node>>; SHARDS] =
    [const { std::sync::Mutex::new(hashbrown::HashTable::new()) }; SHARDS];
/// The table's hash of `Op(o, a, b)`: unseeded, so every call agrees (a default-built seeded hasher may not).
fn op_hash(o: usize, a: Term, b: Term) -> u64 {
    let mut h = o as u64 ^ (a.0 as *const Node as u64).rotate_left(21) ^ (b.0 as *const Node as u64).rotate_left(43);
    h ^= h >> 33;
    h = h.wrapping_mul(0xff51_afd7_ed55_8ccd);
    h ^= h >> 33;
    h = h.wrapping_mul(0xc4ce_b9fe_1a85_ec53);
    h ^ h >> 33
}
impl Term {
    pub const ZERO: Term = Term(&ZERO_NODE);
    pub const ONES: Term = Term(&ONES_NODE);
    pub fn v(i: usize) -> Term {
        assert!(i < LEAVES.len(), "variable {i} past the leaf table");
        Term(&LEAVES[i])
    }
    /// The one node `Op(o, a, b)`, made on first sight. The shard is bits 40..44 of the hash, which hashbrown uses
    /// for neither its tag (top 7 bits) nor its bucket (low bits).
    pub fn op(o: usize, a: Term, b: Term) -> Term {
        let (h, n) = (op_hash(o, a, b), Node::Op(o, a, b));
        let mut t = TABLE[(h >> 40) as usize % SHARDS].lock().unwrap();
        if let Some(&m) = t.find(h, |m| **m == n) {
            return Term(m);
        }
        let m: &'static Node = Box::leak(Box::new(n));
        t.insert_unique(h, m, |m| match **m {
            Node::Op(o, a, b) => op_hash(o, a, b),
            _ => unreachable!("only Op nodes are interned"),
        });
        Term(m)
    }
    pub fn node(&self) -> &'static Node {
        self.0
    }
}
impl PartialEq for Term {
    fn eq(&self, other: &Term) -> bool {
        std::ptr::eq(self.0, other.0)
    }
}
impl Eq for Term {}
impl std::hash::Hash for Term {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        (self.0 as *const Node as usize).hash(h)
    }
}
impl Ord for Term {
    fn cmp(&self, other: &Term) -> std::cmp::Ordering {
        if self == other {
            return std::cmp::Ordering::Equal;
        }
        let rank = |n: &Node| match n {
            Node::V(_) => 0,
            Node::Zero => 1,
            Node::Ones => 2,
            Node::Op(..) => 3,
        };
        match (*self.node(), *other.node()) {
            (Node::V(i), Node::V(j)) => i.cmp(&j),
            (Node::Op(o, a, b), Node::Op(p, c, d)) => o.cmp(&p).then_with(|| a.cmp(&c)).then_with(|| b.cmp(&d)),
            (x, y) => rank(&x).cmp(&rank(&y)),
        }
    }
}
impl PartialOrd for Term {
    fn partial_cmp(&self, other: &Term) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
```

- [ ] **Step 3: Migrate every use site** in rewrite.rs, search.rs and machine.rs, by these rules only:
  - `Term::Op(o, Box::new(a), Box::new(b))` → `Term::op(o, a, b)`; an argument that was `x.clone()` of a `&Term` becomes `*x`; a moved `Term` stays as is.
  - `Term::V(e)` as a value → `Term::v(e)`; `Term::Zero` / `Term::Ones` as values → `Term::ZERO` / `Term::ONES` (`&Term::Zero` → `&Term::ZERO`).
  - A `match t { Term::… }` / `if let Term::…` / `matches!(t, Term::…)` on a `Term` or `&Term` → the same on `*t.node()` with `Node::` patterns. Bindings are now values: drop `*o`, `*i`, `*v` derefs and `&x`/`&**x` around bound children (pass `&a` where a `&Term` is wanted).
  - Tuple matches on two terms (unify, rewrite.rs ~1302) → `match (*ra.node(), *rb.node())`, keeping `ra`/`rb` as named `Term`s; `sub[i] = Some(t)` stays (a `Term` is `Copy`).
  - Every `.clone()` on a `Term` → removed (`cargo clippy --tests` with `clone_on_copy` lists any left).
  - Local helpers such as `let op = |o, a, b| Term::Op(o, Box::new(a), Box::new(b))` keep their names and become `Term::op(o, a, b)`.
  - Nothing else changes: no signature from `&Term` to `Term`, no reordering, no new helpers, no comment rewrites beyond lines that named `Box`.
- [ ] **Step 4: Build and test.** `cargo test --release --test church_bv -j 8` in the worktree. Expected: all pass, including `term_interning` and `term_order_is_the_old_derived_order`, with the same count of passed/ignored tests as at main's HEAD plus 2.
- [ ] **Step 5: Clippy.** `cargo clippy --release --tests -j 8 2>&1 | grep -c "^warning"` is at most Task 1's
  `clippy_base.txt` count; no `clone_on_copy`.
- [ ] **Step 6: Commit.** Check `git diff --stat` (only the three files), then commit "church_bv: hash-consed Term …" with the attribution line.

### Task 3: Identical outputs

**Files:**
- Create: `docs/runs/2026-10-12/scripts/hc_seq.sh` (in the worktree, committed with Task 4)

**Interfaces:**
- Consumes: `$TEMP/kk/hc_old.exe` (Task 1), the Task 2 exe copied to `$TEMP/kk/hc_new.exe`.

- [ ] **Step 1:** Copy `s3_seq.sh` to `hc_seq.sh`; change only its usage comment ("Term hash-consing") and the two `SWEEP="mines own pooled"` occurrences to `SWEEP="mines own cold pooled"`, and its done file to `hc_done.txt`. `diff s3_seq.sh hc_seq.sh` shows only those lines.
- [ ] **Step 2:** Build the Task 2 commit (`--no-run`), copy the exe to `$TEMP/kk/hc_new.exe`. Run `bash hc_seq.sh hc $TEMP/kk/hc_old.exe $TEMP/kk/hc_new.exe` in the background; wait on `hc ALL` in `$TEMP/kk/hc_done.txt` with a loop that exits (about 4 minutes for four sweeps).
- [ ] **Step 3:** Compare:

```bash
k=$(cygpath -u "$TEMP")/kk
for s in 1 2; do echo "salt $s:"; diff -rq $k/hc_old_$s $k/hc_new_$s; done
norm() { sed -E 's/[0-9]+(\.[0-9]+)?(s|ms|µs)\b/T/g; s/hc_(old|new)/RUN/g' "$1"; }
# for each differing file f: diff <(norm $k/hc_old_$s/$f) <(norm $k/hc_new_$s/$f)
```

  Expected: every `.tsv` identical apart from seconds columns, every differing log empty after `norm`, `LEMMA_CACHE` lines equal. Any other difference stops the plan: report it.

### Task 4: Speed, profile, docs

**Files:**
- Modify: `docs/tier-cycle.md` (entry "Where a sweep spends its time", ~line 3148), `docs/runs/2026-10-12/README.md`
- Create: `docs/runs/2026-10-12/scripts/hc_rounds.ps1`

- [ ] **Step 1: Twelve sweeps.** Write `hc_rounds.ps1`: six pairs, order old-new in odd pairs and new-old in even ones, each sweep `powershell -NoProfile -File sweep_job.ps1 <exe> normal <r>` with `r` from 110, every printed line appended to `$env:TEMP\kk\hc_rounds.txt`, then "hc_rounds ALL". Check load and RTP first; run it in the background (about 13 minutes), wait on "hc_rounds ALL" with a loop that exits.
- [ ] **Step 2: Summarize:** median `jobcpu` and `wall` per arm, pairs won by new out of 6, load range, RTP.
- [ ] **Step 3: Profile.** In a scratch copy of the Task 2 tree (never committed), add a `#[test] #[ignore] fn prof_sweep()` that sets `SWEEP_OUT`, `SALT=1` and `SWEEP=mines own cold pooled` and calls
  `driver::sweep()` (made `pub(crate)` in the copy if it is private), build with `CARGO_PROFILE_RELEASE_DEBUG=true`, run `& "$env:USERPROFILE\.claude\samply\profile.ps1" -Exe <copy of exe> -Out <full path>.json.gz -ExeArgs prof_sweep,--exact,--ignored,--nocapture`, and bucket it with the scratchpad's `sw_where.py` as in the 744b31d profile. Report the shares of `Term` clone/drop/hash, mimalloc, `rewrite::rewrite`, the kernel, and the new top entries.
- [ ] **Step 4: Docs.** In tier-cycle.md's "Where a sweep spends its time", replace the first open direction with the result: the distinct-node probe (at most 57,272 distinct `Op`s per process, 32,086 in `lib_cmp3d` against 64.8 M drops, 1.26 M over 171 processes), the design in one sentence, the identical-output gate, the twelve-sweep numbers with load and RTP, and the new profile. Add a README row in the format `(no rows) | desc | scripts | section`.
- [ ] **Step 5: Commit** the docs and scripts in the worktree; then stop and ask the user before merging into main or pushing.
