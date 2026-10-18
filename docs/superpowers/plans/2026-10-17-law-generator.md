---
status: done
---

# Law Generator Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans (the tasks build on each other's interfaces in two files, so it runs inline) to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Turn the law-source probe (`driver::extra_laws`) into a designed extras stage: the non-padding grammar laws, filtered once per scope by a value-class twin filter and a skeleton filter, drawn into fixed-size slices, taken by every mine with rule rounds; then measure its count rule on cold sweeps and fix the default.

**Architecture:** `search.rs` gains `ClassReps` (two-leaf value classes, `normalize`, the renaming-first twin `key`) and a split of `grammar_laws` into sampling (`grammar_sample`) and grouping, with the non-padding filter built in and salt and `deep3` as arguments. `driver.rs` gains a pre-pass in `sweep` that builds every scope's loops, draws each scope's filtered list and slices (`scope_extras`, `extra_slices`, `takes_extras`), checks every scope before any stage runs, and hands each loop its list and slices in two new `LoopCfg` fields; `run_loop`'s mines append their slice. The probe (`extra_laws`, its `MEMO`, `MINE_EXTRA`, `MINE_SOURCE`, `GEN_PAD`, `GEN_TERMS`) goes.

**Tech Stack:** Rust (church_bv test crate, `cargo test --release --test church_bv`), bash run scripts, Python 3 analysis scripts.

**Spec:** `docs/superpowers/specs/2026-10-17-law-generator-design.md` (status draft, approved by the user 2026-10-17 with the source decision "option 1"). Read it before Task 1.

**Scope:** the spec's build order steps 1-3 (code, cold rounds A and B, fixing the default). Steps 4 (warm loops and ref mines, with a temporary `ABLATE=gen_ref`) and 5 (hidden twins beyond two-leaf nodes) depend on step 3's outcome and get their own plan; Task 8 records them in `PARKED.md` so they are not lost.

## Global Constraints

- Source: the non-padding grammar laws only (spec "Decision: the source", option 1). The sample is today's (padding and non-padding grown terms drawn together); padding laws are dropped after grouping.
- Term budget: the constant `GEN_TERMS = 20000` beside `grammar_laws`; no env var.
- Count rule: `n = ⌊f × L⌋`, L the scope's filtered list length. Fresh slices need `6n ≤ L` (f ≤ 1/6), shared `3n ≤ L` (f ≤ 1/3); a short list panics with the counts before the first stage runs.
- Round A (salts 1-10): fresh f ∈ {0.04, 0.08}, shared f ∈ {0.08, 0.16}, plus `ABLATE=gen`, `GEN_COUNTS=legacy` and `GEN_SOURCE=stream` at the fresh 0.08 arm's n. Round B (salts 11-20): the best arm, the cheapest arm meeting the rule, `ABLATE=gen` and the stream control.
- Default rule: the cheapest arm (loop seconds) with no more worse salts than better ones against the best arm (lowest total mined-batch M), over salts 1-20, paired.
- Acceptance: the stage is on by default only if its chosen arm beats the stream control at the same n over salts 1-20, paired (more salts better than worse); otherwise the default is `ABLATE=gen` and the note says so.
- Switches: `ABLATE=gen` (read with `rewrite::ablated`); `GEN_SOURCE=stream` (control only, kept while v0.3 is open). Temporary, deleted in Task 8: `GEN_F` (f, default 0.08), `GEN_SHARED=1`, `GEN_COUNTS=legacy`.
- Mined-batch M: `cold.tsv` column 5's 2nd plus 3rd entries, summed over families. Lower is better.
- Session rules (the user's CLAUDE.md, binding on every step):
  - Never let python read stdin: write the script to a file, run `python -P f.py args < /dev/null`; never `python -`.
  - No fixed sleeps; wait on a condition with a deadline (`ping -n N 127.0.0.1` as the poll interval). Never `tail -F`.
  - cargo with `-j 8` and `CARGO_TARGET_DIR="C:/Users/Winston Li/AppData/Local/Temp/oracle_tgt"`; one cargo per target dir.
  - Long runs launch through `powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind sweep -Name <n> -Command "<cmd>"`, detached with `cmd //c start "" //b`; env vars set before `cmd` are inherited. Report CPU load and Defender real-time protection with every timing; never change Defender or system settings.
  - Never touch other sessions' processes, `.claude/worktrees/*`, or the untracked `tests/ring_spike.rs` and `tests/ring_loop_spike.rs`.
  - Edits with the Edit tool; commit messages written to `$TEMP/msg.txt` with printf, checked with `git diff --cached --stat`, committed with `git commit -q -F "$TEMP/msg.txt"`, ending `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`. No push, tag or version bump.

## Review Focus

1. **A ref scope whose family has no pool** (`grammar_laws` returns nothing for a two-variable family): L is 0, n is 0, the slices fit and the mine takes nothing; it must not panic. Pinned in Task 4 (`extra_slices(0, 1, 1, 0, true)` is `Ok` with one empty range).
2. **The stream control shorter than its slices** (n comes from the generator's L, the slices from the stream's filtered list): the pre-pass must panic naming the scope, before any stage. Pinned by `extra_slices_refuse_a_short_list` and the pre-pass assertion in Task 5; Task 6 Step 2's probe shows it on real lists.
3. **The pooled stage's preference mines** (`rounds == 0`, `mode == "ref"`): they must take no extras even though ref mines now do. Pinned by `no_extras_without_rounds` (Task 4); they are also never put in a scope (Task 5).
4. **The renaming non-equivariance of the normalization:** two laws equal up to renaming must get one key. Pinned in Task 3's `normalize_maps_two_leaf_nodes_to_their_class`.
5. **Laws trivial after normalization** (`sub(x, x) = and(y, 0)` style): they are kept, and a served trivial law yields no key. Pinned in Task 3 (`key` returns `None`; the fixture count leaves them out) and Task 5's `filtered_drops_twins_and_skeletons_only`.
6. **Sweeps with a `mines` stage before the spec's step 4:** ref mines now draw extras, and mix3's (23665-term pool) and u3's generation are unmeasured. Until step 4's plan measures them, such sweeps run with `ABLATE=gen` or after a 1-salt probe; Task 8's docs say so.

---

### Task 1: The Python twin count gets the renaming-first key; fixtures

**Files:**
- Modify: `docs/runs/2026-10-17/scripts/twin_wide.py`
- Create: `docs/runs/2026-10-17/fixtures/pad_1/cold_cmp3d_{1,2,3}_none/laws_serve_{0,100,200}.txt` and `.../laws_extra_0.txt` (copies)
- Modify: `docs/runs/2026-10-17/README.md`

**Interfaces:**
- Produces: the number `CLASS_TWINS` (twin_wide.py's `class` count for `pad cmp3d` over the fixtures), which Task 3's test asserts.

- [ ] **Step 1: Copy the fixtures**

```bash
src="$LOCALAPPDATA/claude-runs/tatic/2026-10-17-gen-cost/pad_1"
dst="C:/Users/Winston Li/Documents/GitHub/tatic/docs/runs/2026-10-17/fixtures/pad_1"
for p in 1 2 3; do mkdir -p "$dst/cold_cmp3d_${p}_none"; for f in laws_serve_0 laws_serve_100 laws_serve_200 laws_extra_0; do cp "$src/cold_cmp3d_${p}_none/$f.txt" "$dst/cold_cmp3d_${p}_none/"; done; done
wc -l "$dst"/*/*.txt | tail -1
```

Expected: `1950 total` (9 served files of 100, 3 extras files of 350).

- [ ] **Step 2: Give twin_wide.py the renaming-first class key and let it skip families with no loops**

In `twin_wide.py`, after `def nkey(...)` add:

```python
PERMS = list(itertools.permutations("xyz"))
def rename(t, p):
    if isinstance(t, str): return p["xyz".index(t)] if t in ("x", "y", "z") else t
    return (t[0], rename(t[1], p), rename(t[2], p))

# the law generator's key (spec §1): rename first, then normalize, least text over the six renamings and both side
# orders; None if the sides normalize to one term (unrenamed)
def ckey(a, b):
    ta, tb = parse(a), parse(b)
    if show(norm_class(ta)) == show(norm_class(tb)): return None
    return min(f"{show(norm_class(rename(l, p)))} = {show(norm_class(rename(r, p)))}" for p in PERMS for l, r in ((ta, tb), (tb, ta)))
```

Replace `s_class = {nkey(a, b, norm_class) for a, b in served}` with `s_class = {ckey(a, b) for a, b in served}` and `kl, kc = nkey(a, b, strip), nkey(a, b, norm_class)` with `kl, kc = nkey(a, b, strip), ckey(a, b)`. After `loops = [...]` add `if not all(os.path.isdir(l) for l in loops): continue`. Update the header comment's `class` line to say the key renames before normalizing (the earlier counts renamed after, so they were lower bounds).

- [ ] **Step 3: Run it on the fixtures**

```bash
cd "C:/Users/Winston Li/Documents/GitHub/tatic/docs/runs/2026-10-17"
python -P scripts/twin_wide.py fixtures pad < /dev/null
```

Expected: a line `pad cmp3d extras 1050 leaf <a> leaf2 <b> class <C> trivial <t>`, and add3 and sbo3 lines of zeros (their loops are absent). Record `<C>` as `CLASS_TWINS` in the ledger, beside the old key's count for comparison (neither key's twins contain the other's, since the normalization is not equivariant):

```bash
mkdir -p "$TEMP/tw_old" && git show HEAD:docs/runs/2026-10-17/scripts/twin_wide.py > "$TEMP/tw_old/twin_wide.py" && cp scripts/pad_strip.py "$TEMP/tw_old/"
python -P "$TEMP/tw_old/twin_wide.py" fixtures pad < /dev/null
```

(Before running it, add the same skip line for absent loops to `$TEMP/tw_old/twin_wide.py` with the Edit tool; it has none.)

- [ ] **Step 4: README entry and commit**

In `docs/runs/2026-10-17/README.md`, in the `twin_wide.py` bullet, add: "Since the generator's plan, its class key renames before normalizing (`ckey`), as the generator's does; `fixtures/pad_1/` holds salt 1 of `-gen-cost`'s pad arm, cmp3d (phase 1-3 served files and mine 0's extras), the input of `search::normalize_finds_the_probes_twins`."

```bash
git add docs/runs/2026-10-17/scripts/twin_wide.py docs/runs/2026-10-17/fixtures docs/runs/2026-10-17/README.md
printf 'twin_wide.py: the class key renames before normalizing; fixtures for the Rust twin check\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n' > "$TEMP/msg.txt"
git diff --cached --stat && git commit -q -F "$TEMP/msg.txt"
```

### Task 2: `grammar_laws` takes salt and `deep3`, and yields non-padding laws only

**Files:**
- Modify: `tests/church_bv/search.rs:1803-1931` (`grammar_laws`, its two tests)
- Modify: `tests/church_bv/driver.rs:449-480` (the probe's call, temporarily)

**Interfaces:**
- Produces: `pub const GEN_TERMS: usize = 20000;`, `pub fn grammar_sample(family: &str, deep3: usize, salt: usize) -> Option<(Vec<Term>, Vec<(Term, bool)>)>`, `pub fn grammar_laws(family: &str, deep3: usize, salt: usize) -> Vec<(Term, Term)>`.

- [ ] **Step 1: Extract the sampling into `grammar_sample` (refactor, behaviour unchanged)**

Move the body of `grammar_laws` from `let Some(pool) = ...` through the sampling loop into:

```rust
/// The generator's term budget: about this many grown terms are sampled per family (the value every probe run used).
pub const GEN_TERMS: usize = 20000;

/// A three-variable family's pool and the generator's sample of grown terms: the pool with one leaf of a pool term grown
/// into a depth-1 term over the pool's own operators, about `GEN_TERMS` of those drawn by a hash of `salt`, each once and
/// with whether its grown leaf was padding (grew into a term equal to a leaf, such as `sub(y, y)`; the first way it was
/// grown). `None` for a family with no pool.
pub fn grammar_sample(family: &str, deep3: usize, salt: usize) -> Option<(Vec<Term>, Vec<(Term, bool)>)> {
    let env = |k: &str, d: usize| if k == "RULEMINER_DEEP3" { deep3 } else { d };
    let pool = pool3(family, &env)?;
    let in_pool: HashSet<Term> = pool.iter().cloned().collect();
    // (ops_of, grow, leaf_count, replaced, total, mix, memo, leaf_values, padding: unchanged from today's grammar_laws)
    let (mut sample, mut seen) = (vec![], HashSet::new());
    let mut i = 0u64;
    for t in &pool {
        for p in 0..leaf_count(*t) {
            for (gi, g) in grow.iter().enumerate() {
                i += 1;
                if (mix(i ^ mix(salt as u64)) % total as u64) < GEN_TERMS as u64 {
                    let w = replaced(*t, &mut Some(p), *g);
                    if !in_pool.contains(&w) && seen.insert(w) {
                        sample.push((w, padding[gi]));
                    }
                }
            }
        }
    }
    Some((pool, sample))
}
```

Keep `ops_of`, `grow`, `leaf_count`, `replaced`, `total`, `mix`, `memo`, `leaf_values` and `padding` exactly as they are (only the `terms` parameter becomes `GEN_TERMS`). Then the old `grammar_laws(family, env, terms, salt, pad)` keeps its signature for this step and becomes:

```rust
pub fn grammar_laws(family: &str, env: &dyn Fn(&str, usize) -> usize, terms: usize, salt: usize, pad: Option<bool>) -> Vec<(Term, Term)> {
    assert_eq!(terms, GEN_TERMS, "the term budget is GEN_TERMS");
    let Some((pool, sample)) = grammar_sample(family, env("RULEMINER_DEEP3", 0), salt) else { return vec![] };
    let in_pool: HashSet<Term> = pool.iter().cloned().collect();
    let padded: HashSet<Term> = sample.iter().filter(|s| s.1).map(|s| s.0).collect();
    let padded_law = |a: &Term, b: &Term| padded.contains(a) || padded.contains(b);
    // the pool first, so a group's first member (each law's left side) is a pool term where the group has one
    let laws = pool_conjectures(pool.iter().cloned().chain(sample.iter().map(|s| s.0)), 4, 3, 0)
        .into_iter()
        .filter(|(a, b)| !in_pool.contains(a) || !in_pool.contains(b))
        .filter(|(a, b)| (0..3).all(|v| a.has_var(v) || b.has_var(v)))
        .filter(|(a, b)| pad.is_none_or(|p| padded_law(a, b) == p))
        .collect();
    shuffled(laws, salt)
}
```

In the two tests, replace `3000` with `GEN_TERMS`.

- [ ] **Step 2: Run the existing tests (still green)**

Run: `CARGO_TARGET_DIR="C:/Users/Winston Li/AppData/Local/Temp/oracle_tgt" cargo test --release --test church_bv -j 8 grammar_ 2>&1 | tail -5`
Expected: `test result: ok. 2 passed`.

- [ ] **Step 3: Write the failing no-padding test**

Replace `grammar_pad_splits_the_laws` with:

```rust
/// The generator takes no padding law: no side of its laws is a sample term whose grown leaf was padding, and the sample
/// has such terms (so the check bites).
#[test]
pub fn grammar_laws_have_no_padding() {
    let env = |k: &str, d: usize| if k == "RULEMINER_DEEP3" { 1 } else { d };
    for f in ["add3", "cmp3d"] {
        let (_, sample) = grammar_sample(f, 1, 1).unwrap();
        let padded: HashSet<Term> = sample.iter().filter(|s| s.1).map(|s| s.0).collect();
        assert!(!padded.is_empty(), "{f}: no padding term in the sample");
        let laws = grammar_laws(f, &env, GEN_TERMS, 1, None);
        let bad = laws.iter().filter(|(a, b)| padded.contains(a) || padded.contains(b)).count();
        assert_eq!(bad, 0, "{f}: {bad} of {} laws have a padded side", laws.len());
    }
}
```

Run: `... cargo test --release --test church_bv -j 8 grammar_laws_have_no_padding 2>&1 | tail -5`
Expected: FAIL with `add3: <k> of <L> laws have a padded side` (k > 0).

- [ ] **Step 4: Change the signature: salt and `deep3` as arguments, padding laws dropped**

```rust
/// The law generator's source (docs/superpowers/specs/2026-10-17-law-generator-design.md): `grammar_sample`'s terms
/// grouped with the pool by their width-4 values (`pool_conjectures`). Its laws are the pairs with a grown side that use all
/// three variables and have no padded grown side, shuffled by `salt`. Pools are closed under renaming variables, so no law
/// here is a stream law or shares a stream law's skeleton.
pub fn grammar_laws(family: &str, deep3: usize, salt: usize) -> Vec<(Term, Term)> {
    let Some((pool, sample)) = grammar_sample(family, deep3, salt) else { return vec![] };
    let in_pool: HashSet<Term> = pool.iter().cloned().collect();
    let padded: HashSet<Term> = sample.iter().filter(|s| s.1).map(|s| s.0).collect();
    // the pool first, so a group's first member (each law's left side) is a pool term where the group has one
    let laws = pool_conjectures(pool.iter().cloned().chain(sample.iter().map(|s| s.0)), 4, 3, 0)
        .into_iter()
        .filter(|(a, b)| !in_pool.contains(a) || !in_pool.contains(b))
        .filter(|(a, b)| (0..3).all(|v| a.has_var(v) || b.has_var(v)))
        .filter(|(a, b)| !padded.contains(a) && !padded.contains(b))
        .collect();
    shuffled(laws, salt)
}
```

In both tests, call `grammar_laws(f, 1, 1)` and drop the `env` closure where it is no longer used (`grammar_laws_lie_outside_the_pool` still needs it for `pool3`).

In `driver.rs`, the probe's grammar branch (temporary until Task 5): delete the `GEN_PAD` match and the `GEN_TERMS` and `pad` parts of the memo key, make the key `(cfg.family.clone(), get("RULEMINER_SHUFFLE", 0), get("RULEMINER_DEEP3", 0))` and the `Memo` alias's key type `(String, usize, usize)`, and call `grammar_laws(&k.0, k.2, k.1)`. Update the doc comment's `GEN_TERMS grown terms` to `non-padding laws`.

- [ ] **Step 5: Run the tests**

Run: `... cargo test --release --test church_bv -j 8 grammar_ 2>&1 | tail -5`
Expected: `test result: ok. 2 passed`.

- [ ] **Step 6: Commit**

```bash
git add tests/church_bv/search.rs tests/church_bv/driver.rs
printf 'church_bv: grammar_laws takes salt and deep3 and yields the non-padding laws only\n\nThe sample is split out (grammar_sample) and unchanged; padding laws are dropped after grouping, as GEN_PAD=nopad did.\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n' > "$TEMP/msg.txt"
git diff --cached --stat && git commit -q -F "$TEMP/msg.txt"
```

### Task 3: `ClassReps`: normalization and the twin key

**Files:**
- Modify: `tests/church_bv/search.rs` (after `grammar_laws_have_no_padding`)

**Interfaces:**
- Consumes: `CLASS_TWINS` from Task 1; `leaves3()`, `mk`, `ValueMemo::<u8>::exhaustive`, `parse_term`, `parse_law` (search.rs/rewrite.rs).
- Produces: `pub struct ClassReps`, `ClassReps::new() -> ClassReps`, `fn normalize(&mut self, t: Term) -> Term`, `fn key(&mut self, a: &Term, b: &Term) -> Option<String>`.

- [ ] **Step 1: Write the failing tests against a stub**

```rust
/// The width-4 value classes of the leaves and the two-leaf terms (the law generator's twin filter,
/// docs/superpowers/specs/2026-10-17-law-generator-design.md §1, `scripts/twin_wide.py`'s `REP`).
pub struct ClassReps {
    memo: ValueMemo<u8>,
    /// a class's values to its representative
    rep: hashbrown::HashMap<Vec<u8>, Term>,
    /// two-leaf nodes already looked up
    done: hashbrown::HashMap<Term, Term>,
}

impl ClassReps {
    pub fn new() -> ClassReps {
        ClassReps { memo: ValueMemo::exhaustive(4, 3), rep: Default::default(), done: Default::default() }
    }

    /// `t` with every node over two leaves (an `lt` aside), bottom-up, replaced by its class's representative.
    pub fn normalize(&mut self, t: Term) -> Term {
        t
    }

    /// A law's twin key: the least `a = b` text, over the six renamings of x, y, z and both side orders, of the law renamed
    /// then normalized (renaming first, since a representative is not preserved by renaming); `None` if the law's sides
    /// normalize to one term.
    pub fn key(&mut self, a: &Term, b: &Term) -> Option<String> {
        Some(format!("{} = {}", a.show(), b.show()))
    }
}

/// Normalization maps padding to its leaf, puts value-equal two-leaf nodes in one class, leaves nodes over a non-leaf and
/// `lt` alone, and the key is the same for two laws that differ by renaming variables.
#[test]
pub fn normalize_maps_two_leaf_nodes_to_their_class() {
    let mut c = ClassReps::new();
    let mut n = |s: &str| c.normalize(parse_term(s)).show();
    assert_eq!(n("sub(y, y)"), "0");
    assert_eq!(n("add(x, 0)"), "x");
    assert_eq!(n("xor(x, -1)"), n("sub(-1, x)"));
    let r = n("or(z, x)");
    assert_eq!(n("add(or(z, x), sub(sub(y, y), 0))"), format!("add({r}, 0)"), "the outer add is over a non-leaf");
    assert_eq!(n("lt(x, x)"), "lt(x, x)");
    let p = parse_term;
    let swap = c.key(&p("sub(or(y, x), y)"), &p("and(y, z)"));
    assert_eq!(c.key(&p("sub(or(x, y), x)"), &p("and(x, z)")), swap, "renaming x and y");
    assert!(swap.is_some());
    assert_eq!(c.key(&p("sub(y, y)"), &p("and(x, 0)")), None, "both sides normalize to 0");
}

/// On the probe's fixture (salt 1 of `-gen-cost`'s pad arm, cmp3d: mine 0's extras of phases 1-3 against the served laws of
/// phases 1-3), the extras whose key is a served law's key are as many as `scripts/twin_wide.py` counts (`class`, trivial
/// laws not counted).
#[test]
pub fn normalize_finds_the_probes_twins() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("docs/runs/2026-10-17/fixtures/pad_1");
    let laws = |p: std::path::PathBuf| -> Vec<(Term, Term)> {
        std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("{}: {e}", p.display())).lines().filter_map(|l| parse_law(l, 3)).collect()
    };
    let loops: Vec<std::path::PathBuf> = (1..=3).map(|p| dir.join(format!("cold_cmp3d_{p}_none"))).collect();
    let served: Vec<(Term, Term)> = loops.iter().flat_map(|l| [0, 100, 200].map(|s| l.join(format!("laws_serve_{s}.txt")))).flat_map(laws).collect();
    let extras: Vec<(Term, Term)> = loops.iter().flat_map(|l| laws(l.join("laws_extra_0.txt"))).collect();
    assert_eq!((served.len(), extras.len()), (900, 1050));
    let mut c = ClassReps::new();
    let keys: HashSet<String> = served.iter().filter_map(|(a, b)| c.key(a, b)).collect();
    let twins = extras.iter().filter(|(a, b)| c.key(a, b).is_some_and(|k| keys.contains(&k))).count();
    assert_eq!(twins, CLASS_TWINS, "twin_wide.py counts CLASS_TWINS; find out which of the two is wrong before going on");
}
```

Write the number from Task 1 in place of `CLASS_TWINS` (a literal).

Run: `... cargo test --release --test church_bv -j 8 normalize_ 2>&1 | tail -8`
Expected: both FAIL: `normalize_maps…` on `left: "sub(y, y)"`, `right: "0"`; `normalize_finds…` on the count (the stub keys are raw texts: few or no twins).

- [ ] **Step 2: Implement**

```rust
    pub fn new() -> ClassReps {
        let mut memo = ValueMemo::exhaustive(4, 3);
        let leaves = leaves3();
        let mut two = vec![];
        for o in [ADD, SUB, XOR, AND, OR] {
            for a in &leaves {
                for b in &leaves {
                    two.push(mk(o, a, b));
                }
            }
        }
        two.extend(leaves.iter().map(|a| mk(SHL1, a, &Term::ZERO)));
        two.sort_by_cached_key(|t| {
            let s = t.show();
            (s.len(), s)
        });
        let mut rep = hashbrown::HashMap::new();
        // a leaf where the class has one (the first in x, y, z, 0, -1), else the least two-leaf term by (length, text)
        for t in leaves.iter().chain(&two) {
            rep.entry(memo.values(t).to_vec()).or_insert(*t);
        }
        ClassReps { memo, rep, done: Default::default() }
    }

    pub fn normalize(&mut self, t: Term) -> Term {
        let Node::Op(o, a, b) = *t.node() else { return t };
        let (a, b) = (self.normalize(a), self.normalize(b));
        let n = Term::op(o, a, b);
        let leaf = |t: Term| !matches!(t.node(), Node::Op(..));
        if o == LT || !leaf(a) || !leaf(b) {
            return n;
        }
        if let Some(r) = self.done.get(&n) {
            return *r;
        }
        let r = self.rep.get(self.memo.values(&n)).copied().unwrap_or(n);
        self.done.insert(n, r);
        r
    }

    pub fn key(&mut self, a: &Term, b: &Term) -> Option<String> {
        if self.normalize(*a) == self.normalize(*b) {
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
                let s = format!("{} = {}", self.normalize(renamed(*l, p)).show(), self.normalize(renamed(*r, p)).show());
                if best.as_ref().is_none_or(|k| s < *k) {
                    best = Some(s);
                }
            }
        }
        best
    }
```

(The leaf order: `leaves3()` is x, y, z, 0, -1, so `or_insert` keeps the first leaf of a class, then the least two-leaf term, as twin_wide.py's `REP` does.)

- [ ] **Step 3: Run the tests**

Run: `... cargo test --release --test church_bv -j 8 normalize_ 2>&1 | tail -5`
Expected: `test result: ok. 2 passed`. If the fixture count differs from `CLASS_TWINS`, stop and find which side is wrong (print the laws one side counts and the other does not, then normalize one by hand); ledger the cause.

- [ ] **Step 4: Commit**

```bash
git add tests/church_bv/search.rs
printf 'church_bv: ClassReps, the value-class normalization and twin key of the law generator\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n' > "$TEMP/msg.txt"
git diff --cached --stat && git commit -q -F "$TEMP/msg.txt"
```

### Task 4: The pure pieces: `extra_slices` and `takes_extras`

**Files:**
- Modify: `tests/church_bv/driver.rs` (beside `LoopCfg`; `#[derive(Clone)]` on `LoopCfg` becomes `#[derive(Clone, Default)]`)

**Interfaces:**
- Produces: `fn extra_slices(len: usize, loops: usize, mines: usize, n: usize, fresh: bool) -> Result<Vec<std::ops::Range<usize>>, usize>` (ranges ordered (loop, mine); `Err` is the shortfall); `fn takes_extras(cfg: &LoopCfg, ablated: bool) -> bool`; `fn mines_of(cfg: &LoopCfg) -> usize`.

- [ ] **Step 1: Write the failing tests against stubs of today's behaviour**

```rust
/// Each mine's slice of a scope's filtered extras list of `len` laws, ordered (loop, mine): `loops` loops of `mines` mines,
/// `n` laws each, fresh (consecutive slices in that order) or one slice per loop for its mines; the shortfall if they do not
/// fit (spec §3).
fn extra_slices(len: usize, loops: usize, mines: usize, n: usize, fresh: bool) -> Result<Vec<std::ops::Range<usize>>, usize> {
    let _ = (len, fresh);
    Ok((0..loops).flat_map(|i| (0..mines).map(move |_| (i + 1) * n..(i + 2) * n)).collect())
}

/// Whether a mine of `cfg` takes extras: it mines (not `none`) with rule rounds, and `ABLATE=gen` is off.
fn takes_extras(cfg: &LoopCfg, ablated: bool) -> bool {
    let _ = ablated;
    cfg.mode == "loop"
}

/// Fresh slices are disjoint, each n long, and cover loops × mines × n; shared slices give a loop's mines one range.
#[test]
fn extra_slices_are_disjoint_and_full() {
    let fresh = extra_slices(100, 3, 2, 10, true).unwrap();
    assert_eq!(fresh.len(), 6);
    assert!(fresh.iter().all(|r| r.len() == 10), "{fresh:?}");
    let mut seen = vec![false; 100];
    for i in fresh.iter().flat_map(|r| r.clone()) {
        assert!(!seen[i], "law {i} in two slices: {fresh:?}");
        seen[i] = true;
    }
    assert_eq!(seen.iter().filter(|&&s| s).count(), 60);
    let shared = extra_slices(100, 3, 2, 10, false).unwrap();
    assert_eq!(shared.len(), 6);
    for l in 0..3 {
        assert_eq!(shared[2 * l], shared[2 * l + 1], "{shared:?}");
        assert_eq!(shared[2 * l].len(), 10);
    }
    assert!(shared[0].end <= shared[2].start && shared[2].end <= shared[4].start, "{shared:?}");
    // a scope with no laws (a family with no pool): n is 0 and the mine takes nothing
    assert_eq!(extra_slices(0, 1, 1, 0, true), Ok(vec![0..0]));
}

/// A list shorter than its slices returns the shortfall.
#[test]
fn extra_slices_refuse_a_short_list() {
    assert_eq!(extra_slices(59, 3, 2, 10, true), Err(1));
    assert_eq!(extra_slices(29, 3, 2, 10, false), Err(1));
    assert!(extra_slices(60, 3, 2, 10, true).is_ok() && extra_slices(30, 3, 2, 10, false).is_ok());
}

/// Extras exist to be mined into rules: a mine with no rule rounds (the pooled stage's preference mines), a loop that only
/// serves, and any mine under `ABLATE=gen` take none; loop mines and ref mines with rounds take them.
#[test]
fn no_extras_without_rounds() {
    let c = |mode: &str, rounds: usize| LoopCfg { mode: mode.into(), rounds, k: 3, ..Default::default() };
    assert!(takes_extras(&c("loop", usize::MAX), false));
    assert!(takes_extras(&c("ref", usize::MAX), false), "a ref mine with rounds");
    assert!(!takes_extras(&c("ref", 0), false), "a mine with no rule rounds");
    assert!(!takes_extras(&c("loop", 0), false), "a mine with no rule rounds");
    assert!(!takes_extras(&c("loop", usize::MAX), true), "ABLATE=gen");
    assert!(!takes_extras(&c("none", usize::MAX), false), "a loop that only serves");
}
```

Add `Default` to `LoopCfg`'s derive.

Run: `... cargo test --release --test church_bv -j 8 -- extra_slices no_extras 2>&1 | tail -12` (libtest takes several filters after `--`)
Expected: `extra_slices_are_disjoint_and_full` FAIL (`law 10 in two slices`), `extra_slices_refuse_a_short_list` FAIL (`left: Ok(..)`, `right: Err(1)`), `no_extras_without_rounds` FAIL (`a ref mine with rounds`).

- [ ] **Step 2: Implement**

```rust
fn extra_slices(len: usize, loops: usize, mines: usize, n: usize, fresh: bool) -> Result<Vec<std::ops::Range<usize>>, usize> {
    let need = if fresh { loops * mines * n } else { loops * n };
    if need > len {
        return Err(need - len);
    }
    Ok((0..loops).flat_map(|i| (0..mines).map(move |j| (if fresh { i * mines + j } else { i }) * n)).map(|s| s..s + n).collect())
}

fn takes_extras(cfg: &LoopCfg, ablated: bool) -> bool {
    !ablated && cfg.rounds > 0 && cfg.mode != "none"
}

/// The mines of one loop of `cfg`: a ref loop mines once, a loop after every batch but its last.
fn mines_of(cfg: &LoopCfg) -> usize {
    if cfg.mode == "ref" { 1 } else { cfg.k.saturating_sub(1) }
}
```

- [ ] **Step 3: Run the tests**

Run the command of Step 1.
Expected: `test result: ok. 3 passed`.

- [ ] **Step 4: Commit**

```bash
git add tests/church_bv/driver.rs
printf 'church_bv: extra_slices and takes_extras, the pure pieces of the extras stage\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n' > "$TEMP/msg.txt"
git diff --cached --stat && git commit -q -F "$TEMP/msg.txt"
```

### Task 5: The extras stage replaces the probe

**Files:**
- Modify: `tests/church_bv/driver.rs` (`LoopCfg` 160-205, `extra_laws` 398-482 replaced, `run_loop`'s `mine` 512-530 and its two call sites, `sweep` 606-700)
- Modify: `tests/church_bv/task.rs:144-156` (`PURE`)

**Interfaces:**
- Consumes: `grammar_laws(family, deep3, salt)` (Task 2), `ClassReps` (Task 3), `extra_slices`, `takes_extras`, `mines_of` (Task 4), `family_laws`, `family_vars`, `env_or`, `env_var`, `rewrite::ablated`.
- Produces: `LoopCfg.extras: std::sync::Arc<Vec<(Term, Term)>>`, `LoopCfg.extra_at: Vec<std::ops::Range<usize>>`; `fn stream_laws(cfg: &LoopCfg, phase: usize, skip: usize, laws: usize) -> Vec<(Term, Term)>`; `fn scope_extras(scope: &mut [LoopCfg], also: &[LoopCfg], draw: &mut Draw) -> Result<(), String>`; per-mine log line `GEN_EXTRA <mine>: <k> laws`; per-scope line `GEN <dir>: L <L> n <n> source <s>`; per-family `GEN_LAWS <family>: <L> laws in <s>s`.

There is no unit test of the whole stage (it needs the stream and the miner); its checks are Task 6's sweeps (off path and on path). The pieces it calls are tested in Tasks 2, 3 and 4, and `filtered` here (Step 2).

- [ ] **Step 1: `LoopCfg` fields**

Add to `struct LoopCfg`, after `check_fast`:

```rust
    /// the extras list of this loop's scope (`scope_extras`), shared by the scope's loops
    extras: std::sync::Arc<Vec<(Term, Term)>>,
    /// each of this loop's mines' slice of `extras`, in mining order (a ref loop's one mine, or a loop's mines 0, 1, ...)
    extra_at: Vec<std::ops::Range<usize>>,
```

In `sweep`'s `base`, add `extras: Default::default(), extra_at: vec![],`; in `from_env`, the same (Step 5 fills them).

- [ ] **Step 1b: The filter's test, against a stub**

Add beside `extra_slices` (the stub is replaced in Step 2):

```rust
fn filtered(source: &[(Term, Term)], served: &[(Term, Term)], reps: &mut ClassReps) -> Vec<(Term, Term)> {
    let _ = (served, reps);
    source.to_vec()
}

/// The filter drops a twin of a served law (here through `sub(y, 0)`, which normalizes to `y`) and a law with a served
/// law's skeleton, and keeps a law trivial after normalizing and an unrelated law, in order.
#[test]
fn filtered_drops_twins_and_skeletons_only() {
    let p = |a: &str, b: &str| (parse_term(a), parse_term(b));
    let served = [p("and(or(x, y), z)", "or(and(x, z), and(y, z))")];
    let twin = p("and(or(x, sub(y, 0)), z)", "or(and(x, z), and(y, z))");
    let skel = p("and(or(x, y), y)", "or(and(x, y), and(y, y))");
    let trivial = p("sub(x, x)", "and(y, 0)");
    let other = p("add(add(x, y), z)", "add(x, add(y, z))");
    // `Term` has no `Debug`, so compare texts
    let text = |(a, b): (Term, Term)| format!("{} = {}", a.show(), b.show());
    let got: Vec<String> = filtered(&[twin, skel, trivial, other], &served, &mut ClassReps::new()).into_iter().map(text).collect();
    assert_eq!(got, [trivial, other].map(text));
}
```

Run: `... cargo test --release --test church_bv -j 8 filtered_drops 2>&1 | tail -6`
Expected: FAIL (`left` has 4 laws, `right` 2). (This step compiles because `extra_laws` still exists; nothing else changes yet.)

- [ ] **Step 2: Replace `extra_laws` with the stage's functions**

Delete `extra_laws` (doc comment "LAW SOURCE PROBE" through its closing brace) and the `filtered` stub, and add in their place:

```rust
/// `cfg`'s value of the child variable `k`: its `env`, then this process's, as `run_loop`'s children read it.
fn cfg_var(cfg: &LoopCfg, k: &str, d: usize) -> usize {
    cfg.env.iter().rev().find(|(kk, _)| kk == k).map_or_else(|| env_or(k, d), |(_, v)| v.parse().unwrap())
}

/// The laws a child of `cfg` takes at stride phase `phase`: `laws` of them from `skip`, through the variables `run_loop` gives
/// its children.
fn stream_laws(cfg: &LoopCfg, phase: usize, skip: usize, laws: usize) -> Vec<(Term, Term)> {
    let env = |k: &str, d: usize| match k {
        "RULEMINER_DEEP3" => cfg.deep3,
        "RULEMINER_STRIDE" => cfg.stride,
        "RULEMINER_PHASE" => phase,
        "RULEMINER_SHAPE" => cfg.split,
        "RULEMINER_SKIP" => skip,
        "RULEMINER_LAWS" => laws,
        _ => cfg_var(cfg, k, d),
    };
    family_laws(&cfg.family, &env, 4, family_vars(&cfg.family), 7).into_iter().map(|(_, a, b)| (a, b)).collect()
}

/// The laws `cfg`'s loop serves, and its mines mine: its K batches of B from OFFSET.
fn served_laws(cfg: &LoopCfg) -> Vec<(Term, Term)> {
    stream_laws(cfg, cfg.sphase, cfg.offset, cfg.b * cfg.k)
}

fn law_text((a, b): &(Term, Term)) -> String {
    format!("{} = {}", a.show(), b.show())
}

/// `s` with every lone lowercase letter (a variable) mapped by `f`.
fn map_vars(s: &str, mut f: impl FnMut(u8) -> char) -> String {
    let b = s.as_bytes();
    (0..b.len())
        .map(|i| {
            let alone = (i == 0 || !b[i - 1].is_ascii_alphanumeric()) && (i + 1 == b.len() || !b[i + 1].is_ascii_alphanumeric());
            if alone && b[i].is_ascii_lowercase() { f(b[i]) } else { b[i] as char }
        })
        .collect()
}

/// A law's skeleton: every variable written `v`, the smaller side first.
fn skeleton(l: &(Term, Term)) -> String {
    let e = map_vars(&law_text(l), |_| 'v');
    let (a, c) = e.split_once(" = ").unwrap();
    if a <= c { format!("{a} = {c}") } else { format!("{c} = {a}") }
}

/// What a sweep's scopes share while their extras are drawn: the class representatives and each family's generator laws.
struct Draw {
    reps: ClassReps,
    laws: hashbrown::HashMap<(String, usize, usize), std::sync::Arc<Vec<(Term, Term)>>>,
}

impl Draw {
    fn new() -> Draw {
        Draw { reps: ClassReps::new(), laws: Default::default() }
    }

    /// `grammar_laws` for `cfg`'s family, `deep3` and salt, generated once per sweep.
    fn grammar(&mut self, cfg: &LoopCfg) -> std::sync::Arc<Vec<(Term, Term)>> {
        let k = (cfg.family.clone(), cfg.deep3, cfg_var(cfg, "RULEMINER_SHUFFLE", 0));
        self.laws
            .entry(k)
            .or_insert_with_key(|k| {
                let t0 = std::time::Instant::now();
                let l = grammar_laws(&k.0, k.1, k.2);
                println!("GEN_LAWS {}: {} laws in {:.1}s", k.0, l.len(), t0.elapsed().as_secs_f64());
                std::sync::Arc::new(l)
            })
            .clone()
    }
}

/// The filter chain (spec §1): the laws of `source` that, against `served`, are no twin after normalizing (a law trivial
/// after normalizing is kept) and have no served law's skeleton, in `source`'s order.
fn filtered(source: &[(Term, Term)], served: &[(Term, Term)], reps: &mut ClassReps) -> Vec<(Term, Term)> {
    let keys: hashbrown::HashSet<String> = served.iter().filter_map(|(a, b)| reps.key(a, b)).collect();
    let skels: hashbrown::HashSet<String> = served.iter().map(skeleton).collect();
    let mut out = vec![];
    for l in source {
        if !reps.key(&l.0, &l.1).is_some_and(|k| keys.contains(&k)) && !skels.contains(&skeleton(l)) {
            out.push(*l);
        }
    }
    out
}

/// Draws one scope's extras (spec §1-3): `scope`'s loops (a stage's 3 loops of one family and source, or one ref mine)
/// against the laws they serve and those of `also` (for a ref mine, every loop the sweep runs). n = ⌊f × L⌋ with f from
/// `GEN_F` (temporary, default 0.08) and L the generator's filtered list; with `GEN_SOURCE=stream` (the control arm) the
/// slices come from the stream phases the scope does not serve, from the one after its last, filtered alike. Fresh slices
/// unless `GEN_SHARED=1` (temporary). Sets each loop's `extras` and `extra_at`, or says by how much the list is short.
fn scope_extras(scope: &mut [LoopCfg], also: &[LoopCfg], draw: &mut Draw) -> Result<(), String> {
    let served: Vec<(Term, Term)> = scope.iter().chain(also).flat_map(served_laws).collect();
    let c = scope[0].clone();
    let gen = filtered(&draw.grammar(&c), &served, &mut draw.reps);
    let n = (env_or("GEN_F", 0.08f64) * gen.len() as f64) as usize;
    let source = env_var("GEN_SOURCE").unwrap_or("grammar");
    let laws = match source {
        "grammar" => gen,
        "stream" => {
            let own: Vec<usize> = scope.iter().map(|c| c.sphase).collect();
            let last = *own.iter().max().unwrap();
            let stream: Vec<(Term, Term)> =
                (1..=c.stride).map(|i| (last + i) % c.stride).filter(|q| !own.contains(q)).flat_map(|q| stream_laws(&c, q, 0, usize::MAX)).collect();
            filtered(&stream, &served, &mut draw.reps)
        }
        s => panic!("GEN_SOURCE must be grammar or stream, got {s}"),
    };
    let (mines, fresh) = (mines_of(&c), env_var("GEN_SHARED") != Some("1"));
    let at = extra_slices(laws.len(), scope.len(), mines, n, fresh)
        .map_err(|short| format!("{}: {source} list of {} laws is {short} short of {} loops x {mines} mines x {n} (fresh {fresh})", c.out.display(), laws.len(), scope.len()))?;
    println!("GEN {}: L {} n {n} source {source}", c.out.display(), laws.len());
    let laws = std::sync::Arc::new(laws);
    for (i, cfg) in scope.iter_mut().enumerate() {
        cfg.extras = laws.clone();
        cfg.extra_at = at[i * mines..(i + 1) * mines].to_vec();
    }
    Ok(())
}

/// `GEN_COUNTS=legacy` (temporary, the on-path check against `-gen-cost`'s nopad arms): the probe's extras per loop mine.
/// Today's counts, the generator's list from `sphase × n`, kept when no law of phases 1-3 up to renaming variables and
/// swapping sides and of none of the mine's own laws' skeletons, then the first n.
fn legacy_extras(cfg: &mut LoopCfg, laws: &[(Term, Term)]) {
    let want = match cfg.family.as_str() {
        "add3" => 60,
        "sbo3" => 180,
        "cmp3d" => 350,
        _ => 0,
    };
    // up to renaming variables (in order of first use) and swapping sides
    let key = |l: &(Term, Term)| {
        let canon = |s: String| {
            let mut seen = vec![];
            map_vars(&s, |c| {
                let j = seen.iter().position(|&m| m == c).unwrap_or_else(|| {
                    seen.push(c);
                    seen.len() - 1
                });
                (b'a' + j as u8) as char
            })
        };
        canon(law_text(l)).min(canon(law_text(&(l.1, l.0))))
    };
    let served: hashbrown::HashSet<String> = (1..=3).flat_map(|q| stream_laws(cfg, q, 0, usize::MAX)).map(|l| key(&l)).collect();
    let (mut all, mut at) = (vec![], vec![]);
    for r in 0..mines_of(cfg) {
        let past: hashbrown::HashSet<String> = stream_laws(cfg, cfg.sphase, cfg.offset + r * cfg.b, cfg.b).iter().map(skeleton).collect();
        let start = all.len();
        all.extend(laws.iter().skip(cfg.sphase * want).filter(|l| !served.contains(&key(*l)) && !past.contains(&skeleton(*l))).take(want).copied());
        at.push(start..all.len());
    }
    (cfg.extras, cfg.extra_at) = (std::sync::Arc::new(all), at);
}
```

(`key`'s `canon(format!("{b} = {a}"))` of the probe is `law_text(&(l.1, l.0))` here: the same text.)

- [ ] **Step 3: The mines take their slice**

In `run_loop`, the `mine` closure gets a fourth parameter `slot: usize` and its extras block becomes:

```rust
        env.push(write_laws(&cfg.family, &env, &out.join(format!("laws_mine_{name}.txt")), "RULEMINER_LAWFILE"));
        if let Some(at) = cfg.extra_at.get(slot) {
            let extra: String = cfg.extras[at.clone()].iter().map(|l| law_text(l) + "\n").collect();
            println!("GEN_EXTRA {name}: {} laws", at.len());
            std::fs::write(out.join(format!("laws_extra_{name}.txt")), &extra).unwrap();
            append(Path::new(&env.last().unwrap().1), &extra);
        }
```

Call sites: `mine("ref", cfg.offset, cfg.b * cfg.k, 0);` and `mine(&r.to_string(), skip, cfg.b, r);`.

- [ ] **Step 4: `sweep` builds every scope first, draws, checks, then runs**

In `sweep`, after `let library = ...` and `mines_warm`, replace the per-stage construction of ref and loop configs with shared closures, and add the pre-pass before `for stage in stages.split_whitespace()`:

```rust
    let stage_fams = |stage: &'static str| stage.split_once(':').unwrap_or((stage, if stage == "mines" { "sbo3,add3,mix3,cmp3d" } else { "cmp3d,add3,sbo3" }));
    let ref_cfg = |fam: &str| {
        let &(fam, stride, split, b) = MINES.iter().find(|m| m.0 == fam).unwrap_or_else(|| panic!("no ref mine for {fam}"));
        LoopCfg { stride, split, b, k: 4, check_fast: false, warm: mines_warm(fam), ..base("ref", out.join(format!("lib_{fam}")), fam) }
    };
    let srcs = |name: &str, fam: &'static str| -> Vec<&'static str> {
        match name {
            "own" => vec![fam],
            "cold" => vec!["none"],
            "cross" => ["cmp3d", "add3", "sbo3"].into_iter().filter(|s| *s != fam).collect(),
            "pooled" => vec!["pooled"],
            "mixed" => vec!["u3"],
            _ => panic!("unknown stage {name}"),
        }
    };
    let loop_cfgs = |stage: &str, fam: &str, src: &str| -> Vec<LoopCfg> {
        let stride = LOOPS.iter().find(|l| l.0 == fam).unwrap_or_else(|| panic!("no loop stride for {fam}")).1;
        let warm = match src {
            "none" => None,
            "pooled" => Some(out.join(format!("pooled_{fam}")).join("rules.txt")),
            s => Some(library(s)),
        };
        (1..=3).map(|p| LoopCfg { stride, sphase: p, warm: warm.clone(), ..base("loop", out.join(format!("{}_{fam}_{p}_{src}", stage.replace(':', "_"))), fam) }).collect()
    };
    // every scope's extras, drawn before the first stage, so a list too short for its slices stops the sweep before any work
    let mut scopes: Vec<Vec<LoopCfg>> = vec![];
    for stage in stages.split_whitespace() {
        let (name, fams) = stage_fams(stage);
        for fam in fams.split(',') {
            if name == "mines" {
                scopes.push(vec![ref_cfg(fam)]);
            } else {
                scopes.extend(srcs(name, fam).into_iter().map(|src| loop_cfgs(stage, fam, src)));
            }
        }
    }
    let legacy = match env_var("GEN_COUNTS") {
        None => false,
        Some("legacy") => true,
        Some(s) => panic!("GEN_COUNTS must be legacy, got {s}"),
    };
    // a ref mine's library is served on the loops of every family the sweep runs (each family's phase 1-3 batches once);
    // a sweep of mines alone runs no loop, so its ref mines filter against their own batches only
    let mut loops: Vec<LoopCfg> = scopes.iter().flatten().filter(|c| c.mode == "loop").cloned().collect();
    loops.sort_by(|a, b| (&a.family, a.sphase).cmp(&(&b.family, b.sphase)));
    loops.dedup_by(|a, b| (&a.family, a.sphase) == (&b.family, b.sphase));
    let (mut draw, mut short) = (Draw::new(), vec![]);
    for scope in &mut scopes {
        if !scope.iter().all(|c| takes_extras(c, ablated("gen"))) {
            continue;
        }
        if legacy {
            // the probe gave loop mines extras only
            if scope[0].mode == "loop" {
                let laws = draw.grammar(&scope[0]);
                scope.iter_mut().for_each(|c| legacy_extras(c, &laws));
            }
            continue;
        }
        let also = if scope[0].mode == "ref" { &loops[..] } else { &[] };
        if let Err(e) = scope_extras(scope, also, &mut draw) {
            short.push(e);
        }
    }
    assert!(short.is_empty(), "extras lists too short for their slices:\n{}", short.join("\n"));
    let drawn: hashbrown::HashMap<PathBuf, LoopCfg> = scopes.into_iter().flatten().map(|c| (c.out.clone(), c)).collect();
    let with_extras = |cfg: LoopCfg| match drawn.get(&cfg.out) {
        Some(d) => LoopCfg { extras: d.extras.clone(), extra_at: d.extra_at.clone(), ..cfg },
        None => cfg,
    };
```

Then in the stage loop:
- `let (name, fams) = stage_fams(stage);` replaces the inline `split_once`.
- In the `mines` branch: `let cfg = with_extras(ref_cfg(fam));` replaces the inline construction (the `let &(fam, stride, split, b) = ...` line goes; use `cfg.family` where `fam` was the found name).
- In the loop branch: `for src in srcs(name, fam) { for cfg in loop_cfgs(stage, fam, src) { let cfg = with_extras(cfg); let p = cfg.sphase; ... } }` replaces the `srcs` match, `warm` match and per-phase construction; the tsv row is unchanged except that its `{stride}` becomes `{}` with `cfg.stride` (the `let stride = LOOPS...` line goes with the construction).
- The pooled branch's preference mines are left as they are (they take no extras: rounds 0, and they are in no scope).

`stages` must be `&'static str` for `stage_fams` (it is: `env_var` returns `&'static str`, `unwrap_or` with a literal). Adjust lifetimes in the closures if the compiler asks; the behaviour is as written.

- [ ] **Step 5: `from_env` draws its own scope**

At the end of `LoopCfg::from_env`, before returning (bind the struct to `let mut cfg = LoopCfg { ... };`):

```rust
        if takes_extras(&cfg, ablated("gen")) {
            let mut scope = [cfg];
            scope_extras(&mut scope, &[], &mut Draw::new()).unwrap_or_else(|e| panic!("{e}"));
            [cfg] = scope;
        }
        cfg
```

(`GEN_COUNTS=legacy` is a sweep-only check; `loop_stream` ignores it.)

- [ ] **Step 6: Remove the probe's leftovers**

- `task.rs`: delete the line `("driver.rs", "MEMO", "extra_laws' grammar_laws, keyed by every variable it reads"),` and change `[(&str, &str, &str); 11]` to `10`.
- `driver.rs`: confirm with `grep -n 'MINE_EXTRA\|MINE_SOURCE\|GEN_PAD\|GEN_TERMS\|extra_laws\|static MEMO' tests/church_bv/*.rs` that nothing is left (only `search.rs`'s `pool3_sequence` MEMO and the `GEN_TERMS` constant may remain).
- `driver.rs`'s module doc: after the `RULEMINER_STEPS` sentence add: "Extras (docs/superpowers/specs/2026-10-17-law-generator-design.md): every mine with rule rounds also mines a slice of the law generator's laws (`scope_extras`); off with ABLATE=gen; GEN_SOURCE=stream is the stream control; GEN_F, GEN_SHARED=1 and GEN_COUNTS=legacy are temporary."

- [ ] **Step 7: Build and run the suite**

Run: `CARGO_TARGET_DIR="C:/Users/Winston Li/AppData/Local/Temp/oracle_tgt" cargo test --release --test church_bv -j 8 > "$TEMP/suite.txt" 2>&1; tail -5 "$TEMP/suite.txt"; grep -c '^test .* FAILED$' "$TEMP/suite.txt"`
Expected: `test result: ok.` with 0 failed (the count of `FAILED` lines is 0), `task_state_is_classified` among the passed.

- [ ] **Step 8: Commit**

```bash
git add tests/church_bv/driver.rs tests/church_bv/task.rs
printf 'church_bv: the law generator becomes the extras stage of every mine with rule rounds\n\nsweep builds every scope first, filters the non-padding grammar laws once per scope (class twins and skeletons against the scope'"'"'s served laws), draws n = f x L laws per mine and checks every scope before the first stage. Removed: extra_laws, its MEMO (PURE 11 to 10), MINE_EXTRA, MINE_SOURCE, GEN_PAD, GEN_TERMS. Off with ABLATE=gen; GEN_SOURCE=stream is the control; GEN_F, GEN_SHARED and GEN_COUNTS=legacy are temporary.\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n' > "$TEMP/msg.txt"
git diff --cached --stat && git commit -q -F "$TEMP/msg.txt"
```

### Task 6: The sweep checks: off path, on path, and a 1-salt probe

**Files:**
- Create: `docs/runs/2026-10-17/scripts/gen_round.sh`
- Create: `docs/runs/2026-10-17/scripts/same_arms.sh`
- Modify: `docs/runs/2026-10-17/README.md`, `docs/runs.md` (the wrapper writes its rows)

**Interfaces:**
- Consumes: the Task 5 commit's build; `$TEMP/bv_padfile.exe` (b492165 + `extra_file.patch`; the code under `tests/` at HEAD before this plan is b492165's, so its plain arm is the off-path control).
- Produces: `gen_round.sh <exe> <salt>...` with arms `off legacy f04 f08 s08 s16` and `stream_<generator arm>` (that arm's stream control: same n and slices; and `plain`, no env, for an old build); `same_arms.sh <dir a> <dir b>` (prints `same` or the differing files).

- [ ] **Step 1: Write the scripts**

`gen_round.sh`:

```bash
# gen_round.sh <exe> <salt>...: cold sweeps per arm of $ARMS (default: off, legacy, the four generator arms and their stream_ controls), one
# after another, into kk.sh's directory ($RUN_DIR under run.ps1): <arm>_<salt>/. Arms (the law generator's plan, Tasks
# 6-7): off (ABLATE=gen), plain (no variables, for a build before the generator), f04 and f08 (fresh slices, GEN_F), s08
# and s16 (GEN_SHARED=1), legacy (GEN_COUNTS=legacy, the probe's counts), stream_<arm> (GEN_SOURCE=stream at that
# generator arm's n and slices: the stream control). Prints mined-batch M per family, rules and summed loop seconds per
# arm and salt.
exe=$1; shift
d=$(bash "$(dirname "$0")/../../2026-10-12/scripts/kk.sh")
arm_env() {
  case $1 in
    plain) ;;
    off) export ABLATE=gen ;;
    f04) export GEN_F=0.04 ;;
    f08) export GEN_F=0.08 ;;
    s08) export GEN_F=0.08 GEN_SHARED=1 ;;
    s16) export GEN_F=0.16 GEN_SHARED=1 ;;
    legacy) export GEN_COUNTS=legacy ;;
    stream_f04|stream_f08|stream_s08|stream_s16) arm_env "${1#stream_}" && export GEN_SOURCE=stream ;;
    *) echo "unknown arm $1"; return 1 ;;
  esac
}
for s in "$@"; do
  for arm in ${ARMS:-off legacy f04 f08 s08 s16 stream_f04 stream_f08 stream_s08 stream_s16}; do
    (
      arm_env "$arm" || exit 1
      o="$d/${arm}_$s"; mkdir -p "$o"; t0=$(date +%s)
      MACHINE_STATE=0 SALT=$s SWEEP=cold SWEEP_OUT="$(cygpath -w "$o")" "$exe" driver::sweep --exact --ignored --nocapture > "$o/log.txt" 2>&1
      echo "$? $(( $(date +%s) - t0 ))" > "$o/exit_secs"
    )
    o="$d/${arm}_$s"
    echo "salt $s $arm: $(awk -F'\t' '{split($5,m,","); t[$1]+=m[2]+m[3]; a+=m[2]+m[3]; r+=$6; c+=$7} END {printf "M %d (cmp3d %d add3 %d sbo3 %d) rules %d loop secs %d", a, t["cmp3d"], t["add3"], t["sbo3"], r, c}' "$o/cold.tsv"), exit+secs $(cat "$o/exit_secs")"
  done
done
```

`same_arms.sh`:

```bash
# same_arms.sh <dir a> <dir b>: whether two sweeps' cold stages agree, time columns aside: cold.tsv without column 7
# (seconds), and every loop's rules.txt. Prints "same" or each differing file.
a=$(cygpath -u "$1"); b=$(cygpath -u "$2"); bad=0  # Unix form: a backslash in a pattern below is an escape
cmp -s <(cut -f1-6,8- "$a/cold.tsv") <(cut -f1-6,8- "$b/cold.tsv") || { echo "cold.tsv"; bad=1; }
for r in "$a"/cold_*/rules.txt; do
  l=${r#"$a"/}; cmp -s "$r" "$b/$l" || { echo "$l"; bad=1; }
done
[ $bad = 0 ] && echo same
```

- [ ] **Step 2: Build, copy, and run a 1-salt probe of every arm**

```bash
cd "C:/Users/Winston Li/Documents/GitHub/tatic"
CARGO_TARGET_DIR="C:/Users/Winston Li/AppData/Local/Temp/oracle_tgt" cargo test --profile sweep --test church_bv -j 8 --no-run 2>&1 | tail -2
cp "C:/Users/Winston Li/AppData/Local/Temp/oracle_tgt/sweep/build/tatic/01b26e36776d44d8/out/church_bv-01b26e36776d44d8.exe" "$TEMP/bv_gen3.exe"
```

(If the build prints another exe path, use that one.) Check for orphans and live leases first (LONG_RUNS.md), then:

```bash
cmd //c start "" //b powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind probe -Name gen-round-probe -Command "bash docs/runs/2026-10-17/scripts/gen_round.sh '$TEMP/bv_gen3.exe' 1"
```

Wait on the run's `run.json` `end` field with a deadline of 30 min (a poll loop: `ping -n 30 127.0.0.1` between checks). Expected: 10 arm lines, each `exit+secs 0 <s>`; `GEN` lines in each `log.txt` (`grep '^GEN ' <arm>_1/log.txt`) with L per scope; no panic. Record each arm's seconds: they replace the spec's estimates (round A at `sum × 10`). If an arm panics as short (likely only a `stream_` arm), ledger it with the printed counts and rule: drop that arm's f to the largest that fits for every scope, or make the stream arm shared; say which in the note.

- [ ] **Step 3: Off path and on path, salts 1-10**

Launch the controls and the two check arms as one run (about 25 min for legacy, a few minutes for the rest):

```bash
ARMS=plain cmd //c start "" //b powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind sweep -Name gen-check-plain -Command "bash docs/runs/2026-10-17/scripts/gen_round.sh '$TEMP/bv_padfile.exe' 1 2 3 4 5 6 7 8 9 10"
```

When it ends:

```bash
ARMS="off legacy" cmd //c start "" //b powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind sweep -Name gen-check -Command "bash docs/runs/2026-10-17/scripts/gen_round.sh '$TEMP/bv_gen3.exe' 1 2 3 4 5 6 7 8 9 10"
```

Then compare (`R=$LOCALAPPDATA/claude-runs/tatic`):

```bash
for s in 1 2 3 4 5 6 7 8 9 10; do echo "salt $s off: $(bash docs/runs/2026-10-17/scripts/same_arms.sh "$R/2026-10-17-gen-check-plain/plain_$s" "$R/2026-10-17-gen-check/off_$s")"; done
for s in 1 2 3 4 5 6 7 8 9 10; do echo "salt $s legacy: $(bash docs/runs/2026-10-17/scripts/same_arms.sh "$R/2026-10-17-gen-cost/nopad_$s" "$R/2026-10-17-gen-check/legacy_$s")"; done
```

(Run ids carry the date the run started; adjust them if a run started on another day.)

Expected: every line `same`. A difference in the off arm is a refactor bug: find it (`systematic-debugging`) before Task 7. A difference in the legacy arm alone: first run `-gen-cost`'s nopad arm on `bv_padfile.exe` (same build as the off control; `MINE_SOURCE=grammar MINE_EXTRA=add3:60,sbo3:180,cmp3d:350 GEN_PAD=nopad`, as `gen_cost.sh`'s nopad arm) for the differing salts and compare against that: a match there is build drift between 4346cda and b492165, a mismatch is a bug in `legacy_extras` or `grammar_laws`.

- [ ] **Step 4: Record and commit**

README: add the two scripts' bullets and rows for `-gen-round-probe`, `-gen-check-plain` and `-gen-check` (build `bv_gen3.exe` = the Task 5 commit; result: per-arm seconds of the probe; `off` and `legacy` same on n of 10 salts). Commit the scripts, README and `docs/runs.md` rows:

```bash
git add docs/runs/2026-10-17/scripts/gen_round.sh docs/runs/2026-10-17/scripts/same_arms.sh docs/runs/2026-10-17/README.md docs/runs.md
printf 'Docs: the extras stage reproduces the plain and probe arms (gen-check)\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n' > "$TEMP/msg.txt"
git diff --cached --stat && git commit -q -F "$TEMP/msg.txt"
```

### Task 7: Rounds A and B

**Files:**
- Create: `docs/runs/2026-10-17/scripts/gen_pairs.py`
- Modify: `docs/runs/2026-10-17/README.md`, `docs/runs.md`

**Interfaces:**
- Consumes: `gen_round.sh`, `bv_gen3.exe`, the `-gen-check` run (its `off` arm is round A's `ABLATE=gen` arm; its `legacy` arm is round A's legacy arm).
- Produces: per-arm totals and paired counts; the arm the default rule picks.

- [ ] **Step 1: Write `gen_pairs.py`**

```python
# gen_pairs.py [--best <arm>] <run dir>...: per arm (<arm>_<salt>/cold.tsv in any of the run dirs), mined-batch M per
# family (column 5's 2nd and 3rd entries), rules and loop seconds (columns 6 and 7) summed over its salts, then its paired
# count against the best arm over the salts both have: better, equal, worse. The best is --best, else the generator arm
# (f04 f08 s08 s16; controls never) with the lowest total among those with the most salts, so totals compare like with
# like. The law generator's plan, Task 7.
import sys, os, re, collections
args = sys.argv[1:]
forced = args[1] if args[:1] == ["--best"] else None
dirs = args[2:] if forced else args
rows = collections.defaultdict(dict)  # arm -> salt -> (M per family, rules, secs)
for d in dirs:
    for e in os.listdir(d):
        m = re.fullmatch(r"(.+)_(\d+)", e)
        p = os.path.join(d, e, "cold.tsv")
        if not m or not os.path.isfile(p): continue
        fam, rules, secs = collections.Counter(), 0, 0
        for line in open(p):
            c = line.rstrip("\n").split("\t")
            ms = [int(x) for x in c[4].split(",")]
            fam[c[0]] += ms[1] + ms[2]; rules += int(c[5]); secs += int(c[6])
        rows[m.group(1)][int(m.group(2))] = (fam, rules, secs)
tot = {a: sum(sum(f.values()) for f, _, _ in s.values()) for a, s in rows.items()}
gens = [a for a in rows if a in ("f04", "f08", "s08", "s16")]
most = max((len(rows[a]) for a in gens), default=0)
best = forced or min((a for a in gens if len(rows[a]) == most), key=lambda a: (tot[a], a))
print(f"best: {best} ({len(rows[best])} salts)")
for a in sorted(rows, key=lambda a: (-len(rows[a]), tot[a], a)):
    s = rows[a]
    fam = collections.Counter()
    for f, _, _ in s.values(): fam.update(f)
    common = sorted(set(s) & set(rows[best]))
    mt = lambda arm, k: sum(rows[arm][k][0].values())
    b = sum(mt(a, k) < mt(best, k) for k in common); w = sum(mt(a, k) > mt(best, k) for k in common)
    print(f"{a}: salts {len(s)} M {tot[a]} (cmp3d {fam['cmp3d']} add3 {fam['add3']} sbo3 {fam['sbo3']}) rules {sum(r for _, r, _ in s.values())} "
          f"loop secs {sum(x for _, _, x in s.values())} vs {best}: better {b} equal {len(common) - b - w} worse {w}")
```

Check it on the `-gen-check` run (`R=$LOCALAPPDATA/claude-runs/tatic` in every shell of this task): `python -P docs/runs/2026-10-17/scripts/gen_pairs.py --best off "$R/2026-10-17-gen-check" < /dev/null`. Expected: a `best: off (10 salts)` line, then two arm lines (`legacy`, `off`), legacy's M equal to `-gen-cost`'s nopad total (9) and off's equal to `-gen-check-plain`'s total (`python -P docs/runs/2026-10-17/scripts/gen_pairs.py --best plain "$R/2026-10-17-gen-check-plain" < /dev/null`). For the record only, also run it on `-gen-src` (`--best plain`; its `plain` arm, salts 1-10: 120 on da775e7) and compare off's total: a difference there is build drift since da775e7, not a check failure. Run with no generator arm and no `--best`, the script fails on `min()` of nothing; that is expected.

- [ ] **Step 2: Round A (salts 1-10)**

Check orphans and leases, then:

```bash
ARMS="f04 f08 s08 s16 stream_f04 stream_f08 stream_s08 stream_s16" cmd //c start "" //b powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind sweep -Name gen-round-a -Command "bash docs/runs/2026-10-17/scripts/gen_round.sh '$TEMP/bv_gen3.exe' 1 2 3 4 5 6 7 8 9 10"
```

Expected duration: the probe's (Task 6 Step 2) per-arm seconds × 10. Arm a Monitor on the run's `out.log` (an exiting poll loop on `run.json`'s `end`, as in Task 6) and report the arm lines as they come. When done:

```bash
python -P docs/runs/2026-10-17/scripts/gen_pairs.py "$R/2026-10-17-gen-round-a" "$R/2026-10-17-gen-check" < /dev/null
```

Ledger the table. The best arm is named on the first line (generator arms only; the `stream_` controls and `off` are paired against it, not candidates). Name round B's arms: the best, and the cheapest (loop seconds) of the arms with `worse ≤ better` against it.

- [ ] **Step 3: Round B (salts 11-20)**

```bash
ARMS="<best> <cheapest> off stream_<cheapest>" cmd //c start "" //b powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind sweep -Name gen-round-b -Command "bash docs/runs/2026-10-17/scripts/gen_round.sh '$TEMP/bv_gen3.exe' 11 12 13 14 15 16 17 18 19 20"
```

(with the two arm names from Step 2; if they are the same arm, run it once). When done:

```bash
python -P docs/runs/2026-10-17/scripts/gen_pairs.py "$R/2026-10-17-gen-round-a" "$R/2026-10-17-gen-check" "$R/2026-10-17-gen-round-b" < /dev/null
```

The best is now chosen among the generator arms with 20 salts (round B's), and the pairs over all 20 salts are those of arms with 20 salts (`gen_pairs.py` pairs over the salts both arms have; the 10-salt arms are listed after them, their totals not comparable). For the record only, compare round B's `off` total with `-gen-salts`' plain arm (101 over salts 11-20, on 4346cda): a difference is build drift, not a failure.

- [ ] **Step 4: Record and commit**

README: `gen_pairs.py` bullet; rows for `-gen-round-a` and `-gen-round-b` with their headline (best arm and its M; the default rule's pick). Commit them with the runs.md rows.

### Task 8: Fix the default; docs

**Files:**
- Modify: `tests/church_bv/driver.rs` (`scope_extras`, `legacy_extras`, `sweep`, module doc)
- Modify: `docs/tier-cycle.md` (new note), `PARKED.md`, `ROADMAP.md`, the spec (status), this plan (status)

- [ ] **Step 1: Apply the default rule and the acceptance rule**

From Task 7's 20-salt pairs: the default arm is the cheapest with `worse ≤ better` against the best. Acceptance (the spec: "at the same n"): compare that arm against its own control `stream_<arm>` over salts 1-20, paired: `python -P docs/runs/2026-10-17/scripts/gen_pairs.py --best <arm> "$R/2026-10-17-gen-round-a" "$R/2026-10-17-gen-round-b" < /dev/null` and read the `stream_<arm>` line (it must show `worse` > `better`, i.e. the arm beats its control on more salts than it loses). Ledger both.

- [ ] **Step 2: Code**

- `scope_extras`: `env_or("GEN_F", 0.08f64)` becomes a constant `const GEN_F: f64 = <the default arm's f>;` with a doc line naming the run; if the default is shared, `fresh` becomes `false` and `extra_slices` drops its `fresh` parameter (fresh lost: delete the fresh branch and its test assertions); if fresh, delete `GEN_SHARED` and the shared branch and its assertions.
- Delete `legacy_extras`, the `GEN_COUNTS` match and its branch in `sweep`.
- If acceptance failed, the stage stays but is off by default (the spec: "the default is `ABLATE=gen`"): both call sites pass `ablated("gen") || env_var("GEN") != Some("1")` as `takes_extras`'s `ablated`, so `GEN=1` turns it on; the module doc says so. Ledger which branch was taken.
- Update the module doc's extras sentence (no temporary variables left but `GEN_SOURCE`).
- Run the suite (Task 5 Step 7's command). Expected: 0 failed.

- [ ] **Step 3: Docs**

- `docs/tier-cycle.md`: a new note after "Where an extras mine's time goes": "*The law generator as a stage (2026-10-1x).*" with the probe's per-arm seconds, the off/on-path checks (`same` on n of 10), round A's and B's tables (from `gen_pairs.py`), the default and the acceptance result, and which side of `ABLATE=gen` later numbers are on.
- `PARKED.md`: in "Law generator as a designed stage", replace the plan sentence with the outcome; add a `decided against` entry: "**Padding laws as the generator's source**: filtered alike they lose to the stream (M 40 against 29, worse on 6 salts of 10, run `2026-10-17-gen-wide`); trigger: none; status: decided against." Add parked entries for the spec's steps 4 (warm loops and ref mines; trigger: this plan done; evidence: the spec's build order) and 5 (hidden twins beyond two-leaf nodes), and for the mixed source if round A's f 0.04 arm decided it (`decided against` if it cost no more than 359 loop seconds at lower M, else held).
- `ROADMAP.md`: the v0.3 line gets the stage's result.
- `docs/runs/2026-10-17/README.md`: in the `gen_src.sh`, `gen_cost.sh`, `gen_twin.sh` bullets: "These no longer run against builds after the generator's stage (`MINE_EXTRA`, `MINE_SOURCE` and `GEN_PAD` are gone)."
- The spec's and this plan's front matter: `status: done` (or `active` while steps 4-5 are open in the spec: the spec stays `active`, this plan `done`).

- [ ] **Step 4: Commit**

```bash
git add tests/church_bv/driver.rs docs/tier-cycle.md PARKED.md ROADMAP.md docs/runs/2026-10-17/README.md docs/superpowers/specs/2026-10-17-law-generator-design.md docs/superpowers/plans/2026-10-17-law-generator.md
printf 'church_bv: the law generator'"'"'s default from rounds A and B\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n' > "$TEMP/msg.txt"
git diff --cached --stat && git commit -q -F "$TEMP/msg.txt"
```
