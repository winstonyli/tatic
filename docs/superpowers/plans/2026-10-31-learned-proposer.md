---
status: active
---

# v0.6 stage 1: a learned scorer over the extras draw (implementation plan)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Find out whether a logistic-regression scorer, trained on the miner's own credit labels, orders each mine's extras so that the frontier moves beyond a random draw at equal or lower mining CPU.

**Architecture:** `scope_extras` (`tests/church_bv/driver.rs`) gains a pool factor `POOL` and an optional `SCORER` weights file; per mine it cuts `POOL x n` kept laws and keeps the best `n` (stable on ties). A new `tests/church_bv/scorer.rs` holds features, fit, AUC and the weights text. The miner prints one `RULEMINER label:` line per straggler; a dump tool turns mine logs into label rows; a fit tool trains and reports AUC. Tasks 6 and 7 are recorded runs that decide the stage.

**Tech Stack:** Rust (the `church_bv` test crate, no new dependencies), bash for run scripts, `~/.claude/runs/run.ps1` for recorded runs, `scripts/streams_ab.sh` for the gate.

**Spec:** `docs/superpowers/specs/2026-10-31-learned-proposer-design.md` (approved 2026-10-31). Correction recorded in Task 7: the gate is deterministic, so the A/A spread is the redraw spread (`GEN_DRAW`), not a rerun.

## Global Constraints

- `kind: experiment`; no compatibility shims; Cargo dependencies unchanged ("No new dependency").
- The scorer only orders candidate laws; every law still passes the existing filter and the kernel; no score reaches the kernel.
- Unset `POOL` and `SCORER` leave `scope_extras` behaving exactly as today (pool 1, no scorer: the identity selection).
- Train on salts 4-10, judge on gate salts 1-3, never on a held-out band (`filter` already removes held-out laws).
- Long runs launch through `~/.claude/runs/run.ps1` (`-Kind gate|probe`, `-Affinity CFF`, from inside the repo), pass paths in 8.3 form (`cygpath -d`), one row each in `docs/runs.md`. Untimed gates: `JOBS=3`, `ARM_CACHE`. Leave stray processes never; no fixed sleeps.
- Commit after each task with the trailer `Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>`; never push, tag or bump.
- Thresholds in Tasks 6 and 7 are set here, before any data.

## Review Focus

1. `EXTRAS_N=0` or a pool of 0: `select_extras` returns nothing and does not panic on `chunks(0)` (test in Task 1).
2. A pool that does not fit the sequence: `scope_extras` errors with the shortfall, naming `POOL`, not a slice panic (test in Task 1).
3. A missing or garbled `SCORER` file: a panic that names the path and what is wrong, not a silent zero scorer (test in Task 2).
4. A law of constants and no variables, or `x = x`-shaped laws: features stay finite (test in Task 2).
5. All-equal scores keep the stream order, so zero weights equal the baseline (test in Task 3).
6. A mine log with stragglers but no `RULEMINER label:` lines (a log from before Task 4): the dump refuses it instead of reading every law as y = 0 (test in Task 4).

## File Structure

- `tests/church_bv/driver.rs`: `select_extras` (new), `scope_extras` (pool, scorer), tests.
- `tests/church_bv/scorer.rs` (new): `features`, `Scorer`, `fit`, `auc`, text load/save, label parsing, `dump_labels` and `fit_scorer` ignored tools, tests.
- `tests/church_bv/miner.rs`: one print line in `Rounds::report`.
- `tests/church_bv/main.rs`: `mod scorer;`.
- `docs/runs/2026-10-31/scripts/`: `gate.sh`, `curve.sh`.
- `docs/tier-cycle.md`, `ROADMAP.md`, `PARKED.md`: results (Task 7).

---

### Task 1: Pool factor in `scope_extras`, and the sequence-length probe

**Files:**
- Modify: `tests/church_bv/driver.rs` (`extra_slices` neighbours, `scope_extras`, module doc, tests)

**Interfaces:**
- Produces: `fn select_extras(kept: &[(Term, Term)], block: usize, n: usize, score: Option<&dyn Fn(&(Term, Term)) -> f32>) -> Vec<(Term, Term)>`: per block of `block` laws the best `n` by `score` (a stable sort, so ties keep stream order); with no score the block's first `n`. `block == 0` or `n == 0` gives an empty list. Env `POOL` (default 1) is the block factor: `block = POOL * n`.

- [ ] **Step 1: Write the failing tests** (after `extra_slices_refuse_a_short_list`)

```rust
/// Distinct laws for the selection tests: law `i` is `add(.. add(x, y) .. y) = 0` with `i` additions, so its size grows with `i`.
fn nested_laws(count: usize) -> Vec<(Term, Term)> {
    (0..count).map(|i| ((0..i).fold(Term::v(0), |t, _| Term::op(ADD, t, Term::v(1))), Term::ZERO)).collect()
}

#[test]
fn select_extras_takes_the_first_n_of_each_block_without_a_score() {
    let laws = nested_laws(12);
    let texts = |ls: &[(Term, Term)]| ls.iter().map(law_text).collect::<Vec<_>>();
    assert_eq!(texts(&select_extras(&laws, 6, 2, None)), texts(&[laws[0], laws[1], laws[6], laws[7]]));
    assert_eq!(texts(&select_extras(&laws, 3, 3, None)), texts(&laws), "a block of n is the whole list: pool 1 changes nothing");
    assert!(select_extras(&laws, 0, 0, None).is_empty(), "n 0 takes nothing and a block of 0 does not panic");
}

#[test]
fn select_extras_takes_the_best_n_of_each_block_and_keeps_ties_in_order() {
    let laws = nested_laws(12);
    let texts = |ls: &[(Term, Term)]| ls.iter().map(law_text).collect::<Vec<_>>();
    let by_size = |l: &(Term, Term)| l.0.size() as f32;
    assert_eq!(texts(&select_extras(&laws, 6, 2, Some(&by_size))), texts(&[laws[5], laws[4], laws[11], laws[10]]));
    let flat = |_: &(Term, Term)| 0.0;
    assert_eq!(texts(&select_extras(&laws, 6, 2, Some(&flat))), texts(&select_extras(&laws, 6, 2, None)), "equal scores keep the stream order");
}

#[test]
fn extra_slices_refuse_a_pool_that_does_not_fit() {
    // 3 loops x 2 mines x (pool 4 x n 319) laws needed
    assert_eq!(extra_slices(6 * 4 * 319 - 1, 3, 2, 4 * 319), Err(1));
    assert!(extra_slices(6 * 4 * 319, 3, 2, 4 * 319).is_ok());
}
```

- [ ] **Step 2: Run to verify they fail**

Run: `cargo test --release --test church_bv select_extras -- --nocapture`
Expected: compile error, `cannot find function select_extras`.

- [ ] **Step 3: Implement `select_extras` and use it in `scope_extras`**

Add after `extra_slices`:

```rust
/// The extras a scope's mines take from `kept` (its first `loops x mines x block` kept laws): from each block of `block`
/// laws the `n` with the highest `score` (a stable sort, so ties keep stream order), or the block's first `n` with no
/// score. A block of `n` (pool 1) is the identity. `docs/superpowers/specs/2026-10-31-learned-proposer-design.md`.
fn select_extras(kept: &[(Term, Term)], block: usize, n: usize, score: Option<&dyn Fn(&(Term, Term)) -> f32>) -> Vec<(Term, Term)> {
    if block == 0 || n == 0 {
        return vec![];
    }
    kept.chunks(block)
        .flat_map(|chunk| {
            let mut order: Vec<usize> = (0..chunk.len()).collect();
            if let Some(f) = score {
                let s: Vec<f32> = chunk.iter().map(f).collect();
                order.sort_by(|&i, &j| s[j].total_cmp(&s[i]));
            }
            order.into_iter().take(n).map(|i| chunk[i]).collect::<Vec<_>>()
        })
        .collect()
}
```

In `scope_extras`, replace the `laws`/`at` lines:

```rust
    let (n, mines) = (setup.or("EXTRAS_N", EXTRAS_N), c.mines.len());
    let pool = setup.or("POOL", 1usize);
    // built once per process and salt (its `STREAMS` lines give the time)
    let deep = stream_sequence(salt, held_levels(HELD_BANDS.into_iter().max().unwrap()));
    let keep = filter(&served, &held);
    let kept: Vec<(Term, Term)> = deep.iter().filter(|l| keep(l)).take(scope.len() * mines * pool * n).copied().collect();
    extra_slices(kept.len(), scope.len(), mines, pool * n).map_err(|short| {
        format!("{}: the extras sequence of {} laws keeps {}, {short} short of {} loops x {mines} mines x POOL {pool} x n {n}", c.out.display(), deep.len(), kept.len(), scope.len())
    })?;
    let laws = select_extras(&kept, pool * n, n, None);
    let at = extra_slices(laws.len(), scope.len(), mines, n).expect("a selection of n per block fills the slices");
    println!("GEN {}: n {n}, pool {pool}, {} laws from a sequence of {}", c.out.display(), laws.len(), deep.len());
```

Add to the module doc (after the `GEN_DRAW=d` sentence): `POOL=p cuts p x n kept laws per mine and keeps n (the first n, or the best n by SCORER=<weights file>, scorer.rs).`

- [ ] **Step 4: Run to verify they pass**

Run: `cargo test --release --test church_bv select_extras extra_slices -- --nocapture`
Expected: PASS (the three new tests, and the existing `extra_slices_*`).

- [ ] **Step 5: Commit**

```bash
git add tests/church_bv/driver.rs
git commit -m "church_bv: scope_extras cuts POOL x n kept laws per mine and keeps n (select_extras); pool 1 is today's draw

Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>"
```

- [ ] **Step 6: Probe the sequence length (expected: minutes of CPU, one arm-salt)**

Build the exe and copy it to a fixed place; run salt 1 of a sweep at `POOL=4`, `EXTRAS_N=319` through the wrapper; the pool check fails fast, before any mining, if the sequence is too short.

```bash
cargo test --release --test church_bv --no-run   # the printed "Executable" line is the exe
mkdir -p "$LOCALAPPDATA/claude-runs/tatic/v06-exes"
cp <the printed exe> "$LOCALAPPDATA/claude-runs/tatic/v06-exes/pool.exe"
printf 'POOL=4\n' > "$LOCALAPPDATA/claude-runs/tatic/v06-exes/pool.exe.env"
```

Then, from the repo root (paths in 8.3 form, `cygpath -d`):

```bash
X=$(cygpath -m "$(cygpath -d "$LOCALAPPDATA/claude-runs/tatic/v06-exes/pool.exe")")
powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind probe -Name v06-pool-fit -Affinity CFF -Detach -Command "bash -c 'MACHINE_STATE=0 SWEEP=cold:streams SALT=1 SWEEP_OUT=\"\$RUN_DIR/s1_P\" $X driver::sweep --exact --ignored --nocapture'"
```

Arm a watcher (a background `until` loop on `run.json`'s `"end"` with a 20-minute deadline). Read `out.log`: a `GEN ...: n 319, pool 4, <k> laws from a sequence of <m>` line means POOL=4 fits; a `short of` error means it does not.

- [ ] **Step 7: Rule on the pool**

If `short of`: rerun with `POOL=3`, then `POOL=2` (edit `pool.exe.env`; the exe is unchanged). Record the largest pool that fits in `docs/runs.md`'s headline and in the ledger as `Ruling: POOL=<p>`. If even `POOL=2` is short, stop and report to the user: stage 1 cannot run as designed without growing the sequence.

---

### Task 2: The scorer module

**Files:**
- Create: `tests/church_bv/scorer.rs`
- Modify: `tests/church_bv/main.rs` (add `mod scorer;` after `mod search;`)

**Interfaces:**
- Produces: `pub const F: usize = 26`; `pub fn features(law: &(Term, Term)) -> [f32; F]` (symmetric in the two sides); `pub struct Scorer` with `zero()`, `with_weights(w: [f64; F])`, `score(&self, law: &(Term, Term)) -> f32`, `to_text(&self) -> String`, `from_text(text: &str) -> Result<Scorer, String>`; `pub fn fit(rows: &[([f32; F], bool)]) -> Scorer`; `pub fn auc(scored: &[(f64, bool)]) -> f64`.

- [ ] **Step 1: Write the failing tests** (the file starts with the tests module and stubs fail to compile)

Create `tests/church_bv/scorer.rs`:

```rust
//! The extras scorer (docs/superpowers/specs/2026-10-31-learned-proposer-design.md): a logistic regression over counts of a
//! law's two sides that orders candidate laws for a mine. It only orders; the filter and the kernel judge every law.
use super::*;
use crate::classes::OPS;

#[cfg(test)]
mod tests {
    use super::*;

    fn p(a: &str, b: &str) -> (Term, Term) {
        (parse_term(a), parse_term(b))
    }

    #[test]
    fn features_are_symmetric_finite_and_the_same_length() {
        let l = p("add(x, y)", "add(y, x)");
        let r = p("add(y, x)", "add(x, y)");
        assert_eq!(features(&l), features(&r));
        let consts = (Term::ZERO, Term::ONES);
        assert!(features(&consts).iter().all(|f| f.is_finite()), "a law with no variables");
        let same = p("x", "x");
        assert!(features(&same).iter().all(|f| f.is_finite()));
        assert_eq!(features(&l).len(), F);
    }

    #[test]
    fn the_zero_scorer_scores_zero_and_weights_round_trip() {
        let l = p("and(x, y)", "and(y, x)");
        assert_eq!(Scorer::zero().score(&l), 0.0);
        let mut w = [0.0; F];
        w[1] = 0.25;
        w[10] = -1.5;
        let s = Scorer::with_weights(w);
        assert_eq!(Scorer::from_text(&s.to_text()).unwrap(), s);
        assert!(Scorer::from_text("w 1 2 3").is_err(), "a garbled file is an error that says so");
        assert!(Scorer::from_text("").is_err());
    }

    #[test]
    fn auc_of_known_scores() {
        assert_eq!(auc(&[(0.1, false), (0.4, false), (0.35, true), (0.8, true)]), 0.75);
        assert_eq!(auc(&[(1.0, true), (1.0, false)]), 0.5, "a tie counts half");
        assert_eq!(auc(&[(1.0, true), (2.0, true)]), 0.5, "no negatives: no information");
    }

    #[test]
    fn fit_separates_a_separable_set_and_repeats_bit_for_bit() {
        let rows: Vec<([f32; F], bool)> = (1..=10)
            .map(|i| {
                let mut f = [0.0f32; F];
                f[0] = 1.0;
                f[1] = i as f32;
                (f, i > 5)
            })
            .collect();
        let a = fit(&rows);
        let b = fit(&rows);
        assert_eq!(a, b);
        let scored: Vec<(f64, bool)> = rows.iter().map(|(f, y)| (a.logit(f), *y)).collect();
        assert_eq!(auc(&scored), 1.0);
    }
}
```

Add `mod scorer;` to `tests/church_bv/main.rs`.

- [ ] **Step 2: Run to verify they fail**

Run: `cargo test --release --test church_bv scorer:: -- --nocapture`
Expected: compile errors, `cannot find function features` and the like.

- [ ] **Step 3: Implement** (above the tests module)

```rust
/// Operators counted per side, in `OPS` order.
const OPN: usize = OPS.len();
/// Features: 0 bias; 1 size sum; 2 size gap; 3 larger size; 4 depth; 5 variables used; 6 variables on one side only; 7 most
/// occurrences of a variable; 8 constants; 9 equal variable counts on both sides; then per operator of `OPS` the count over
/// both sides (10..) and the gap between the sides (10 + OPN..).
pub const F: usize = 10 + 2 * OPN;
const FIT_STEPS: usize = 400;
const FIT_RATE: f64 = 0.5;
const FIT_L2: f64 = 1e-3;

fn depth(t: &Term) -> usize {
    match *t.node() {
        Node::Op(_, a, b) => 1 + depth(&a).max(depth(&b)),
        _ => 1,
    }
}

fn consts(t: &Term) -> usize {
    match *t.node() {
        Node::Zero | Node::Ones => 1,
        Node::Op(_, a, b) => consts(&a) + consts(&b),
        Node::V(_) => 0,
    }
}

fn op_counts(t: &Term, out: &mut [usize; OPN]) {
    if let Node::Op(o, a, b) = *t.node() {
        if let Some(i) = OPS.iter().position(|&p| p == o) {
            out[i] += 1;
        }
        op_counts(&a, out);
        op_counts(&b, out);
    }
}

/// A law's feature vector. Symmetric: a law and its mirror image give the same vector.
pub fn features((l, r): &(Term, Term)) -> [f32; F] {
    let (mut va, mut vb) = ([0usize; 8], [0usize; 8]);
    l.occurrences(&mut va);
    r.occurrences(&mut vb);
    let (mut ca, mut cb) = ([0usize; OPN], [0usize; OPN]);
    op_counts(l, &mut ca);
    op_counts(r, &mut cb);
    let (sl, sr) = (l.size(), r.size());
    let mut f = [0f32; F];
    f[0] = 1.0;
    f[1] = (sl + sr) as f32;
    f[2] = sl.abs_diff(sr) as f32;
    f[3] = sl.max(sr) as f32;
    f[4] = depth(l).max(depth(r)) as f32;
    f[5] = (0..8).filter(|&v| va[v] + vb[v] > 0).count() as f32;
    f[6] = (0..8).filter(|&v| (va[v] > 0) != (vb[v] > 0)).count() as f32;
    f[7] = (0..8).map(|v| va[v] + vb[v]).max().unwrap() as f32;
    f[8] = (consts(l) + consts(r)) as f32;
    f[9] = (va == vb) as u8 as f32;
    for i in 0..OPN {
        f[10 + i] = (ca[i] + cb[i]) as f32;
        f[10 + OPN + i] = ca[i].abs_diff(cb[i]) as f32;
    }
    f
}

/// A logistic regression on standardized features. Column 0 (the bias) is not standardized.
#[derive(Clone, Debug, PartialEq)]
pub struct Scorer {
    mean: [f64; F],
    scale: [f64; F],
    w: [f64; F],
}

impl Scorer {
    pub fn zero() -> Scorer {
        Scorer::with_weights([0.0; F])
    }

    pub fn with_weights(w: [f64; F]) -> Scorer {
        Scorer { mean: [0.0; F], scale: [1.0; F], w }
    }

    fn logit(&self, f: &[f32; F]) -> f64 {
        (0..F).map(|i| self.w[i] * (f[i] as f64 - self.mean[i]) / self.scale[i]).sum()
    }

    /// The log-odds that the law pays for a rule; larger is better, 0 for the zero scorer.
    pub fn score(&self, law: &(Term, Term)) -> f32 {
        self.logit(&features(law)) as f32
    }

    /// Three lines, `mean`, `scale` and `w`, each with `F` numbers (`{:?}` prints the shortest text that reads back equal).
    pub fn to_text(&self) -> String {
        let line = |name: &str, v: &[f64; F]| format!("{name} {}\n", v.iter().map(|x| format!("{x:?}")).collect::<Vec<_>>().join(" "));
        line("mean", &self.mean) + &line("scale", &self.scale) + &line("w", &self.w)
    }

    pub fn from_text(text: &str) -> Result<Scorer, String> {
        let mut s = Scorer::zero();
        for name in ["mean", "scale", "w"] {
            let line = text.lines().find_map(|l| l.strip_prefix(name).and_then(|r| r.strip_prefix(' '))).ok_or(format!("no `{name}` line"))?;
            let v: Vec<f64> = line.split(' ').map(|x| x.parse::<f64>().map_err(|e| format!("`{name}`: {x}: {e}"))).collect::<Result<_, _>>()?;
            let v: [f64; F] = v.try_into().map_err(|v: Vec<f64>| format!("`{name}` has {} numbers, expected {F}", v.len()))?;
            match name {
                "mean" => s.mean = v,
                "scale" => s.scale = v,
                _ => s.w = v,
            }
        }
        Ok(s)
    }
}

/// Full-batch gradient descent for the logistic loss with a small L2 penalty, from zero weights: deterministic.
pub fn fit(rows: &[([f32; F], bool)]) -> Scorer {
    let n = rows.len() as f64;
    let (mut mean, mut scale) = ([0.0; F], [1.0; F]);
    for i in 1..F {
        let m = rows.iter().map(|r| r.0[i] as f64).sum::<f64>() / n;
        let v = rows.iter().map(|r| (r.0[i] as f64 - m).powi(2)).sum::<f64>() / n;
        mean[i] = m;
        scale[i] = if v > 0.0 { v.sqrt() } else { 1.0 };
    }
    let mut s = Scorer { mean, scale, w: [0.0; F] };
    for _ in 0..FIT_STEPS {
        let mut g = [0.0; F];
        for (f, y) in rows {
            let e = 1.0 / (1.0 + (-s.logit(f)).exp()) - *y as u8 as f64;
            for i in 0..F {
                g[i] += e * (f[i] as f64 - s.mean[i]) / s.scale[i];
            }
        }
        for i in 0..F {
            s.w[i] -= FIT_RATE * (g[i] / n + FIT_L2 * s.w[i]);
        }
    }
    s
}

/// The area under the ROC curve (Mann-Whitney: the chance a random positive outscores a random negative, a tie counting
/// half); 0.5 when either class is empty.
pub fn auc(scored: &[(f64, bool)]) -> f64 {
    let (pos, neg) = (scored.iter().filter(|s| s.1).count() as f64, scored.iter().filter(|s| !s.1).count() as f64);
    if pos == 0.0 || neg == 0.0 {
        return 0.5;
    }
    let mut order: Vec<usize> = (0..scored.len()).collect();
    order.sort_by(|&i, &j| scored[i].0.total_cmp(&scored[j].0));
    let (mut rank_sum, mut i) = (0.0, 0);
    while i < order.len() {
        let mut j = i;
        while j + 1 < order.len() && scored[order[j + 1]].0 == scored[order[i]].0 {
            j += 1;
        }
        let avg = (i + j) as f64 / 2.0 + 1.0;
        rank_sum += order[i..=j].iter().filter(|&&k| scored[k].1).count() as f64 * avg;
        i = j + 1;
    }
    (rank_sum - pos * (pos + 1.0) / 2.0) / (pos * neg)
}
```

`logit` is private; the test module is a child module so it may call `a.logit`.

- [ ] **Step 4: Run to verify they pass**

Run: `cargo test --release --test church_bv scorer:: -- --nocapture`
Expected: PASS, 4 tests. If `fit_separates...` stops short of AUC 1.0, raise `FIT_STEPS` before touching anything else.

- [ ] **Step 5: Commit**

```bash
git add tests/church_bv/scorer.rs tests/church_bv/main.rs
git commit -m "church_bv: scorer.rs, a logistic regression over counts of a law's sides (features, fit, AUC, weights text)

Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>"
```

---

### Task 3: Wire `SCORER` into `scope_extras`

**Files:**
- Modify: `tests/church_bv/driver.rs` (`scope_extras`, one test)

**Interfaces:**
- Consumes: `select_extras` (Task 1), `scorer::Scorer` (Task 2).
- Produces: env `SCORER=<weights file>` makes `scope_extras` select the best `n` per `POOL x n` block by `Scorer::score`.

- [ ] **Step 1: Write the failing test** (next to the `select_extras` tests)

```rust
#[test]
fn zero_weights_select_the_baseline_and_a_size_weight_prefers_big_laws() {
    let laws = nested_laws(12);
    let texts = |ls: &[(Term, Term)]| ls.iter().map(law_text).collect::<Vec<_>>();
    let zero = crate::scorer::Scorer::zero();
    let z = |l: &(Term, Term)| zero.score(l);
    assert_eq!(texts(&select_extras(&laws, 6, 2, Some(&z))), texts(&select_extras(&laws, 6, 2, None)), "zero weights are the baseline");
    let mut w = [0.0; crate::scorer::F];
    w[1] = 1.0;
    let big = crate::scorer::Scorer::with_weights(w);
    let b = |l: &(Term, Term)| big.score(l);
    assert_eq!(texts(&select_extras(&laws, 6, 2, Some(&b))), texts(&[laws[5], laws[4], laws[11], laws[10]]));
}
```

- [ ] **Step 2: Run to verify it passes the selection but the wiring is absent**

Run: `cargo test --release --test church_bv zero_weights_select -- --nocapture`
Expected: PASS (the pure functions exist already; this pins the contract before the wiring).

- [ ] **Step 3: Wire the scorer into `scope_extras`**

In `scope_extras`, after `let pool = ...;` add:

```rust
    let scorer = setup.var("SCORER").map(|p| {
        let text = std::fs::read_to_string(p).unwrap_or_else(|e| panic!("SCORER {p}: {e}"));
        crate::scorer::Scorer::from_text(&text).unwrap_or_else(|e| panic!("SCORER {p}: {e}"))
    });
    let score = scorer.as_ref().map(|s| move |l: &(Term, Term)| s.score(l));
```

and change the selection line to

```rust
    let laws = select_extras(&kept, pool * n, n, score.as_ref().map(|f| f as &dyn Fn(&(Term, Term)) -> f32));
```

and the `GEN` print to include `, scorer {}` with `scorer.is_some()`.

- [ ] **Step 4: Run the church_bv driver tests**

Run: `cargo test --release --test church_bv driver:: -- --nocapture`
Expected: PASS (the existing driver tests plus the new ones).

- [ ] **Step 5: Commit**

```bash
git add tests/church_bv/driver.rs
git commit -m "church_bv: SCORER=<weights file> orders each mine's pool in scope_extras; zero weights equal the baseline

Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>"
```

---

### Task 4: Labels: the miner's credit line, the parser, the dump tool

**Files:**
- Modify: `tests/church_bv/miner.rs` (`Rounds::report`)
- Modify: `tests/church_bv/scorer.rs` (label parsing, `dump_labels`)

**Interfaces:**
- Produces: log line `RULEMINER label: <1|0> <law>` per straggler (1 = a chosen rule covers it); `pub fn mine_labels(extras: &str, log: &str) -> Result<Vec<(String, bool)>, String>` (one row per extras line, y = 1 only for a covered straggler; an error for a log with stragglers and no label line); `pub fn salt_of(path: &str) -> Option<usize>` (the `s<digits>_` path component); ignored test `dump_labels` (env `LABEL_DIRS` `;`-separated arm folders, `LABEL_OUT` the TSV, rows `salt<TAB>y<TAB>law`).

- [ ] **Step 1: Write the failing tests** (in the `scorer.rs` tests module)

```rust
    #[test]
    fn labels_credit_covered_stragglers_only() {
        let extras = "add(x, y) = add(y, x)\nand(x, y) = and(y, x)\nor(x, y) = or(y, x)\n";
        let log = "RULEMINER 2 stragglers of 9 laws, 1.0s base (0 unproved)\n\
                   RULEMINER label: 1 add(x, y) = add(y, x)\n\
                   RULEMINER label: 0 and(x, y) = and(y, x)\n\
                   RULEMINER label: 1 some(other, law) = served\n";
        let rows = mine_labels(extras, log).unwrap();
        assert_eq!(rows, vec![("add(x, y) = add(y, x)".to_string(), true), ("and(x, y) = and(y, x)".to_string(), false), ("or(x, y) = or(y, x)".to_string(), false)]);
    }

    #[test]
    fn a_log_with_stragglers_and_no_label_lines_is_refused() {
        let old = "RULEMINER 5 stragglers of 9 laws, 1.0s base (0 unproved)\nRULEMINER uncovered: x\n";
        assert!(mine_labels("add(x, y) = add(y, x)\n", old).is_err());
        let none = "RULEMINER 0 stragglers of 9 laws, 1.0s base (0 unproved)\n";
        assert_eq!(mine_labels("add(x, y) = add(y, x)\n", none).unwrap(), vec![("add(x, y) = add(y, x)".to_string(), false)]);
    }

    #[test]
    fn the_salt_is_the_arm_folders_number() {
        assert_eq!(salt_of("C:/runs/2026-11-01-v06-dump/s7_A/cold_streams_streams_1_none"), Some(7));
        assert_eq!(salt_of("C:/runs/s12_B"), Some(12));
        assert_eq!(salt_of("C:/runs/state/none"), None);
    }
```

- [ ] **Step 2: Run to verify they fail**

Run: `cargo test --release --test church_bv scorer:: -- --nocapture`
Expected: compile error, `cannot find function mine_labels`.

- [ ] **Step 3: Implement the parser, the print and the dump tool**

In `scorer.rs` (above the tests):

```rust
/// The label rows of one mine: for each law of its extras file (`lhs = rhs` lines) whether its log credits it
/// (`RULEMINER label: 1 <law>`: a straggler a chosen rule covers). A log that counts stragglers but has no label line was
/// written before the miner printed them: refused, because every law would read as y = 0.
pub fn mine_labels(extras: &str, log: &str) -> Result<Vec<(String, bool)>, String> {
    let credited: std::collections::HashSet<&str> = log.lines().filter_map(|l| l.strip_prefix("RULEMINER label: 1 ")).collect();
    let labelled = log.lines().any(|l| l.starts_with("RULEMINER label: "));
    let stragglers = log
        .lines()
        .filter_map(|l| l.strip_prefix("RULEMINER ")?.split_once(" stragglers of ")?.0.parse::<usize>().ok())
        .next()
        .unwrap_or(0);
    if stragglers > 0 && !labelled {
        return Err(format!("{stragglers} stragglers but no `RULEMINER label:` line"));
    }
    Ok(extras.lines().filter(|l| !l.is_empty()).map(|l| (l.to_string(), credited.contains(l))).collect())
}

/// The number in the first path component that reads `s<digits>_...` (a gate arm folder, `s7_A`).
pub fn salt_of(path: &str) -> Option<usize> {
    path.split(['/', '\\']).find_map(|c| {
        let rest = c.strip_prefix('s')?;
        let (digits, _) = rest.split_once('_')?;
        digits.parse().ok()
    })
}

fn walk(dir: &std::path::Path, out: &mut Vec<std::path::PathBuf>) {
    for e in std::fs::read_dir(dir).unwrap_or_else(|e| panic!("{}: {e}", dir.display())) {
        let p = e.unwrap().path();
        if p.is_dir() {
            walk(&p, out);
        } else {
            out.push(p);
        }
    }
}

/// `LABEL_DIRS=<arm folder>;<arm folder>.. LABEL_OUT=<tsv> <exe> scorer::dump_labels --exact --ignored --nocapture`: one row
/// `salt<TAB>y<TAB>law` per extras law of every mine under the folders (`laws_extra_<m>.txt` with its `mine_<m>.log`).
#[test]
#[ignore]
fn dump_labels() {
    let setup = &job::Setup::process();
    let dirs = setup.var("LABEL_DIRS").expect("LABEL_DIRS");
    let out = setup.var("LABEL_OUT").expect("LABEL_OUT");
    let mut rows = String::new();
    let (mut mines, mut laws, mut pos) = (0, 0, 0);
    for d in dirs.split(';') {
        let mut files = vec![];
        walk(std::path::Path::new(d), &mut files);
        files.sort();
        for f in files.iter().filter(|f| f.file_name().is_some_and(|n| n.to_string_lossy().starts_with("laws_extra_"))) {
            let name = f.file_name().unwrap().to_string_lossy().replace("laws_extra_", "").replace(".txt", "");
            let log = f.with_file_name(format!("mine_{name}.log"));
            let salt = salt_of(&f.to_string_lossy()).unwrap_or_else(|| panic!("no s<salt>_ folder in {}", f.display()));
            let (extras, log_text) = (std::fs::read_to_string(f).unwrap(), std::fs::read_to_string(&log).unwrap_or_else(|e| panic!("{}: {e}", log.display())));
            for (law, y) in mine_labels(&extras, &log_text).unwrap_or_else(|e| panic!("{}: {e}", log.display())) {
                rows += &format!("{salt}\t{}\t{law}\n", y as u8);
                laws += 1;
                pos += y as usize;
            }
            mines += 1;
        }
    }
    std::fs::write(out, rows).unwrap();
    println!("LABELS {mines} mines, {laws} laws, {pos} credited");
}
```

In `miner.rs` `Rounds::report`, inside the loop `for (st, c) in stragglers.iter().zip(covered)`, add as its first line:

```rust
            println!("RULEMINER label: {} {}", *c as u8, st.0);
```

(the existing `if !c { println!("RULEMINER uncovered: ...") }` stays).

- [ ] **Step 4: Run to verify they pass**

Run: `cargo test --release --test church_bv scorer:: miner:: -- --nocapture`
Expected: PASS. Then confirm the print on a real mine log in the next task's run (Task 6 checks `LABELS` shows credited > 0).

- [ ] **Step 5: Commit**

```bash
git add tests/church_bv/miner.rs tests/church_bv/scorer.rs
git commit -m "church_bv: the miner prints a credit label per straggler; scorer.rs parses mine logs into label rows (dump_labels)

Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>"
```

---

### Task 5: The fit tool

**Files:**
- Modify: `tests/church_bv/scorer.rs` (`fit_scorer`)

**Interfaces:**
- Consumes: `fit`, `auc`, `features`, label TSV (Task 4).
- Produces: ignored test `fit_scorer` (env `LABELS` the TSV, `TRAIN_SALTS` and `TEST_SALTS` comma lists, `SCORER_OUT` the weights file): fits on the train rows, writes the weights, prints `AUC train <a> test <b> sizeonly-test <c> rows <n> positives <k>`.

- [ ] **Step 1: Write the failing test** (pure part: reading rows)

```rust
    #[test]
    fn rows_split_by_salt() {
        let tsv = "4\t1\tadd(x, y) = add(y, x)\n5\t0\tand(x, y) = and(y, x)\n4\t0\tor(x, y) = or(y, x)\n";
        let (a, b) = split_rows(tsv, &[4], &[5]);
        assert_eq!((a.len(), b.len()), (2, 1));
        assert!(a[0].1 && !a[1].1 && !b[0].1);
    }
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test --release --test church_bv rows_split_by_salt -- --nocapture`
Expected: compile error, `cannot find function split_rows`.

- [ ] **Step 3: Implement**

```rust
type Rows = Vec<([f32; F], bool)>;

/// The label TSV's rows (`salt<TAB>y<TAB>law`) of the `train` salts and of the `test` salts, as feature rows.
pub fn split_rows(tsv: &str, train: &[usize], test: &[usize]) -> (Rows, Rows) {
    let (mut a, mut b) = (vec![], vec![]);
    for l in tsv.lines() {
        let mut p = l.splitn(3, '\t');
        let (salt, y, law) = (p.next().unwrap().parse::<usize>().unwrap(), p.next().unwrap() == "1", p.next().unwrap());
        let (lhs, rhs) = law.split_once(" = ").unwrap_or_else(|| panic!("not a law: {law}"));
        let row = (features(&(parse_term(lhs), parse_term(rhs))), y);
        if train.contains(&salt) {
            a.push(row);
        } else if test.contains(&salt) {
            b.push(row);
        }
    }
    (a, b)
}

/// `LABELS=<tsv> TRAIN_SALTS=4,5,.. TEST_SALTS=10 SCORER_OUT=<weights> <exe> scorer::fit_scorer --exact --ignored --nocapture`.
/// Fits on the train salts, writes the weights, and prints the AUC on the train rows, on the test rows, and of the size
/// feature alone on the test rows (the baseline the scorer must beat).
#[test]
#[ignore]
fn fit_scorer() {
    let setup = &job::Setup::process();
    let salts = |k: &str| -> Vec<usize> { setup.var(k).unwrap_or("").split(',').filter(|s| !s.is_empty()).map(|s| s.parse().unwrap()).collect() };
    let tsv = std::fs::read_to_string(setup.var("LABELS").expect("LABELS")).unwrap();
    let (train, test) = split_rows(&tsv, &salts("TRAIN_SALTS"), &salts("TEST_SALTS"));
    let s = fit(&train);
    std::fs::write(setup.var("SCORER_OUT").expect("SCORER_OUT"), s.to_text()).unwrap();
    let on = |rows: &Rows, f: &dyn Fn(&[f32; F]) -> f64| auc(&rows.iter().map(|(x, y)| (f(x), *y)).collect::<Vec<_>>());
    println!(
        "AUC train {:.4} test {:.4} sizeonly-test {:.4} rows {} positives {}",
        on(&train, &|f| s.logit(f)),
        on(&test, &|f| s.logit(f)),
        on(&test, &|f| f[1] as f64),
        train.len(),
        train.iter().filter(|r| r.1).count()
    );
}
```

- [ ] **Step 4: Run to verify it passes**

Run: `cargo test --release --test church_bv scorer:: -- --nocapture`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add tests/church_bv/scorer.rs
git commit -m "church_bv: fit_scorer fits on the label rows of the train salts and prints test AUC against size alone

Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>"
```

---

### Task 6: Dump labels on salts 4-10, fit, and the signal verdict (a recorded run)

**Files:**
- Create: `docs/runs/2026-10-31/scripts/gate.sh`
- Modify: `docs/runs.md` (rows added by `run.ps1`)

Expected duration: the earlier two-arm gate on three salts took about 22 minutes wall at JOBS=3; seven salts at JOBS=3 is about 50 minutes wall, about 100 minutes of job CPU. Check for orphans (`Get-Process`) and live CPU leases first (`LONG_RUNS.md`); report Defender real-time state with the result.

- [ ] **Step 1: Write the gate wrapper**

Create `docs/runs/2026-10-31/scripts/gate.sh`:

```bash
#!/bin/bash
# gate.sh <exe A> <exe B> <salts...>: the untimed gate (docs/tier-cycle.md, "Under load too"), JOBS=3 with the arm cache.
export JOBS=3 ARM_CACHE="$LOCALAPPDATA/claude-runs/tatic/arm-cache"
cd "$(dirname "$0")/../../../.." && exec scripts/streams_ab.sh "$@"
```

- [ ] **Step 2: Build the exes**

Rebuild after Task 5 (`cargo test --release --test church_bv --no-run`), copy the printed exe to `$LOCALAPPDATA/claude-runs/tatic/v06-exes/base.exe` and `.../base2.exe` (the same bytes; the gate needs two paths), each with a `.exe.env` containing `POOL=1` (explicit, so the `ENV` line prints).

- [ ] **Step 3: Run the label gate**

```bash
A=$(cygpath -m "$(cygpath -d "$LOCALAPPDATA/claude-runs/tatic/v06-exes/base.exe")")
B=$(cygpath -m "$(cygpath -d "$LOCALAPPDATA/claude-runs/tatic/v06-exes/base2.exe")")
G=$(cygpath -m "$(cygpath -d "$PWD/docs/runs/2026-10-31/scripts/gate.sh")")
powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind gate -Name v06-labels -Affinity CFF -Detach -Command "bash $G $A $B 4 5 6 7 8 9 10"
```

Arm a watcher on `run.json`'s `"end"` (deadline 120 minutes). Expected: both arms of every salt give the same rules and M (the gate is deterministic); the labels come from arm A.

- [ ] **Step 4: Dump the labels**

```bash
R="$LOCALAPPDATA/claude-runs/tatic/$(ls "$LOCALAPPDATA/claude-runs/tatic" | grep 'v06-labels$')"
L=""; for s in 4 5 6 7 8 9 10; do L="$L;$R/s${s}_A"; done
LABEL_DIRS="${L#;}" LABEL_OUT="$R/labels.tsv" "<the exe>" scorer::dump_labels --exact --ignored --nocapture
```

Expected: `LABELS 42 mines, 13398 laws, <k> credited` (7 salts x 3 loops x 2 mines x 319; `k` > 0). If `k` is 0 or the dump refuses a log, stop: the label line did not print.

- [ ] **Step 5: Fit and read the verdict**

```bash
SCORER_OUT="$R/weights_4_9.txt" LABELS="$R/labels.tsv" TRAIN_SALTS=4,5,6,7,8,9 TEST_SALTS=10 "<the exe>" scorer::fit_scorer --exact --ignored --nocapture
```

**Verdict rule (set before the data):** continue only if test AUC >= 0.55 and test AUC >= size-only test AUC + 0.02. Otherwise stop here: record `labels.tsv` path, the AUC line, the credited rate and the negative result in `docs/tier-cycle.md` (a section "A learned scorer over the extras: no signal in count features", with the run id), park stage 2 and the next steps (a richer model, a w2 transfer label) in `PARKED.md` with the trigger "a result that suggests count features are too weak", and report to the user.

- [ ] **Step 6: Fit the final weights**

If the verdict continues: `TRAIN_SALTS=4,5,6,7,8,9,10 TEST_SALTS=` (empty) `SCORER_OUT="$R/weights.txt"` and copy `weights.txt` to `$LOCALAPPDATA/claude-runs/tatic/v06-exes/weights.txt`.

- [ ] **Step 7: Commit**

```bash
git add docs/runs/2026-10-31/scripts/gate.sh docs/runs.md
git commit -m "docs: v0.6 stage 1 label run v06-labels and the fit verdict

Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>"
```

---

### Task 7: The gate matrix, the curve verdict, and the record (recorded runs)

**Files:**
- Create: `docs/runs/2026-10-31/scripts/curve.sh`
- Modify: `docs/tier-cycle.md`, `ROADMAP.md`, `PARKED.md`, `docs/superpowers/specs/2026-10-31-learned-proposer-design.md`, `docs/runs.md`

**Correction to the spec, applied in this task.** The gate is deterministic (same exe and environment give the same rules and M), so "a second random run as the A/A" would read zero spread. The A/A spread is the redraw spread: the random arm with `GEN_DRAW=1` and `GEN_DRAW=2` against `GEN_DRAW=0`, summed over the same salts. Edit the spec's Stage 1 step 3 and "Question and success" to say so.

Expected duration: six gate runs on salts 1-3, about 22 minutes each at n 319 and less at n 80 and 160 (cost is about linear in n), with the arm cache reusing the unchanged random arm: about 1.5 to 2 hours wall in all.

- [ ] **Step 1: Arm exes**

All from the exe of Task 6 Step 2 (the bytes never change; only `.exe.env`). In `$LOCALAPPDATA/claude-runs/tatic/v06-exes/` make copies and env files (`P` is the pool Task 1 Step 7 ruled; every file also has `POOL` or the `SCORER` line as shown):

| exe copy | `.exe.env` lines |
|---|---|
| `r80.exe`, `r160.exe`, `r319.exe` | `EXTRAS_N=80`, `EXTRAS_N=160`, `EXTRAS_N=319` |
| `s80.exe`, `s160.exe`, `s319.exe` | the same `EXTRAS_N`, plus `POOL=P` and `SCORER=<full path of weights.txt>` |
| `c319.exe` | `EXTRAS_N=319` and `POOL=P` (the control: pool P, first n) |
| `d1.exe`, `d2.exe` | `EXTRAS_N=319` and `GEN_DRAW=1` / `GEN_DRAW=2` (redraws for the spread) |

- [ ] **Step 2: The summary script**

Create `docs/runs/2026-10-31/scripts/curve.sh`:

```bash
#!/bin/bash
# curve.sh <label> <A|B> <run name>... : one line per arm summed over its salts, from the gate runs' out.log:
# held-out M, loop M, rules, job CPU, walk/match/op (G), bands 11-17 per 1000 laws | free share. The `row` function of
# docs/runs/2026-10-28/scripts/salts.sh (lines 6-21) is used unchanged.
source <(sed -n 6,21p "$(dirname "$0")/../../2026-10-28/scripts/salts.sh")
label=$1; arm=$2; shift 2
args=(); for r in "$@"; do for s in 1 2 3; do args+=("$r@$s"); done; done
row "$label" "$arm" "${args[@]}"
```

(run `bash -n` on it; `row` prints `label | held | M | rules | cpu | work | bands`.)

- [ ] **Step 3: Run the six gates** (each through `run.ps1 -Kind gate -Affinity CFF -Detach`, salts `1 2 3`, with a watcher; names `v06-g1` ... `v06-g6`)

| run | A | B | answers |
|---|---|---|---|
| `v06-g1` | `r319` | `d1` | redraw spread (1) |
| `v06-g2` | `r319` | `d2` | redraw spread (2) |
| `v06-g3` | `r319` | `c319` | what the pool alone does |
| `v06-g4` | `r80` | `s80` | the curve at n 80 |
| `v06-g5` | `r160` | `s160` | the curve at n 160 |
| `v06-g6` | `r319` | `s319` | the curve at n 319 |

Before each run's results are read, check that its `out.log` shows `ENV SCORER=` or `ENV POOL=` or `ENV EXTRAS_N=` lines for the arms it should have (`changed` flags a switch that never took effect), and that the scorer arms' `GEN` lines say `scorer true`.

- [ ] **Step 4: Read the curve**

```bash
bash docs/runs/2026-10-31/scripts/curve.sh r319 A v06-g1
bash docs/runs/2026-10-31/scripts/curve.sh d1 B v06-g1
bash docs/runs/2026-10-31/scripts/curve.sh d2 B v06-g2
bash docs/runs/2026-10-31/scripts/curve.sh c319 B v06-g3
bash docs/runs/2026-10-31/scripts/curve.sh r80 A v06-g4;  bash docs/runs/2026-10-31/scripts/curve.sh s80 B v06-g4
bash docs/runs/2026-10-31/scripts/curve.sh r160 A v06-g5; bash docs/runs/2026-10-31/scripts/curve.sh s160 B v06-g5
bash docs/runs/2026-10-31/scripts/curve.sh r319 A v06-g6; bash docs/runs/2026-10-31/scripts/curve.sh s319 B v06-g6
```

**Verdict rule (set before the data).** Let `sigma` be the larger of the two redraw gaps in held-out M (`|r319 - d1|`, `|r319 - d2|`), summed over salts 1-3. A **win** is either (a) `held(s_n) < held(r_n) - sigma` for some n with job CPU of `s_n` no more than 1.1x that of `r_n`, or (b) `held(s_n) <= held(r_2n)` with job CPU of `s_n` below that of `r_2n` (n 80 against 160, 160 against 319). The control `c319` must be within `sigma` of `r319`, otherwise the pool, not the ranking, moved the result. Report all three numbers per n.

- [ ] **Step 5: Record**

In `docs/tier-cycle.md`, a section "A learned scorer over the extras (v0.6 stage 1)" with the AUC line, the curve table (the rows above), `sigma`, the verdict, the run ids and the label bias note. Update `ROADMAP.md` v0.6: a win -> add a stage 2 line with its `Done when`; no win -> v0.6 stays with the negative result linked and the next step named. `PARKED.md`: stage 2 (the cycle) as an entry with the stage 1 verdict as its trigger; the richer-model and w2-transfer-label options. Set the spec's `status:` to `done` when stage 1 is recorded, with leftovers parked first.

- [ ] **Step 6: Commit**

```bash
git add docs/ ROADMAP.md PARKED.md
git commit -m "docs: v0.6 stage 1 result, a learned scorer over the extras (runs v06-g1..g6)

Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>"
```

---

## Self-review

- **Spec coverage:** scorer interface and features (Task 2); `scope_extras` selection with pool and zero-weights equality (Tasks 1, 3); label dump (Task 4); fit and AUC against size only (Tasks 5, 6); gate A/B at n 80/160/319 with control (Task 7); the 4n sequence-length check first (Task 1 Steps 6-7); trust (global constraint; no kernel code touched); stage 2 as an outline stays in the spec and `PARKED.md` (Task 7). Gap fixed: the spec's A/A is replaced by the redraw spread (Task 7 header).
- **Placeholders:** `<the exe>` and `<the printed exe>` in run commands name a file the build prints (`scripts/experiments/README.md` documents the step); no step leaves code or a decision rule open.
- **Types:** `select_extras(&[(Term, Term)], usize, usize, Option<&dyn Fn(&(Term, Term)) -> f32>)` is called with `None` (Task 1), `Some(&closure)` (Tasks 1, 3); `Scorer::{zero, with_weights, score, to_text, from_text}`, `fit`, `auc`, `features`, `F` agree across Tasks 2-5; `mine_labels` -> `Result<Vec<(String, bool)>, String>` is used in `dump_labels`.
