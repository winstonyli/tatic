---
status: done
---

# Belief layer, calibration milestone: implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Execution note (2026-11-01):** Tasks 1-4 and 6 ran; Task 5 (logistic arm) did not start because the stage-1 gate found 0 hard negatives. `oof` was not added. See `docs/tier-cycle.md`, "The belief layer's calibration milestone stops at its first gate".

**Goal:** Measure whether shape plus cheap evidence predicts which claimed equalities are false or unprovable, better than the fixed screen (spec question), and record the finding.

**Architecture:** One new test module `tests/church_bv/belief.rs` holds pure statistics (AUC, paired bootstrap, grouped folds, reliability), the two estimators (smoothed counts, logistic), a claim dump (ignored test, uses `Classes::build`'s merge sample) and a report (ignored test reading the dump). Nothing in the kernel, miner or class table reads belief.

**Tech Stack:** Rust, the existing `tests/church_bv` crate; no new dependency; hand-rolled numerics.

**Spec:** `docs/superpowers/specs/2026-10-31-belief-layer-design.md` (approved 2026-10-31; amended at this plan: the dump uses `Classes::build`'s sample, not a rebuilt probe).

## Global Constraints

- No new dependency; numerics hand-rolled, deterministic (fixed LCG seeds, no `rand`).
- Belief orders and budgets only: no code path outside `belief.rs` calls it.
- S1 (256 inputs) and S2 (4096 inputs) are fixed, disjoint input sets; S2 uses seed `0x6a09_e667_f3bc_c908`, the claim sample seed `0x51ed_270b_27a3_c1f5`, S1 a new seed `0x1b87_3593_0000_0001`; the test compares the sets, not the seeds.
- The label counts a claim refuted on any S2, S1, width-4 or screen difference; evidence tiers are key, `w4`, `screen`, `extra[n]`, n in {0, 8, 64, 256}.
- Primary: paired AUC difference at n = 0 on A_ref over the screen-pass subset, belief minus the better of {0.5, size-only}; required co-primary: the no-key arm; 95% bootstrap over claims; resamples with no negative skipped.
- Stage-1 gate: at least 100 subset negatives in all and at least 10 in each fold, else stop and record.
- Grouped 5-fold cross-validation over connected components of shared side terms; folds fixed before any fit.
- Claim cap per key fixed by claim count from a pilot (Task 3), never a wall-clock deadline.
- Counts are instruction counts (`~/.claude/ICOUNT.md`); no timed claims. Long runs go through `~/.claude/runs/run.ps1`.
- Never push, tag or bump unasked. `docs/TOUR.md` is updated with the module and `bash scripts/tour_check.sh` passes in the same commit.
- Never let `python` read stdin; use `-I` and a script file (subagents: repeat this in any brief that may edit files).

## Review Focus

- A fold with no negatives or no positives: AUC is `None`, not a panic or a NaN; the bootstrap skips such resamples.
- A cell with no training claims: the fallback chain answers and flags it; belief never NaN.
- All-tied scores (the screen, bitwise key): AUC is exactly 0.5.
- A claim failing `extra[n]`: belief is 1 (decided), never the cell estimate.
- A `claims.tsv` with an unknown kind or key name: the report fails loudly naming the line.

---

## File structure

- Create: `tests/church_bv/belief.rs` (statistics, estimators, dump, report).
- Modify: `tests/church_bv/main.rs` (`mod belief;`).
- Modify: `tests/church_bv/classes.rs` (`verdict` to `pub(crate)`), `tests/church_bv/rewrite.rs` (`with_screen`, `ValueMemo::values` and `SCREEN_INPUTS` to `pub(crate)` as the compiler demands; nothing else).
- Modify at the end: `docs/TOUR.md`, `docs/tier-cycle.md`, `ROADMAP.md`, `docs/runs.md` (by the wrapper).

---

### Task 1: Statistics core

**Files:**
- Create: `tests/church_bv/belief.rs`
- Modify: `tests/church_bv/main.rs`

**Interfaces:**
- Produces: `auc(score: &[f64], neg: &[bool]) -> Option<f64>` (probability a random negative scores above a random positive, ties half; high score = negative class); `paired_bootstrap(a: &[f64], b: &[f64], neg: &[bool], reps: usize, seed: u64) -> Option<(f64, f64, usize)>` (2.5% and 97.5% of AUC(a) − AUC(b), and the resamples used); `fold_of(claims: &[(String, String)]) -> Vec<usize>` (5 folds by connected components of shared sides); `reliability(score: &[f64], neg: &[bool], bins: usize) -> Vec<(f64, f64, usize)>` (mean score, negative rate, count per equal-count bin).

- [ ] **Step 1: Write the failing tests**

Create `tests/church_bv/belief.rs`:

```rust
//! The belief layer's calibration milestone (docs/superpowers/specs/2026-10-31-belief-layer-design.md): statistics,
//! estimators, the claim dump and the report. Nothing outside this file reads a belief.

#[cfg(test)]
mod stats_tests {
    use super::*;

    #[test]
    fn auc_perfect_constant_reversed_and_ties() {
        let neg = [false, false, true, true];
        assert_eq!(auc(&[0.1, 0.2, 0.8, 0.9], &neg), Some(1.0));
        assert_eq!(auc(&[0.5; 4], &neg), Some(0.5));
        assert_eq!(auc(&[0.9, 0.8, 0.2, 0.1], &neg), Some(0.0));
        // one tie between a positive and a negative counts half: pairs (0.1,0.5)=1, (0.1,0.9)=1, (0.5,0.5)=.5, (0.5,0.9)=1
        assert_eq!(auc(&[0.1, 0.5, 0.5, 0.9], &neg), Some(3.5 / 4.0));
        assert_eq!(auc(&[0.1, 0.2], &[false, false]), None);
        assert_eq!(auc(&[0.1, 0.2], &[true, true]), None);
    }

    #[test]
    fn bootstrap_of_identical_scores_has_zero_width_and_a_real_gap_is_positive() {
        let neg: Vec<bool> = (0..200).map(|i| i % 4 == 0).collect();
        let same: Vec<f64> = (0..200).map(|i| (i % 7) as f64).collect();
        let (lo, hi, used) = paired_bootstrap(&same, &same, &neg, 200, 7).unwrap();
        assert_eq!((lo, hi), (0.0, 0.0));
        assert_eq!(used, 200);
        let perfect: Vec<f64> = neg.iter().map(|n| if *n { 1.0 } else { 0.0 }).collect();
        let (lo, _, _) = paired_bootstrap(&perfect, &[0.5; 200], &neg, 200, 7).unwrap();
        assert!(lo > 0.4, "{lo}");
    }

    #[test]
    fn folds_keep_claims_that_share_a_side_together() {
        let c = |a: &str, b: &str| (a.to_string(), b.to_string());
        let claims = vec![c("a", "r1"), c("b", "r1"), c("c", "r2"), c("a", "r3"), c("d", "r4")];
        let f = fold_of(&claims);
        assert_eq!(f[0], f[1]); // share r1
        assert_eq!(f[0], f[3]); // share a
        assert!(f.iter().all(|x| *x < 5));
    }

    #[test]
    fn reliability_bins_are_equal_count_and_cover_everything() {
        let score: Vec<f64> = (0..100).map(|i| i as f64 / 100.0).collect();
        let neg: Vec<bool> = (0..100).map(|i| i >= 50).collect();
        let b = reliability(&score, &neg, 10);
        assert_eq!(b.len(), 10);
        assert!(b.iter().all(|x| x.2 == 10));
        assert_eq!(b[0].1, 0.0);
        assert_eq!(b[9].1, 1.0);
    }
}
```

Add `mod belief;` after `mod classes;` in `tests/church_bv/main.rs`.

- [ ] **Step 2: Run to verify they fail**

Run: `cargo test --test church_bv stats_tests 2>&1 | tail -15`
Expected: compile error, `cannot find function auc` (and the other three).

- [ ] **Step 3: Implement**

Insert above the `#[cfg(test)]` block in `belief.rs`:

```rust
use std::collections::HashMap;

/// The probability that a random negative scores above a random positive, ties half (Mann-Whitney); `None` with no
/// negative or no positive.
pub fn auc(score: &[f64], neg: &[bool]) -> Option<f64> {
    let n = score.len();
    let nn = neg.iter().filter(|x| **x).count();
    let np = n - nn;
    if nn == 0 || np == 0 {
        return None;
    }
    let mut idx: Vec<usize> = (0..n).collect();
    idx.sort_by(|&a, &b| score[a].total_cmp(&score[b]));
    let (mut rank_sum, mut i) = (0.0f64, 0);
    while i < n {
        let mut j = i;
        while j + 1 < n && score[idx[j + 1]] == score[idx[i]] {
            j += 1;
        }
        let avg = (i + j) as f64 / 2.0 + 1.0;
        for k in i..=j {
            if neg[idx[k]] {
                rank_sum += avg;
            }
        }
        i = j + 1;
    }
    Some((rank_sum - (nn * (nn + 1)) as f64 / 2.0) / (nn as f64 * np as f64))
}

fn lcg(s: &mut u64) -> u64 {
    *s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
    *s >> 33
}

/// The 2.5% and 97.5% points of AUC(a) − AUC(b) over `reps` resamples of the claims (the same resample scores both), and
/// how many resamples had a negative and a positive; `None` when none did.
pub fn paired_bootstrap(a: &[f64], b: &[f64], neg: &[bool], reps: usize, seed: u64) -> Option<(f64, f64, usize)> {
    let n = a.len();
    let (mut s, mut diffs) = (seed, vec![]);
    for _ in 0..reps {
        let idx: Vec<usize> = (0..n).map(|_| lcg(&mut s) as usize % n).collect();
        let (ra, rb, rn): (Vec<f64>, Vec<f64>, Vec<bool>) = (idx.iter().map(|&i| a[i]).collect(), idx.iter().map(|&i| b[i]).collect(), idx.iter().map(|&i| neg[i]).collect());
        if let (Some(x), Some(y)) = (auc(&ra, &rn), auc(&rb, &rn)) {
            diffs.push(x - y);
        }
    }
    if diffs.is_empty() {
        return None;
    }
    diffs.sort_by(|x, y| x.total_cmp(y));
    let at = |q: f64| diffs[((diffs.len() - 1) as f64 * q).round() as usize];
    Some((at(0.025), at(0.975), diffs.len()))
}

/// A fold in 0..5 per claim `(u, r)`: claims sharing a side term are one component, and a hash of the component's
/// first-seen side picks the fold, so no side term is split between training and test.
pub fn fold_of(claims: &[(String, String)]) -> Vec<usize> {
    fn find(p: &mut [usize], mut x: usize) -> usize {
        while p[x] != x {
            p[x] = p[p[x]];
            x = p[x];
        }
        x
    }
    let mut ids: HashMap<&str, usize> = HashMap::new();
    let mut pairs = Vec::with_capacity(claims.len());
    for (u, r) in claims {
        let n = ids.len();
        let a = *ids.entry(u.as_str()).or_insert(n);
        let n = ids.len();
        let b = *ids.entry(r.as_str()).or_insert(n);
        pairs.push((a, b));
    }
    let mut parent: Vec<usize> = (0..ids.len()).collect();
    for &(a, b) in &pairs {
        let (ra, rb) = (find(&mut parent, a), find(&mut parent, b));
        if ra != rb {
            parent[ra.max(rb)] = ra.min(rb); // a component's root is its smallest id, the first-seen side
        }
    }
    let mut text = vec![""; ids.len()];
    for (s, &i) in &ids {
        text[i] = s;
    }
    pairs
        .iter()
        .map(|&(a, _)| {
            let mut h: u64 = 0xcbf29ce484222325; // FNV-1a: stable across runs
            for b in text[find(&mut parent, a)].bytes() {
                h = (h ^ b as u64).wrapping_mul(0x100000001b3);
            }
            (h % 5) as usize
        })
        .collect()
}

/// Equal-count bins by score: (mean score, negative rate, count).
pub fn reliability(score: &[f64], neg: &[bool], bins: usize) -> Vec<(f64, f64, usize)> {
    let mut idx: Vec<usize> = (0..score.len()).collect();
    idx.sort_by(|&a, &b| score[a].total_cmp(&score[b]));
    (0..bins)
        .map(|k| {
            let s = &idx[k * idx.len() / bins..(k + 1) * idx.len() / bins];
            let n = s.len().max(1) as f64;
            (s.iter().map(|&i| score[i]).sum::<f64>() / n, s.iter().filter(|&&i| neg[i]).count() as f64 / n, s.len())
        })
        .collect()
}
```

- [ ] **Step 4: Run to verify they pass**

Run: `cargo test --test church_bv stats_tests 2>&1 | tail -15`
Expected: 4 passed.

- [ ] **Step 5: Commit**

Add the `docs/TOUR.md` entry now (concepts and flow only, no measurements): the belief layer as a calibrated P(claim is refuted or unprovable) from shape and evidence that orders and budgets work and never accepts a claim, with cites `tests/church_bv/belief.rs#auc` and `tests/church_bv/belief.rs#fold_of`; run `bash scripts/tour_check.sh` (it checks that each cited symbol appears in its file).

```bash
git add tests/church_bv/belief.rs tests/church_bv/main.rs docs/TOUR.md
git commit -m "belief: AUC, paired bootstrap, grouped folds, reliability bins; tour entry"
```

---

### Task 2: Estimators (counts and logistic)

**Files:**
- Modify: `tests/church_bv/belief.rs`

**Interfaces:**
- Consumes: Task 1's `auc`.
- Produces: `struct Cell { kind: u8, key: u8, w4: bool, screen: bool, n: u8 }` (derive `Clone, Copy, PartialEq, Eq, Hash`); `struct Counts` with `Counts::fit(cells: &[Cell], hit: &[bool]) -> Counts` and `Counts::p(&self, c: Cell) -> (f64, u8)` (Beta(1,1)-smoothed hit fraction and the fallback level used: 0 exact cell, 1 (kind,key,n), 2 (kind,key), 3 (key), 4 global); `logistic_fit(x: &[Vec<f64>], y: &[bool], l2: f64) -> Vec<f64>` and `logistic_p(w: &[f64], x: &[f64]) -> f64` (the last feature of every row is a constant 1.0 added by the caller).

- [ ] **Step 1: Write the failing tests**

Append inside a new `#[cfg(test)] mod estimator_tests` in `belief.rs`:

```rust
#[cfg(test)]
mod estimator_tests {
    use super::*;

    fn cell(kind: u8, key: u8, n: u8) -> Cell {
        Cell { kind, key, w4: true, screen: true, n }
    }

    #[test]
    fn counts_are_beta_smoothed_and_fall_back_when_a_cell_is_empty() {
        let cells = [cell(1, 0, 0), cell(1, 0, 0), cell(1, 0, 0), cell(1, 0, 1)];
        let hit = [true, false, false, true];
        let c = Counts::fit(&cells, &hit);
        // cell (1,0,0): 1 hit of 3 -> (1+1)/(3+2)
        assert_eq!(c.p(cell(1, 0, 0)), (2.0 / 5.0, 0));
        // an unseen n has no (kind,key,n) cell, so level 2 (kind,key) answers: 2 hits of 4 -> 3/6
        assert_eq!(c.p(cell(1, 0, 2)), (3.0 / 6.0, 2));
        // an unseen key falls back to the global: 2 hits of 4 -> 3/6
        assert_eq!(c.p(cell(3, 9, 0)), (3.0 / 6.0, 4));
    }

    #[test]
    fn logistic_separates_a_separable_toy_set() {
        let x: Vec<Vec<f64>> = (0..40).map(|i| vec![(i as f64 - 20.0) / 10.0, 1.0]).collect();
        let y: Vec<bool> = (0..40).map(|i| i >= 20).collect();
        let w = logistic_fit(&x, &y, 0.1);
        let p: Vec<f64> = x.iter().map(|r| logistic_p(&w, r)).collect();
        assert_eq!(auc(&p, &y), Some(1.0));
        assert!(p[0] < 0.2 && p[39] > 0.8, "{} {}", p[0], p[39]);
    }

    #[test]
    fn logistic_with_one_class_or_no_rows_is_finite() {
        let x = vec![vec![1.0, 1.0], vec![2.0, 1.0]];
        for y in [[true, true], [false, false]] {
            let w = logistic_fit(&x, &y, 1.0);
            assert!(w.iter().all(|v| v.is_finite()) && logistic_p(&w, &x[0]).is_finite());
        }
        assert!(logistic_fit(&[], &[], 1.0).iter().all(|v| v.is_finite()));
    }
}
```

- [ ] **Step 2: Run to verify they fail**

Run: `cargo test --test church_bv estimator_tests 2>&1 | tail -15`
Expected: compile error, `cannot find type Cell`.

- [ ] **Step 3: Implement**

Add to `belief.rs`:

```rust
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Cell {
    pub kind: u8,
    pub key: u8,
    pub w4: bool,
    pub screen: bool,
    pub n: u8,
}

/// Smoothed hit fractions per cell, with the fallback chain exact cell, (kind, key, n), (kind, key), key, global.
pub struct Counts {
    levels: [HashMap<(u8, u8, u8, u8, u8), (usize, usize)>; 5],
}

fn level_key(c: Cell, level: usize) -> (u8, u8, u8, u8, u8) {
    match level {
        0 => (c.kind, c.key, c.w4 as u8, c.screen as u8, c.n),
        1 => (c.kind, c.key, 0, 0, c.n),
        2 => (c.kind, c.key, 0, 0, 0),
        3 => (0, c.key, 0, 0, 0),
        _ => (0, 0, 0, 0, 0),
    }
}

impl Counts {
    pub fn fit(cells: &[Cell], hit: &[bool]) -> Counts {
        let mut levels: [HashMap<_, (usize, usize)>; 5] = Default::default();
        for (c, h) in cells.iter().zip(hit) {
            for (l, m) in levels.iter_mut().enumerate() {
                let e = m.entry(level_key(*c, l)).or_default();
                e.0 += *h as usize;
                e.1 += 1;
            }
        }
        Counts { levels }
    }

    /// The smoothed hit fraction and the level that answered.
    pub fn p(&self, c: Cell) -> (f64, u8) {
        for l in 0..5 {
            if let Some(&(h, t)) = self.levels[l].get(&level_key(c, l)) {
                return ((h + 1) as f64 / (t + 2) as f64, l as u8);
            }
        }
        (0.5, 4)
    }
}

pub fn logistic_p(w: &[f64], x: &[f64]) -> f64 {
    1.0 / (1.0 + (-w.iter().zip(x).map(|(a, b)| a * b).sum::<f64>()).exp())
}

/// L2-regularised logistic regression by Newton steps (the last feature is the caller's constant 1.0, unpenalised).
pub fn logistic_fit(x: &[Vec<f64>], y: &[bool], l2: f64) -> Vec<f64> {
    let d = x.first().map_or(1, |r| r.len());
    let mut w = vec![0.0; d];
    let pos = y.iter().filter(|b| **b).count();
    if x.is_empty() || pos == 0 || pos == y.len() {
        // one class (or none): the unpenalised intercept would diverge, so answer the smoothed rate with no slopes
        let q = (pos as f64 + 1.0) / (y.len() as f64 + 2.0);
        w[d - 1] = (q / (1.0 - q)).ln();
        return w;
    }
    for _ in 0..25 {
        let (mut g, mut h) = (vec![0.0; d], vec![vec![0.0; d]; d]);
        for (r, yi) in x.iter().zip(y) {
            let p = logistic_p(&w, r);
            let (e, v) = (p - *yi as u8 as f64, (p * (1.0 - p)).max(1e-9));
            for i in 0..d {
                g[i] += e * r[i];
                for j in 0..d {
                    h[i][j] += v * r[i] * r[j];
                }
            }
        }
        for i in 0..d - 1 {
            g[i] += l2 * w[i];
            h[i][i] += l2;
        }
        h[d - 1][d - 1] += 1e-9;
        // solve h * step = g by Gaussian elimination with partial pivoting
        let mut a: Vec<Vec<f64>> = h.into_iter().zip(&g).map(|(mut r, gi)| { r.push(*gi); r }).collect();
        for c in 0..d {
            let p = (c..d).max_by(|&i, &j| a[i][c].abs().total_cmp(&a[j][c].abs())).unwrap();
            a.swap(c, p);
            for r in c + 1..d {
                let f = a[r][c] / a[c][c];
                for k in c..=d {
                    a[r][k] -= f * a[c][k];
                }
            }
        }
        let mut step = vec![0.0; d];
        for i in (0..d).rev() {
            step[i] = (a[i][d] - (i + 1..d).map(|j| a[i][j] * step[j]).sum::<f64>()) / a[i][i];
        }
        let moved: f64 = step.iter().map(|s| s.abs()).sum();
        for i in 0..d {
            w[i] -= step[i];
        }
        if moved < 1e-8 {
            break;
        }
    }
    w
}
```

- [ ] **Step 4: Run to verify they pass**

Run: `cargo test --test church_bv estimator_tests 2>&1 | tail -15`
Expected: 2 passed.

- [ ] **Step 5: Commit**

```bash
git add tests/church_bv/belief.rs
git commit -m "belief: smoothed-count cells with fallback, logistic fit"
```

---

### Task 3: The claim dump

**Files:**
- Modify: `tests/church_bv/belief.rs`, `tests/church_bv/classes.rs` (`verdict` to `pub(crate)`), `tests/church_bv/rewrite.rs` (visibility only, as the compiler demands)

**Interfaces:**
- Consumes: `Classes::build(&Key, size, sample_n, seed) -> (Classes, BuildStats)` with `BuildStats.sample: Vec<(Term, Term)>` (member, representative); `ValueMemo::<u8>::new(8, len, vars)`, `.values(&Term)`, `.first_difference(&a, &b, tries)`, `ValueMemo::exhaustive(4, 3)`, `with_screen(8, 3, f)`, `SCREEN_INPUTS`; `classes::verdict(&Job, 4, &u, &r) -> Option<Verdict>`; `prove_rule(job, 4, k, &l, &r)`.
- Produces: an ignored test `belief_dump` writing `$RUN_DIR/claims.tsv` with the columns `key kind size vars w4 screen extra8 extra64 extra256 d label index u r` (tab-separated; `u` and `r` are `Term::show()` text; flags are 0/1; `label` is `proved`, `refuted` or `unproved`), and printing `BELIEF DUMP` summary lines.

- [ ] **Step 1: Write the failing test (the dump's row format)**

```rust
#[cfg(test)]
mod dump_tests {
    use super::*;

    #[test]
    fn a_row_round_trips_and_a_bad_kind_names_its_line() {
        let r = Row { key: 1, kind: 2, size: 7, vars: 3, w4: true, screen: true, extra: [true, true, false], d: 12, label: Label::Refuted, index: 5, u: "add(x, y)".into(), r: "add(y, x)".into() };
        assert_eq!(Row::parse(&r.line(), 9).unwrap(), r);
        let bad = "1\tnope\t7\t3\t1\t1\t1\t1\t0\t12\trefuted\t5\tu\tr";
        let e = Row::parse(bad, 42).unwrap_err();
        assert!(e.contains("line 42") && e.contains("nope"), "{e}");
    }

    #[test]
    fn s1_and_s2_are_disjoint_input_sets() {
        let s2 = input_set(S2_SEED, 4096, &[]);
        let s1 = input_set(S1_SEED, 256, &s2);
        let a: std::collections::HashSet<[u8; 3]> = s1.into_iter().collect();
        assert!(s2.iter().all(|t| !a.contains(t)), "S1 and S2 share a triple");
    }
}
```

- [ ] **Step 2: Run to verify they fail**

Run: `cargo test --test church_bv dump_tests 2>&1 | tail -10`
Expected: compile error, `cannot find type Row`.

- [ ] **Step 3: Implement the row, the input sets and the dump**

Add to `belief.rs` (imports the executor needs: `use crate::classes::{Classes, Key, SIZE};` `use crate::rewrite::{Term, Node, ...}` as the compiler asks):

```rust
pub const S1_SEED: u128 = 0x1b87_3593_0000_0001;
pub const S2_SEED: u128 = 0x6a09_e667_f3bc_c908;
pub const CLAIM_SEED: u128 = 0x51ed_270b_27a3_c1f5;
pub const KINDS: [&str; 4] = ["bitwise", "add/sub", "shl1", "lt"];
pub const KEYS: [&str; 4] = ["bool8", "plus4", "plus64", "exh"];

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Label {
    Proved,
    Refuted,
    Unproved,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Row {
    pub key: u8,
    pub kind: u8,
    pub size: usize,
    pub vars: usize,
    pub w4: bool,
    pub screen: bool,
    pub extra: [bool; 3], // passes the first 8, 64, 256 of S1
    pub d: usize,         // differing inputs of S2's 4096
    pub label: Label,
    pub index: usize,
    pub u: String,
    pub r: String,
}

impl Row {
    pub fn line(&self) -> String {
        let b = |x: bool| x as u8;
        let l = match self.label { Label::Proved => "proved", Label::Refuted => "refuted", Label::Unproved => "unproved" };
        format!("{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}", self.key, KINDS[self.kind as usize], self.size, self.vars, b(self.w4), b(self.screen), b(self.extra[0]), b(self.extra[1]), b(self.extra[2]), self.d, l, self.index, self.u, self.r)
    }

    pub fn parse(line: &str, no: usize) -> Result<Row, String> {
        let f: Vec<&str> = line.split('\t').collect();
        let err = |what: &str, v: &str| format!("claims.tsv line {no}: bad {what} {v:?}");
        if f.len() != 14 {
            return Err(format!("claims.tsv line {no}: {} fields, expected 14", f.len()));
        }
        let num = |i: usize, w: &str| f[i].parse::<usize>().map_err(|_| err(w, f[i]));
        let flag = |i: usize, w: &str| match f[i] { "1" => Ok(true), "0" => Ok(false), v => Err(err(w, v)) };
        Ok(Row {
            key: f[0].parse::<u8>().map_err(|_| err("key", f[0]))?,
            kind: KINDS.iter().position(|k| *k == f[1]).ok_or_else(|| err("kind", f[1]))? as u8,
            size: num(2, "size")?,
            vars: num(3, "vars")?,
            w4: flag(4, "w4")?,
            screen: flag(5, "screen")?,
            extra: [flag(6, "extra8")?, flag(7, "extra64")?, flag(8, "extra256")?],
            d: num(9, "d")?,
            label: match f[10] { "proved" => Label::Proved, "refuted" => Label::Refuted, "unproved" => Label::Unproved, v => return Err(err("label", v)) },
            index: num(11, "index")?,
            u: f[12].to_string(),
            r: f[13].to_string(),
        })
    }
}

/// `count` pseudo-random width-8 triples from `seed` (the old probe's generator), none of them in `avoid` and no repeats
/// (256 by 4096 draws from 2^24 triples collide about 6% of the time, so S1 is drawn by rejection against S2).
pub fn input_set(seed: u128, count: usize, avoid: &[[u8; 3]]) -> Vec<[u8; 3]> {
    let (mut s, mut out) = (seed, vec![]);
    let seen: std::collections::HashSet<[u8; 3]> = avoid.iter().copied().collect();
    while out.len() < count {
        let t = [(); 3].map(|_| { s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); (s >> 40) as u8 });
        if !seen.contains(&t) && !out.contains(&t) {
            out.push(t);
        }
    }
    out
}
```

Then the dump itself (an `#[ignore]` test `belief_dump`). Keys are built as in the old probe: `bool8` is `Key::start()`, `plusN` is `Key::start()` plus N random width-8 tuples (generator seed `0x2545_f491_4f6c_dd1d`, tuple = `(seed >> 40) & 0xff` per variable), `exh` is every input at widths 3 and 4. Per key: `Classes::build(&key, SIZE, 20000, CLAIM_SEED)`, then for the first `cap` claims of `stats.sample` (cap from `BELIEF_CAP`, default 10000):

```rust
#[test]
#[ignore]
fn belief_dump() {
    use std::io::Write;
    let out = std::env::var("RUN_DIR").expect("RUN_DIR: the run wrapper's folder");
    let cap: usize = std::env::var("BELIEF_CAP").map_or(10000, |v| v.parse().unwrap());
    let keys = std::env::var("BELIEF_KEYS").unwrap_or("bool8 plus4 plus64 exh".into());
    let mut file = std::io::BufWriter::new(std::fs::File::create(format!("{out}/claims.tsv")).unwrap());
    let s2 = input_set(S2_SEED, 4096, &[]);
    let s1 = input_set(S1_SEED, 256, &s2);
    let cols = |s: &[[u8; 3]]| -> std::sync::Arc<[Box<[u8]>]> { (0..3).map(|v| s.iter().map(|t| t[v]).collect::<Box<[u8]>>()).collect() };
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        for name in keys.split_whitespace() {
            let ki = KEYS.iter().position(|k| *k == name).unwrap_or_else(|| panic!("unknown key {name}"));
            let key = make_key(name);
            let (_c, st) = Classes::build(&key, SIZE, 20000, CLAIM_SEED);
            println!("BELIEF DUMP key {name}: {} merges proposed, {} sampled, cap {cap}", st.merges, st.sample.len());
            let (mut r1, mut r2) = (ValueMemo::<u8>::new(8, 256, cols(&s1)), ValueMemo::<u8>::new(8, 4096, cols(&s2)));
            let mut e4 = ValueMemo::exhaustive(4, 3);
            let (mut agree, mut checked) = (0, 0);
            for (index, (u, r)) in st.sample.iter().take(cap).enumerate() {
                let a = r2.values(u).to_vec();
                let d = a.iter().zip(r2.values(r)).filter(|(p, q)| p != q).count();
                let w4 = e4.first_difference(u, r, 1 << 12).is_none();
                let screen = with_screen(8, 3, |m| m.first_difference(u, r, SCREEN_INPUTS)).is_none();
                let extra = [8, 64, 256].map(|n| r1.first_difference(u, r, n).is_none());
                let refuted = d > 0 || !w4 || !screen || !extra[2];
                let label = if refuted {
                    Label::Refuted
                } else if verdict(job, 4, u, r).is_some() {
                    if index % 20 == 0 {
                        checked += 1;
                        agree += prove_rule(job, 4, 1 + u.max_var().max(r.max_var()), u, r).is_some() as usize;
                    }
                    Label::Proved
                } else {
                    Label::Unproved
                };
                let row = Row { key: ki as u8, kind: kind_of(u, r), size: u.size() + r.size(), vars: 1 + u.max_var().max(r.max_var()), w4, screen, extra, d, label, index, u: u.show(), r: r.show() };
                writeln!(file, "{}", row.line()).unwrap();
            }
            println!("BELIEF DUMP key {name}: kernel-path check on every 20th proved claim: {agree} of {checked} agree");
        }
    });
}
```

with `make_key(name) -> Key` copied from the old probe's key construction, and `kind_of(u, r) -> u8` implementing the old probe's `group` closure (patch `claim_calibration.patch`, the `let group = |u, r|` closure inside `class_table_probe`) with an `ops_in(t, &mut mask)` walk that sets bit `1 << op` for every operator of both sides: `u` rooted at `LT` → 3; else any `SHL1` → 2; else any `ADD` or `SUB` → 1; else 0, and `Term::size()` as the operator-plus-leaf count (`rewrite.rs`: `size`); `size` here is `u.size() + r.size()` as in the table's own ranking. Make `verdict`, `with_screen`, `ValueMemo::values` and `SCREEN_INPUTS` `pub(crate)` only as far as the compiler requires.

- [ ] **Step 4: Run the format tests, then pilot the dump**

Run: `cargo test --test church_bv dump_tests 2>&1 | tail -10`
Expected: 2 passed.

Pilot for the cap (Global Constraints: fixed by claim count from a pilot). First the `LONG_RUNS.md` pre-checks: orphans (`Get-Process`), free disk over 5 GB, free memory, CPU load. Build the test exe with `cargo test --test church_bv --no-run`, copy it out of `target` into `%LOCALAPPDATA%\claude-runs\tatic\belief-exes\`, then launch through the wrapper from PowerShell. The variables are set in the launcher (the child inherits them) and the wrapper's `RUN_DIR` is the output folder, so no path goes through `cmd`:

```powershell
$env:BELIEF_CAP = '1000'; $env:BELIEF_KEYS = 'plus64'
$exe = "$env:LOCALAPPDATA\claude-runs\tatic\belief-exes\church_bv.exe"
powershell -NoProfile -File "$env:USERPROFILE\.claude\runs\run.ps1" -Kind probe -Name belief-pilot -Affinity CFF -Detach -Command "& '$exe' belief::belief_dump --exact --ignored --nocapture"
```

Arm a watcher (a `run_in_background` `until` loop on the run's `run.json` `"end"` no longer `null`, with a deadline); do not poll. Repeat for `bool8` and `exh`. Read the time per **tried** claim (proved plus unproved, since failed searches dominate) from each log, set the cap so each key's proving fits about 10 minutes, and write the chosen cap and the pilot run ids in the spec's Data section.
Expected: `BELIEF DUMP` lines for all four keys; a `kernel-path check` line per key whose disagreements (if any) are reported, not hidden.

- [ ] **Step 5: Commit**

```bash
git add tests/church_bv/belief.rs tests/church_bv/classes.rs tests/church_bv/rewrite.rs docs/superpowers/specs/2026-10-31-belief-layer-design.md
git commit -m "belief: claim dump (Classes::build sample, S1/S2 evidence and label sets); cap from a pilot"
```

---

### Task 4: The report and the stage-1 gate

**Files:**
- Modify: `tests/church_bv/belief.rs`

**Interfaces:**
- Consumes: Tasks 1 to 3.
- Produces: `read_rows(path) -> Vec<Row>`; `gate(rows: &[Row], folds: &[usize]) -> Result<(), String>` (the screen-pass subset: `w4 && screen`; negatives are `Refuted` rows; fails under 100 in all or 10 in any fold, naming per key and kind counts); an ignored test `belief_report` printing `BELIEF` lines from `$BELIEF_TSV`.

- [ ] **Step 1: Write the failing tests**

```rust
#[cfg(test)]
mod report_tests {
    use super::*;

    fn row(label: Label, w4: bool, screen: bool, fold_marker: usize) -> Row {
        Row { key: 0, kind: 3, size: 5, vars: 2, w4, screen, extra: [true; 3], d: 1, label, index: fold_marker, u: format!("u{fold_marker}"), r: format!("r{fold_marker}") }
    }

    #[test]
    fn the_gate_counts_only_screen_pass_refutations_and_names_the_shortfall() {
        let mut rows: Vec<Row> = (0..30).map(|i| row(Label::Refuted, true, true, i)).collect();
        rows.extend((30..60).map(|i| row(Label::Refuted, false, true, i))); // caught by w4: not in the subset
        let folds: Vec<usize> = (0..rows.len()).map(|i| i % 5).collect(); // balanced, so the shortfall is what fails
        let e = gate(&rows, &folds).unwrap_err();
        assert!(e.contains("30 negatives") && e.contains("100"), "{e}");
    }

    #[test]
    fn belief_is_one_for_a_claim_that_failed_the_evidence_at_that_level() {
        let c = Counts::fit(&[Cell { kind: 3, key: 0, w4: true, screen: true, n: 0 }], &[false]);
        let mut r = row(Label::Refuted, true, true, 1);
        r.extra = [true, false, false];
        // level 1 (n = 8): extra8 passed, so the cell answers; no (kind,key,n=1) cell exists, so (kind,key) answers: (0+1)/(1+2)
        assert_eq!(belief_counts(&c, &r, 1), 1.0 / 3.0);
        assert_eq!(belief_counts(&c, &r, 2), 1.0); // level 2 (n = 64): extra64 failed, decided
    }
}
```

- [ ] **Step 2: Run to verify they fail**

Run: `cargo test --test church_bv report_tests 2>&1 | tail -10`
Expected: compile error, `cannot find function gate`.

- [ ] **Step 3: Implement**

```rust
pub fn read_rows(path: &str) -> Vec<Row> {
    std::fs::read_to_string(path).unwrap().lines().enumerate().map(|(i, l)| Row::parse(l, i + 1).unwrap_or_else(|e| panic!("{e}"))).collect()
}

/// The screen-pass subset at level `lvl`: passes `w4`, `screen` and the first `lvl` S1 prefixes.
fn in_subset(r: &Row, lvl: usize) -> bool {
    r.w4 && r.screen && (1..=lvl).all(|l| r.extra[l - 1])
}

/// The counts arm's training cells at level `lvl`: only rows in the level's subset are fitted (a row that failed a check
/// is decided, not estimated), with `Cell.n = lvl`, so the n = 8 cell is not the n = 0 cell.
pub fn cells_at(rows: &[Row], lvl: usize, with_key: bool) -> Vec<Option<Cell>> {
    rows.iter().map(|r| in_subset(r, lvl).then_some(Cell { kind: r.kind, key: if with_key { r.key } else { 0 }, w4: r.w4, screen: r.screen, n: lvl as u8 })).collect()
}

pub fn gate(rows: &[Row], folds: &[usize]) -> Result<(), String> {
    let (mut all, mut per_fold, mut per_kk) = (0, [0usize; 5], HashMap::<(u8, u8), usize>::new());
    for (r, f) in rows.iter().zip(folds) {
        if in_subset(r, 0) && r.label == Label::Refuted {
            all += 1;
            per_fold[*f] += 1;
            *per_kk.entry((r.key, r.kind)).or_default() += 1;
        }
    }
    let mut kk: Vec<_> = per_kk.into_iter().collect();
    kk.sort();
    let detail = format!("{all} negatives in the screen-pass subset; per fold {per_fold:?}; per (key, kind) {kk:?}");
    let sizes: Vec<usize> = (0..5).map(|f| folds.iter().filter(|x| **x == f).count()).collect();
    println!("BELIEF folds: rows per fold {sizes:?}");
    if sizes.iter().any(|n| *n * 100 > rows.len() * 40) {
        return Err(format!("stage-1 gate failed: fold sizes {sizes:?} are unbalanced (a fold holds over 40% of {} rows; a giant component of shared sides?)", rows.len()));
    }
    if all < 100 || per_fold.iter().any(|n| *n < 10) {
        return Err(format!("stage-1 gate failed (needs 100 in all and 10 per fold): {detail}"));
    }
    println!("BELIEF gate passed: {detail}");
    Ok(())
}

/// The counts arm's belief that `r` is negative (refuted) when scored at level `lvl` (0..=3 for n = 0, 8, 64, 256):
/// 1.0 when a check it has passed at that level is failed (decided), else the smoothed cell estimate.
pub fn belief_counts(c: &Counts, r: &Row, lvl: usize) -> f64 {
    if !r.w4 || !r.screen || (1..=lvl).any(|l| !r.extra[l - 1]) {
        return 1.0;
    }
    if r.kind == 0 && r.key == 0 {
        return 0.0; // a pure bitwise term on the 8 Boolean tuples is decided by its truth table (spec): never wrong
    }
    c.p(Cell { kind: r.kind, key: r.key, w4: r.w4, screen: r.screen, n: lvl as u8 }).0
}
```

Then the ignored `belief_report` test, which does, in order, printing a `BELIEF` line per result:
1. read rows from `$BELIEF_TSV`; `folds = fold_of(&rows.map(|r| (r.u.clone(), r.r.clone())))`; `gate(...)` and stop with a `panic!` carrying its message when it fails (the finding is then "too few hard negatives", recorded by hand);
2. per score and arm, a grouped 5-fold loop (for each held-out fold, fit `Counts` on the other folds with `hit = (label == Refuted)` for A_ref, or `hit = (label == Unproved)` among unrefuted rows for A_unp, and score the held-out rows with `belief_counts`), pooled out-of-fold scores;
3. the arms, each fitted per level on `cells_at(rows, lvl, ...)` (training rows in the level's subset only) and scored with `belief_counts`: **full** (cells as above), **no-key** (counts, kind-only; reported beside the logistic no-key co-primary of Task 5), **size-only** (a count-based cell `(0, 0, false, false, min(size, 15))`, fitted on the level's subset rows), and **screen** (constant 0.5 inside the subset; on all rows `1.0` when `!(w4 && screen)`, else 0.0);
4. the primary: on subset rows at level 0, `paired_bootstrap(full, better_of(0.5, size-only), neg, 2000, 1)` where `better_of` is whichever has the larger point AUC, plus the same for **no-key** (co-primary); print the interval, the resamples used and the negative count;
5. the per-feature ablation (counts arm: remove kind, then key; logistic arm: remove kind, key, size, vars in turn, in Task 5), n = 8, 64, 256 on the level's subset and on all rows with the same-n pass/fail of the first n S1 inputs as comparator, the d strata (d = 0 and d ≤ 1% of 4096, i.e. d ≤ 40) and `lt` on its own, A_unp descriptive as "x of n unproved" with a Wilson 95% interval, the all-claims table, per-kind reliability (`reliability(..., 10)`), and the internal consistency check (the unsmoothed old formula `P = proved / (proved + sum (1 − d/4096)^n over refuted)` per (kind, key, n) against the counts cells' empirical proved fraction among claims that passed n tests, within 0.01 for every cell of at least 200 claims), with the per-kind refuted and unproved counts printed beside the 2026-10-22 table;
6. the logistic arm (Task 5).

Concrete code for the loop in step 2 (the executor extends it per arm):

```rust
fn oof<F: Fn(&[usize], &[usize]) -> Vec<f64>>(folds: &[usize], score_fold: F) -> Vec<f64> {
    let mut out = vec![0.5; folds.len()];
    for f in 0..5 {
        let (test, train): (Vec<usize>, Vec<usize>) = ((0..folds.len()).filter(|&i| folds[i] == f).collect(), (0..folds.len()).filter(|&i| folds[i] != f).collect());
        for (i, s) in test.iter().zip(score_fold(&train, &test)) {
            out[*i] = s;
        }
    }
    out
}
```

- [ ] **Step 4: Run the unit tests, then the report on the pilot dump**

Run: `cargo test --test church_bv report_tests 2>&1 | tail -10`
Expected: 2 passed.

Run (on the pilot's `claims.tsv`): `$env:BELIEF_TSV = '<pilot run folder>\claims.tsv'; cargo test --test church_bv belief_report -- --ignored --nocapture 2>&1 | Select-String BELIEF` (PowerShell; path quoted)
Expected: either `BELIEF gate passed:` followed by the result lines, or the gate's panic message, which is a valid result to record.

- [ ] **Step 5: Commit**

```bash
git add tests/church_bv/belief.rs
git commit -m "belief: report, stage-1 gate, counts arm with ablations"
```

---

### Task 5: Logistic arm and the comparison

**Files:**
- Modify: `tests/church_bv/belief.rs`

**Ruling (plan review):** the spec's no-key co-primary is "kind, size, vars", which only the logistic arm has (the counts arm's no-key variant is kind-only). The co-primary is therefore carried by the **logistic no-key arm** (paired against the better of {0.5, size-only}), and the counts no-key arm is reported beside it. The logistic arm is kept for this regardless of how it compares with counts; "kept as the answer" in the spec means only which estimator is the headline.

**Interfaces:**
- Consumes: Task 2's `logistic_fit`, `logistic_p`; Task 4's `oof`.
- Produces: the logistic arm inside `belief_report`: features = kind one-hot (4), key one-hot (4, zeroed for the no-key arm), `size` (÷10), `vars`, `w4`, `screen`, the first `level` `extra` bits (3 slots, later ones zeroed), constant 1.0; its out-of-fold scores; the paired interval `logistic − counts` at level 0 on the subset (kept only if the interval lies above 0).

- [ ] **Step 1: Write the failing test**

```rust
#[test]
fn the_logistic_features_zero_the_key_for_the_no_key_arm() {
    let r = Row { key: 2, kind: 1, size: 7, vars: 3, w4: true, screen: true, extra: [true, false, true], d: 0, label: Label::Proved, index: 0, u: "u".into(), r: "r".into() };
    let with = logistic_features(&r, true, 3);
    let without = logistic_features(&r, false, 3);
    // at level 1 only the first extra bit is evidence: the others are zeroed, so S1 failures past it never leak in
    let l1 = logistic_features(&r, true, 1);
    assert_eq!(&l1[l1.len() - 4..l1.len() - 1], &[1.0, 0.0, 0.0]);
    assert!(logistic_features(&r, true, 0)[l1.len() - 4..l1.len() - 1].iter().all(|x| *x == 0.0));
    assert_eq!(with.len(), without.len());
    assert_eq!(with[4 + 2], 1.0); // key one-hot at 2
    assert!(without[4..8].iter().all(|x| *x == 0.0));
    assert_eq!(*with.last().unwrap(), 1.0);
}
```

(place it in `report_tests`).

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test --test church_bv the_logistic_features 2>&1 | tail -8`
Expected: compile error, `cannot find function logistic_features`.

- [ ] **Step 3: Implement**

```rust
/// Features at level `level` (0..=3 passed S1 prefixes count as evidence; later `extra` bits are zeroed).
pub fn logistic_features(r: &Row, with_key: bool, level: usize) -> Vec<f64> {
    let mut x = vec![0.0; 4 + 4];
    x[r.kind as usize] = 1.0;
    if with_key {
        x[4 + r.key as usize] = 1.0;
    }
    x.extend([r.size as f64 / 10.0, r.vars as f64, r.w4 as u8 as f64, r.screen as u8 as f64]);
    x.extend(r.extra.iter().enumerate().map(|(i, b)| (i < level && *b) as u8 as f64));
    x.push(1.0);
    x
}
```

Wire the arm into `belief_report` through `oof`: train `logistic_fit(&x_train, &y_train, 1.0)` with `y = (label == Refuted)` on the training folds, score the held-out rows with `logistic_p`. Print its AUC, the paired interval against the counts arm, and the same for the no-key variant.

- [ ] **Step 4: Run**

Run: `cargo test --test church_bv the_logistic_features 2>&1 | tail -8`
Expected: 1 passed. Then rerun `belief_report` on the pilot dump; expected: the logistic lines appear.

- [ ] **Step 5: Commit**

```bash
git add tests/church_bv/belief.rs
git commit -m "belief: logistic arm and its paired comparison with the counts arm"
```

---

### Task 6: The full run, the record and the tour

**Files:**
- Modify: `docs/tier-cycle.md`, `docs/TOUR.md`, `ROADMAP.md`, `docs/superpowers/specs/2026-10-31-belief-layer-design.md` (status), this plan (status)

**Interfaces:**
- Consumes: everything above.

- [ ] **Step 1: Pre-run checks**

Run the checks of `LONG_RUNS.md` before the full dump: orphan processes (`Get-Process`), free disk (`(Get-PSDrive C).Free/1GB` over 5), memory, CPU under 30%, Defender state (report it). The dump is untimed (no `-Timed`); pin it with `-Affinity CFF` at BelowNormal.

- [ ] **Step 2: Full dump**

```bash
powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind sweep -Name belief-dump -Affinity CFF -Detach -Command "<exe> belief::belief_dump --exact --ignored --nocapture"
```

with `$env:BELIEF_CAP` from the pilot and `BELIEF_KEYS` unset (all four keys), launched as in Task 3's pilot (pre-checks, `-Affinity CFF -Detach`, a watcher, no polling).
Expected: `claims.tsv` with four keys' rows and a `BELIEF DUMP` summary per key.

- [ ] **Step 3: Full report**

Run `belief_report` on that `claims.tsv`, redirecting output to the run folder, and read the `BELIEF` lines.
Expected: the gate line, the primary and co-primary intervals, the ablations, the n = 8, 64, 256 rows, A_unp, reliability and the logistic comparison. A failed gate is recorded as the finding.

- [ ] **Step 4: Record**

Add a section to `docs/tier-cycle.md` (after "How much random testing is worth"): the run ids (dump, report), the gate counts, the primary and co-primary intervals, the ablation, what the key contributes, the decision (belief beats the screen or not), and the patch-free note that the code is `tests/church_bv/belief.rs`. Add a `docs/TOUR.md` entry for `belief` (concepts and flow only, no measurements) and run `bash scripts/tour_check.sh`. In `ROADMAP.md` record the milestone's outcome and, if belief wins, say the open item is g2 (a proposer); if it ties or loses, say what that implies for goal 3 and update the "calibrated belief layer" paragraph. Set the spec and this plan to `status: done`.

- [ ] **Step 5: Docs check and commit**

grep `ROADMAP.md`, `PARKED.md`, `docs/tier-cycle.md`, `docs/decisions/2026-10-31-learned-target-model.md` for "belief layer", "nothing built" and "calibrat": fix any stale line. Then:

```bash
git add -A docs ROADMAP.md
git commit -m "docs: belief-layer calibration finding; tour entry; milestone closed"
```
