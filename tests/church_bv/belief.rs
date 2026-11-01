//! The belief layer's calibration milestone (docs/superpowers/specs/2026-10-31-belief-layer-design.md): statistics,
//! estimators, the claim dump and the report. Nothing outside this file reads a belief.

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
