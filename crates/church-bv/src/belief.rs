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
    if n == 0 {
        return None;
    }
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

pub const S1_SEED: u128 = 0x1b87_3593_0000_0001;
pub const S2_SEED: u128 = 0x6a09_e667_f3bc_c908;
pub const CLAIM_SEED: u128 = 0x51ed_270b_27a3_c1f5;
pub const KINDS: [&str; 4] = ["bitwise", "add/sub", "shift", "lt"];
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
            key: f[0].parse::<u8>().ok().filter(|k| (*k as usize) < KEYS.len()).ok_or_else(|| err("key", f[0]))?,
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

use super::*;
use crate::classes::{Classes, Key, SIZE};
use crate::rewrite::{with_screen, Node, ValueMemo, ADD, LT, SCREEN_INPUTS, SHL1, SHR1, SUB};

/// The key named `name` (`bool8`, `plus4`, `plus64`, `exh`), built as the 2026-10-22 probe built its keys.
fn make_key(name: &str) -> Key {
    if name == "exh" {
        return Key { sets: [3usize, 4].iter().map(|&w| (w, (0..1usize << (3 * w)).map(|i| [0, 1, 2].map(|v| (i >> (w * v) & ((1 << w) - 1)) as u128)).collect())).collect() };
    }
    let mut key = Key::start();
    let count: usize = name.strip_prefix("plus").map_or(0, |n| n.parse().unwrap_or_else(|_| panic!("unknown key {name}")));
    if count == 0 && name != "bool8" {
        panic!("unknown key {name}");
    }
    let mut seed = 0x2545_f491_4f6c_dd1du128;
    for _ in 0..count {
        key.push(8, [0, 1, 2].map(|_| {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            (seed >> 40) & 0xff
        }));
    }
    key
}

fn ops_in(t: Term, acc: &mut u32) {
    if let Node::Op(o, a, b) = *t.node() {
        *acc |= 1 << o;
        ops_in(a, acc);
        ops_in(b, acc);
    }
}

/// The claim's kind (an index into `KINDS`): `lt` at the root, else any `shl1` or `shr1`, else any `add`/`sub`, else bitwise.
fn kind_of(u: &Term, r: &Term) -> u8 {
    let mut m = 0u32;
    ops_in(*u, &mut m);
    ops_in(*r, &mut m);
    if matches!(*u.node(), Node::Op(LT, ..)) {
        3
    } else if m & (1 << SHL1 | 1 << SHR1) != 0 {
        2
    } else if m & (1 << ADD | 1 << SUB) != 0 {
        1
    } else {
        0
    }
}

#[test]
#[ignore]
fn belief_dump() {
    use std::io::Write;
    use crate::classes::verdict;
    let setup = Setup::process();
    let out = setup.var("RUN_DIR").expect("RUN_DIR: the run wrapper's folder");
    let cap: usize = setup.or("BELIEF_CAP", 10000);
    let keys = setup.var("BELIEF_KEYS").unwrap_or("bool8 plus4 plus64 exh").to_string();
    let mut file = std::io::BufWriter::new(std::fs::File::create(format!("{out}/claims.tsv")).unwrap());
    let s2 = input_set(S2_SEED, 4096, &[]);
    let s1 = input_set(S1_SEED, 256, &s2);
    let cols = |s: &[[u8; 3]]| -> std::sync::Arc<[Box<[u8]>]> { (0..3).map(|v| s.iter().map(|t| t[v]).collect::<Box<[u8]>>()).collect() };
    let job = &mut Job::new(Setup::process());
    tatic_kernel::scoped(|| {
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
/// 1.0 when a check it has passed at that level is failed (decided), else the smoothed cell estimate. The second value
/// is the fallback level the estimate came from (`Counts::p`; 0 is the exact cell, and a decided claim reports 0).
pub fn belief_counts(c: &Counts, r: &Row, lvl: usize, with_key: bool) -> (f64, u8) {
    if !r.w4 || !r.screen || (1..=lvl).any(|l| !r.extra[l - 1]) {
        return (1.0, 0);
    }
    if with_key && r.kind == 0 && r.key == 0 {
        return (0.0, 0); // a pure bitwise term on the 8 Boolean tuples is decided by its truth table (spec): never wrong
    }
    c.p(Cell { kind: r.kind, key: if with_key { r.key } else { 0 }, w4: r.w4, screen: r.screen, n: lvl as u8 })
}

/// The stage-1 report on a claim dump (`$BELIEF_TSV`): per key and kind, how many claims each label holds, how many pass
/// `w4` and the screen, and how many of those are refuted anyway (the hard negatives A_ref ranks); then the gate. A failed
/// gate is the milestone's recorded finding ("too few hard negatives to compare"), so stage 2 never starts.
#[test]
#[ignore]
fn belief_report() {
    let rows = read_rows(Setup::process().var("BELIEF_TSV").expect("BELIEF_TSV: the claim dump"));
    println!("BELIEF stage 1: key kind claims proved refuted unproved | screen-pass refuted unproved | screen-pass refuted by S2/S1/d");
    for key in 0..KEYS.len() as u8 {
        for kind in 0..KINDS.len() as u8 {
            let g: Vec<&Row> = rows.iter().filter(|r| r.key == key && r.kind == kind).collect();
            let n = |f: &dyn Fn(&&Row) -> bool| g.iter().filter(|r| f(r)).count();
            let sub = n(&|r| in_subset(r, 0));
            println!(
                "BELIEF {:7} {:8} {:6} {:6} {:6} {:6} | {:6} {:4} {:6} | {}",
                KEYS[key as usize],
                KINDS[kind as usize],
                g.len(),
                n(&|r| r.label == Label::Proved),
                n(&|r| r.label == Label::Refuted),
                n(&|r| r.label == Label::Unproved),
                sub,
                n(&|r| in_subset(r, 0) && r.label == Label::Refuted),
                n(&|r| in_subset(r, 0) && r.label == Label::Unproved),
                n(&|r| in_subset(r, 0) && (r.d > 0 || r.extra.iter().any(|b| !b))),
            );
        }
    }
    let folds = fold_of(&rows.iter().map(|r| (r.u.clone(), r.r.clone())).collect::<Vec<_>>());
    if let Err(e) = gate(&rows, &folds) {
        panic!("{e}");
    }
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
        assert_eq!(belief_counts(&c, &r, 1, true).0, 1.0 / 3.0);
        assert_eq!(belief_counts(&c, &r, 2, true).0, 1.0); // level 2 (n = 64): extra64 failed, decided
    }
}

#[cfg(test)]
mod review_fix_tests {
    use super::*;
    use crate::rewrite::parse_term;

    #[test]
    fn a_claim_with_shr1_is_a_shift_claim_not_bitwise() {
        let (u, r) = (parse_term("shr1(xor(x, y), 0)"), parse_term("0"));
        assert_eq!(kind_of(&u, &r), 2);
        assert_eq!(kind_of(&parse_term("xor(x, y)"), &parse_term("xor(y, x)")), 0);
    }

    #[test]
    fn the_no_key_arm_queries_the_cells_it_was_fitted_on() {
        let row = |key: u8, label: Label| Row { key, kind: 1, size: 5, vars: 2, w4: true, screen: true, extra: [true; 3], d: 0, label, index: 0, u: "u".into(), r: "r".into() };
        let rows = vec![row(2, Label::Refuted), row(2, Label::Refuted), row(2, Label::Proved), row(3, Label::Proved)];
        let cells: Vec<Cell> = cells_at(&rows, 0, false).into_iter().flatten().collect();
        let hit: Vec<bool> = rows.iter().map(|r| r.label == Label::Refuted).collect();
        let c = Counts::fit(&cells, &hit);
        // key is dropped on both sides: (kind 1, key 0) holds 2 hits of 4 -> 3/6, answered by the exact cell
        assert_eq!(belief_counts(&c, &rows[0], 0, false).0, 3.0 / 6.0);
        assert_eq!(c.p(Cell { kind: 1, key: 0, w4: true, screen: true, n: 0 }).1, 0);
    }

    #[test]
    fn a_row_with_an_unknown_key_is_rejected() {
        let row = Row { key: 0, kind: 1, size: 5, vars: 2, w4: true, screen: true, extra: [true; 3], d: 0, label: Label::Proved, index: 0, u: "u".into(), r: "r".into() };
        assert!(Row::parse(&row.line(), 1).is_ok());
        let bad = Row { key: KEYS.len() as u8, ..row };
        assert!(Row::parse(&bad.line(), 1).is_err());
    }

    #[test]
    fn an_empty_bootstrap_has_no_interval() {
        assert_eq!(paired_bootstrap(&[], &[], &[], 10, 1), None);
    }

    #[test]
    fn belief_counts_reports_the_fallback_level_it_answered_from() {
        let cells = [Cell { kind: 1, key: 0, w4: true, screen: true, n: 0 }; 2];
        let c = Counts::fit(&cells, &[true, false]);
        let row = |key: u8| Row { key, kind: 1, size: 5, vars: 2, w4: true, screen: true, extra: [true; 3], d: 0, label: Label::Proved, index: 0, u: "u".into(), r: "r".into() };
        assert_eq!(belief_counts(&c, &row(0), 0, true).1, 0);
        assert!(belief_counts(&c, &row(3), 0, true).1 > 0, "an unseen key falls back");
        let mut failed = row(0);
        failed.w4 = false;
        assert_eq!(belief_counts(&c, &failed, 0, true), (1.0, 0), "a decided claim is not estimated");
    }

    #[test]
    fn the_sample_holds_no_self_claim() {
        let (_c, st) = Classes::build(&make_key("exh"), SIZE, 20000, CLAIM_SEED);
        let selfs = st.sample.iter().filter(|(u, r)| u == r).count();
        assert_eq!(selfs, 0, "{selfs} of {} sampled claims are a term against itself", st.sample.len());
    }
}

/// Spike (d1, 2026-11-01): what the screen-pass claims `verdict` leaves unproved are, from a dump (`$BELIEF_TSV`, every
/// `$BELIEF_STEP`-th unproved claim). Per claim: whether it has `shr1`, whether it holds on every width-6 input, and
/// whether `prove_rule` (the every-input route, width 4) proves it and in how long.
#[test]
#[ignore]
fn belief_shr1_spike() {
    use crate::rewrite::{parse_term, prove_rule};
    let rows = read_rows(Setup::process().var("BELIEF_TSV").expect("BELIEF_TSV: the claim dump"));
    let setup = Setup::process();
    let step: usize = setup.or("BELIEF_STEP", 1);
    let pick: Vec<&Row> = rows.iter().filter(|r| r.label == Label::Unproved && in_subset(r, 0)).step_by(step).skip(setup.or("BELIEF_SKIP", 0)).collect();
    let mut job = Job::new(Setup::process());
    let mut w6 = ValueMemo::exhaustive(6, 3);
    // (claims, with shr1, true at width 6, proved by prove_rule, proved with shr1, seconds in prove_rule)
    let (mut n, mut with_shr1, mut true6, mut proved, mut proved_shr1, mut secs) = (0, 0, 0, 0, 0, 0.0);
    tatic_kernel::scoped(|| {
        for r in pick {
            let (u, v) = (parse_term(&r.u), parse_term(&r.r));
            let has = r.u.contains("shr1") || r.r.contains("shr1");
            if n % 50 == 0 {
                // both grow with every claim (the memo 3 GB by claim ~100, the job's lemmas until the paging file ran out)
                w6 = ValueMemo::exhaustive(6, 3);
                job = Job::new(Setup::process());
                println!("SHR1 progress: {n} claims, {secs:.0} s in prove_rule");
            }
            println!("SHR1 at {n}: {} -> {}", r.u, r.r); // a crash names its claim
            let agree = w6.agree(&u, &v);
            let t0 = std::time::Instant::now();
            let ok = prove_rule(&mut job, 4, 1 + u.max_var().max(v.max_var()), &u, &v).is_some();
            secs += t0.elapsed().as_secs_f64();
            n += 1;
            with_shr1 += has as usize;
            true6 += agree as usize;
            proved += ok as usize;
            proved_shr1 += (ok && has) as usize;
            if !ok || !agree {
                println!("SHR1 odd: key {} kind {} shr1 {has} true6 {agree} proved {ok}: {} -> {}", KEYS[r.key as usize], KINDS[r.kind as usize], r.u, r.r);
            }
        }
    });
    println!("SHR1 unproved screen-pass claims {n}: with shr1 {with_shr1}, true at width 6 {true6}, proved by prove_rule {proved} (with shr1 {proved_shr1}), {secs:.1} s in prove_rule");
}
