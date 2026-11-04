//! The context-aware scorer study (docs/superpowers/specs/2026-11-01-context-aware-scorer-design.md): the stage-1 model,
//! recovered from `8d9ceaf^:tests/church_bv/scorer.rs` with a runtime width, the pool-context features, and the offline
//! (Q1) report. Nothing here reaches the kernel; a scorer only orders laws.
use super::rewrite::Node;
use super::*;
use crate::classes::OPS;

/// Operators counted per side, in `OPS` order.
const OPN: usize = OPS.len();
/// Per-law features: 0 bias; 1 size sum; 2 size gap; 3 larger size; 4 depth; 5 variables used; 6 variables on one side only;
/// 7 most occurrences of a variable; 8 constants; 9 equal variable counts on both sides; then per operator of `OPS` the count
/// over both sides (10..) and the gap between the sides (10 + OPN..).
pub const PER_LAW: usize = 10 + 2 * OPN;
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

/// A law's per-law feature vector. Symmetric: a law and its mirror image give the same vector.
pub fn per_law_features((l, r): &(Term, Term)) -> [f32; PER_LAW] {
    let (mut va, mut vb) = ([0usize; 8], [0usize; 8]);
    l.occurrences(&mut va);
    r.occurrences(&mut vb);
    let (mut ca, mut cb) = ([0usize; OPN], [0usize; OPN]);
    op_counts(l, &mut ca);
    op_counts(r, &mut cb);
    let (sl, sr) = (l.size(), r.size());
    let mut f = [0f32; PER_LAW];
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

/// A logistic regression on standardized features of a runtime width. Column 0 (the bias) is kept unstandardized; a column
/// with no spread on the training rows is left out (`keep` lists the columns the model reads).
#[derive(Clone, Debug, PartialEq)]
pub struct Model {
    width: usize,
    keep: Vec<usize>,
    mean: Vec<f64>,
    scale: Vec<f64>,
    w: Vec<f64>,
}

impl Model {
    /// The log-odds that the law pays for a rule; larger is better.
    pub fn score(&self, x: &[f32]) -> f64 {
        assert_eq!(x.len(), self.width, "a feature vector of the wrong width");
        self.keep.iter().enumerate().map(|(j, &i)| self.w[j] * (x[i] as f64 - self.mean[j]) / self.scale[j]).sum()
    }

    /// The columns of the training rows the model dropped for having no spread.
    pub fn dropped(&self) -> Vec<usize> {
        (0..self.width).filter(|i| !self.keep.contains(i)).collect()
    }

    /// Six lines: `layout`, `width`, `keep`, `mean`, `scale`, `w` (`{:?}` prints the shortest text that reads back equal).
    pub fn to_text(&self, layout: &str) -> String {
        let nums = |name: &str, v: &[f64]| format!("{name} {}\n", v.iter().map(|x| format!("{x:?}")).collect::<Vec<_>>().join(" "));
        let keep: Vec<String> = self.keep.iter().map(|i| i.to_string()).collect();
        format!("layout {layout}\nwidth {}\nkeep {}\n", self.width, keep.join(" ")) + &nums("mean", &self.mean) + &nums("scale", &self.scale) + &nums("w", &self.w)
    }

    pub fn from_text(text: &str, layout: &str) -> Result<Model, String> {
        let line = |name: &str| text.lines().find_map(|l| l.strip_prefix(name).and_then(|r| r.strip_prefix(' '))).ok_or(format!("no `{name}` line"));
        if line("layout")? != layout {
            return Err(format!("layout `{}` is not `{layout}`", line("layout")?));
        }
        let width: usize = line("width")?.parse().map_err(|e| format!("`width`: {e}"))?;
        let keep: Vec<usize> = line("keep")?.split_whitespace().map(|x| x.parse::<usize>().map_err(|e| format!("`keep`: {x}: {e}"))).collect::<Result<_, _>>()?;
        if keep.iter().any(|&i| i >= width) {
            return Err("`keep` names a column past the width".to_string());
        }
        let nums = |name: &str| -> Result<Vec<f64>, String> {
            let v: Vec<f64> = line(name)?.split_whitespace().map(|x| x.parse::<f64>().map_err(|e| format!("`{name}`: {x}: {e}"))).collect::<Result<_, _>>()?;
            if v.len() != keep.len() || v.iter().any(|x| !x.is_finite()) || (name == "scale" && v.iter().any(|&x| x <= 0.0)) {
                return Err(format!("`{name}` has {} numbers (expected {}), a non-finite one or a scale <= 0", v.len(), keep.len()));
            }
            Ok(v)
        };
        let (mean, scale, w) = (nums("mean")?, nums("scale")?, nums("w")?);
        Ok(Model { width, keep, mean, scale, w })
    }
}

/// Full-batch gradient descent for the logistic loss with a small L2 penalty, from zero weights: deterministic. The rows are
/// the caller's to filter; they must share one width.
pub fn fit(rows: &[(Vec<f32>, bool)]) -> Model {
    assert!(!rows.is_empty(), "fit needs rows");
    let (width, n) = (rows[0].0.len(), rows.len() as f64);
    assert!(rows.iter().all(|r| r.0.len() == width), "rows of different widths");
    let (mut keep, mut mean, mut scale) = (vec![], vec![], vec![]);
    for i in 0..width {
        let (m, s) = if i == 0 {
            (0.0, 1.0)
        } else {
            let m = rows.iter().map(|r| r.0[i] as f64).sum::<f64>() / n;
            let v = rows.iter().map(|r| (r.0[i] as f64 - m).powi(2)).sum::<f64>() / n;
            if v <= 0.0 {
                continue;
            }
            (m, v.sqrt())
        };
        keep.push(i);
        mean.push(m);
        scale.push(s);
    }
    let w = vec![0.0; keep.len()];
    let mut s = Model { width, keep, mean, scale, w };
    for _ in 0..FIT_STEPS {
        let mut g = vec![0.0; s.keep.len()];
        for (f, y) in rows {
            let e = 1.0 / (1.0 + (-s.score(f)).exp()) - *y as u8 as f64;
            for (j, &i) in s.keep.iter().enumerate() {
                g[j] += e * (f[i] as f64 - s.mean[j]) / s.scale[j];
            }
        }
        for j in 0..s.keep.len() {
            s.w[j] -= FIT_RATE * (g[j] / n + FIT_L2 * s.w[j]);
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

/// The label rows of one mine: for each law of its extras file (`lhs = rhs` lines) whether its log credits it
/// (`RULEMINER label: 1 <law>`: a straggler a chosen rule covers). A log that counts stragglers but has no label line was
/// written before the miner printed them: refused, because every law would read as y = 0.
pub fn mine_labels(extras: &str, log: &str, tag: &str) -> Result<Vec<(String, bool)>, String> {
    let (yes, any) = (format!("RULEMINER {tag}: 1 "), format!("RULEMINER {tag}: "));
    let credited: std::collections::HashSet<&str> = log.lines().filter_map(|l| l.strip_prefix(yes.as_str())).collect();
    let labelled = log.lines().any(|l| l.starts_with(any.as_str()));
    let stragglers = log
        .lines()
        .filter_map(|l| l.strip_prefix("RULEMINER ")?.split_once(" stragglers of ")?.0.parse::<usize>().ok())
        .next()
        .ok_or("no `RULEMINER N stragglers of M laws` line (a crashed or foreign log)")?;
    if stragglers > 0 && !labelled {
        return Err(format!("{stragglers} stragglers but no `RULEMINER {tag}:` line"));
    }
    Ok(extras.lines().filter(|l| !l.is_empty()).map(|l| (l.to_string(), credited.contains(l))).collect())
}

/// The number in the last path component that reads `s<digits>_...` (a gate arm folder, `s7_A`; the one nearest the file).
pub fn salt_of(path: &str) -> Option<usize> {
    path.split(['/', '\\'])
        .filter_map(|c| {
            let rest = c.strip_prefix('s')?;
            let (digits, _) = rest.split_once('_')?;
            digits.parse().ok()
        })
        .last()
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

/// `LABEL_DIRS=<arm folder>;<arm folder>.. LABEL_OUT=<tsv> <exe> ctx_scorer::dump_labels --exact --ignored --nocapture`: one row
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
            for (law, y) in mine_labels(&extras, &log_text, "label").unwrap_or_else(|e| panic!("{}: {e}", log.display())) {
                rows += &format!("{salt}\t{}\t{law}\n", y as u8);
                laws += 1;
                pos += y as usize;
            }
            mines += 1;
        }
    }
    assert!(mines > 0, "no laws_extra_*.txt under {dirs}");
    std::fs::write(out, rows).unwrap();
    println!("LABELS {mines} mines, {laws} laws, {pos} credited");
}

/// The label TSV's (`salt<TAB>y<TAB>law`) rows as (salt, per-law features, y).
fn read_labels(tsv: &str) -> Vec<(usize, Vec<f32>, bool)> {
    tsv.lines()
        .map(|l| {
            let mut p = l.splitn(3, '\t');
            let (salt, y, law) = (p.next().unwrap().parse::<usize>().unwrap(), p.next().unwrap() == "1", p.next().unwrap());
            let (lhs, rhs) = law.split_once(" = ").unwrap_or_else(|| panic!("not a law: {law}"));
            (salt, per_law_features(&(parse_term(lhs), parse_term(rhs))).to_vec(), y)
        })
        .collect()
}

/// `LABELS=<tsv> <exe> ctx_scorer::reproduce_stage1 --exact --ignored --nocapture`: stage 1's recorded offline numbers
/// (docs/tier-cycle.md, "A learned scorer over the extras"): fit on salts 4 to 9, test on salt 10, all rows.
#[test]
#[ignore]
fn reproduce_stage1() {
    let setup = &job::Setup::process();
    let rows = read_labels(&std::fs::read_to_string(setup.var("LABELS").expect("LABELS")).unwrap());
    let (laws, credited) = (rows.len(), rows.iter().filter(|r| r.2).count());
    assert_eq!((laws, credited), (13_398, 3_282), "the cached labels are not the recorded ones");
    let part = |keep: &dyn Fn(usize) -> bool| -> Vec<(Vec<f32>, bool)> { rows.iter().filter(|r| keep(r.0)).map(|r| (r.1.clone(), r.2)).collect() };
    let (train, test) = (part(&|s| (4..=9).contains(&s)), part(&|s| s == 10));
    let m = fit(&train);
    let on = |rs: &[(Vec<f32>, bool)], f: &dyn Fn(&[f32]) -> f64| auc(&rs.iter().map(|(x, y)| (f(x), *y)).collect::<Vec<_>>());
    let (tr, te, size) = (on(&train, &|x| m.score(x)), on(&test, &|x| m.score(x)), on(&test, &|x| x[1] as f64));
    println!("AUC train {tr:.4} test {te:.4} sizeonly-test {size:.4} rows {} positives {}", train.len(), train.iter().filter(|r| r.1).count());
    for (got, want, what) in [(te, 0.691, "test"), (tr, 0.711, "train"), (size, 0.528, "size-only")] {
        assert!((got - want).abs() <= 0.005, "{what} AUC {got:.4}, recorded {want}");
    }
}

/// The columns of the context model: the per-law block, then group 1 (3), group 2 (4), group 3 (2).
pub const WIDTH: usize = PER_LAW + 3 + 4 + 2;

/// One law of a mine's pool, from the dump. `steps`, `size`, `fallbacks` and `uncovered` mean something only for a straggler
/// (the laws the base rules leave); `uncovered` is whether it is still one after the served-only cover.
#[derive(Clone)]
pub struct PoolLaw {
    pub law: (Term, Term),
    pub straggler: bool,
    pub steps: i64,
    pub size: i64,
    pub fallbacks: u64,
    pub uncovered: bool,
}

/// The percentile of each value among `values`: (average rank - 1) / (m - 1), equal values sharing the average rank, 0.5 for
/// a single value.
pub fn percentiles(values: &[f64]) -> Vec<f64> {
    let m = values.len();
    if m == 1 {
        return vec![0.5];
    }
    let mut order: Vec<usize> = (0..m).collect();
    order.sort_by(|&i, &j| values[i].total_cmp(&values[j]));
    let mut out = vec![0.0; m];
    let mut i = 0;
    while i < m {
        let mut j = i;
        while j + 1 < m && values[order[j + 1]] == values[order[i]] {
            j += 1;
        }
        let avg = (i + j) as f64 / 2.0; // zero-based average rank
        for &k in &order[i..=j] {
            out[k] = avg / (m - 1) as f64;
        }
        i = j + 1;
    }
    out
}

/// Group 1, per pool law: the percentiles of its steps, normal-form size and fallbacks among the pool's stragglers; zeros for
/// a law that is not a straggler.
pub fn group1(pool: &[PoolLaw]) -> Vec<[f32; 3]> {
    let idx: Vec<usize> = (0..pool.len()).filter(|&i| pool[i].straggler).collect();
    let col = |f: &dyn Fn(&PoolLaw) -> f64| percentiles(&idx.iter().map(|&i| f(&pool[i])).collect::<Vec<_>>());
    let (a, b, c) = (col(&|l| l.steps as f64), col(&|l| l.size as f64), col(&|l| l.fallbacks as f64));
    let mut out = vec![[0.0f32; 3]; pool.len()];
    for (k, &i) in idx.iter().enumerate() {
        out[i] = [a[k] as f32, b[k] as f32, c[k] as f32];
    }
    out
}

fn ops_of(ts: &[&Term]) -> [usize; OPN] {
    let mut c = [0usize; OPN];
    ts.iter().for_each(|t| op_counts(t, &mut c));
    c
}

/// Sum of the element-wise minima over the sum of the maxima; 0 when both are empty.
fn jaccard(a: &[usize; OPN], b: &[usize; OPN]) -> f32 {
    let (lo, hi): (usize, usize) = (0..OPN).fold((0, 0), |(l, h), i| (l + a[i].min(b[i]), h + a[i].max(b[i])));
    if hi == 0 {
        0.0
    } else {
        lo as f32 / hi as f32
    }
}

/// The operator at the top of a term; a leaf has none.
fn root(t: &Term) -> Option<usize> {
    match *t.node() {
        Node::Op(o, ..) => Some(o),
        _ => None,
    }
}

/// Group 2, per pool law, against `served` (the served stragglers' normal forms): the Jaccard of the law's operator multiset
/// (both sides) with the multiset union (element-wise maximum) of the served normal forms'; the same for the left side alone;
/// the fraction of `served` whose left-side root operator is the law's; the same for the right side. Zeros when nothing is
/// served, and for a side that is a leaf.
pub fn group2(pool: &[PoolLaw], served: &[(Term, Term)]) -> Vec<[f32; 4]> {
    let union = |side: &dyn Fn(&(Term, Term)) -> Vec<Term>| -> [usize; OPN] {
        served.iter().fold([0usize; OPN], |mut u, s| {
            let c = ops_of(&side(s).iter().collect::<Vec<_>>());
            (0..OPN).for_each(|i| u[i] = u[i].max(c[i]));
            u
        })
    };
    let (both_u, left_u) = (union(&|s| vec![s.0, s.1]), union(&|s| vec![s.0]));
    let frac = |r: Option<usize>, side: &dyn Fn(&(Term, Term)) -> Term| -> f32 {
        match (r, served.len()) {
            (Some(o), n) if n > 0 => served.iter().filter(|s| root(&side(s)) == Some(o)).count() as f32 / n as f32,
            _ => 0.0,
        }
    };
    pool.iter()
        .map(|l| {
            if served.is_empty() {
                return [0.0; 4];
            }
            [jaccard(&ops_of(&[&l.law.0, &l.law.1]), &both_u), jaccard(&ops_of(&[&l.law.0]), &left_u), frac(root(&l.law.0), &|s| s.0), frac(root(&l.law.1), &|s| s.1)]
        })
        .collect()
}

/// Group 3, per pool law: 1 if it is a straggler the served-only cover leaves uncovered, and the fraction of the pool's
/// stragglers with the same left-side root operator that stay uncovered. Zeros for a law that is not a straggler.
pub fn group3(pool: &[PoolLaw]) -> Vec<[f32; 2]> {
    pool.iter()
        .map(|l| {
            let Some(o) = root(&l.law.0).filter(|_| l.straggler) else { return [(l.straggler && l.uncovered) as u8 as f32, 0.0] };
            let same: Vec<&PoolLaw> = pool.iter().filter(|m| m.straggler && root(&m.law.0) == Some(o)).collect();
            [l.uncovered as u8 as f32, same.iter().filter(|m| m.uncovered).count() as f32 / same.len() as f32]
        })
        .collect()
}

/// The pool dump's file (`RULEMINER_POOL_DUMP`): a line per pool law, tab-separated: its index in the pool, the law as
/// `lhs = rhs`, whether it is a straggler (0/1), its steps, normal-form size and machine proofs (empty for a clean law), and
/// whether it is still a straggler after the served-only cover (0/1). The facts are raw; the features are computed from them.
pub fn pool_tsv(rows: &[(usize, String, Option<(i64, i64, u64)>, bool)]) -> String {
    rows.iter()
        .map(|(i, law, facts, uncovered)| match facts {
            Some((steps, size, fallbacks)) => format!("{i}\t{law}\t1\t{steps}\t{size}\t{fallbacks}\t{}\n", *uncovered as u8),
            None => format!("{i}\t{law}\t0\t\t\t\t{}\n", *uncovered as u8),
        })
        .collect()
}

/// The pool `pool_tsv` wrote, in order.
pub fn read_pool(tsv: &str) -> Vec<PoolLaw> {
    tsv.lines()
        .map(|line| {
            let f: Vec<&str> = line.split('\t').collect();
            assert_eq!(f.len(), 7, "a pool line has 7 fields: {line:?}");
            let (lhs, rhs) = f[1].split_once(" = ").unwrap_or_else(|| panic!("a pool law is `lhs = rhs`: {line:?}"));
            let num = |s: &str| s.parse::<i64>().unwrap_or(0);
            PoolLaw { law: (parse_term(lhs), parse_term(rhs)), straggler: f[2] == "1", steps: num(f[3]), size: num(f[4]), fallbacks: num(f[5]) as u64, uncovered: f[6] == "1" }
        })
        .collect()
}

/// The `WIDTH` columns of every pool law, in pool order.
pub fn rows(pool: &[PoolLaw], served: &[(Term, Term)]) -> Vec<Vec<f32>> {
    let (g1, g2, g3) = (group1(pool), group2(pool, served), group3(pool));
    (0..pool.len()).map(|i| per_law_features(&pool[i].law).iter().chain(&g1[i]).chain(&g2[i]).chain(&g3[i]).copied().collect()).collect()
}

/// SplitMix64: a seeded generator for the shuffles and the bootstrap (no dependency, the same stream on every machine).
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let z = (self.0 ^ (self.0 >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        let z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

/// How many of the first `k` laws of `order` (indices into `y`) are positive.
pub fn capture_at_k(order: &[usize], y: &[bool], k: usize) -> usize {
    order.iter().take(k).filter(|&&i| y[i]).count()
}

/// The mean, over one shuffle per seed, of the positives among the first `k` of `y` (the labels of the laws a random ranker
/// orders).
pub fn random_capture(y: &[bool], k: usize, seeds: std::ops::RangeInclusive<u64>) -> f64 {
    let (mut total, mut runs) = (0usize, 0usize);
    for seed in seeds {
        let (mut v, mut rng) = (y.to_vec(), Rng(seed));
        for i in (1..v.len()).rev() {
            v.swap(i, rng.below(i + 1));
        }
        total += v.iter().take(k).filter(|&&b| b).count();
        runs += 1;
    }
    total as f64 / runs.max(1) as f64
}

/// The `Small` key (`miner::Keep::Small`) over the first `slice` laws of a pool: stragglers by (steps, size), equal keys in stream
/// order, then the other laws in stream order.
pub fn small_order(pool: &[PoolLaw], slice: usize) -> Vec<usize> {
    let (mut s, rest): (Vec<usize>, Vec<usize>) = (0..slice.min(pool.len())).partition(|&i| pool[i].straggler);
    s.sort_by_key(|&i| (pool[i].steps, pool[i].size));
    s.into_iter().chain(rest).collect()
}

/// The order a model ranks the live laws: stragglers by descending score (equal scores in stream order), then the other live
/// laws in stream order.
fn score_order(scores: &[f64], straggler: &[bool], live: &[bool]) -> Vec<usize> {
    let mut s: Vec<usize> = (0..scores.len()).filter(|&i| live[i] && straggler[i]).collect();
    s.sort_by(|&a, &b| scores[b].total_cmp(&scores[a]));
    s.extend((0..scores.len()).filter(|&i| live[i] && !straggler[i]));
    s
}

/// The 95% percentile interval of the mean of `diffs` over `resamples` resamples with replacement.
pub fn bootstrap_interval(diffs: &[f64], resamples: usize, seed: u64) -> (f64, f64) {
    if diffs.is_empty() {
        return (0.0, 0.0);
    }
    let (mut rng, n) = (Rng(seed), diffs.len());
    let mut means: Vec<f64> = (0..resamples).map(|_| (0..n).map(|_| diffs[rng.below(n)]).sum::<f64>() / n as f64).collect();
    means.sort_by(f64::total_cmp);
    (means[resamples * 25 / 1000], means[(resamples * 975 / 1000).min(resamples - 1)])
}

/// The Q1 bar (m1) at one k: both intervals clear zero from below and at least 5 salts have d and e both above zero.
pub fn gate_ok(d: (f64, f64), e: (f64, f64), salts_both: usize) -> bool {
    d.0 > 0.0 && e.0 > 0.0 && salts_both >= 5
}

/// Each held-out salt with the other salts, ascending.
pub fn loo_split(salts: &[usize]) -> Vec<(usize, Vec<usize>)> {
    let mut all = salts.to_vec();
    all.sort_unstable();
    all.dedup();
    all.iter().map(|&s| (s, all.iter().copied().filter(|&t| t != s).collect())).collect()
}

/// One mine of the dump: its pool (all `4n` laws), the served stragglers' normal forms, and for the first `n` pool laws (the
/// labelled slice) whether the mine's log credits them (`y`) and whether they are the first occurrence of their text across
/// the loaded mines (`live`; a later copy is dropped from rankings and fits).
pub struct Mine {
    pub salt: usize,
    pub pool: Vec<PoolLaw>,
    pub served: Vec<(Term, Term)>,
    pub y: Vec<bool>,
    pub live: Vec<bool>,
}

/// Every mine under the arm folders `dirs` (a `dump_<m>_pool.tsv` with its `dump_<m>_served.txt`, `laws_extra_<m>.txt` and
/// `mine_<m>.log`), by salt then path, with the number of later duplicate laws dropped. Refused: a pool whose first `n` laws are
/// not the first `n` lines of `laws_extra`, a repeat inside one mine's slice, a credited law the dump calls clean.
pub fn load_mines(dirs: &[&std::path::Path], n: usize) -> Result<(Vec<Mine>, usize), String> {
    let mut files = vec![];
    dirs.iter().for_each(|d| walk(d, &mut files));
    files.retain(|f| f.file_name().is_some_and(|s| s.to_string_lossy().starts_with("dump_") && s.to_string_lossy().ends_with("_pool.tsv")));
    files.sort_by_key(|f| (salt_of(&f.to_string_lossy()), f.clone()));
    let (mut mines, mut seen, mut dropped) = (vec![], std::collections::HashSet::new(), 0);
    for f in files {
        let shown = f.display().to_string();
        let name = f.file_name().unwrap().to_string_lossy().replace("dump_", "").replace("_pool.tsv", "");
        let salt = salt_of(&shown).ok_or(format!("{shown}: no s<salt>_ folder"))?;
        let read = |file: String| std::fs::read_to_string(f.with_file_name(&file)).map_err(|e| format!("{shown}: {file}: {e}"));
        let (tsv, extras, log, served) = (read(format!("dump_{name}_pool.tsv"))?, read(format!("laws_extra_{name}.txt"))?, read(format!("mine_{name}.log"))?, read(format!("dump_{name}_served.txt"))?);
        let pool = read_pool(&tsv);
        let texts: Vec<&str> = extras.lines().filter(|l| !l.is_empty()).collect();
        if pool.len() < n || texts.len() < n {
            return Err(format!("{shown}: {} pool laws and {} laws_extra lines, fewer than n = {n}", pool.len(), texts.len()));
        }
        for (i, line) in tsv.lines().take(n).enumerate() {
            if line.split('\t').nth(1) != Some(texts[i]) {
                return Err(format!("{shown}: pool law {i} is not laws_extra line {i}"));
            }
        }
        let slice = texts[..n].join("\n");
        let own: std::collections::HashSet<&str> = texts[..n].iter().copied().collect();
        if own.len() < n {
            return Err(format!("{shown}: a law repeats inside the first {n} laws_extra lines"));
        }
        let y: Vec<bool> = mine_labels(&slice, &log, "label").map_err(|e| format!("{shown}: {e}"))?.into_iter().map(|r| r.1).collect();
        if let Some(i) = (0..n).find(|&i| y[i] && !pool[i].straggler) {
            return Err(format!("{shown}: law {i} is credited but the dump says it is no straggler"));
        }
        let live: Vec<bool> = texts[..n].iter().map(|t| seen.insert(t.to_string())).collect();
        dropped += live.iter().filter(|&&l| !l).count();
        let served = served
            .lines()
            .filter(|l| !l.is_empty())
            .map(|l| l.split_once(" = ").map(|(a, b)| (parse_term(a), parse_term(b))).ok_or(format!("{shown}: served line is not `lhs = rhs`: {l:?}")))
            .collect::<Result<Vec<_>, _>>()?;
        mines.push(Mine { salt, pool, served, y, live });
    }
    Ok((mines, dropped))
}

/// The `variants()` entry for the model without the marginal-coverage group: the 33 columns Q2 runs (decision c1).
pub const NO_G3: &str = "drop group 3";

/// The model variants of the ablation, as the columns each reads: the context model, the per-law model, then the context model
/// without group 1, 2, 3 and without the per-law block (the bias stays).
fn variants() -> Vec<(&'static str, Vec<usize>)> {
    let without = |lo: usize, hi: usize| (0..WIDTH).filter(|&c| c < lo || c >= hi).collect::<Vec<_>>();
    vec![
        ("context", (0..WIDTH).collect()),
        ("per-law", (0..PER_LAW).collect()),
        ("drop group 1", without(PER_LAW, PER_LAW + 3)),
        ("drop group 2", without(PER_LAW + 3, PER_LAW + 7)),
        ("drop group 3", without(PER_LAW + 7, WIDTH)),
        ("drop per-law", (0..1).chain(PER_LAW..WIDTH).collect()),
    ]
}

fn project(x: &[f32], cols: &[usize]) -> Vec<f32> {
    cols.iter().map(|&c| x[c]).collect()
}

/// The Q1 report. Leave-one-salt-out: for each salt, fit every variant on the labelled live stragglers of the other salts, rank
/// that salt's mines (stragglers by score, the rest in stream order), and compare the capture at each k of `ks` with the
/// per-law model, the `small` key and a random ranker. d = context - per-law and e = context - small per mine, bootstrapped
/// over the mines; the last line is the verdict of the gate at every k.
pub fn q1(mines: &[Mine], ks: &[usize], context: &str) -> String {
    use std::fmt::Write;
    let mut salts: Vec<usize> = mines.iter().map(|m| m.salt).collect();
    salts.sort_unstable();
    salts.dedup();
    let feats: Vec<Vec<Vec<f32>>> = mines.iter().map(|m| rows(&m.pool, &m.served)[..m.y.len()].to_vec()).collect();
    let mut vs = variants();
    let at = vs.iter().position(|(name, _)| *name == context).unwrap_or_else(|| panic!("no model variant named {context:?}"));
    vs.swap(0, at);
    let mut orders: Vec<Vec<Vec<usize>>> = vec![vec![vec![]; mines.len()]; vs.len()];
    let mut fold_auc: Vec<Vec<f64>> = vec![vec![]; 2];
    for (held, _) in loo_split(&salts) {
        for (vi, (_, cols)) in vs.iter().enumerate() {
            let mut train = vec![];
            for (mi, m) in mines.iter().enumerate().filter(|(_, m)| m.salt != held) {
                for i in (0..m.y.len()).filter(|&i| m.live[i] && m.pool[i].straggler) {
                    train.push((project(&feats[mi][i], cols), m.y[i]));
                }
            }
            assert!(!train.is_empty(), "salt {held}: no labelled stragglers outside it to fit on");
            let model = fit(&train);
            let mut scored = vec![];
            for (mi, m) in mines.iter().enumerate().filter(|(_, m)| m.salt == held) {
                let scores: Vec<f64> = (0..m.y.len()).map(|i| model.score(&project(&feats[mi][i], cols))).collect();
                let strag: Vec<bool> = (0..m.y.len()).map(|i| m.pool[i].straggler).collect();
                orders[vi][mi] = score_order(&scores, &strag, &m.live);
                scored.extend((0..m.y.len()).filter(|&i| m.live[i] && strag[i]).map(|i| (scores[i], m.y[i])));
            }
            if vi < 2 {
                fold_auc[vi].push(auc(&scored));
            }
        }
    }
    let small: Vec<Vec<usize>> = mines
        .iter()
        .map(|m| {
            let mut o = small_order(&m.pool, m.y.len());
            o.retain(|&i| m.live[i]);
            o
        })
        .collect();
    let live_strag: Vec<Vec<bool>> = mines.iter().map(|m| (0..m.y.len()).filter(|&i| m.live[i] && m.pool[i].straggler).map(|i| m.y[i]).collect()).collect();
    let positives: Vec<usize> = live_strag.iter().map(|v| v.iter().filter(|&&b| b).count()).collect();
    let mut t = String::new();
    let mean = |v: &[f64]| v.iter().sum::<f64>() / v.len().max(1) as f64;
    writeln!(t, "context model: {} ({} columns)", vs[0].0, vs[0].1.len()).unwrap();
    writeln!(t, "Q1 {} mines, {} salts, slice {} laws; live stragglers {}, credited {}", mines.len(), salts.len(), mines.first().map_or(0, |m| m.y.len()), live_strag.iter().map(Vec::len).sum::<usize>(), positives.iter().sum::<usize>()).unwrap();
    for &s in &salts {
        let (ms, ps) = (mines.iter().filter(|m| m.salt == s).count(), mines.iter().enumerate().filter(|(_, m)| m.salt == s).map(|(i, _)| positives[i]).sum::<usize>());
        let st: usize = mines.iter().enumerate().filter(|(_, m)| m.salt == s).map(|(i, _)| live_strag[i].len()).sum();
        writeln!(t, "salt {s}: {ms} mines, {st} live stragglers, {ps} credited").unwrap();
    }
    writeln!(t, "held-out AUC (mean over salts): context {:.4}, per-law {:.4}", mean(&fold_auc[0]), mean(&fold_auc[1])).unwrap();
    let (mut pass, mut met, mut no_room) = (true, vec![], vec![]);
    for &k in ks {
        let cap = |o: &[Vec<usize>]| -> Vec<f64> { (0..mines.len()).map(|mi| capture_at_k(&o[mi], &mines[mi].y, k) as f64).collect() };
        let (ctx, per, sm) = (cap(&orders[0]), cap(&orders[1]), cap(&small));
        let rand: Vec<f64> = mines.iter().map(|m| random_capture(&(0..m.y.len()).filter(|&i| m.live[i]).map(|i| m.y[i]).collect::<Vec<_>>(), k, 1..=200)).collect();
        let rand_s: Vec<f64> = live_strag.iter().map(|y| random_capture(y, k, 1..=200)).collect();
        let ceiling: usize = positives.iter().map(|&p| p.min(k)).sum();
        let sum = |v: &[f64]| v.iter().sum::<f64>();
        writeln!(t, "k={k}: ceiling {ceiling}; capture sums: context {}, per-law {}, small {}, random {:.1}, random stragglers-first {:.1}", sum(&ctx), sum(&per), sum(&sm), sum(&rand), sum(&rand_s)).unwrap();
        if sum(&sm) >= 0.99 * ceiling as f64 {
            writeln!(t, "k={k}: no room: the `small` key is at the ceiling, so no ranker can beat it here").unwrap();
            no_room.push(k);
        }
        let (d, e): (Vec<f64>, Vec<f64>) = (0..mines.len()).map(|i| (ctx[i] - per[i], ctx[i] - sm[i])).unzip();
        let (di, ei) = (bootstrap_interval(&d, 2000, 1), bootstrap_interval(&e, 2000, 1));
        let by_salt = |v: &[f64]| -> Vec<f64> { salts.iter().map(|&s| (0..mines.len()).filter(|&i| mines[i].salt == s).map(|i| v[i]).sum()).collect() };
        let (ds, es) = (by_salt(&d), by_salt(&e));
        let both = (0..salts.len()).filter(|&j| ds[j] > 0.0 && es[j] > 0.0).count();
        let ok = gate_ok(di, ei, both);
        pass &= ok;
        if ok {
            met.push(k);
        }
        writeln!(t, "k={k}: d (context - per-law) mean {:.3}, 95% [{:.3}, {:.3}]; salts above 0: {}/{}", mean(&d), di.0, di.1, ds.iter().filter(|&&x| x > 0.0).count(), salts.len()).unwrap();
        writeln!(t, "k={k}: e (context - small) mean {:.3}, 95% [{:.3}, {:.3}]; salts above 0: {}/{}", mean(&e), ei.0, ei.1, es.iter().filter(|&&x| x > 0.0).count(), salts.len()).unwrap();
        writeln!(t, "k={k}: per-salt d {ds:?}, e {es:?}; salts with both above 0: {both}/{}; gate {}", salts.len(), if ok { "met" } else { "not met" }).unwrap();
        let abl: Vec<String> = vs.iter().enumerate().map(|(vi, (name, _))| format!("{name} {}", sum(&cap(&orders[vi])))).collect();
        writeln!(t, "k={k}: ablation capture sums: {}", abl.join(", ")).unwrap();
    }
    writeln!(t, "gate met at k in {met:?}; no room at k in {no_room:?}").unwrap();
    writeln!(t, "verdict {}", if pass { "PASS" } else { "FAIL" }).unwrap();
    t
}

/// `Q1_DIRS=<arm folder>;<arm folder>.. <exe> ctx_scorer::q1_report --exact --ignored --nocapture`: the offline answer to Q1 on a
/// pool dump (`scripts/ctx_dump.sh`): prints the report; a FAIL is a result, not an error.
#[test]
#[ignore]
fn q1_report() {
    let setup = &job::Setup::process();
    let dirs = setup.var("Q1_DIRS").expect("Q1_DIRS");
    let dirs: Vec<&std::path::Path> = dirs.split(';').map(std::path::Path::new).collect();
    let (mines, dropped) = load_mines(&dirs, 319).unwrap_or_else(|e| panic!("{e}"));
    assert_eq!(mines.len(), 42, "the dump has 42 mines");
    println!("LOADED {} mines, {dropped} later duplicate laws dropped from the {} labelled", mines.len(), mines.len() * 319);
    print!("{}", q1(&mines, &[40, 80], &setup.var("Q1_CONTEXT").unwrap_or_else(|| "context".into())));
}

#[cfg(test)]
mod tests {
    use super::*;

    fn p(a: &str, b: &str) -> (Term, Term) {
        (parse_term(a), parse_term(b))
    }

    fn pl(a: &str, b: &str, straggler: bool, steps: i64, uncovered: bool) -> PoolLaw {
        PoolLaw { law: p(a, b), straggler, steps, size: steps, fallbacks: steps as u64, uncovered }
    }

    #[test]
    fn pool_tsv_has_one_line_per_law_and_empty_cells_for_clean_laws() {
        let rows = vec![(0, "add(x, y) = add(y, x)".to_string(), Some((3, 7, 2)), true), (1, "and(x, y) = and(y, x)".to_string(), None, false)];
        let text = pool_tsv(&rows);
        let lines: Vec<&str> = text.lines().collect();
        assert_eq!(lines, vec!["0\tadd(x, y) = add(y, x)\t1\t3\t7\t2\t1", "1\tand(x, y) = and(y, x)\t0\t\t\t\t0"]);
    }

    #[test]
    fn read_pool_inverts_pool_tsv() {
        let rows = vec![(0, "add(x, y) = add(y, x)".to_string(), Some((3, 7, 2)), true), (1, "and(x, y) = and(y, x)".to_string(), None, false), (2, "or(x, y) = or(y, x)".to_string(), Some((1, 4, 1)), false)];
        let pool = read_pool(&pool_tsv(&rows));
        assert_eq!(pool.len(), 3);
        assert!(pool[0].straggler && pool[0].uncovered && (pool[0].steps, pool[0].size, pool[0].fallbacks) == (3, 7, 2));
        assert!(!pool[1].straggler && !pool[1].uncovered);
        assert!(pool[2].straggler && !pool[2].uncovered);
        assert!(pool[1].law == p("and(x, y)", "and(y, x)"));
    }

    #[test]
    fn percentiles_share_the_average_rank_for_ties() {
        assert_eq!(percentiles(&[1.0, 2.0, 2.0, 3.0]), vec![0.0, 0.5, 0.5, 1.0]);
        assert_eq!(percentiles(&[3.0, 1.0]), vec![1.0, 0.0]);
    }

    #[test]
    fn percentiles_of_one_value_is_half() {
        assert_eq!(percentiles(&[7.0]), vec![0.5]);
        assert!(percentiles(&[]).is_empty());
    }

    #[test]
    fn group1_is_zero_for_non_stragglers_and_in_unit_range() {
        let pool = vec![pl("add(x, y)", "add(y, x)", true, 3, true), pl("and(x, y)", "and(y, x)", false, 9, false), pl("or(x, y)", "or(y, x)", true, 8, false)];
        let g = group1(&pool);
        assert_eq!(g[1], [0.0; 3]);
        assert_eq!((g[0], g[2]), ([0.0; 3], [1.0; 3]));
        assert!(g.iter().flatten().all(|v| (0.0..=1.0).contains(v)));
    }

    #[test]
    fn group2_identical_operator_multiset_gives_jaccard_one() {
        let pool = vec![pl("add(x, y)", "add(y, x)", true, 1, true)];
        let g = group2(&pool, &[p("add(x, y)", "add(y, x)")]);
        assert_eq!(g[0], [1.0, 1.0, 1.0, 1.0]);
    }

    #[test]
    fn group2_with_no_served_stragglers_is_zero_not_nan() {
        let pool = vec![pl("add(x, y)", "add(y, x)", true, 1, true)];
        assert_eq!(group2(&pool, &[])[0], [0.0; 4]);
        // a law that is all leaves has no operator and matches nothing
        let leaf = vec![pl("x", "x", true, 1, true)];
        assert_eq!(group2(&leaf, &[p("add(x, y)", "add(y, x)")])[0], [0.0; 4]);
    }

    #[test]
    fn group3_is_zero_for_clean_laws_and_the_uncovered_fraction_otherwise() {
        let pool = vec![
            pl("add(x, y)", "add(y, x)", true, 1, true),
            pl("add(x, 0)", "x", true, 2, false),
            pl("and(x, y)", "and(y, x)", false, 0, false),
            pl("and(x, x)", "x", true, 3, true),
        ];
        let g = group3(&pool);
        assert_eq!(g[0], [1.0, 0.5]); // one of the two `add` stragglers stays uncovered
        assert_eq!(g[1], [0.0, 0.5]);
        assert_eq!(g[2], [0.0, 0.0]);
        assert_eq!(g[3], [1.0, 1.0]);
    }

    #[test]
    fn rows_are_deterministic_35_wide_and_finite() {
        let pool = vec![pl("add(x, y)", "add(y, x)", true, 1, true), pl("and(x, y)", "and(y, x)", false, 0, false)];
        let served = [p("sub(x, y)", "sub(y, x)")];
        let (a, b) = (rows(&pool, &served), rows(&pool, &served));
        assert_eq!(a, b);
        assert!(a.iter().all(|r| r.len() == WIDTH && WIDTH == 35 && r.iter().all(|v| v.is_finite())));
    }

    #[test]
    fn a_pool_with_no_stragglers_gives_finite_columns() {
        let pool = vec![pl("and(x, y)", "and(y, x)", false, 0, false)];
        let r = rows(&pool, &[]);
        assert!(r[0].iter().all(|v| v.is_finite()));
        assert_eq!(&r[0][PER_LAW..], &[0.0; 9]);
    }

    #[test]
    fn auc_of_known_scores() {
        assert_eq!(auc(&[(0.1, false), (0.4, false), (0.35, true), (0.8, true)]), 0.75);
        assert_eq!(auc(&[(1.0, true), (1.0, false)]), 0.5, "a tie counts half");
        assert_eq!(auc(&[(1.0, true), (2.0, true)]), 0.5, "no negatives: no information");
        assert_eq!(auc(&[(1.0, true), (1.0, false), (2.0, true), (0.0, false)]), 0.875);
    }

    #[test]
    #[should_panic(expected = "fit needs rows")]
    fn fit_refuses_no_rows() {
        fit(&[]);
    }

    #[test]
    fn per_law_features_are_symmetric_finite_and_26_long() {
        let (l, r) = (p("add(x, y)", "add(y, x)"), p("add(y, x)", "add(x, y)"));
        assert_eq!(per_law_features(&l), per_law_features(&r));
        assert!(per_law_features(&(Term::ZERO, Term::ONES)).iter().all(|f| f.is_finite()), "a law with no variables");
        assert_eq!(per_law_features(&l).len(), 26);
    }

    #[test]
    fn model_text_round_trips_and_refuses_a_wrong_layout() {
        let rows: Vec<(Vec<f32>, bool)> = (0..20).map(|i| (vec![1.0, i as f32, (i % 3) as f32], i > 9)).collect();
        let m = fit(&rows);
        assert_eq!(Model::from_text(&m.to_text("v1"), "v1").unwrap(), m);
        assert!(Model::from_text(&m.to_text("v1"), "v2").is_err());
        assert!(Model::from_text("layout v1\nwidth 3", "v1").is_err(), "a garbled file is an error that says so");
        assert!(Model::from_text("", "v1").is_err());
    }

    #[test]
    fn fit_separates_a_separable_set_and_repeats_bit_for_bit() {
        let rows: Vec<(Vec<f32>, bool)> = (1..=10).map(|i| (vec![1.0, i as f32], i > 5)).collect();
        let (a, b) = (fit(&rows), fit(&rows));
        assert_eq!(a, b);
        assert_eq!(auc(&rows.iter().map(|(f, y)| (a.score(f), *y)).collect::<Vec<_>>()), 1.0);
    }

    #[test]
    fn a_constant_column_is_omitted_and_scores_finite() {
        let rows: Vec<(Vec<f32>, bool)> = (0..10).map(|i| (vec![1.0, 7.0, i as f32], i > 4)).collect();
        let m = fit(&rows);
        assert_eq!(m.dropped(), vec![1]);
        assert!(m.score(&[1.0, 7.0, 3.0]).is_finite());
    }

    #[test]
    fn labels_credit_covered_stragglers_only() {
        let extras = "add(x, y) = add(y, x)\nand(x, y) = and(y, x)\nor(x, y) = or(y, x)\n";
        let log = "RULEMINER 2 stragglers of 9 laws, 1.0s base (0 unproved)\n\
                   RULEMINER label: 1 add(x, y) = add(y, x)\n\
                   RULEMINER label: 0 and(x, y) = and(y, x)\n\
                   RULEMINER label: 1 some(other, law) = served\n";
        let rows = mine_labels(extras, log, "label").unwrap();
        assert_eq!(rows, vec![("add(x, y) = add(y, x)".to_string(), true), ("and(x, y) = and(y, x)".to_string(), false), ("or(x, y) = or(y, x)".to_string(), false)]);
    }

    #[test]
    fn a_log_with_stragglers_and_no_label_lines_is_refused() {
        let old = "RULEMINER 5 stragglers of 9 laws, 1.0s base (0 unproved)\nRULEMINER uncovered: x\n";
        assert!(mine_labels("add(x, y) = add(y, x)\n", old, "label").is_err());
        let none = "RULEMINER 0 stragglers of 9 laws, 1.0s base (0 unproved)\n";
        assert_eq!(mine_labels("add(x, y) = add(y, x)\n", none, "label").unwrap(), vec![("add(x, y) = add(y, x)".to_string(), false)]);
        assert!(mine_labels("add(x, y) = add(y, x)\n", "RULEMINER something else\n", "label").is_err());
    }

    #[test]
    fn the_salt_is_the_arm_folders_number() {
        assert_eq!(salt_of("C:/runs/2026-11-01-v06-dump/s7_A/cold_streams_streams_1_none"), Some(7));
        assert_eq!(salt_of("C:/runs/state/none"), None);
        assert_eq!(salt_of("C:\\runs\\s7_A\\x"), Some(7), "backslash paths");
        assert_eq!(salt_of("C:/runs/s3_old/s9_B/x"), Some(9), "the folder nearest the file wins");
    }

    #[test]
    fn capture_at_k_counts_positives_in_the_top_k() {
        let (order, y) = ([2, 0, 1, 3], [true, false, true, false]);
        assert_eq!(capture_at_k(&order, &y, 2), 2);
        assert_eq!(capture_at_k(&order, &y, 1), 1);
        assert_eq!(capture_at_k(&order, &y, 0), 0);
        assert_eq!(capture_at_k(&order, &y, 99), 2, "k past the order counts the whole order");
        assert_eq!(capture_at_k(&[3, 1], &y, 2), 0, "only the ordered laws count");
    }

    #[test]
    fn random_capture_of_all_positives_is_k() {
        assert_eq!(random_capture(&[true; 10], 4, 1..=200), 4.0);
        assert_eq!(random_capture(&[true; 10], 20, 1..=200), 10.0, "k past the laws counts them all");
        assert_eq!(random_capture(&[false; 10], 4, 1..=200), 0.0);
        let one = random_capture(&[true, false, false, false], 2, 1..=200);
        assert!((one - 0.5).abs() < 0.1, "one positive in four, top two: {one}");
    }

    #[test]
    fn small_order_matches_kept_indices_semantics() {
        let st = |steps: i64, size: i64| PoolLaw { law: p("x", "x"), straggler: true, steps, size, fallbacks: 0, uncovered: false };
        let clean = || PoolLaw { law: p("x", "x"), straggler: false, steps: 0, size: 0, fallbacks: 0, uncovered: false };
        let pool = vec![clean(), st(2, 5), clean(), st(0, 9), st(2, 3), clean()];
        assert_eq!(small_order(&pool, 6), vec![3, 4, 1, 0, 2, 5], "stragglers by (steps, size), then the rest in stream order");
        assert_eq!(small_order(&pool, 4), vec![3, 1, 0, 2], "a slice reads only its first laws");
        let rank = |i: usize| pool[i].straggler.then_some((pool[i].steps, pool[i].size));
        for m in 0..=6 {
            let mut top = small_order(&pool, 6)[..m].to_vec();
            top.sort_unstable();
            assert_eq!(top, super::super::miner::kept_indices(6, 0, m, &rank), "the first {m}");
        }
    }

    #[test]
    fn bootstrap_interval_of_a_constant_positive_sample_excludes_zero() {
        let (lo, hi) = bootstrap_interval(&[3.0; 42], 2000, 7);
        assert!(lo > 0.0 && lo == 3.0 && hi == 3.0, "{lo} {hi}");
        let signs: Vec<f64> = (0..42).map(|i| if i % 2 == 0 { 1.0 } else { -1.0 }).collect();
        let (lo, hi) = bootstrap_interval(&signs, 2000, 7);
        assert!(lo < 0.0 && hi > 0.0, "a mean of zero straddles it: {lo} {hi}");
    }

    #[test]
    fn bootstrap_is_deterministic_for_a_seed() {
        let xs: Vec<f64> = (0..42).map(|i| (i * 37 % 11) as f64 - 3.0).collect();
        assert_eq!(bootstrap_interval(&xs, 2000, 7), bootstrap_interval(&xs, 2000, 7));
        assert_ne!(bootstrap_interval(&xs, 2000, 7), bootstrap_interval(&xs, 2000, 8));
    }

    #[test]
    fn the_gate_needs_both_intervals_and_five_salts() {
        assert!(gate_ok((0.1, 0.3), (0.2, 0.5), 5));
        assert!(!gate_ok((0.0, 0.3), (0.2, 0.5), 7), "d's interval touches zero");
        assert!(!gate_ok((0.1, 0.3), (-0.1, 0.5), 7), "e's interval straddles zero");
        assert!(!gate_ok((0.1, 0.3), (0.2, 0.5), 4), "four salts of seven");
    }

    #[test]
    fn loo_split_never_shares_a_salt() {
        let s = loo_split(&[5, 4, 6, 4]);
        assert_eq!(s, vec![(4, vec![5, 6]), (5, vec![4, 6]), (6, vec![4, 5])], "sorted, repeats collapsed");
        assert!(s.iter().all(|(held, train)| !train.contains(held)));
    }

    const FIVE: [&str; 5] = ["add(x, y) = add(y, x)", "and(x, y) = and(y, x)", "or(x, y) = or(y, x)", "xor(x, y) = xor(y, x)", "add(x, 0) = x"];

    /// Writes one mine under `root/s<salt>_A/cold_streams_streams_1_none/`: a pool dump whose first law is a straggler, the
    /// `laws_extra` file `extras`, one served law and a log crediting the pool's first law.
    fn write_mine(root: &std::path::Path, salt: usize, m: &str, pool: &[&str], extras: &[&str]) {
        let d = root.join(format!("s{salt}_A")).join("cold_streams_streams_1_none");
        std::fs::create_dir_all(&d).unwrap();
        let tsv: String = pool.iter().enumerate().map(|(i, l)| if i == 0 { format!("{i}\t{l}\t1\t2\t9\t0\t0\n") } else { format!("{i}\t{l}\t0\t\t\t\t0\n") }).collect();
        std::fs::write(d.join(format!("dump_{m}_pool.tsv")), tsv).unwrap();
        std::fs::write(d.join(format!("dump_{m}_served.txt")), "sub(y, 0) = y\n").unwrap();
        std::fs::write(d.join(format!("laws_extra_{m}.txt")), extras.join("\n") + "\n").unwrap();
        std::fs::write(d.join(format!("mine_{m}.log")), format!("RULEMINER 1 stragglers of 9 laws, 0.0s base (0 unproved)\nRULEMINER label: 1 {}\n", pool[0])).unwrap();
    }

    fn scratch(tag: &str) -> std::path::PathBuf {
        let root = std::env::temp_dir().join(format!("ctx_scorer_{tag}_{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        root
    }

    #[test]
    fn load_mines_drops_later_duplicates_and_counts_them() {
        let root = scratch("dup");
        write_mine(&root, 4, "0", &FIVE, &FIVE);
        let b = [FIVE[2], FIVE[1], FIVE[3], FIVE[0], FIVE[4]]; // its first two laws repeat salt 4's
        write_mine(&root, 5, "0", &b, &b);
        let (mines, dropped) = load_mines(&[&root.join("s4_A"), &root.join("s5_A")], 3).unwrap();
        assert_eq!((mines.len(), dropped), (2, 2));
        assert_eq!(mines[0].live, vec![true, true, true]);
        assert_eq!(mines[1].live, vec![false, false, true], "the first occurrence (salt 4) stays, later copies go");
        assert_eq!((mines[0].salt, mines[1].salt, mines[0].y.len(), mines[0].pool.len(), mines[0].served.len()), (4, 5, 3, 5, 1));
        assert_eq!(mines[0].y, vec![true, false, false], "the log credits the pool's first law");
    }

    #[test]
    fn load_mines_stops_when_the_first_n_pool_laws_do_not_match_laws_extra() {
        let root = scratch("mismatch");
        let swapped = [FIVE[1], FIVE[0], FIVE[2], FIVE[3], FIVE[4]];
        write_mine(&root, 4, "0", &FIVE, &swapped);
        let err = load_mines(&[&root.join("s4_A")], 3).err().expect("a refusal");
        assert!(err.contains("laws_extra"), "{err}");
    }

    #[test]
    fn load_mines_stops_on_a_repeat_inside_one_mines_own_file() {
        let root = scratch("repeat");
        let twice = [FIVE[0], FIVE[1], FIVE[0], FIVE[3], FIVE[4]];
        write_mine(&root, 4, "0", &twice, &twice);
        let err = load_mines(&[&root.join("s4_A")], 3).err().expect("a refusal");
        assert!(err.contains("repeat"), "{err}");
    }

    #[test]
    fn load_mines_stops_when_a_credited_law_is_no_straggler() {
        let root = scratch("credit");
        write_mine(&root, 4, "0", &FIVE, &FIVE);
        let log = root.join("s4_A/cold_streams_streams_1_none/mine_0.log");
        std::fs::write(&log, format!("RULEMINER 1 stragglers of 9 laws, 0.0s base (0 unproved)\nRULEMINER label: 1 {}\n", FIVE[1])).unwrap();
        let err = load_mines(&[&root.join("s4_A")], 3).err().expect("a refusal");
        assert!(err.contains("straggler"), "{err}");
    }

    /// A mine of 20 pool laws (the first 15 labelled) built from `seed` alone.
    fn synthetic(salt: usize, seed: usize) -> Mine {
        let nest = |op: &str, d: usize| (0..d).fold("x".to_string(), |s, _| format!("{op}({s}, y)"));
        let pool: Vec<PoolLaw> = (0..20)
            .map(|i| {
                let j = i + seed;
                PoolLaw { law: p(&nest("add", j % 5 + 1), &nest("and", j % 3 + 1)), straggler: j % 3 != 0, steps: (j % 7) as i64, size: (j % 11) as i64, fallbacks: (j % 2) as u64, uncovered: j % 4 == 0 }
            })
            .collect();
        let y: Vec<bool> = (0..15).map(|i| pool[i].straggler && (i + seed) % 4 < 2).collect();
        Mine { salt, pool, served: vec![p("add(x, y)", "add(y, x)")], y, live: vec![true; 15] }
    }

    fn fixture_mines() -> Vec<Mine> {
        (4..=10).flat_map(|s| (0..2).map(move |m| synthetic(s, s * 2 + m))).collect()
    }

    #[test]
    fn q1_header_names_the_context_variant() {
        let mines = fixture_mines();
        let full = q1(&mines, &[3], "context");
        assert!(full.starts_with("context model: context (35 columns)\n"), "{full}");
        let no_g3 = q1(&mines, &[3], NO_G3);
        assert!(no_g3.starts_with("context model: drop group 3 (33 columns)\n"), "{no_g3}");
    }

    #[test]
    fn q1_context_report_apart_from_the_header_equals_the_old_report() {
        let full = q1(&fixture_mines(), &[3, 6], "context");
        let rest = full.split_once('\n').unwrap().1;
        assert_eq!(rest, GOLDEN_Q1);
    }

    #[test]
    fn q1_swapped_context_keeps_every_variant_in_the_ablation() {
        let t = q1(&fixture_mines(), &[3], NO_G3);
        for name in ["context ", "per-law ", "drop group 1 ", "drop group 2 ", "drop group 3 ", "drop per-law "] {
            assert!(t.contains(&format!("{name}")), "{name}: {t}");
        }
    }

    #[test]
    #[should_panic(expected = "bogus")]
    fn q1_refuses_an_unknown_variant() {
        q1(&fixture_mines(), &[3], "bogus");
    }

    const GOLDEN_Q1: &str = r#"Q1 14 mines, 7 salts, slice 15 laws; live stragglers 140, credited 69
salt 4: 2 mines, 20 live stragglers, 9 credited
salt 5: 2 mines, 20 live stragglers, 9 credited
salt 6: 2 mines, 20 live stragglers, 10 credited
salt 7: 2 mines, 20 live stragglers, 11 credited
salt 8: 2 mines, 20 live stragglers, 11 credited
salt 9: 2 mines, 20 live stragglers, 10 credited
salt 10: 2 mines, 20 live stragglers, 9 credited
held-out AUC (mean over salts): context 0.9209, per-law 0.7605
k=3: ceiling 42; capture sums: context 42, per-law 36, small 15, random 14.0, random stragglers-first 20.7
k=3: d (context - per-law) mean 0.429, 95% [0.143, 0.786]; salts above 0: 3/7
k=3: e (context - small) mean 1.929, 95% [1.500, 2.357]; salts above 0: 7/7
k=3: per-salt d [0.0, 0.0, 0.0, 0.0, 1.0, 2.0, 3.0], e [5.0, 6.0, 6.0, 3.0, 2.0, 2.0, 3.0]; salts with both above 0: 3/7; gate not met
k=3: ablation capture sums: context 42, per-law 36, drop group 1 42, drop group 2 38, drop group 3 38, drop per-law 39
k=6: ceiling 69; capture sums: context 58, per-law 47, small 40, random 27.8, random stragglers-first 41.4
k=6: d (context - per-law) mean 0.786, 95% [0.429, 1.143]; salts above 0: 5/7
k=6: e (context - small) mean 1.286, 95% [1.071, 1.571]; salts above 0: 7/7
k=6: per-salt d [1.0, 0.0, 0.0, 2.0, 2.0, 2.0, 4.0], e [2.0, 3.0, 2.0, 3.0, 2.0, 2.0, 4.0]; salts with both above 0: 5/7; gate met
k=6: ablation capture sums: context 58, per-law 47, drop group 1 58, drop group 2 56, drop group 3 55, drop per-law 62
gate met at k in [6]; no room at k in []
verdict FAIL
"#;

    #[test]
    fn q1_is_deterministic_and_reports_both_ks_and_a_verdict() {
        let mines: Vec<Mine> = (4..=10).flat_map(|s| (0..2).map(move |m| synthetic(s, s * 2 + m))).collect();
        let (a, b) = (q1(&mines, &[3, 6], "context"), q1(&mines, &[3, 6], "context"));
        assert_eq!(a, b);
        assert!(a.contains("k=3") && a.contains("k=6") && a.contains("verdict"), "{}", a);
        assert!(a.contains("drop group 1") && a.contains("drop per-law"), "{}", a);
    }
}
