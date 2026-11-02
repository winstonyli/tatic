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

/// The `WIDTH` columns of every pool law, in pool order.
pub fn rows(pool: &[PoolLaw], served: &[(Term, Term)]) -> Vec<Vec<f32>> {
    let (g1, g2, g3) = (group1(pool), group2(pool, served), group3(pool));
    (0..pool.len()).map(|i| per_law_features(&pool[i].law).iter().chain(&g1[i]).chain(&g2[i]).chain(&g3[i]).copied().collect()).collect()
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
}
