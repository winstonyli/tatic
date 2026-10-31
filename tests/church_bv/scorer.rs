//! The extras scorer (docs/superpowers/specs/2026-10-31-learned-proposer-design.md): a logistic regression over counts of a
//! law's two sides that orders candidate laws for a mine. It only orders; the filter and the kernel judge every law.
use super::*;
use crate::classes::OPS;
use super::rewrite::Node;



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
        .ok_or("no `RULEMINER N stragglers of M laws` line (a crashed or foreign log)")?;
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

    #[test]
    fn rows_split_by_salt() {
        let tsv = "4\t1\tadd(x, y) = add(y, x)\n5\t0\tand(x, y) = and(y, x)\n4\t0\tor(x, y) = or(y, x)\n";
        let (a, b) = split_rows(tsv, &[4], &[5]);
        assert_eq!((a.len(), b.len()), (2, 1));
        assert!(a[0].1 && !a[1].1 && !b[0].1);
    }

    #[test]
    fn a_log_without_a_stragglers_count_is_refused() {
        assert!(mine_labels("add(x, y) = add(y, x)\n", "RULEMINER something else\n").is_err());
    }

    #[test]
    fn auc_with_a_mixed_tie_group() {
        // positives 1, 2; negatives 1, 0: pairs (1,1) tie 0.5, (1,0) 1, (2,1) 1, (2,0) 1 -> 3.5 / 4
        assert_eq!(auc(&[(1.0, true), (1.0, false), (2.0, true), (0.0, false)]), 0.875);
    }

    #[test]
    fn a_fitted_scorer_round_trips_through_text() {
        let rows: Vec<([f32; F], bool)> = (0..20).map(|i| { let mut f = [0f32; F]; f[0] = 1.0; f[1] = i as f32; f[2] = (i % 3) as f32; (f, i > 9) }).collect();
        let s = fit(&rows);
        assert_ne!(s.mean[1], 0.0);
        assert_eq!(Scorer::from_text(&s.to_text()).unwrap(), s);
    }
}
