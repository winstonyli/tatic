// External and hand-written corpora: fixed lists of named expressions in the loop's term language (`docs/corpora/<source>/`),
// and the measurement of what the class table and the rewriter do to them.
use crate::classes::Classes;
use crate::job::{Job, Setup};
use crate::rewrite::{parse_rules, parse_term, rewrite, Node, Term};

/// One corpus case: a name and an expression over the variables `x`, `y`, `z`.
pub struct Case {
    pub name: String,
    pub term: Term,
}

/// The cases of `name<TAB>term` lines (`show` syntax); blank lines and `#` comments are skipped. A line that is not two
/// tab-separated fields, or a repeated name, is an error naming its line.
pub fn read_cases(text: &str) -> Result<Vec<Case>, String> {
    let mut cases: Vec<Case> = Vec::new();
    for (i, l) in text.lines().enumerate().filter(|(_, l)| !l.trim().is_empty() && !l.starts_with('#')) {
        let line = i + 1;
        let fields: Vec<&str> = l.split('\t').collect();
        let [name, term] = fields[..] else { return Err(format!("line {line}: want `name<TAB>term`, got {} field(s)", fields.len())) };
        if cases.iter().any(|c| c.name == name) {
            return Err(format!("line {line}: duplicate name `{name}`"));
        }
        cases.push(Case { name: name.to_string(), term: parse_term(term) });
    }
    Ok(cases)
}

/// Operators in a term.
pub fn ops(t: &Term) -> usize {
    match *t.node() {
        Node::Op(_, a, b) => 1 + ops(&a) + ops(&b),
        _ => 0,
    }
}

/// What the table and the rewriter do to one case.
#[derive(Debug, PartialEq)]
pub struct Row {
    pub name: String,
    pub before: usize,
    /// Operators after `Classes::canonical`, and whether that term differs from the case (it can differ at equal size).
    pub table: usize,
    pub table_changed: bool,
    /// Operators after a width-4 `rewrite` under the base rules plus the mined ones.
    pub rules: usize,
}

pub fn measure(cases: &[Case], mined: Vec<(Term, Term)>) -> Vec<Row> {
    let classes = Classes::get();
    let job = &mut Job::new(Setup::process());
    cases
        .iter()
        .map(|c| {
            let (rw, _) = job.with_mined(mined.clone(), |j| rewrite(j, &c.term, 4, 3));
            let canon = classes.canonical(&c.term);
            Row { name: c.name.clone(), before: ops(&c.term), table: ops(&canon), table_changed: canon != c.term, rules: ops(&rw) }
        })
        .collect()
}

/// A path from the environment, relative to the repo root (two levels above the package directory, whatever the working
/// directory; `cargo test` runs from the package directory); an absolute path is unchanged.
fn from_repo_root(p: String) -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..").join(p)
}

/// Prints the per-case and total counts of a corpus file (env `CORPUS`; optional mined rules in `CORPUS_RULES`).
#[test]
#[ignore]
fn corpus_report() {
    let path = from_repo_root(std::env::var("CORPUS").expect("CORPUS=docs/corpora/<source>/cases.txt"));
    let cases = read_cases(&std::fs::read_to_string(&path).unwrap()).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    let mined = std::env::var("CORPUS_RULES").map(|p| parse_rules(&std::fs::read_to_string(from_repo_root(p)).unwrap())).unwrap_or_default();
    tatic_kernel::scoped(|| {
        let m = measure(&cases, mined.clone());
        for r in &m {
            println!("CORPUS {}: {} ops | table {} | rules {}", r.name, r.before, r.table, r.rules);
        }
        let sum = |f: fn(&Row) -> usize| m.iter().map(f).sum::<usize>();
        let changed = m.iter().filter(|r| r.table_changed).count();
        println!("CORPUS total: cases={} ops={} table_changed={changed} table_ops={} rules_ops={} mined_rules={}", m.len(), sum(|r| r.before), sum(|r| r.table), sum(|r| r.rules), mined.len());
    });
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cases_parse_and_bad_lines_name_their_line() {
        let ok = read_cases("# comment\n\nswap\txor(xor(x, y), y)\nnot\tsub(-1, x)\n").unwrap();
        assert_eq!(ok.iter().map(|c| c.name.as_str()).collect::<Vec<_>>(), ["swap", "not"]);
        assert_eq!(ops(&ok[0].term), 2);
        for (text, line) in [("a\tx\nb x\n", "line 2"), ("a\tx\nb\tx\ty\n", "line 2"), ("a\tx\na\ty\n", "line 2")] {
            let e = read_cases(text).err().expect(text);
            assert!(e.contains(line), "{e}");
        }
    }

    #[test]
    fn the_table_shrinks_a_swap_xor_leftover() {
        tatic_kernel::scoped(|| {
            let cases = read_cases("swap\txor(xor(x, y), y)\nplain\tadd(x, y)\n").unwrap();
            let m = measure(&cases, vec![]);
            assert_eq!(m[0], Row { name: "swap".into(), before: 2, table: 0, table_changed: true, rules: 0 });
            assert_eq!(m[1], Row { name: "plain".into(), before: 1, table: 1, table_changed: false, rules: 1 });
        });
    }

    #[test]
    fn the_hand_written_corpus_reproduces_the_probe_counts() {
        tatic_kernel::scoped(|| {
            let cases = read_cases(include_str!("../../../../docs/corpora/hd-own/cases.txt")).unwrap();
            let m = measure(&cases, vec![]);
            let (before, table, rules) = m.iter().fold((0, 0, 0), |a, r| (a.0 + r.before, a.1 + r.table, a.2 + r.rules));
            let changed = m.iter().filter(|r| r.table_changed).count();
            // the 2026-10-31 probe: 80 operators, the table leaves 54 (26 saved) and changes 17; base rules alone also leave 54
            assert_eq!((cases.len(), before, table, changed, rules), (25, 80, 54, 17, 54));
        });
    }

    #[test]
    fn the_souper_corpus_reproduces_its_source_counts() {
        tatic_kernel::scoped(|| {
            let cases = read_cases(include_str!("../../../../docs/corpora/souper/cases.txt")).unwrap();
            let m = measure(&cases, vec![]);
            let (before, table, rules) = m.iter().fold((0, 0, 0), |a, r| (a.0 + r.before, a.1 + r.table, a.2 + r.rules));
            let changed = m.iter().filter(|r| r.table_changed).count();
            assert_eq!((cases.len(), before, table, changed, rules), (14, 52, 42, 10, 42));
        });
    }

    #[test]
    fn an_lt_word_under_a_bitwise_operator_is_measured() {
        tatic_kernel::scoped(|| {
            let cases = read_cases("ule	xor(lt(and(x, y), xor(x, y)), sub(0, -1))
mask	and(x, lt(y, z))
").unwrap();
            let m = measure(&cases, vec![]);
            assert!(m.iter().all(|r| r.table <= r.before && r.rules <= r.before), "{m:?}");
        });
    }
}
