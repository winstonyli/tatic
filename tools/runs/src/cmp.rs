//! `runs cmp <tag>`: compares `<tag>_old_<s>` with `<tag>_new_<s>` (salts 1 and 2) under the run directory, with
//! timings and libtest's harness lines normalized away; a difference that sorting both files removes is reported as
//! "(order only)". Ported line for line from `gate_cmp.py`, its regular expressions kept in byte mode (`(?-u)`), with
//! one intended change: a missing run directory is an `ERROR`, where `os.walk` silently listed no files.

use regex::bytes::{NoExpand, Regex};
use std::path::Path;

/// The 1-based tab-separated field dropped from each stage file (its seconds).
const CUT: [(&str, usize); 3] = [("cold.tsv", 7), ("cold_streams.tsv", 7), ("m.tsv", 5)];

struct Norm {
    time: Regex,
    drop: Regex,
    filtered: Regex,
    run: Regex,
}

impl Norm {
    fn new(tag: &str) -> Norm {
        Norm {
            time: Regex::new(r"(?-u)[0-9]+(\.[0-9]+)?(s|ms|\xC2\xB5s)\b").unwrap(),
            drop: Regex::new(r"(?-u)^(running [0-9]+ tests?|test .* \.\.\. (ok|FAILED|ignored)|test result: .*|)$").unwrap(),
            filtered: Regex::new(r"(?-u)[0-9]+ filtered out").unwrap(),
            run: Regex::new(&format!(r"(?-u){}_(old|new)", regex::escape(tag))).unwrap(),
        }
    }

    /// A file's lines, normalized by its name.
    fn file(&self, path: &Path) -> std::io::Result<Vec<Vec<u8>>> {
        let data = std::fs::read(path)?;
        let name = path.file_name().map(|n| n.to_string_lossy().into_owned()).unwrap_or_default();
        let mut lines: Vec<&[u8]> = data.split(|&b| b == b'\n').collect();
        if lines.last().is_some_and(|l| l.is_empty()) {
            lines.pop();
        }
        if let Some(&(_, field)) = CUT.iter().find(|(n, _)| *n == name) {
            // as `cut`: a line with no tab is kept whole
            return Ok(lines
                .iter()
                .map(|l| {
                    if l.contains(&b'\t') {
                        l.split(|&b| b == b'\t').enumerate().filter(|&(i, _)| i != field - 1).map(|(_, p)| p).collect::<Vec<_>>().join(&b'\t')
                    } else {
                        l.to_vec()
                    }
                })
                .collect());
        }
        if name.ends_with(".txt") || name.ends_with(".log") {
            return Ok(lines
                .iter()
                .filter_map(|l| {
                    let l = self.time.replace_all(l, NoExpand(b"T"));
                    let l = self.run.replace_all(&l, NoExpand(b"RUN"));
                    let l = self.filtered.replacen(&l, 1, NoExpand(b"N filtered out"));
                    (!self.drop.is_match(&l)).then(|| l.into_owned())
                })
                .collect());
        }
        Ok(lines.iter().map(|l| l.to_vec()).collect())
    }
}

/// Every file under `d`, as sorted `./`-relative paths with `/`; an error if `d` itself cannot be listed (`os.walk`
/// skipped unreadable subdirectories, and so does this).
fn files(d: &Path) -> std::io::Result<Vec<String>> {
    let mut out = Vec::new();
    let mut stack = vec![d.to_path_buf()];
    let mut top = true;
    while let Some(dir) = stack.pop() {
        let entries = match std::fs::read_dir(&dir) {
            Ok(e) => e,
            Err(e) if top => return Err(e),
            Err(_) => continue,
        };
        top = false;
        for e in entries.flatten() {
            let p = e.path();
            if p.is_dir() {
                stack.push(p);
            } else {
                out.push(format!("./{}", p.strip_prefix(d).unwrap().to_string_lossy().replace('\\', "/")));
            }
        }
    }
    out.sort();
    Ok(out)
}

/// `gate_cmp.py`'s output for `tag` under `dir`, one entry per line.
pub fn cmp(dir: &Path, tag: &str) -> Vec<String> {
    let norm = Norm::new(tag);
    let mut out = Vec::new();
    for s in 1..=2 {
        let (o, n) = (dir.join(format!("{tag}_old_{s}")), dir.join(format!("{tag}_new_{s}")));
        let (lo, ln) = match (files(&o), files(&n)) {
            (Ok(lo), Ok(ln)) => (lo, ln),
            (Err(e), _) | (_, Err(e)) => {
                out.push(format!("ERROR salt {s}: listing failed ({e})"));
                continue;
            }
        };
        if lo == ln {
            out.push(format!("salt {s}: same file list ({} files)", lo.len()));
        } else {
            out.extend(lo.iter().filter(|f| !ln.contains(f)).map(|f| format!("< {f}")));
            out.extend(ln.iter().filter(|f| !lo.contains(f)).map(|f| format!("> {f}")));
        }
        for f in &lo {
            let (a, b) = match (norm.file(&o.join(&f[2..])), norm.file(&n.join(&f[2..]))) {
                (Ok(a), Ok(b)) => (a, b),
                (Err(e), _) | (_, Err(e)) => {
                    out.push(format!("ERROR salt {s}: normalizing {f} failed ({e})"));
                    continue;
                }
            };
            if a == b {
                continue;
            }
            let (mut sa, mut sb) = (a, b);
            sa.sort();
            sb.sort();
            out.push(if sa == sb { format!("DIFF salt {s} {f} (order only)") } else { format!("DIFF salt {s} {f}") });
        }
    }
    out.push("cmp done".into());
    out
}

/// Whether `cmp`'s lines say the sides are the same: nothing but `salt <s>: same file list (..)` and `cmp done`. So
/// `DIFF`, `(order only)`, `ERROR`, `< f` and `> f` all count as a difference.
pub fn same(lines: &[String]) -> bool {
    lines.iter().all(|l| l == "cmp done" || (l.starts_with("salt ") && l.contains(": same file list (")))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scratch(name: &str) -> crate::Scratch {
        crate::Scratch::new(&format!("cmp-{name}"))
    }

    fn write(d: &Path, f: &str, s: &str) {
        let p = d.join(f);
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(p, s).unwrap();
    }

    /// gate_cmp_check.sh's four files on two salts, with its exact expected output.
    #[test]
    fn gate_cmp_check_cases() {
        let k = scratch("check");
        for s in 1..=2 {
            let (o, n) = (k.join(format!("t_old_{s}")), k.join(format!("t_new_{s}")));
            write(&o, "same.txt", "a\nb\n");
            write(&n, "same.txt", "a\nb\n");
            write(&o, "order.txt", "a\nb\n");
            write(&n, "order.txt", "b\na\n");
            write(&o, "changed.txt", "a\n");
            write(&n, "changed.txt", "c\n");
            write(&o, "time.log", "took 1.5s\n");
            write(&n, "time.log", "took 2.25s\n");
        }
        let want = "salt 1: same file list (4 files)\nDIFF salt 1 ./changed.txt\nDIFF salt 1 ./order.txt (order only)\n\
                    salt 2: same file list (4 files)\nDIFF salt 2 ./changed.txt\nDIFF salt 2 ./order.txt (order only)\ncmp done";
        let got = cmp(&k, "t");
        assert_eq!(got.join("\n"), want);
        assert!(!same(&got));
    }

    #[test]
    fn a_file_only_on_one_side_is_listed() {
        let k = scratch("sides");
        for s in 1..=2 {
            write(&k.join(format!("t_old_{s}")), "a.txt", "x\n");
            write(&k.join(format!("t_new_{s}")), "a.txt", "x\n");
        }
        write(&k.join("t_old_1"), "gone.txt", "x\n");
        let got = cmp(&k, "t");
        assert_eq!(got[0], "< ./gone.txt");
        assert!(got[1].starts_with("ERROR salt 1: normalizing ./gone.txt failed ("), "{got:?}");
        assert!(!same(&got));
    }

    /// A file only the new side has prints just `> f`, which a check for DIFF alone would miss.
    #[test]
    fn a_new_file_alone_fails_the_verdict() {
        let k = scratch("newonly");
        for s in 1..=2 {
            write(&k.join(format!("t_old_{s}")), "a.txt", "x\n");
            write(&k.join(format!("t_new_{s}")), "a.txt", "x\n");
            write(&k.join(format!("t_new_{s}")), "extra.txt", "x\n");
        }
        let got = cmp(&k, "t");
        assert_eq!(got, ["> ./extra.txt", "> ./extra.txt", "cmp done"]);
        assert!(!same(&got));
    }

    #[test]
    fn stage_files_drop_their_seconds_and_keep_lines_without_tabs() {
        let k = scratch("cut");
        for s in 1..=2 {
            write(&k.join(format!("t_old_{s}")), "cold.tsv", "cmp3d\t7-1\tfrom_none\t10\t1,2\t3\t5\tfalse\nheader\n");
            write(&k.join(format!("t_new_{s}")), "cold.tsv", "cmp3d\t7-1\tfrom_none\t10\t1,2\t3\t9\tfalse\nheader\n");
        }
        assert!(same(&cmp(&k, "t")));
        write(&k.join("t_new_1"), "cold.tsv", "cmp3d\t7-1\tfrom_none\t10\t1,2\t3\t5\tfalse\nheader2\n");
        assert!(cmp(&k, "t").contains(&"DIFF salt 1 ./cold.tsv".to_string()));
    }

    #[test]
    fn logs_normalize_timings_run_names_and_harness_lines() {
        let k = scratch("logs");
        for s in 1..=2 {
            write(&k.join(format!("t_old_{s}")), "log.txt", "running 3 tests\nout t_old_1/x in 1.5ms\ntest a ... ok\n2 filtered out\nµ 3µs\n");
            write(&k.join(format!("t_new_{s}")), "log.txt", "out t_new_1/x in 20ms\n7 filtered out\nµ 9µs\ntest result: ok. 1 passed\n");
        }
        assert!(same(&cmp(&k, "t")), "{:?}", cmp(&k, "t"));
    }

    /// gate_cmp.py's os.walk ignored a missing directory and printed "same file list (0 files)"; here it is an error.
    #[test]
    fn a_missing_run_is_an_error() {
        let k = scratch("missing");
        write(&k.join("t_old_1"), "a.txt", "x\n");
        let got = cmp(&k, "t");
        assert!(got[0].starts_with("ERROR salt 1: listing failed ("), "{got:?}");
        assert!(!same(&got));
    }
}
