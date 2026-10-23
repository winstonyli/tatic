//! `runs gate <tag> <old exe> <new exe>`: four sweeps in `hc_seq.sh`'s order (new 1, old 1, old 2, new 2), each in a
//! job (`runs::job`), into `<run dir>/<tag>_<arm>_<salt>`, then `runs cmp`. Progress goes to stdout and to
//! `<run dir>/<tag>_gate.txt`, which ends with `<tag> ALL` (the verdict, `<tag> cmp same|differs`, on the line before)
//! or `<tag> FAILED <why>`, so a background gate can be watched for it.

use crate::{append, cmp, job};
use std::path::Path;

/// The sweep's stage (`SWEEP`): the cold mine on the streams (spec §10).
pub const SWEEP: &str = "cold:streams";

/// A sweep's arguments to the church_bv exe.
pub fn sweep_args() -> Vec<String> {
    ["driver::sweep", "--exact", "--ignored", "--nocapture"].map(String::from).to_vec()
}

/// Runs the gate under `dir`; Ok(true) when every sweep succeeded and `cmp` found the sides the same.
pub fn gate(dir: &Path, tag: &str, old: &Path, new: &Path) -> Result<bool, String> {
    let log = dir.join(format!("{tag}_gate.txt"));
    let _ = std::fs::remove_file(&log);
    for arm in ["old", "new"] {
        for s in 1..=2 {
            let d = dir.join(format!("{tag}_{arm}_{s}"));
            if d.exists() {
                std::fs::remove_dir_all(&d).map_err(|e| format!("{}: {e}", d.display()))?;
            }
        }
    }
    let say = |line: String| -> Result<(), String> {
        println!("{line}");
        append(&log, &line)
    };
    for (arm, exe, s) in [("new", new, 1), ("old", old, 1), ("old", old, 2), ("new", new, 2)] {
        let out = dir.join(format!("{tag}_{arm}_{s}"));
        std::fs::create_dir_all(&out).map_err(|e| format!("{}: {e}", out.display()))?;
        let mut spec = job::RunSpec::new(exe, sweep_args(), job::Output::Both(out.join("log.txt")));
        spec.env = [("MACHINE_STATE", "0".to_string()), ("SWEEP_OUT", out.display().to_string()), ("SALT", s.to_string()), ("SWEEP", SWEEP.to_string())]
            .map(|(k, v)| (k.to_string(), v))
            .to_vec();
        match job::run(&spec) {
            Ok(r) if r.exit == 0 => say(format!("{tag} {arm} {s} {:.0}s cpu={:.1}", r.wall, r.job_cpu))?,
            Ok(r) => {
                say(format!("{tag} FAILED {arm} {s} exit={} (see {})", r.exit, out.join("log.txt").display()))?;
                return Ok(false);
            }
            Err(e) => {
                say(format!("{tag} FAILED {arm} {s}: {e}"))?;
                return Ok(false);
            }
        }
    }
    let lines = cmp::cmp(dir, tag);
    for l in &lines {
        println!("{l}");
    }
    let cmp_txt = dir.join(format!("{tag}_cmp.txt"));
    std::fs::write(&cmp_txt, lines.join("\n") + "\n").map_err(|e| format!("{}: {e}", cmp_txt.display()))?;
    let same = cmp::same(&lines);
    say(format!("{tag} cmp {}", if same { "same" } else { "differs" }))?;
    say(format!("{tag} ALL"))?;
    Ok(same)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scratch(name: &str) -> crate::Scratch {
        crate::Scratch::new(&format!("gate-{name}"))
    }

    /// The test exe stands in for a sweep: its harness finds no `driver::sweep` test, exits 0, and prints the same
    /// lines but timings both times.
    #[test]
    fn a_gate_of_two_identical_exes_passes() {
        let d = scratch("pass");
        let exe = std::env::current_exe().unwrap();
        std::fs::create_dir_all(d.join("g_old_1/stale")).unwrap(); // a reused tag starts clean
        assert!(gate(&d, "g", &exe, &exe).unwrap());
        let log = std::fs::read_to_string(d.join("g_gate.txt")).unwrap();
        let lines: Vec<&str> = log.lines().collect();
        assert_eq!(lines.len(), 6, "{log}");
        for (line, want) in lines.iter().zip(["g new 1 ", "g old 1 ", "g old 2 ", "g new 2 "]) {
            assert!(line.starts_with(want) && line.contains(" cpu="), "{log}");
        }
        assert_eq!(&lines[4..], ["g cmp same", "g ALL"]);
        assert!(!d.join("g_old_1/stale").exists());
        assert!(std::fs::read_to_string(d.join("g_cmp.txt")).unwrap().ends_with("cmp done\n"));
    }

    #[test]
    fn a_failed_sweep_stops_the_gate() {
        let d = scratch("fail");
        let exe = std::env::current_exe().unwrap();
        // where.exe rejects the sweep's arguments and exits nonzero
        assert!(!gate(&d, "g", Path::new(r"C:\Windows\System32\where.exe"), &exe).unwrap());
        let log = std::fs::read_to_string(d.join("g_gate.txt")).unwrap();
        assert!(log.lines().last().unwrap().starts_with("g FAILED old 1 exit="), "{log}");
    }
}
