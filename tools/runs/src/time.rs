//! `runs time`: alternating timing of two or more arms in rounds, each run measured by `runs::job`. Before each round
//! it waits for a quiet machine, and it counts only rounds no one else loaded: `scripts/quiet_ab`'s rules, which it
//! replaced, with `cpu_ab.ps1`'s, `cpu_arms.ps1`'s and `hc_rounds.ps1`'s experiments as presets.

use crate::{append, job, state};
use regex::Regex;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

#[derive(Clone, Debug, PartialEq)]
pub struct Arm {
    pub name: String,
    pub env: Vec<(String, String)>,
    pub exe: String,
    pub args: Vec<String>,
}

/// `--grep NAME=REGEX`: the first capture group of the last output line REGEX matches becomes column NAME.
pub struct Grep {
    pub name: String,
    pub re: Regex,
}

pub struct Timing {
    pub dir: PathBuf,
    pub rounds: usize,
    pub max_hours: f64,
    pub others: Vec<String>,
    pub foreign_max: f64,
    pub quiet_secs: u64,
    pub keep_dirty: bool,
    pub max_rounds: usize,
    pub greps: Vec<Grep>,
    pub affinity: usize,
    pub priority: job::Priority,
    pub arms: Vec<Arm>,
}

/// One arm from its words: `<name> [VAR=val]... <exe> <args>...`.
pub fn parse_arm(words: &[String]) -> Result<Arm, String> {
    let (name, rest) = words.split_first().ok_or("an empty arm")?;
    let (env, cmd) = crate::split_env(rest);
    let (exe, args) = cmd.split_first().ok_or_else(|| format!("arm {name} has no exe"))?;
    Ok(Arm { name: name.clone(), env, exe: exe.clone(), args: args.to_vec() })
}

pub fn parse_grep(s: &str) -> Result<Grep, String> {
    let (name, re) = s.split_once('=').ok_or_else(|| format!("--grep {s}: expected NAME=REGEX"))?;
    let re = Regex::new(re).map_err(|e| format!("--grep {name}: {e}"))?;
    if re.captures_len() < 2 {
        return Err(format!("--grep {name}: the regex needs a capture group"));
    }
    Ok(Grep { name: name.to_string(), re })
}

/// The first capture of the last line of `text` that `re` matches (`cpu_ab.ps1` took the first line; it matters only
/// if a line repeats). `lines` drops a CR before each LF.
pub fn grep_last(re: &Regex, text: &str) -> Option<String> {
    text.lines().rev().find_map(|l| re.captures(l)).and_then(|c| c.get(1)).map(|m| m.as_str().to_string())
}

/// The arms' order in round `r` (from 1): rotated left by r - 1, so two arms go AB, BA, AB, ... as `ab.sh` and
/// `hc_rounds.ps1` did, and more arms rotate as `cpu_arms.ps1` did.
pub fn order(arms: usize, r: usize) -> Vec<usize> {
    (0..arms).map(|i| (i + r - 1) % arms).collect()
}

/// `s` with `{r}`, `{arm}` and `{dir}` replaced.
pub fn subst(s: &str, r: usize, arm: &str, dir: &Path) -> String {
    s.replace("{r}", &r.to_string()).replace("{arm}", arm).replace("{dir}", &dir.display().to_string())
}

/// `--sweep`: `hc_rounds.ps1`'s experiment, full salt-1 sweeps on normal pages, with the sweep's machine-state checks
/// moved out of the job (`runs` records the machine itself).
pub fn sweep_arms(old: &str, new: &str) -> Vec<Arm> {
    let env: Vec<(String, String)> = [("MACHINE_STATE", "0"), ("SALT", "1"), ("SWEEP", crate::gate::SWEEP), ("MIMALLOC_ALLOW_LARGE_OS_PAGES", "0"), ("SWEEP_OUT", "{dir}/{arm}.{r}")]
        .map(|(k, v)| (k.to_string(), v.to_string()))
        .to_vec();
    [("old", old), ("new", new)].map(|(name, exe)| Arm { name: name.into(), env: env.clone(), exe: exe.into(), args: crate::gate::sweep_args() }).to_vec()
}

/// `--pcs`: `proof_cost_split` on the held-out band 11 (1000 laws) with no mined rules (`<root>` is the checkout). With one
/// exe the arms come from `arm_envs` (`NAME:VAR=val,...`; `NAME:` for none); with two exes they are `old` and `new`.
pub fn pcs_arms(root: &Path, exes: &[String], arm_envs: &[String]) -> Result<Vec<Arm>, String> {
    let base = vec![
        ("CHECK_LAWFILE".to_string(), root.join(r"tests\church_bv\held_11.txt").display().to_string()),
    ];
    let args: Vec<String> = ["search::proof_cost_split", "--exact", "--ignored", "--nocapture"].map(String::from).to_vec();
    let arm = |name: &str, exe: &str, extra: Vec<(String, String)>| Arm { name: name.into(), env: [base.clone(), extra].concat(), exe: exe.into(), args: args.clone() };
    match (exes, arm_envs.is_empty()) {
        ([old, new], true) => Ok(vec![arm("old", old.as_str(), vec![]), arm("new", new.as_str(), vec![])]),
        ([exe], false) => arm_envs
            .iter()
            .map(|a| {
                let (name, vars) = a.split_once(':').ok_or_else(|| format!("--arm-env {a}: expected NAME:VAR=val,..."))?;
                let env = vars
                    .split(',')
                    .filter(|v| !v.is_empty())
                    .map(|v| v.split_once('=').map(|(k, x)| (k.to_string(), x.to_string())).ok_or_else(|| format!("--arm-env {a}: {v} is not VAR=val")))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(arm(name, exe.as_str(), env))
            })
            .collect(),
        _ => Err("--pcs takes <exe> with --arm-env options, or <old exe> <new exe> without".into()),
    }
}

/// `proof_cost_split`'s `COST rule-proofs: n=.. build=..ms check=..ms ...` line (search.rs), whose build and check
/// times `cpu_ab.ps1` printed.
pub fn pcs_greps() -> Vec<Grep> {
    Vec::from(["build", "check"].map(|f| parse_grep(&format!(r"{f}=^COST rule-proofs:.* {f}=([0-9.]+)ms")).unwrap()))
}

struct Row {
    arm: String,
    round: usize,
    pos: usize,
    start: u64,
    r: job::RunResult,
    rtp: Option<bool>,
    clean: bool,
    greps: Vec<Option<String>>,
}

fn tsv_header(greps: &[Grep]) -> String {
    let mut h = "arm\tround\tposition\tstart\twall_s\tjobcpu_s\tprocs\tstragglers\tpeakproc_mb\tpeakjob_mb\tpeakws_mb\tother_pct\tothers\trtp\texit\tclean".to_string();
    for g in greps {
        h.push('\t');
        h.push_str(&g.name);
    }
    h
}

fn tsv_row(w: &Row) -> String {
    let r = &w.r;
    let mut s = format!(
        "{}\t{}\t{}\t{}\t{:.2}\t{:.3}\t{}\t{}\t{:.0}\t{:.0}\t{:.0}\t{:.1}\t{}\t{}\t{}\t{}",
        w.arm, w.round, w.pos, w.start, r.wall, r.job_cpu, r.procs, r.stragglers, r.peak_proc_mb, r.peak_job_mb, r.peak_ws_mb, r.other_pct, r.others, state::rtp_text(w.rtp), r.exit, w.clean
    );
    for g in &w.greps {
        s.push('\t');
        s.push_str(g.as_deref().unwrap_or(""));
    }
    s
}

fn median(mut v: Vec<f64>) -> f64 {
    v.sort_by(f64::total_cmp);
    match v.len() {
        0 => f64::NAN,
        n if n % 2 == 1 => v[n / 2],
        n => (v[n / 2 - 1] + v[n / 2]) / 2.0,
    }
}

/// Per arm over `rounds`: median and best of job CPU, wall and each grep column. Then each arm against the first,
/// paired by round: the differences, their median, how many rounds it won (lower wins), and the mean over the two
/// orders (the mean of the rounds it ran first and the mean of those it ran second, halved), which cancels a cost of
/// running second (2026-10-19: about 3% in the church_bv sweep) that the won count reads as a gain or a loss.
fn summary(rows: &[Row], arms: &[String], greps: &[String], rounds: &[usize]) -> String {
    let names: Vec<String> = ["jobcpu".to_string(), "wall".to_string()].into_iter().chain(greps.iter().cloned()).collect();
    let value = |w: &Row, m: usize| -> Option<f64> {
        match m {
            0 => Some(w.r.job_cpu),
            1 => Some(w.r.wall),
            _ => w.greps.get(m - 2)?.as_deref()?.parse().ok(),
        }
    };
    let get = |arm: &str, r: usize, m: usize| rows.iter().find(|w| w.arm == arm && w.round == r).and_then(|w| value(w, m));
    let pos = |arm: &str, r: usize| rows.iter().find(|w| w.arm == arm && w.round == r).map(|w| w.pos);
    let mut s = format!("{} rounds: {:?}\n", rounds.len(), rounds);
    for arm in arms {
        write!(s, "{arm}:").unwrap();
        for (m, name) in names.iter().enumerate() {
            let v: Vec<f64> = rounds.iter().filter_map(|&r| get(arm, r, m)).collect();
            let best = v.iter().copied().fold(f64::INFINITY, f64::min);
            write!(s, " {name} median={:.3} best={best:.3}", median(v)).unwrap();
        }
        s.push('\n');
    }
    if let Some((first, rest)) = arms.split_first() {
        for arm in rest {
            for (m, name) in names.iter().enumerate() {
                let d: Vec<(usize, f64)> = rounds.iter().filter_map(|&r| Some((r, get(arm, r, m)? - get(first, r, m)?))).collect();
                let wins = d.iter().filter(|(_, x)| *x < 0.0).count();
                let list: Vec<String> = d.iter().map(|(r, x)| format!("r{r} {x:+.3}")).collect();
                let med = median(d.iter().map(|x| x.1).collect());
                writeln!(s, "{arm} - {first} {name}: median {med:+.3}, won {wins}/{}: {}", d.len(), list.join(", ")).unwrap();
                // the won count mixes the order effect in; the mean over the two orders cancels it
                let ran_first = |r: usize| Some(pos(arm, r)? < pos(first, r)?);
                let mean_of = |f: bool| {
                    let v: Vec<f64> = d.iter().filter(|(r, _)| ran_first(*r) == Some(f)).map(|x| x.1).collect();
                    (v.iter().sum::<f64>() / v.len() as f64, v.len())
                };
                let ((a, na), (b, nb)) = (mean_of(true), mean_of(false));
                writeln!(s, "{arm} - {first} {name} over the two orders: {:+.3} ({arm} first {a:+.3} in {na}, second {b:+.3} in {nb}), running second {:+.3}", (a + b) / 2.0, (b - a) / 2.0).unwrap();
            }
        }
    }
    s
}

/// Waits until the last `quiet_secs` of 2 s samples all had the machine under `foreign_max`% busy and no others'
/// process: nothing of ours runs meanwhile, so all of the load is others'. Err(why) at the deadline or on `stop`.
fn wait_quiet(t: &Timing, deadline: Instant, stop: &Path) -> Result<(), String> {
    let check = || {
        if Instant::now() >= deadline {
            Err("deadline".to_string())
        } else if stop.exists() {
            Err("stop".to_string())
        } else {
            Ok(())
        }
    };
    check()?;
    let need = (t.quiet_secs / 2) as usize;
    let (mut good, mut prev) = (0, state::times());
    while good < need {
        std::thread::sleep(Duration::from_secs(2)); // one sample
        check()?;
        let now = state::times();
        let quiet = now.load_since(&prev) < t.foreign_max && job::count_others(&t.others) == 0;
        prev = now;
        good = if quiet { good + 1 } else { 0 };
    }
    Ok(())
}

fn log_state(dir: &Path, when: &str) -> Result<(), String> {
    let line = format!("{when}: {}", state::line());
    println!("{line}");
    append(&dir.join("state.txt"), &line)
}

/// What the rounds produced so far, kept when they end on an error.
#[derive(Default)]
struct Progress {
    rows: Vec<Row>,
    round: usize,
    clean_rounds: Vec<usize>,
}

/// Arm names become file names (`<arm>.<round>.out.txt`), so they are plain name parts, and distinct even ignoring case
/// (Windows file names ignore it).
fn check_arm_names(arms: &[Arm]) -> Result<(), String> {
    for (i, a) in arms.iter().enumerate() {
        if a.name.is_empty() || !a.name.bytes().all(|c| c.is_ascii_alphanumeric() || b"_.-".contains(&c)) {
            return Err(format!("arm name {:?}: use letters, digits, '_', '.' and '-' (it names the arm's files)", a.name));
        }
        if arms[..i].iter().any(|b| b.name.eq_ignore_ascii_case(&a.name)) {
            return Err(format!("arm {} appears twice; arms need distinct names, case aside", a.name));
        }
    }
    Ok(())
}

/// Runs the timing; Ok(true) when a run or a write of its records failed (`runs time` then exits 1). Err only when it
/// refuses to start (nothing written); once the directory exists every ending, failures included, writes `done.txt`
/// (`done <clean rounds>/<rounds> <why it stopped>`), so a watcher polling for it always sees one.
pub fn time(t: &Timing) -> Result<bool, String> {
    let dir = &t.dir;
    check_arm_names(&t.arms)?;
    let deadline = Duration::try_from_secs_f64(t.max_hours * 3600.0)
        .ok()
        .and_then(|d| Instant::now().checked_add(d))
        .ok_or_else(|| format!("--max-hours {}: give a number of hours, 0 or more", t.max_hours))?;
    let tsv = dir.join("runs.tsv");
    if tsv.exists() {
        return Err(format!("{} already holds runs.tsv; use a fresh directory", dir.display()));
    }
    std::fs::create_dir_all(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    let stop = dir.join("stop");
    let _ = std::fs::remove_file(&stop);
    let _ = std::fs::remove_file(dir.join("done.txt"));
    let mut p = Progress::default();
    let (mut why, mut failed) = rounds(t, &tsv, &stop, deadline, &mut p).unwrap_or_else(|e| (e, true));
    if let Err(e) = finish(t, &p) {
        why = format!("{why}; {e}");
        failed = true;
    }
    let line = format!("done {}/{} {why}", p.clean_rounds.len(), p.round);
    std::fs::write(dir.join("done.txt"), format!("{line}\n")).map_err(|e| format!("{}: {e}", dir.display()))?;
    println!("{line}");
    Ok(failed)
}

/// The rounds: Ok holds why they stopped and whether a run failed.
fn rounds(t: &Timing, tsv: &Path, stop: &Path, deadline: Instant, p: &mut Progress) -> Result<(String, bool), String> {
    let dir = &t.dir;
    append(tsv, &tsv_header(&t.greps))?;
    log_state(dir, "start")?;
    let mut rtp_seen: Option<Option<bool>> = None;
    Ok('timing: loop {
        let counted = if t.keep_dirty { p.round } else { p.clean_rounds.len() };
        if counted >= t.rounds {
            break (if t.keep_dirty { "all rounds" } else { "clean rounds" }.to_string(), false);
        }
        if !t.keep_dirty && p.round >= t.max_rounds {
            break (format!("max-rounds {}", t.max_rounds), false);
        }
        if let Err(why) = wait_quiet(t, deadline, stop) {
            break (why, false);
        }
        p.round += 1;
        let round = p.round;
        let rtp = state::rtp();
        if rtp_seen.is_some_and(|seen| seen != rtp) {
            println!("rtp changed to {}", state::rtp_text(rtp));
        }
        rtp_seen = Some(rtp);
        let mut all_clean = true;
        for (pos, &i) in order(t.arms.len(), round).iter().enumerate() {
            let a = &t.arms[i];
            let label = format!("{}.{round}", a.name);
            let out = dir.join(format!("{label}.out.txt"));
            let sub = |s: &str| subst(s, round, &a.name, dir);
            let mut spec = job::RunSpec::new(sub(&a.exe), a.args.iter().map(|x| sub(x)).collect(), job::Output::Split(out.clone(), dir.join(format!("{label}.err.txt"))));
            spec.env = a.env.iter().map(|(k, v)| (k.clone(), sub(v))).collect();
            spec.affinity = t.affinity;
            spec.priority = t.priority;
            spec.others = t.others.clone();
            let start = SystemTime::now().duration_since(UNIX_EPOCH).map_or(0, |d| d.as_secs());
            let r = match job::run(&spec) {
                Ok(r) => r,
                Err(e) => break 'timing (format!("{label}: {e}"), true),
            };
            let text = String::from_utf8_lossy(&std::fs::read(&out).unwrap_or_default()).into_owned();
            let greps = t.greps.iter().map(|g| grep_last(&g.re, &text)).collect();
            let clean = job::clean(r.exit, r.other_pct, r.others, t.foreign_max);
            println!("{}", crate::result_line(&label, &r, rtp));
            let row = Row { arm: a.name.clone(), round, pos: pos + 1, start, r, rtp, clean, greps };
            append(tsv, &tsv_row(&row))?;
            all_clean &= clean;
            let exit = row.r.exit;
            p.rows.push(row);
            if exit != 0 {
                // a failing run would only fail again
                break 'timing (format!("{label} failed (exit {exit}); see {}", out.display()), true);
            }
        }
        if all_clean {
            p.clean_rounds.push(round);
        }
        println!("round {round} done, clean rounds {}", p.clean_rounds.len());
    })
}

/// After the rounds: the end state and `summary.txt`.
fn finish(t: &Timing, p: &Progress) -> Result<(), String> {
    log_state(&t.dir, "end")?;
    let names: Vec<String> = t.arms.iter().map(|a| a.name.clone()).collect();
    let gnames: Vec<String> = t.greps.iter().map(|g| g.name.clone()).collect();
    let mut s = format!("clean {}", summary(&p.rows, &names, &gnames, &p.clean_rounds));
    if t.keep_dirty {
        let all: Vec<usize> = (1..=p.round).collect();
        s += &format!("all {}", summary(&p.rows, &names, &gnames, &all));
    }
    let path = t.dir.join("summary.txt");
    std::fs::write(&path, &s).map_err(|e| format!("{}: {e}", path.display()))?;
    print!("{s}");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scratch(name: &str) -> crate::Scratch {
        crate::Scratch::new(&format!("time-{name}"))
    }

    fn done_line(d: &Path) -> String {
        std::fs::read_to_string(d.join("done.txt")).unwrap().trim_end().to_string()
    }

    fn where_arm(name: &str, arg: &str) -> Arm {
        Arm { name: name.into(), env: vec![], exe: r"C:\Windows\System32\where.exe".into(), args: vec![arg.into()] }
    }

    /// A timing that never waits and finds every run dirty (nothing is under 0%).
    fn timing(dir: PathBuf, arms: Vec<Arm>) -> Timing {
        Timing {
            dir,
            rounds: 1,
            max_hours: 0.1,
            others: job::default_others(),
            foreign_max: 0.0,
            quiet_secs: 0,
            keep_dirty: false,
            max_rounds: 2,
            greps: vec![parse_grep("dir=(System32)").unwrap()],
            affinity: 0xFFF,
            priority: job::Priority::BelowNormal,
            arms,
        }
    }

    #[test]
    fn rounds_rotate_left() {
        let names = |r| order(3, r).iter().map(|&i| b"ABC"[i] as char).collect::<String>();
        assert_eq!([names(1), names(2), names(3), names(4)], ["ABC", "BCA", "CAB", "ABC"]);
        assert_eq!([order(2, 1), order(2, 2)], [vec![0, 1], vec![1, 0]]);
    }

    #[test]
    fn an_arm_is_a_name_environment_and_command() {
        let w: Vec<String> = "old MACHINE_STATE=0 X= bf.exe a B=1".split(' ').map(String::from).collect();
        let a = parse_arm(&w).unwrap();
        assert_eq!(a.name, "old");
        assert_eq!(a.env, [("MACHINE_STATE".to_string(), "0".to_string()), ("X".to_string(), String::new())]);
        assert_eq!((a.exe.as_str(), a.args.clone()), ("bf.exe", vec!["a".to_string(), "B=1".to_string()]));
        assert!(parse_arm(&["lonely".to_string()]).is_err());
    }

    #[test]
    fn placeholders_are_substituted() {
        assert_eq!(subst("{dir}/{arm}.{r}", 3, "new", Path::new(r"C:\k")), r"C:\k/new.3");
    }

    #[test]
    fn grep_takes_the_last_matching_line() {
        let text = "COST rule-proofs: n=1 build=1.0ms check=2.0ms nodes=3\nCOST rule-proofs: n=1 build=3.5ms check=4.25ms nodes=3\nCOST other: build=9ms\n";
        let g = pcs_greps();
        assert_eq!(g.iter().map(|g| grep_last(&g.re, text)).collect::<Vec<_>>(), [Some("3.5".to_string()), Some("4.25".to_string())]);
        assert!(parse_grep("nocapture=x").is_err());
    }

    #[test]
    fn grep_reads_crlf_and_invalid_utf8() {
        let bytes = b"x=1\r\n\xff\xfe junk\r\nx=2\r\n";
        let text = String::from_utf8_lossy(bytes);
        assert_eq!(grep_last(&parse_grep("x=^x=([0-9]+)$").unwrap().re, &text), Some("2".to_string()));
    }

    #[test]
    fn pcs_arms_from_one_exe_or_two() {
        let s = Path::new(r"C:\s");
        let one = pcs_arms(s, &["bf.exe".into()], &["old:".into(), "new:NO_PREFETCH=1,X=2".into()]).unwrap();
        assert_eq!(one.iter().map(|a| a.name.as_str()).collect::<Vec<_>>(), ["old", "new"]);
        assert_eq!(one[1].env.last().unwrap(), &("X".to_string(), "2".to_string()));
        assert!(one[0].env.contains(&("CHECK_LAWFILE".to_string(), r"C:\s\tests\church_bv\held_11.txt".to_string())));
        let two = pcs_arms(s, &["a.exe".into(), "b.exe".into()], &[]).unwrap();
        assert_eq!((two[0].exe.as_str(), two[1].exe.as_str()), ("a.exe", "b.exe"));
        assert!(pcs_arms(s, &["bf.exe".into()], &[]).is_err());
        assert!(pcs_arms(s, &["bf.exe".into()], &["bad".into()]).is_err());
    }

    #[test]
    fn dirty_rounds_end_at_max_rounds_and_a_used_dir_is_refused() {
        let d = scratch("maxrounds");
        let t = timing(d.to_path_buf(), vec![where_arm("a", "where.exe"), where_arm("b", "cmd.exe")]);
        let failed = time(&t).unwrap();
        let line = done_line(&d);
        assert_eq!((line.as_str(), failed), ("done 0/2 max-rounds 2", false));
        let tsv = std::fs::read_to_string(d.join("runs.tsv")).unwrap();
        let rows: Vec<&str> = tsv.lines().collect();
        assert_eq!(rows.len(), 5, "{tsv}");
        assert!(rows[0].ends_with("\tclean\tdir"), "{tsv}");
        assert!(rows[1].starts_with("a\t1\t1\t") && rows[2].starts_with("b\t1\t2\t"), "{tsv}");
        assert!(rows[3].starts_with("b\t2\t1\t") && rows[4].starts_with("a\t2\t2\t"), "{tsv}");
        assert!(rows[1..].iter().all(|r| r.ends_with("\tfalse\tSystem32")), "{tsv}");
        assert_eq!(std::fs::read_to_string(d.join("done.txt")).unwrap(), "done 0/2 max-rounds 2\n");
        assert_eq!(std::fs::read_to_string(d.join("state.txt")).unwrap().lines().count(), 2);
        assert!(d.join("b.2.out.txt").is_file());
        assert!(time(&t).unwrap_err().contains("already holds runs.tsv"));
    }

    #[test]
    fn a_failed_run_stops_the_timing() {
        let d = scratch("failed");
        let mut t = timing(d.to_path_buf(), vec![where_arm("a", "where.exe"), where_arm("b", "no_such_file_zz.exe")]);
        t.foreign_max = 100.0;
        let failed = time(&t).unwrap();
        let line = done_line(&d);
        assert!(line.starts_with("done 0/1 b.1 failed (exit 1)"), "{line}");
        assert!(failed);
    }

    #[test]
    fn an_io_error_mid_timing_still_writes_done_and_fails() {
        // summary.txt and state.txt as directories make their writes fail, after and before the rounds
        for (blocker, prefix) in [("summary.txt", "done 0/2 max-rounds 2; "), ("state.txt", "done 0/0 ")] {
            let d = scratch(&format!("io-{blocker}"));
            std::fs::create_dir_all(d.join(blocker)).unwrap();
            let failed = time(&timing(d.to_path_buf(), vec![where_arm("a", "where.exe")])).unwrap();
            let line = done_line(&d);
            assert!(failed && line.starts_with(prefix) && line.contains(blocker), "{line}");
        }
    }

    #[test]
    fn a_missing_exe_stops_the_timing() {
        let d = scratch("noexe");
        let mut a = where_arm("a", "x");
        a.exe = d.join("no_such.exe").display().to_string();
        let failed = time(&timing(d.to_path_buf(), vec![a])).unwrap();
        let line = done_line(&d);
        assert!(line.starts_with("done 0/1 a.1: starting "), "{line}");
        assert!(failed);
        assert!(d.join("done.txt").is_file());
    }

    #[test]
    fn keep_dirty_counts_every_round() {
        let d = scratch("keepdirty");
        let mut t = timing(d.to_path_buf(), vec![where_arm("a", "where.exe")]);
        t.keep_dirty = true;
        t.rounds = 3;
        let failed = time(&t).unwrap();
        let line = done_line(&d);
        assert_eq!((line.as_str(), failed), ("done 0/3 all rounds", false));
        let s = std::fs::read_to_string(d.join("summary.txt")).unwrap();
        assert!(s.contains("clean 0 rounds") && s.contains("all 3 rounds"), "{s}");
    }

    #[test]
    fn duplicate_arm_names_are_refused() {
        let d = scratch("dup");
        let t = timing(d.to_path_buf(), vec![where_arm("a", "where.exe"), where_arm("a", "cmd.exe")]);
        assert!(time(&t).unwrap_err().contains("arm a appears twice"));
        // file names are case-insensitive on Windows: A and a would write the same a.1.out.txt
        let t = timing(d.to_path_buf(), vec![where_arm("A", "where.exe"), where_arm("a", "cmd.exe")]);
        assert!(time(&t).unwrap_err().contains("arm a appears twice"));
    }

    #[test]
    fn arm_names_must_be_plain_file_name_parts() {
        let d = scratch("names");
        for name in ["x/y", r"x\y", "x:y", "MACHINE_STATE=0", "", "a b"] {
            let t = timing(d.join("t"), vec![where_arm(name, "where.exe")]);
            let e = time(&t).unwrap_err();
            assert!(e.contains("letters, digits"), "{name:?}: {e}");
            assert!(!d.join("t").exists(), "{name:?} wrote before refusing");
        }
        for name in ["old", "new-2", "a.b_C"] {
            assert!(check_arm_names(&[where_arm(name, "where.exe")]).is_ok(), "{name}");
        }
    }

    #[test]
    fn a_bad_max_hours_is_refused_before_anything_is_written() {
        let d = scratch("maxhours");
        for h in [f64::NAN, -1.0, f64::INFINITY, 1e300] {
            let mut t = timing(d.join("t"), vec![where_arm("a", "where.exe")]);
            t.max_hours = h;
            let e = time(&t).unwrap_err();
            assert!(e.contains("--max-hours"), "{h}: {e}");
            assert!(!d.join("t").exists(), "{h} wrote before refusing");
        }
    }

    #[test]
    fn the_quiet_wait_ends_on_stop() {
        let d = scratch("stop");
        std::fs::create_dir_all(&d).unwrap();
        std::fs::write(d.join("stop"), "").unwrap();
        let mut t = timing(d.to_path_buf(), vec![]);
        t.quiet_secs = 60;
        let far = Instant::now() + Duration::from_secs(3600);
        assert_eq!(wait_quiet(&t, far, &d.join("stop")), Err("stop".to_string()));
        assert_eq!(wait_quiet(&t, Instant::now(), &d.join("none")), Err("deadline".to_string()));
    }

    #[test]
    fn summary_pairs_rounds_against_the_first_arm() {
        let row = |arm: &str, round, cpu| Row {
            arm: arm.into(),
            round,
            // AB, BA, AB as `order` runs them
            pos: 1 + ((arm == "new") != (round == 2)) as usize,
            start: 0,
            r: job::RunResult { exit: 0, wall: 1.0, job_cpu: cpu, procs: 1, stragglers: 0, peak_proc_mb: 0.0, peak_job_mb: 0.0, peak_ws_mb: 0.0, other_pct: 0.0, others: 0 },
            rtp: None,
            clean: true,
            greps: vec![],
        };
        let rows = [row("old", 1, 10.0), row("new", 1, 9.0), row("old", 2, 10.0), row("new", 2, 11.0), row("old", 3, 12.0), row("new", 3, 10.0)];
        let s = summary(&rows, &["old".into(), "new".into()], &[], &[1, 2, 3]);
        assert!(s.contains("old: jobcpu median=10.000 best=10.000"), "{s}");
        assert!(s.contains("new - old jobcpu: median -1.000, won 2/3: r1 -1.000, r2 +1.000, r3 -2.000"), "{s}");
        // new ran first in r2 (+1) and second in r1, r3 (-1.5 on average): -0.25 over the two orders, and a run's
        // second place costs it (-1.5 - 1) / 2
        assert!(s.contains("new - old jobcpu over the two orders: -0.250 (new first +1.000 in 1, second -1.500 in 2), running second -1.250"), "{s}");
    }
}
