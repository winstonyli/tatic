//! `runs`: gates, timings and machine state for church_bv's sweeps, in one tool (README, "Benchmarks"). Build it with
//! `cargo build --release --manifest-path tools/runs/Cargo.toml` and run `tools/runs/target/release/runs.exe`. Every
//! command prints progress as it goes and writes its records under the run directory (`runs dir`).
#[cfg(not(windows))]
compile_error!("tools/runs is Windows-only: it measures runs with job objects and reads Windows' machine state");

mod cmp;
mod gate;
mod job;
mod state;
#[cfg(test)]
mod state_tests;

use std::ffi::OsString;
use std::os::windows::ffi::{OsStrExt, OsStringExt};
use std::path::{Path, PathBuf};

const USAGE: &str = "usage:
  runs dir                    this checkout's run directory, %TEMP%\\tatic-runs\\<checkout folder>
  runs state                  RTP=.. CPU=..% lockpriv=..
  runs run <dir> [--affinity M] [--priority P] -- [VAR=val]... <exe> <args>...
                              one measured run; output in <dir>/out.txt and err.txt
  runs cmp <tag> [--dir D]     compare <tag>_old_<s> with <tag>_new_<s>, salts 1 and 2 (exit 1 if they differ)
  runs gate <tag> <old exe> <new exe>   four sweeps (new 1, old 1, old 2, new 2), then cmp; <run dir>/<tag>_gate.txt";

fn main() {
    // `runs` and its sampler thread stay out of the way of the run they measure (ab.sh lowered itself too)
    use windows_sys::Win32::System::Threading::{BELOW_NORMAL_PRIORITY_CLASS, GetCurrentProcess, SetPriorityClass};
    unsafe { SetPriorityClass(GetCurrentProcess(), BELOW_NORMAL_PRIORITY_CLASS) };
    let args: Vec<String> = std::env::args().skip(1).collect();
    let code = match dispatch(&args) {
        Ok(code) => code,
        Err(e) => {
            eprintln!("runs: {e}\n{USAGE}");
            2
        }
    };
    std::process::exit(code);
}

fn dispatch(args: &[String]) -> Result<i32, String> {
    let (cmd, rest) = args.split_first().ok_or("no command")?;
    match cmd.as_str() {
        "dir" => {
            println!("{}", run_dir()?.display());
            Ok(0)
        }
        "state" => {
            println!("{}", state::line());
            Ok(0)
        }
        "run" => cmd_run(rest),
        "cmp" => cmd_cmp(rest),
        "gate" => cmd_gate(rest),
        _ => Err(format!("unknown command {cmd}")),
    }
}

/// `runs run`: one measured run; exits with its exit code, as `pin.ps1` did.
fn cmd_run(words: &[String]) -> Result<i32, String> {
    let p = parse(words);
    p.check(&["affinity", "priority"])?;
    let [dir] = &p.pos[..] else { return Err("run takes one directory".into()) };
    let (env, cmd) = split_env(&p.rest);
    let (exe, args) = cmd.split_first().ok_or("run needs an exe after --")?;
    let dir = PathBuf::from(dir);
    std::fs::create_dir_all(&dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    let mut spec = job::RunSpec::new(exe, args.to_vec(), job::Output::Split(dir.join("out.txt"), dir.join("err.txt")));
    spec.env = env;
    apply_limits(&mut spec, &p)?;
    let rtp = state::rtp();
    let r = job::run(&spec)?;
    let label = dir.file_name().map_or("run".to_string(), |n| n.to_string_lossy().into_owned());
    println!("{}", result_line(&label, &r, rtp));
    Ok(r.exit)
}

/// `runs cmp`: prints `cmp::cmp`'s lines; exits 1 if the sides differ.
fn cmd_cmp(words: &[String]) -> Result<i32, String> {
    let p = parse(words);
    p.check(&["dir"])?;
    let [tag] = &p.pos[..] else { return Err("cmp takes one tag".into()) };
    let dir = match p.one("dir")? {
        Some(d) => PathBuf::from(d),
        None => run_dir()?,
    };
    let lines = cmp::cmp(&dir, tag);
    for l in &lines {
        println!("{l}");
    }
    Ok(if cmp::same(&lines) { 0 } else { 1 })
}
/// `runs gate`: exits 0 when the gate passes, 1 when a sweep failed or the outputs differ.
fn cmd_gate(words: &[String]) -> Result<i32, String> {
    let p = parse(words);
    p.check(&[])?;
    let [tag, old, new] = &p.pos[..] else { return Err("gate takes <tag> <old exe> <new exe>".into()) };
    Ok(if gate::gate(&run_dir()?, tag, Path::new(old), Path::new(new))? { 0 } else { 1 })
}

/// Appends `line` and a newline to `path`.
fn append(path: &Path, line: &str) -> Result<(), String> {
    use std::io::Write;
    let mut f = std::fs::OpenOptions::new().create(true).append(true).open(path).map_err(|e| format!("{}: {e}", path.display()))?;
    writeln!(f, "{line}").map_err(|e| format!("{}: {e}", path.display()))
}
/// `--affinity` and `--priority`, where given.
fn apply_limits(spec: &mut job::RunSpec, p: &Parsed) -> Result<(), String> {
    if let Some(m) = p.one("affinity")? {
        spec.affinity = parse_mask(m)?;
    }
    if let Some(v) = p.one("priority")? {
        spec.priority = job::Priority::parse(v)?;
    }
    Ok(())
}

/// The one line per run that `run` prints and `time` logs, with units as `sweep_job.ps1` wrote them.
fn result_line(label: &str, r: &job::RunResult, rtp: Option<bool>) -> String {
    format!(
        "{label} wall={:.1}s jobcpu={:.2}s procs={} stragglers={} peakproc={:.0}MB peakjob={:.0}MB other={:.0}% others={} rtp={} exit={}",
        r.wall,
        r.job_cpu,
        r.procs,
        r.stragglers,
        r.peak_proc_mb,
        r.peak_job_mb,
        r.other_pct,
        r.others,
        state::rtp_text(rtp),
        r.exit
    )
}

/// Command-line words as `runs` reads them: positional words, then `--name [value]...` options (an option takes the
/// words up to the next `--name`), then, after a bare `--`, the rest as given.
#[derive(Debug)]
struct Parsed {
    pos: Vec<String>,
    opts: Vec<(String, Vec<String>)>,
    rest: Vec<String>,
}

fn parse(words: &[String]) -> Parsed {
    let mut p = Parsed { pos: vec![], opts: vec![], rest: vec![] };
    for (i, w) in words.iter().enumerate() {
        if w == "--" {
            p.rest = words[i + 1..].to_vec();
            break;
        }
        if let Some(name) = w.strip_prefix("--") {
            p.opts.push((name.to_string(), vec![]));
        } else if let Some((_, values)) = p.opts.last_mut() {
            values.push(w.clone());
        } else {
            p.pos.push(w.clone());
        }
    }
    p
}

impl Parsed {
    /// An error for an option not in `known`.
    fn check(&self, known: &[&str]) -> Result<(), String> {
        match self.opts.iter().find(|(n, _)| !known.contains(&n.as_str())) {
            Some((n, _)) => Err(format!("unknown option --{n}")),
            None => Ok(()),
        }
    }

    /// Every occurrence's values of a repeatable option.
    fn all(&self, name: &str) -> Vec<&[String]> {
        self.opts.iter().filter(|(n, _)| n == name).map(|(_, v)| &v[..]).collect()
    }

    /// The value of a one-value option, if given (the last occurrence wins).
    fn one(&self, name: &str) -> Result<Option<&str>, String> {
        match self.all(name).last() {
            None => Ok(None),
            Some([v]) => Ok(Some(v)),
            Some(_) => Err(format!("--{name} takes one value")),
        }
    }

    /// Whether a switch with no value was given.
    fn flag(&self, name: &str) -> Result<bool, String> {
        match self.all(name).last() {
            None => Ok(false),
            Some([]) => Ok(true),
            Some(_) => Err(format!("--{name} takes no value")),
        }
    }
}

/// Whether `w` is `VAR=value` with VAR matching `[A-Za-z_][A-Za-z0-9_]*`.
fn is_env(w: &str) -> bool {
    let Some((k, _)) = w.split_once('=') else { return false };
    let mut c = k.chars();
    c.next().is_some_and(|f| f == '_' || f.is_ascii_alphabetic()) && c.all(|x| x == '_' || x.is_ascii_alphanumeric())
}

/// The leading `VAR=value` words as environment, and the rest: the exe and its arguments.
fn split_env(words: &[String]) -> (Vec<(String, String)>, &[String]) {
    let n = words.iter().take_while(|w| is_env(w)).count();
    let env = words[..n].iter().map(|w| w.split_once('=').map(|(k, v)| (k.to_string(), v.to_string())).unwrap()).collect();
    (env, &words[n..])
}

/// An affinity mask in hex, as `start /affinity` takes it (`FFF`, or `0xFFF`).
fn parse_mask(s: &str) -> Result<usize, String> {
    let hex = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")).unwrap_or(s);
    usize::from_str_radix(hex, 16).map_err(|_| format!("bad affinity mask {s} (hex, as FFF)"))
}

/// The checkout this exe was built in: the nearest folder above it holding `tools/runs/Cargo.toml` (four levels for
/// `target/release/runs.exe`, five for a test exe in `target/debug/deps`). `kk.sh` follows its own script's checkout
/// the same way, so a tool built in a worktree writes to that worktree's run directory wherever it is called from.
fn checkout() -> Result<PathBuf, String> {
    let exe = std::env::current_exe().map_err(|e| e.to_string())?;
    exe.ancestors()
        .find(|a| a.join(r"tools\runs\Cargo.toml").is_file())
        .map(Path::to_path_buf)
        .ok_or_else(|| format!("{} is not inside a checkout's tools/runs", exe.display()))
}

/// This checkout's run directory, `%TEMP%\tatic-runs\<checkout folder>`, created (`kk.sh`'s rule).
fn run_dir() -> Result<PathBuf, String> {
    let c = checkout()?;
    let d = long_path(&std::env::temp_dir()).join("tatic-runs").join(c.file_name().ok_or("the checkout has no folder name")?);
    std::fs::create_dir_all(&d).map_err(|e| format!("{}: {e}", d.display()))?;
    Ok(d)
}

/// `p` with 8.3 short names expanded (`%TEMP%` can be `C:\Users\WINSTO~1\...`); `p` itself if that fails.
fn long_path(p: &Path) -> PathBuf {
    let w: Vec<u16> = p.as_os_str().encode_wide().chain([0]).collect();
    let mut buf = vec![0u16; 32768];
    let n = unsafe { windows_sys::Win32::Storage::FileSystem::GetLongPathNameW(w.as_ptr(), buf.as_mut_ptr(), buf.len() as u32) } as usize;
    if n == 0 || n >= buf.len() { p.to_path_buf() } else { PathBuf::from(OsString::from_wide(&buf[..n])) }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn words(s: &str) -> Vec<String> {
        s.split(' ').map(String::from).collect()
    }

    #[test]
    fn words_split_into_positions_options_and_the_rest() {
        let p = parse(&words("D --rounds 6 --keep-dirty --sweep a b -- x --y"));
        assert_eq!(p.pos, ["D"]);
        let s = |x: &str| x.to_string();
        assert_eq!(p.opts, vec![(s("rounds"), vec![s("6")]), (s("keep-dirty"), vec![]), (s("sweep"), vec![s("a"), s("b")])]);
        assert_eq!(p.rest, ["x", "--y"]);
        assert_eq!(p.one("rounds").unwrap(), Some("6"));
        assert!(p.flag("keep-dirty").unwrap());
        assert!(p.one("sweep").is_err());
        assert!(p.check(&["rounds", "keep-dirty"]).is_err());
    }

    #[test]
    fn leading_assignments_are_environment() {
        let w = words("A=1 _B= x.exe C=2");
        let (env, rest) = split_env(&w);
        assert_eq!(env, [("A".to_string(), "1".to_string()), ("_B".to_string(), String::new())]);
        assert_eq!(rest, ["x.exe", "C=2"]);
        assert!(!is_env("1A=x") && !is_env("A-B=x") && !is_env("plain"));
    }

    #[test]
    fn masks_are_hex() {
        assert_eq!(parse_mask("FFF").unwrap(), 0xFFF);
        assert_eq!(parse_mask("0x3").unwrap(), 3);
        assert!(parse_mask("12 cores").is_err());
    }

    #[test]
    fn the_result_line() {
        let r = job::RunResult { exit: 0, wall: 12.34, job_cpu: 10.411, procs: 5, stragglers: 0, peak_proc_mb: 279.4, peak_job_mb: 412.6, other_pct: 3.2, others: 0 };
        assert_eq!(
            result_line("old.1", &r, Some(false)),
            "old.1 wall=12.3s jobcpu=10.41s procs=5 stragglers=0 peakproc=279MB peakjob=413MB other=3% others=0 rtp=False exit=0"
        );
    }

    #[test]
    fn run_dir_agrees_with_kk_sh() {
        let bash = std::env::var("RUNS_BASH").unwrap_or_else(|_| r"C:\Program Files\Git\bin\bash.exe".into());
        if !Path::new(&bash).is_file() {
            eprintln!("skipped: no Git Bash at {bash} (set RUNS_BASH)");
            return;
        }
        let kk = checkout().unwrap().join(r"docs\runs\2026-10-12\scripts\kk.sh").display().to_string().replace('\\', "/");
        let o = std::process::Command::new(&bash)
            .args(["-c", r#"cygpath -w "$(bash "$1")""#, "kk", &kk])
            .stdin(std::process::Stdio::null())
            .output()
            .unwrap();
        assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
        let theirs = long_path(Path::new(String::from_utf8_lossy(&o.stdout).trim()));
        assert_eq!(theirs.display().to_string().to_lowercase(), run_dir().unwrap().display().to_string().to_lowercase());
    }
}
