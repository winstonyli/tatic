//! One measured run (`run`). The exe starts suspended, joins a new job object, then resumes, so every process it starts
//! is in the job with no race (`pin.ps1` assigned after the start, and `sweep_job.ps1` put its own PowerShell in the
//! job). The job sets priority, affinity and kill-on-close for all of them, and its accounting gives the run's CPU,
//! process count and peak commit. Meanwhile a sampler thread counts other jobs' processes, and `GetSystemTimes` at both
//! ends gives the load the rest of the machine added.

use crate::state;
use std::fs::File;
use std::os::windows::io::AsRawHandle;
use std::os::windows::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::mpsc;
use std::time::{Duration, Instant};
use windows_sys::Win32::Foundation::{CloseHandle, HANDLE, INVALID_HANDLE_VALUE};
use windows_sys::Win32::System::Diagnostics::ToolHelp::{
    CreateToolhelp32Snapshot, PROCESSENTRY32W, Process32FirstW, Process32NextW, TH32CS_SNAPPROCESS, TH32CS_SNAPTHREAD,
    THREADENTRY32, Thread32First, Thread32Next,
};
use windows_sys::Win32::System::JobObjects::{
    AssignProcessToJobObject, CreateJobObjectW, JOB_OBJECT_LIMIT_AFFINITY, JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE,
    JOB_OBJECT_LIMIT_PRIORITY_CLASS, JOBOBJECT_BASIC_ACCOUNTING_INFORMATION, JOBOBJECT_EXTENDED_LIMIT_INFORMATION,
    JobObjectBasicAccountingInformation, JobObjectExtendedLimitInformation, QueryInformationJobObject,
    SetInformationJobObject,
};
use windows_sys::Win32::System::Threading::{
    BELOW_NORMAL_PRIORITY_CLASS, CREATE_SUSPENDED, NORMAL_PRIORITY_CLASS, OpenThread, ResumeThread, THREAD_SUSPEND_RESUME,
};

/// Where a run's output goes: one file for both streams through one handle (as `> log.txt 2>&1`), or two files.
pub enum Output {
    Both(PathBuf),
    Split(PathBuf, PathBuf),
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Priority {
    BelowNormal,
    /// For GPU-feeding jobs, which starve at BelowNormal (LONG_RUNS.md).
    Normal,
}

impl Priority {
    pub fn parse(s: &str) -> Result<Priority, String> {
        match s.to_ascii_lowercase().as_str() {
            "belownormal" => Ok(Priority::BelowNormal),
            "normal" => Ok(Priority::Normal),
            _ => Err(format!("unknown priority {s} (BelowNormal or Normal)")),
        }
    }

    fn class(self) -> u32 {
        match self {
            Priority::BelowNormal => BELOW_NORMAL_PRIORITY_CLASS,
            Priority::Normal => NORMAL_PRIORITY_CLASS,
        }
    }
}

pub struct RunSpec {
    /// A path with a directory part is made absolute against `runs`'s own working directory; a bare name is searched on PATH.
    pub exe: PathBuf,
    pub args: Vec<String>,
    /// `(VAR, value)` set for the run; an empty value removes VAR (as `cpu_ab.ps1`'s old arm unset its variable).
    pub env: Vec<(String, String)>,
    pub cwd: Option<PathBuf>,
    pub output: Output,
    pub priority: Priority,
    pub affinity: usize,
    /// How long to wait, after the main process exits, for the rest of the job to exit.
    pub straggler_wait: Duration,
    /// Other jobs' process name patterns (`matches`).
    pub others: Vec<String>,
}

impl RunSpec {
    pub fn new(exe: impl Into<PathBuf>, args: Vec<String>, output: Output) -> RunSpec {
        RunSpec {
            exe: exe.into(),
            args,
            env: Vec::new(),
            cwd: None,
            output,
            priority: Priority::BelowNormal,
            affinity: 0xFFF,
            straggler_wait: Duration::from_secs(60),
            others: default_others(),
        }
    }
}

/// Other sessions' jobs (`quiet_ab`'s list): self-play training and the League client.
pub fn default_others() -> Vec<String> {
    vec!["selfplay*".into(), "League*".into()]
}

#[derive(Debug, Clone)]
pub struct RunResult {
    pub exit: i32,
    /// Seconds from the start to the main process's exit.
    pub wall: f64,
    /// User plus kernel seconds of every process the job held (the split is unreliable here, LONG_RUNS.md).
    pub job_cpu: f64,
    pub procs: u32,
    /// Processes still running when the straggler wait ran out; closing the job killed them.
    pub stragglers: u32,
    pub peak_proc_mb: f64,
    pub peak_job_mb: f64,
    /// Other processes' share of the machine during the run (`other_pct`).
    pub other_pct: f64,
    /// The most other jobs' processes seen at once.
    pub others: u32,
}

struct Handle(HANDLE);

impl Drop for Handle {
    fn drop(&mut self) {
        unsafe { CloseHandle(self.0) };
    }
}

/// A job object with the run's limits; closing it kills whatever is still in it.
struct Job(Handle);

impl Job {
    fn new(priority: Priority, affinity: usize) -> Result<Job, String> {
        let h = unsafe { CreateJobObjectW(std::ptr::null(), std::ptr::null()) };
        if h.is_null() {
            return Err(last_error("CreateJobObjectW"));
        }
        let job = Job(Handle(h));
        let mut info: JOBOBJECT_EXTENDED_LIMIT_INFORMATION = unsafe { std::mem::zeroed() };
        info.BasicLimitInformation.LimitFlags = JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE | JOB_OBJECT_LIMIT_AFFINITY | JOB_OBJECT_LIMIT_PRIORITY_CLASS;
        info.BasicLimitInformation.Affinity = affinity;
        info.BasicLimitInformation.PriorityClass = priority.class();
        let ok = unsafe { SetInformationJobObject(h, JobObjectExtendedLimitInformation, (&raw const info).cast(), size_of_val(&info) as u32) };
        if ok == 0 {
            return Err(last_error("SetInformationJobObject"));
        }
        Ok(job)
    }

    fn basic(&self) -> JOBOBJECT_BASIC_ACCOUNTING_INFORMATION {
        let mut b: JOBOBJECT_BASIC_ACCOUNTING_INFORMATION = unsafe { std::mem::zeroed() };
        unsafe { QueryInformationJobObject(self.0.0, JobObjectBasicAccountingInformation, (&raw mut b).cast(), size_of_val(&b) as u32, std::ptr::null_mut()) };
        b
    }

    fn extended(&self) -> JOBOBJECT_EXTENDED_LIMIT_INFORMATION {
        let mut e: JOBOBJECT_EXTENDED_LIMIT_INFORMATION = unsafe { std::mem::zeroed() };
        unsafe { QueryInformationJobObject(self.0.0, JobObjectExtendedLimitInformation, (&raw mut e).cast(), size_of_val(&e) as u32, std::ptr::null_mut()) };
        e
    }
}

fn last_error(what: &str) -> String {
    format!("{what} failed: {}", std::io::Error::last_os_error())
}

fn create(p: &Path) -> Result<File, String> {
    File::create(p).map_err(|e| format!("{}: {e}", p.display()))
}

/// A relative path with a directory part, made absolute against this process's directory: with the child's
/// `current_dir` set, Rust leaves it unspecified which directory a relative program path is resolved against
/// (`pin.ps1` had this bug, RELATED_WORK §66). A bare name is left for the PATH search.
fn resolve_exe(exe: &Path) -> Result<PathBuf, String> {
    if exe.components().count() > 1 {
        std::path::absolute(exe).map_err(|e| format!("{}: {e}", exe.display()))
    } else {
        Ok(exe.to_path_buf())
    }
}

/// Resumes every thread of `pid` (a process started suspended has one).
fn resume(pid: u32) -> Result<(), String> {
    let snap = unsafe { CreateToolhelp32Snapshot(TH32CS_SNAPTHREAD, 0) };
    if snap == INVALID_HANDLE_VALUE {
        return Err(last_error("CreateToolhelp32Snapshot"));
    }
    let snap = Handle(snap);
    let mut e: THREADENTRY32 = unsafe { std::mem::zeroed() };
    e.dwSize = size_of::<THREADENTRY32>() as u32;
    let mut resumed = 0;
    let mut more = unsafe { Thread32First(snap.0, &mut e) };
    while more != 0 {
        if e.th32OwnerProcessID == pid {
            let t = unsafe { OpenThread(THREAD_SUSPEND_RESUME, 0, e.th32ThreadID) };
            if t.is_null() {
                return Err(last_error("OpenThread"));
            }
            let t = Handle(t);
            if unsafe { ResumeThread(t.0) } == u32::MAX {
                return Err(last_error("ResumeThread"));
            }
            resumed += 1;
        }
        more = unsafe { Thread32Next(snap.0, &mut e) };
    }
    if resumed == 0 { Err(format!("no thread of process {pid} to resume")) } else { Ok(()) }
}

/// Every running process: (pid, name in lower case without `.exe`).
pub fn processes() -> Vec<(u32, String)> {
    let mut out = Vec::new();
    let snap = unsafe { CreateToolhelp32Snapshot(TH32CS_SNAPPROCESS, 0) };
    if snap == INVALID_HANDLE_VALUE {
        return out;
    }
    let snap = Handle(snap);
    let mut e: PROCESSENTRY32W = unsafe { std::mem::zeroed() };
    e.dwSize = size_of::<PROCESSENTRY32W>() as u32;
    let mut more = unsafe { Process32FirstW(snap.0, &mut e) };
    while more != 0 {
        let n = e.szExeFile.iter().position(|&c| c == 0).unwrap_or(e.szExeFile.len());
        let name = String::from_utf16_lossy(&e.szExeFile[..n]).to_lowercase();
        out.push((e.th32ProcessID, name.strip_suffix(".exe").unwrap_or(&name).to_string()));
        more = unsafe { Process32NextW(snap.0, &mut e) };
    }
    out
}

/// Whether process `name` matches `pattern`, as PowerShell's `-like` on `ProcessName` did: `*` matches any run of
/// characters, case is ignored, and the name's `.exe` is dropped.
pub fn matches(pattern: &str, name: &str) -> bool {
    fn go(p: &[u8], n: &[u8]) -> bool {
        match p.split_first() {
            None => n.is_empty(),
            Some((b'*', rest)) => (0..=n.len()).any(|i| go(rest, &n[i..])),
            Some((c, rest)) => n.first() == Some(c) && go(rest, &n[1..]),
        }
    }
    let name = name.to_lowercase();
    go(pattern.to_lowercase().as_bytes(), name.strip_suffix(".exe").unwrap_or(&name).as_bytes())
}

pub fn count_others(patterns: &[String]) -> u32 {
    processes().iter().filter(|(_, n)| patterns.iter().any(|p| matches(p, n))).count() as u32
}

/// Other processes' share of the machine in percent: its busy time less the job's CPU, over its total processor time
/// (wall × logical processors), the subtraction `clean.py` did. `GetSystemTimes`'s busy time includes interrupt and
/// DPC time no job is charged, so this reads slightly high, as `clean.py`'s `% Processor Time` did.
pub fn other_pct(busy: f64, total: f64, job_cpu: f64) -> f64 {
    if total <= 0.0 { 0.0 } else { (100.0 * (busy - job_cpu) / total).max(0.0) }
}

/// `quiet_ab`'s cleaning rule: a run counts when it succeeded, other processes stayed under `foreign_max`% of the
/// machine, and no other job's process appeared.
pub fn clean(exit: i32, other_pct: f64, others: u32, foreign_max: f64) -> bool {
    exit == 0 && others == 0 && other_pct < foreign_max
}

pub fn run(spec: &RunSpec) -> Result<RunResult, String> {
    let exe = resolve_exe(&spec.exe)?;
    let mut cmd = Command::new(&exe);
    cmd.args(&spec.args).stdin(Stdio::null()).creation_flags(CREATE_SUSPENDED);
    for (k, v) in &spec.env {
        if v.is_empty() {
            cmd.env_remove(k);
        } else {
            cmd.env(k, v);
        }
    }
    if let Some(d) = &spec.cwd {
        cmd.current_dir(d);
    }
    match &spec.output {
        Output::Both(p) => {
            let f = create(p)?;
            cmd.stderr(f.try_clone().map_err(|e| format!("{}: {e}", p.display()))?).stdout(f);
        }
        Output::Split(o, e) => {
            cmd.stdout(create(o)?).stderr(create(e)?);
        }
    }
    let job = Job::new(spec.priority, spec.affinity)?;
    // The sampler ends when `stop` is dropped, on every return path.
    let (stop, stopped) = mpsc::channel::<()>();
    let patterns = spec.others.clone();
    let sampler = std::thread::spawn(move || {
        let mut most = count_others(&patterns);
        while let Err(mpsc::RecvTimeoutError::Timeout) = stopped.recv_timeout(Duration::from_secs(2)) {
            most = most.max(count_others(&patterns));
        }
        most.max(count_others(&patterns))
    });
    let t0 = state::times();
    let start = Instant::now();
    let mut child = cmd.spawn().map_err(|e| format!("starting {}: {e}", exe.display()))?;
    if unsafe { AssignProcessToJobObject(job.0.0, child.as_raw_handle() as HANDLE) } == 0 {
        // for example a parent job whose affinity limit rejects ours: a run outside the job would count only itself
        let err = last_error("AssignProcessToJobObject");
        let _ = child.kill();
        let _ = child.wait();
        return Err(format!("{err}; the run was not started"));
    }
    if let Err(e) = resume(child.id()) {
        let _ = child.kill();
        let _ = child.wait();
        return Err(e);
    }
    let status = child.wait().map_err(|e| format!("waiting for {}: {e}", exe.display()))?;
    let wall = start.elapsed().as_secs_f64();
    // the job counts until its last process exits (sweep_job.ps1's note)
    let deadline = Instant::now() + spec.straggler_wait;
    let mut basic = job.basic();
    while basic.ActiveProcesses > 0 && Instant::now() < deadline {
        std::thread::sleep(Duration::from_millis(50));
        basic = job.basic();
    }
    let ext = job.extended();
    let t1 = state::times();
    drop(stop);
    let others = sampler.join().unwrap_or(0);
    let job_cpu = (basic.TotalUserTime + basic.TotalKernelTime) as f64 / 1e7;
    let (busy, total) = t1.since(&t0);
    let mb = |b: usize| b as f64 / 1048576.0;
    Ok(RunResult {
        exit: status.code().unwrap_or(-1),
        wall,
        job_cpu,
        procs: basic.TotalProcesses,
        stragglers: basic.ActiveProcesses,
        peak_proc_mb: mb(ext.PeakProcessMemoryUsed),
        peak_job_mb: mb(ext.PeakJobMemoryUsed),
        other_pct: other_pct(busy, total, job_cpu),
        others,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Not a test: the child process the tests below start, doing what `RUNS_HELPER` says.
    #[test]
    #[ignore]
    #[allow(clippy::zombie_processes)] // the orphan is the point: the job must count a child its parent never waits for
    fn helper() {
        let Ok(mode) = std::env::var("RUNS_HELPER") else { return };
        match mode.as_str() {
            "spin" => spin(Duration::from_millis(500)),
            "env" => println!("OS={}", std::env::var("OS").unwrap_or_else(|_| "unset".into())),
            "sleep" => {
                std::fs::write(std::env::var("RUNS_PID_FILE").unwrap(), std::process::id().to_string()).unwrap();
                std::thread::sleep(Duration::from_secs(30));
            }
            // `orphan_<mode>`: start a child doing <mode>, and exit without waiting for it
            m => {
                let rest = m.strip_prefix("orphan_").expect("unknown RUNS_HELPER");
                let (exe, args) = helper_cmd();
                Command::new(exe).args(args).env("RUNS_HELPER", rest).stdout(Stdio::null()).spawn().unwrap();
            }
        }
    }

    fn spin(d: Duration) {
        let t = Instant::now();
        let mut x = 0u64;
        while t.elapsed() < d {
            x = std::hint::black_box(x.wrapping_add(1));
        }
    }

    /// This test exe (under `C:\Users\Winston Li\...`, so its path has a space) running only `helper`.
    fn helper_cmd() -> (PathBuf, Vec<String>) {
        (std::env::current_exe().unwrap(), ["job::tests::helper", "--exact", "--ignored", "--nocapture"].map(String::from).to_vec())
    }

    fn scratch(name: &str) -> crate::Scratch {
        crate::Scratch::new(&format!("job-{name}"))
    }

    fn helper_spec(mode: &str, d: &Path) -> RunSpec {
        let (exe, args) = helper_cmd();
        let mut s = RunSpec::new(exe, args, Output::Split(d.join("out.txt"), d.join("err.txt")));
        s.env.push(("RUNS_HELPER".into(), mode.into()));
        s
    }

    #[test]
    fn children_are_counted() {
        let d = scratch("children");
        let (exe, args) = helper_cmd();
        let words = [vec!["/c".to_string(), exe.display().to_string()], args].concat();
        let mut s = RunSpec::new("cmd", words, Output::Split(d.join("out.txt"), d.join("err.txt")));
        s.env.push(("RUNS_HELPER".into(), "spin".into()));
        let r = run(&s).unwrap();
        assert_eq!(r.exit, 0, "{r:?}");
        assert!(r.procs >= 2, "{r:?}");
        assert!(r.job_cpu >= 0.4, "{r:?}");
    }

    #[test]
    fn a_child_left_running_is_waited_for_and_counted() {
        let d = scratch("orphan_spin");
        let r = run(&helper_spec("orphan_spin", &d)).unwrap();
        assert_eq!((r.exit, r.stragglers), (0, 0), "{r:?}");
        assert!(r.procs >= 2 && r.job_cpu >= 0.4, "{r:?}");
    }

    #[test]
    fn stragglers_are_reported_and_killed_with_the_job() {
        let d = scratch("orphan_sleep");
        let pid_file = d.join("pid.txt");
        let mut s = helper_spec("orphan_sleep", &d);
        s.env.push(("RUNS_PID_FILE".into(), pid_file.display().to_string()));
        s.straggler_wait = Duration::from_secs(3);
        let r = run(&s).unwrap();
        assert_eq!(r.stragglers, 1, "{r:?}");
        let pid: u32 = std::fs::read_to_string(&pid_file).unwrap().trim().parse().unwrap();
        let deadline = Instant::now() + Duration::from_secs(10);
        while processes().iter().any(|&(p, _)| p == pid) {
            assert!(Instant::now() < deadline, "process {pid} outlived its job");
            std::thread::sleep(Duration::from_millis(50));
        }
    }

    #[test]
    fn a_relative_exe_is_found_from_the_callers_directory() {
        // test_clean.sh's pin case: a relative path with a directory part, run with another current_dir
        let rel = PathBuf::from(format!("target/runs-test-{}/bin", std::process::id()));
        std::fs::create_dir_all(&rel).unwrap();
        std::fs::copy(r"C:\Windows\System32\where.exe", rel.join("where.exe")).unwrap();
        let d = scratch("relative");
        let mut s = RunSpec::new(rel.join("where.exe"), vec!["where.exe".into()], Output::Split(d.join("out.txt"), d.join("err.txt")));
        s.cwd = Some(d.to_path_buf());
        let r = run(&s);
        let _ = std::fs::remove_dir_all(rel.parent().unwrap());
        assert_eq!(r.unwrap().exit, 0);
    }

    #[test]
    fn an_empty_value_removes_the_variable() {
        let d = scratch("env");
        let mut s = helper_spec("env", &d);
        s.env.push(("OS".into(), String::new()));
        assert_eq!(run(&s).unwrap().exit, 0);
        assert!(std::fs::read_to_string(d.join("out.txt")).unwrap().contains("OS=unset"));
        let d2 = scratch("env_kept");
        assert_eq!(run(&helper_spec("env", &d2)).unwrap().exit, 0);
        assert!(std::fs::read_to_string(d2.join("out.txt")).unwrap().contains("OS=Windows_NT"));
    }

    #[test]
    fn a_missing_exe_is_an_error() {
        let d = scratch("missing");
        let s = RunSpec::new(d.join("no_such.exe"), vec![], Output::Both(d.join("log.txt")));
        assert!(run(&s).unwrap_err().starts_with("starting "));
    }

    #[test]
    fn the_cleaning_rule() {
        // test_clean.sh's cases, on 16 processors over one 2 s sample: 32 processor-seconds
        assert!((other_pct(3.84, 32.0, 0.0) - 12.0).abs() < 1e-9);
        assert!(clean(0, other_pct(3.84, 32.0, 0.0), 0, 20.0)); // A1: 12% total, no own load
        assert!(!clean(0, other_pct(9.6, 32.0, 0.32), 0, 20.0)); // B1: 30% total less own 1%: 29%
        assert!(!clean(0, other_pct(3.2, 32.0, 0.0), 1, 20.0)); // A2: an others' process
        assert!(!clean(1, other_pct(0.0, 32.0, 0.0), 0, 20.0)); // A3: failed
        assert!(clean(0, other_pct(9.6, 32.0, 4.0), 0, 20.0)); // B3: 30% less own 12.5%: 17.5%
        assert_eq!(other_pct(1.0, 32.0, 2.0), 0.0); // own CPU above the machine's busy time: none
    }

    #[test]
    fn others_patterns_match_as_powershell_like_did() {
        assert!(matches("selfplay*", "SelfPlay-burn.exe"));
        assert!(matches("League*", "leagueclient"));
        assert!(!matches("League*", "myleague"));
        assert!(matches("*play", "selfplay.EXE"));
    }
}
