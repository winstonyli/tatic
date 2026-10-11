//! The mine-and-serve loop driver (formerly `scripts/loop_stream.sh`). It runs this exe's `search::rule_set_kernel_check` (serve) and
//! `search::rule_miner` (mine) as child processes, so each keeps its own thread-locals and env-read config. A shell driver spent
//! about half a loop in Git Bash forks (docs/tier-cycle.md, "Loop overhead").
//!
//!   LOOP_MODE=none|ref|loop LOOP_OUT=<dir> [options] <exe> driver::loop_stream --ignored --nocapture
//!
//! Batch r is the laws OFFSET+r*B .. OFFSET+(r+1)*B of the family's sequence (residue class SPHASE of stride STRIDE). It is served under
//! the rules in force *before* it is mined, so M is what the stream costs when rules arrive as it does. `ref` mines once on all K
//! batches before serving them; `loop` mines each batch after serving it (not the last, which could not change any M); `none` only
//! serves.
//! Options (env, defaults in brackets): FAMILY [add3] (add3|mix3|sbo3|cmp3|cmp3d|u3|u3w, THREE_VAR_FAMILIES in search.rs), STRIDE [7],
//! SPHASE [0], B [150], K [4], OFFSET [0], THREADS [2] (miner pool), ROUNDS [8], DEEP3 [1] (add3 only), SPLIT [2] (0|1 restricts
//! everything to one structure-based half of the laws; RULEMINER_SHAPE_SALT picks another split), WARM_RULES=<file> (start with those
//! rules in force), CHECK_FAST [0] (serve without proof building or kernel checks; M is unchanged), MACHINE_STATE [1] (a machine-state
//! line at start and end, about 6 s each). Other variables pass through to the children: RULEMINER_FAST=1 (exact counts without
//! proving every candidate, docs/tier-cycle.md "Miner speedups"), RULEMINER_SHUFFLE=<salt> (hash-ordered law sequence, so batches and
//! phases are random samples), RULEMINER_STEPS (default 200, serving's budget).
//! To share the machine, launch at low priority and pinned (children inherit both): cmd //c start "" //b //belownormal //affinity 3 ...
//!
//! Output in LOOP_OUT: rules.txt (the rules in force at the end), m.tsv (batch, M, laws, rules in force, serve seconds, laws that used
//! up the rule budget: nonzero means a rewrite cycle or growing rules), mine_<name>.log and serve_<skip>.log. The last line printed is
//! `mode=.. B=.. K=.. offset=.. total_M=.. rules=.. exhausted=..`.

use super::*;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

struct Loop {
    out: PathBuf,
    rules: PathBuf,
    /// variables both children get
    common: Vec<(&'static str, String)>,
    exe: PathBuf,
}

impl Loop {
    /// Runs test `name` of this exe with `env` added, output to `log`; returns whether it succeeded.
    fn child(&self, name: &str, env: &[(&str, String)], log: &Path) -> bool {
        let f = std::fs::File::create(log).unwrap();
        let mut c = Command::new(&self.exe);
        c.args([name, "--exact", "--ignored", "--nocapture"]).stdout(f.try_clone().unwrap()).stderr(f);
        c.envs(self.common.iter().map(|(k, v)| (*k, v.as_str()))).envs(env.iter().map(|(k, v)| (*k, v.as_str())));
        c.status().unwrap().success()
    }

    fn mine(&self, name: &str, skip: usize, laws: usize) {
        let log = self.out.join(format!("mine_{name}.log"));
        let env = [
            ("RULEMINER_PERM", "1".to_string()),
            ("RULEMINER_THREADS", env_or("THREADS", 2usize).to_string()),
            ("RULEMINER_ROUNDS", env_or("ROUNDS", 8usize).to_string()),
            ("RULEMINER_SKIP", skip.to_string()),
            ("RULEMINER_LAWS", laws.to_string()),
            ("RULEMINER_BASE", self.rules.display().to_string()),
        ];
        assert!(self.child("search::rule_miner", &env, &log), "rule_miner failed (see {})", log.display());
        let chosen: String = std::fs::read_to_string(&log)
            .unwrap()
            .lines()
            .filter(|l| l.contains("RULEMINER chosen") && l.contains(" -> "))
            .map(|l| format!("{}\n", l.rsplit_once("size): ").map_or(l, |(_, r)| r)))
            .collect();
        std::fs::OpenOptions::new().append(true).open(&self.rules).unwrap().write_all(chosen.as_bytes()).unwrap();
    }

    /// (M, laws, laws that used up the rule budget) of the batch at `skip`
    fn serve(&self, skip: usize, b: usize) -> (usize, usize, usize) {
        let log = self.out.join(format!("serve_{skip}.log"));
        let env = [
            ("CHECK_FAST", env_or("CHECK_FAST", 0usize).to_string()),
            ("RULEMINER_SKIP", skip.to_string()),
            ("RULEMINER_LAWS", b.to_string()),
            ("CHECK_RULES", self.rules.display().to_string()),
        ];
        self.child("search::rule_set_kernel_check", &env, &log);
        // CHECKED <n> laws kernel-checked (<k> with no whole-term machine proof), <p> not proved, <x> used up the rule budget
        let text = std::fs::read_to_string(&log).unwrap();
        let line = text.lines().find(|l| l.starts_with("CHECKED ")).unwrap_or_else(|| panic!("no CHECKED line (see {})", log.display()));
        let nums: Vec<usize> = line.split(|c: char| !c.is_ascii_digit()).filter_map(|w| w.parse().ok()).collect();
        let &[n, k, p, x] = &nums[..] else { panic!("unexpected CHECKED line: {line}") };
        (n - k + p, n + p, x)
    }

    fn machine_state(&self, when: &str) {
        if env_or("MACHINE_STATE", 1usize) == 0 {
            return;
        }
        let o = Command::new(&self.exe).args(["machine::machine_state_line", "--exact", "--ignored", "--nocapture"]).output().unwrap();
        let text = String::from_utf8_lossy(&o.stdout);
        eprintln!("loop machine at {when}: {}", text.lines().find(|l| l.contains("machine state:")).unwrap_or(""));
    }

    fn rule_count(&self) -> usize {
        std::fs::read_to_string(&self.rules).unwrap().lines().count()
    }
}

#[test]
#[ignore]
fn loop_stream() {
    let mode = std::env::var("LOOP_MODE").expect("set LOOP_MODE=none|ref|loop");
    assert!(["none", "ref", "loop"].contains(&mode.as_str()), "LOOP_MODE must be none, ref or loop, got {mode}");
    let out = PathBuf::from(std::env::var("LOOP_OUT").expect("set LOOP_OUT=<dir>"));
    std::fs::create_dir_all(&out).unwrap();
    let (b, k, offset) = (env_or("B", 150usize), env_or("K", 4usize), env_or("OFFSET", 0usize));
    let family = std::env::var("FAMILY").unwrap_or_else(|_| "add3".into());
    let common = vec![
        ("RULEMINER_FAMILY", family.clone()),
        ("CHECK_FAMILY", family),
        ("RULEMINER_DEEP3", env_or("DEEP3", 1usize).to_string()),
        ("RULEMINER_STRIDE", env_or("STRIDE", 7usize).to_string()),
        ("RULEMINER_PHASE", env_or("SPHASE", 0usize).to_string()),
        ("RULEMINER_SHAPE", env_or("SPLIT", 2usize).to_string()),
        // one machine-state line per loop instead of one per child
        ("MACHINE_BANNER", "0".to_string()),
    ];
    let lp = Loop { rules: out.join("rules.txt"), out: out.clone(), common, exe: std::env::current_exe().unwrap() };
    match std::env::var("WARM_RULES") {
        Ok(w) if mode != "ref" => {
            std::fs::copy(&w, &lp.rules).unwrap_or_else(|e| panic!("WARM_RULES {w}: {e}"));
        }
        _ => std::fs::write(&lp.rules, "").unwrap(),
    }
    std::fs::write(out.join("m.tsv"), "").unwrap();
    lp.machine_state("start");
    if mode == "ref" {
        lp.mine("ref", offset, b * k);
    }
    let (mut total, mut exhausted) = (0, 0);
    for r in 0..k {
        let (skip, t0) = (offset + r * b, std::time::Instant::now());
        let (m, laws, ex) = lp.serve(skip, b);
        let row = format!("{r}\t{m}\t{laws}\t{}\t{}\t{ex}\n", lp.rule_count(), t0.elapsed().as_secs());
        std::fs::OpenOptions::new().append(true).open(out.join("m.tsv")).unwrap().write_all(row.as_bytes()).unwrap();
        (total, exhausted) = (total + m, exhausted + ex);
        if mode == "loop" && r + 1 < k {
            lp.mine(&r.to_string(), skip, b);
        }
    }
    lp.machine_state("end");
    println!("mode={mode} B={b} K={k} offset={offset} total_M={total} rules={} exhausted={exhausted}", lp.rule_count());
}
