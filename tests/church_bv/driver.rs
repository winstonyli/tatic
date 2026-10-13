//! The mine-and-serve loop and the sweeps over it (formerly `scripts/loop_stream.sh` and local sweep scripts). Serving
//! (`search::rule_set_kernel_check`) and mining (`search::rule_miner`) run as child processes of this exe, so each keeps its own
//! thread-locals and env-read config. Shell drivers spent much of a loop in Git Bash forks (docs/tier-cycle.md, "Loop overhead").
//! To share the machine, launch at low priority and pinned (children inherit both): cmd //c start "" //b //belownormal //affinity 3 ...
//!
//! **One loop:** `LOOP_MODE=none|ref|loop LOOP_OUT=<dir> [options] <exe> driver::loop_stream --exact --ignored --nocapture`.
//! Batch r is the laws OFFSET+r*B .. OFFSET+(r+1)*B of the family's sequence (residue class SPHASE of stride STRIDE). It is served under
//! the rules in force *before* it is mined, so M is what the stream costs when rules arrive as it does. `ref` mines once on all K
//! batches before serving them; `loop` mines each batch after serving it (not the last, which could not change any M); `none` only
//! serves.
//! Options (env, defaults in brackets): FAMILY [add3] (add3|mix3|sbo3|cmp3|cmp3d|u3|u3w, THREE_VAR_FAMILIES in search.rs), STRIDE [7],
//! SPHASE [0], B [150], K [4], OFFSET [0], THREADS [2] (miner pool), ROUNDS [no cap], DEEP3 [1] (add3 only), SPLIT [2] (0|1 restricts
//! everything to one structure-based half of the laws; RULEMINER_SHAPE_SALT picks another split), WARM_RULES=<file> (start with those
//! rules in force), CHECK_FAST [0] (serve without proof building or kernel checks; M is unchanged), MACHINE_STATE [1] (a machine-state
//! line at start and end, about 6 s each). Other variables pass through to the children: RULEMINER_FAST=1 (exact counts without
//! proving every candidate, docs/tier-cycle.md "Miner speedups"), RULEMINER_SHUFFLE=<salt> (hash-ordered law sequence, so batches and
//! phases are random samples), RULEMINER_STEPS (default 200, serving's budget).
//! The children share the lemma statements they check through LOOP_OUT/lemmas.bin (`LEMMA_CACHE`, `lemma_cache.rs`; deleted when
//! the loop starts and ends; a sweep shares one SWEEP_OUT/lemmas.bin across all its loops instead); LEMMA_RECHECK=1 audits it. The driver computes each child's laws (its window of the family's
//! sequence, built once per family) and passes them as a file, LOOP_OUT/laws_<mine|serve>_<name>.txt (`RULEMINER_LAWFILE`,
//! `CHECK_LAWFILE`).
//! Output in LOOP_OUT: rules.txt (the rules in force at the end, then their learned preferences, `winner  OVER  loser` lines), m.tsv (batch, M, laws, rules in force, serve seconds, laws that used
//! up the rule budget: nonzero means a rewrite cycle or growing rules), mine_<name>.log and serve_<skip>.log. The last line printed is
//! `mode=.. B=.. K=.. offset=.. total_M=.. rules=.. exhausted=..`.
//!
//! **A sweep** (the experiments of docs/loop-result.md): `SWEEP_OUT=<dir> [SALT=1] [LIB=<dir>] [SWEEP="mines own cold"] <exe>
//! driver::sweep --exact --ignored --nocapture` (`MACHINE_STATE=0` skips its two machine-state lines too). Every stage uses `RULEMINER_FAST=1` and `RULEMINER_SHUFFLE=$SALT`. Stages, in order:
//! - `mines`, optionally `:<family>,..` (default sbo3,add3,mix3,cmp3d; u3 only when named): one ref mine per family on its phase-0
//!   stream (`MINES`) -> `lib_<family>/`, summary rows in `<stage>.tsv` (family, seconds, total M, rules, exhausted).
//! - `own`, `cold`, `cross`, `pooled`, `mixed`, optionally `:<family>,<family>` (default cmp3d,add3,sbo3): loops (`LOOPS` settings) on
//!   phases 1-3, seeded with the family's own library, nothing, each other family's library, the pooled library (cmp3d's, add3's and
//!   sbo3's, `pooled.rules`, plus the preferences and rule drops the family learns on it on its phase-0 stream, `pooled_<family>/`; rows in
//!   `pooled_prefs.tsv` as for mines), or the library mined on u3. Libraries are read from `LIB/lib_<family>/rules.txt`
//!   (default LIB = SWEEP_OUT). One row per loop in `<stage>.tsv` (`:` becomes `_`): family, stride-phase, from_<source>, total M,
//!   per-batch M, rules at the end, seconds, exhausted.

use super::*;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

#[derive(Clone)]
struct LoopCfg {
    /// none|ref|loop
    mode: String,
    out: PathBuf,
    family: String,
    stride: usize,
    sphase: usize,
    b: usize,
    k: usize,
    offset: usize,
    threads: usize,
    rounds: usize,
    deep3: usize,
    split: usize,
    warm: Option<PathBuf>,
    check_fast: bool,
    /// further variables for the children (a sweep's RULEMINER_FAST and RULEMINER_SHUFFLE)
    env: Vec<(String, String)>,
}

impl LoopCfg {
    fn from_env() -> LoopCfg {
        let mode = std::env::var("LOOP_MODE").expect("set LOOP_MODE=none|ref|loop");
        assert!(["none", "ref", "loop"].contains(&mode.as_str()), "LOOP_MODE must be none, ref or loop, got {mode}");
        LoopCfg {
            mode,
            out: PathBuf::from(std::env::var("LOOP_OUT").expect("set LOOP_OUT=<dir>")),
            family: std::env::var("FAMILY").unwrap_or_else(|_| "add3".into()),
            stride: env_or("STRIDE", 7),
            sphase: env_or("SPHASE", 0),
            b: env_or("B", 150),
            k: env_or("K", 4),
            offset: env_or("OFFSET", 0),
            threads: env_or("THREADS", 2),
            rounds: env_or("ROUNDS", usize::MAX),
            deep3: env_or("DEEP3", 1),
            split: env_or("SPLIT", 2),
            warm: std::env::var("WARM_RULES").ok().map(PathBuf::from),
            check_fast: env_or("CHECK_FAST", 0usize) == 1,
            env: vec![],
        }
    }
}

struct Summary {
    total: usize,
    /// M per batch
    ms: Vec<usize>,
    rules: usize,
    exhausted: usize,
}

/// Runs test `name` of this exe with `env` added, output to `log`; returns whether it succeeded.
fn child(name: &str, env: &[(String, String)], log: &Path) -> bool {
    let f = std::fs::File::create(log).unwrap();
    let mut c = Command::new(std::env::current_exe().unwrap());
    c.args([name, "--exact", "--ignored", "--nocapture"]).stdout(f.try_clone().unwrap()).stderr(f).envs(env.iter().cloned());
    c.status().unwrap().success()
}

fn append(path: &Path, text: &str) {
    std::fs::OpenOptions::new().create(true).append(true).open(path).unwrap().write_all(text.as_bytes()).unwrap();
}

/// A machine-state line on stderr (about 6 s); `MACHINE_STATE=0` skips it, in a loop or a sweep.
fn machine_state(when: &str) {
    if env_or("MACHINE_STATE", 1usize) == 0 {
        return;
    }
    let o = Command::new(std::env::current_exe().unwrap()).args(["machine::machine_state_line", "--exact", "--ignored", "--nocapture"]).output().unwrap();
    let text = String::from_utf8_lossy(&o.stdout);
    eprintln!("machine at {when}: {}", text.lines().find(|l| l.contains("machine state:")).unwrap_or(""));
}

/// Writes to `path` the laws a child with `env` (over this process's environment) would take from `family`'s sequence, as
/// `lhs = rhs` lines for `RULEMINER_LAWFILE`/`CHECK_LAWFILE`, and returns the variable that passes them. The driver builds a
/// family's law pool once (`family_laws` keeps it) where every child used to rebuild it: 35% of a sweep's loops
/// (docs/tier-cycle.md).
fn write_laws(family: &str, env: &[(String, String)], path: &Path, var: &str) -> (String, String) {
    let get = |k: &str, d: usize| env.iter().rev().find(|(kk, _)| kk == k).map_or_else(|| env_or(k, d), |(_, v)| v.parse().unwrap());
    std::fs::write(path, laws_text(&family_laws(family, &get, 4, family_vars(family), 7))).unwrap();
    (var.to_string(), path.display().to_string())
}

/// One loop; its children share the lemma file `lemmas`, which the caller owns (creates nothing, deletes it when done).
fn run_loop(cfg: &LoopCfg, lemmas: &Path) -> Summary {
    let (out, rules) = (&cfg.out, cfg.out.join("rules.txt"));
    std::fs::create_dir_all(out).unwrap();
    let s = |v: usize| v.to_string();
    let mut common: Vec<(String, String)> = [
        ("RULEMINER_FAMILY", cfg.family.clone()),
        ("CHECK_FAMILY", cfg.family.clone()),
        ("RULEMINER_DEEP3", s(cfg.deep3)),
        ("RULEMINER_STRIDE", s(cfg.stride)),
        ("RULEMINER_PHASE", s(cfg.sphase)),
        ("RULEMINER_SHAPE", s(cfg.split)),
        // one machine-state line per loop or sweep instead of one per child
        ("MACHINE_BANNER", "0".to_string()),
        ("LEMMA_CACHE", lemmas.display().to_string()),
    ]
    .into_iter()
    .map(|(k, v)| (k.to_string(), v))
    .collect();
    common.extend(cfg.env.iter().cloned());
    let with = |extra: &[(&str, String)]| common.iter().cloned().chain(extra.iter().map(|(k, v)| (k.to_string(), v.clone()))).collect::<Vec<_>>();
    let count = || parse_rules(&std::fs::read_to_string(&rules).unwrap()).len();
    let mine = |name: &str, skip: usize, laws: usize| {
        let log = out.join(format!("mine_{name}.log"));
        let mut env = with(&[
            ("RULEMINER_PERM", s(1)),
            ("RULEMINER_THREADS", s(cfg.threads)),
            ("RULEMINER_ROUNDS", s(cfg.rounds)),
            ("RULEMINER_SKIP", s(skip)),
            ("RULEMINER_LAWS", s(laws)),
            ("RULEMINER_BASE", rules.display().to_string()),
        ]);
        env.push(write_laws(&cfg.family, &env, &out.join(format!("laws_mine_{name}.txt")), "RULEMINER_LAWFILE"));
        assert!(child("search::rule_miner", &env, &log), "rule_miner failed (see {})", log.display());
        // the chosen rules, then the learned preferences (`winner  OVER  loser` lines; the library file carries both)
        let text = std::fs::read_to_string(&log).unwrap();
        // the base rules a preference phase dropped leave the file
        let rule = |l: &str| (!l.contains("  OVER  ")).then(|| l.trim().split_once(" -> ")).flatten().map(|(a, b)| (parse_term(a.trim()), parse_term(b.trim())));
        let dropped: std::collections::HashSet<RuleKey> = text.lines().filter_map(|l| l.strip_prefix("RULEMINER drop (")).filter_map(|l| l.split_once("): ")).filter_map(|(_, r)| rule(r)).collect();
        if !dropped.is_empty() {
            let kept: String = std::fs::read_to_string(&rules).unwrap().lines().filter(|l| !rule(l).is_some_and(|r| dropped.contains(&r))).map(|l| format!("{l}\n")).collect();
            std::fs::write(&rules, kept).unwrap();
        }
        let chosen: String = text
            .lines()
            .filter(|l| (l.contains("RULEMINER chosen") || l.contains("RULEMINER prefer")) && l.contains(" -> "))
            .map(|l| format!("{}\n", l.split_once("): ").map_or(l, |(_, r)| r)))
            .collect();
        append(&rules, &chosen);
    };
    // (M, laws, laws that used up the rule budget) of the batch at `skip`
    let serve = |skip: usize| {
        let log = out.join(format!("serve_{skip}.log"));
        let mut env = with(&[("CHECK_FAST", s(cfg.check_fast as usize)), ("RULEMINER_SKIP", s(skip)), ("RULEMINER_LAWS", s(cfg.b)), ("CHECK_RULES", rules.display().to_string())]);
        env.push(write_laws(&cfg.family, &env, &out.join(format!("laws_serve_{skip}.txt")), "CHECK_LAWFILE"));
        child("search::rule_set_kernel_check", &env, &log);
        // CHECKED <n> laws kernel-checked (<k> with no whole-term machine proof), <p> not proved, <x> used up the rule budget
        let text = std::fs::read_to_string(&log).unwrap();
        let line = text.lines().find(|l| l.starts_with("CHECKED ")).unwrap_or_else(|| panic!("no CHECKED line (see {})", log.display()));
        let nums: Vec<usize> = line.split(|c: char| !c.is_ascii_digit()).filter_map(|w| w.parse().ok()).collect();
        let &[n, k, p, x] = &nums[..] else { panic!("unexpected CHECKED line: {line}") };
        (n - k + p, n + p, x)
    };
    match &cfg.warm {
        Some(w) => {
            std::fs::copy(w, &rules).unwrap_or_else(|e| panic!("WARM_RULES {}: {e}", w.display()));
        }
        _ => std::fs::write(&rules, "").unwrap(),
    }
    std::fs::write(out.join("m.tsv"), "").unwrap();
    if cfg.mode == "ref" {
        mine("ref", cfg.offset, cfg.b * cfg.k);
    }
    let (mut ms, mut exhausted) = (vec![], 0);
    for r in 0..cfg.k {
        let (skip, t0) = (cfg.offset + r * cfg.b, std::time::Instant::now());
        let (m, laws, ex) = serve(skip);
        append(&out.join("m.tsv"), &format!("{r}\t{m}\t{laws}\t{}\t{}\t{ex}\n", count(), t0.elapsed().as_secs()));
        ms.push(m);
        exhausted += ex;
        if cfg.mode == "loop" && r + 1 < cfg.k {
            mine(&r.to_string(), skip, cfg.b);
        }
    }
    let sum = Summary { total: ms.iter().sum(), ms, rules: count(), exhausted };
    println!("mode={} B={} K={} offset={} total_M={} rules={} exhausted={}", cfg.mode, cfg.b, cfg.k, cfg.offset, sum.total, sum.rules, sum.exhausted);
    sum
}

#[test]
#[ignore]
fn loop_stream() {
    let cfg = LoopCfg::from_env();
    machine_state("start");
    let lemmas = cfg.out.join("lemmas.bin");
    let _ = std::fs::remove_file(&lemmas);
    run_loop(&cfg, &lemmas);
    let _ = std::fs::remove_file(&lemmas);
    machine_state("end");
}

/// The ref mines: (family, stride, split, B); each mines K=4 batches of its phase-0 stream (2 threads, no round cap, full serving check).
/// u3 (the union of add3, sbo3 and cmp3d) is mined only when named (`mines:u3`).
const MINES: [(&str, usize, usize, usize); 5] =
    [("sbo3", 11, 2, 50), ("add3", 7, 2, 50), ("mix3", 1, 1, 50), ("cmp3d", 15, 2, 100), ("u3", 11, 2, 100)];
/// The loops' stride per family; each loop serves K=3 batches of B=100 on phases 1-3 (6 threads, no round cap, CHECK_FAST).
const LOOPS: [(&str, usize); 4] = [("cmp3d", 15), ("add3", 7), ("sbo3", 11), ("mix3", 7)];

#[test]
#[ignore]
fn sweep() {
    let out = PathBuf::from(std::env::var("SWEEP_OUT").expect("set SWEEP_OUT=<dir>"));
    std::fs::create_dir_all(&out).unwrap();
    let salt: usize = env_or("SALT", 1);
    let lib = std::env::var("LIB").map(PathBuf::from).unwrap_or_else(|_| out.clone());
    let stages = std::env::var("SWEEP").unwrap_or_else(|_| "mines own cold".into());
    let env = vec![("RULEMINER_FAST".to_string(), "1".to_string()), ("RULEMINER_SHUFFLE".to_string(), salt.to_string())];
    let base = |mode: &str, out: PathBuf, family: &str| LoopCfg {
        mode: mode.into(),
        out,
        family: family.into(),
        stride: 1,
        sphase: 0,
        b: 100,
        k: 3,
        offset: 0,
        threads: 6,
        rounds: usize::MAX,
        deep3: 1,
        split: 2,
        warm: None,
        check_fast: true,
        env: env.clone(),
    };
    let library = |fam: &str| lib.join(format!("lib_{fam}")).join("rules.txt");
    // `MINES_WARM=<sweep dir>`: each ref mine starts from that sweep's pooled library for its family, where there is one
    // (docs/tier-cycle.md, "Promotion as an iterated sweep": one iteration lowers the best loops 157 to 142, a second adds nothing)
    let mines_warm = |fam: &str| std::env::var("MINES_WARM").ok().map(|d| PathBuf::from(d).join(format!("pooled_{fam}")).join("rules.txt")).filter(|p| p.exists());
    // one lemma file for every loop of the sweep: all its processes run this exe, so every statement in it was checked by this build
    let lemmas = out.join("lemmas.bin");
    let _ = std::fs::remove_file(&lemmas);
    machine_state("start");
    for stage in stages.split_whitespace() {
        let (name, fams) = stage.split_once(':').unwrap_or((stage, if stage == "mines" { "sbo3,add3,mix3,cmp3d" } else { "cmp3d,add3,sbo3" }));
        let tsv = out.join(format!("{}.tsv", stage.replace(':', "_")));
        std::fs::write(&tsv, "").unwrap();
        if name == "mines" {
            for fam in fams.split(',') {
                let &(fam, stride, split, b) = MINES.iter().find(|m| m.0 == fam).unwrap_or_else(|| panic!("no ref mine for {fam}"));
                let cfg = LoopCfg { stride, split, b, k: 4, threads: 2, check_fast: false, warm: mines_warm(fam), ..base("ref", out.join(format!("lib_{fam}")), fam) };
                let t0 = std::time::Instant::now();
                let s = run_loop(&cfg, &lemmas);
                append(&tsv, &format!("{fam}\t{}\t{}\t{}\t{}\n", t0.elapsed().as_secs(), s.total, s.rules, s.exhausted));
            }
            continue;
        }
        let pooled = out.join("pooled.rules");
        let pooled_for = |fam: &str| out.join(format!("pooled_{fam}")).join("rules.txt");
        if name == "pooled" {
            // a section per library (`library_sections`; `parse_rules` reads a rule two libraries share once)
            let text: String = ["cmp3d", "add3", "sbo3"].iter().map(|fam| format!("# library {fam}\n{}\n", std::fs::read_to_string(library(fam)).unwrap().trim_end())).collect();
            std::fs::write(&pooled, &text).unwrap();
            let units = out.join("pooled.units");
            std::fs::write(&units, units_text(&joinability_units(&text, 4, env_or("RULEMINER_STEPS", 200i64)))).unwrap();
            std::fs::write(out.join("pooled_prefs.tsv"), "").unwrap();
            // the libraries' rules can conflict (two right sides for one left side, say); each family learns which wins, and which
            // rules where two libraries' normal forms meet to drop (`drop_units`), on its phase-0 stream: a mine with no rule
            // rounds, only preferences (`RULEMINER_PREFS`), on the pooled library
            for fam in fams.split(',') {
                let &(fam, stride, split, b) = MINES.iter().find(|m| m.0 == fam).unwrap_or_else(|| panic!("no ref mine for {fam}"));
                let mut cfg = LoopCfg { stride, split, b, k: 4, threads: 2, rounds: 0, warm: Some(pooled.clone()), ..base("ref", pooled_for(fam).parent().unwrap().into(), fam) };
                cfg.env.push(("RULEMINER_PREFS".into(), "1".into()));
                cfg.env.push(("RULEMINER_UNITS".into(), units.display().to_string()));
                let t0 = std::time::Instant::now();
                let s = run_loop(&cfg, &lemmas);
                append(&out.join("pooled_prefs.tsv"), &format!("{fam}\t{}\t{}\t{}\t{}\n", t0.elapsed().as_secs(), s.total, s.rules, s.exhausted));
            }
        }
        for fam in fams.split(',') {
            let stride = LOOPS.iter().find(|l| l.0 == fam).unwrap_or_else(|| panic!("no loop stride for {fam}")).1;
            let srcs: Vec<&str> = match name {
                "own" => vec![fam],
                "cold" => vec!["none"],
                "cross" => ["cmp3d", "add3", "sbo3"].into_iter().filter(|s| *s != fam).collect(),
                "pooled" => vec!["pooled"],
                "mixed" => vec!["u3"],
                _ => panic!("unknown stage {stage}"),
            };
            for src in srcs {
                let warm = match src {
                    "none" => None,
                    "pooled" => Some(pooled_for(fam)),
                    s => Some(library(s)),
                };
                for p in 1..=3 {
                    let dir = out.join(format!("{}_{fam}_{p}_{src}", stage.replace(':', "_")));
                    let cfg = LoopCfg { stride, sphase: p, warm: warm.clone(), ..base("loop", dir, fam) };
                    let t0 = std::time::Instant::now();
                    let s = run_loop(&cfg, &lemmas);
                    let ms: Vec<String> = s.ms.iter().map(|m| m.to_string()).collect();
                    append(&tsv, &format!("{fam}\t{stride}-{p}\tfrom_{src}\t{}\t{}\t{}\t{}\t{}\n", s.total, ms.join(","), s.rules, t0.elapsed().as_secs(), s.exhausted));
                }
            }
        }
    }
    let _ = std::fs::remove_file(&lemmas);
    machine_state("end");
}
