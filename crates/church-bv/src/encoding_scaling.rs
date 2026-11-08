//! The encoding's scaling and profiling tests that read a `Setup` or run in a `Job` (church-bv types), over
//! `tatic_wasm::encoding`; all ignored, run by name.
use super::*;

/// Build and check time of one lemma at the widths in `env` (comma separated, else `default`), each built and checked
/// inside one `scoped` call so the proof is interned as it is built (design doc section 69); `NO_SCOPE=1` is the
/// unscoped control. Prints `<label> n=..: build .., check .., proof dag=..`. `lemma_times.sh` (in the gitignored `scripts/experiments/`, kept on one machine)
/// runs the callers by name.
fn scaling_scoped(label: &str, env: &str, default: &str, build: impl Fn(usize) -> (Expr, Expr)) {
    let job = &Job::new(Setup::process());
    let ns: Vec<usize> = job.setup().var(env).unwrap_or(default).split(',').map(|v| v.trim().parse().unwrap()).collect();
    for n in ns {
        let body = || {
            let t0 = Instant::now();
            let (proof, stmt) = build(n);
            let built = t0.elapsed();
            let t1 = Instant::now();
            job.lemmas.ck(&format!("n={n}"), &proof, &stmt);
            println!("{label} n={n}: build {built:?}, check {:?}, proof dag={}", t1.elapsed(), tatic_kernel::term_sizes(&proof).0);
        };
        if job.setup().flag("NO_SCOPE", false) { body() } else { tatic_kernel::scoped(body) }
    }
}

/// `add x 0 = x` (`scaling_scoped`, widths `ZERO_NS`).
#[test]
#[ignore]
pub fn add_zero_lemma_scaling_scoped() {
    scaling_scoped("SCOPED", "ZERO_NS", "8,16,32,64,128,256,512", |n| add_zero_proof(n, 0));
}

/// `add x y = add y x` (`scaling_scoped`, widths `COMM_NS`; design doc section 81).
#[test]
#[ignore]
pub fn add_comm_scaling_scoped() {
    scaling_scoped("COMM-SCOPED", "COMM_NS", "8,16,32,64", |n| add_comm_proof(n, false));
}

/// One check of the universal `add x 0 = x` lemma for profiling (`SAMPLY.md`), with no timing: width `PROFILE_N`
/// (default 64); built and checked inside one `scoped` call with `PROFILE_SCOPED=1`; on a thread with a
/// `PROFILE_STACK_MB` stack when set (1024 keeps `grow` from ever needing a new segment). The profiling task passes no
/// environment, so these go in `<exe>.env` beside the profiled exe.
#[test]
#[ignore]
pub fn profile_add_zero() {
    let setup = Setup::process();
    let (n, scoped, stack_mb) = (setup.or("PROFILE_N", 64usize), setup.flag("PROFILE_SCOPED", false), setup.or("PROFILE_STACK_MB", 0usize));
    let run = move || {
        let check = || {
            let (proof, stmt) = add_zero_proof(n, 0);
            ck(&format!("profile n={n}"), &proof, &stmt)
        };
        if scoped { tatic_kernel::scoped(check) } else { check() }
    };
    if stack_mb == 0 { run() } else { std::thread::Builder::new().stack_size(stack_mb << 20).spawn(run).unwrap().join().unwrap() }
}

/// `add (add x y) z = add x (add y z)` (`scaling_scoped`, widths `ASSOC_NS`).
#[test]
#[ignore]
pub fn add_assoc_scaling_scoped() {
    scaling_scoped("ASSOC-SCOPED", "ASSOC_NS", "8,16,32,64", |n| add_assoc_proof(n, false));
}
