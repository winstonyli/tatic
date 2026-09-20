//! Fuzzes `kernel.rs`'s own type-checker directly: random, mostly
//! ill-typed (and sometimes genuinely malformed -- out-of-range `Var`
//! indices, a universe level at `u32::MAX`, mismatched `Pi`/`Lam`
//! domains) `Expr` trees, confirming `infer`/`check`/`typecheck` only
//! ever return `Ok` or `Err`, never panic.
//!
//! This is a different property from `compile_fuzz.rs`'s own semantic
//! fuzzing, which only ever feeds `jit::JitEngine`/`eval::apply_term`
//! terms translated from `proof.rs`'s own postulate-based denotations --
//! by construction, always well-typed on both readings. Here there is no
//! well-typedness discipline at all: most generated trees are simply
//! rejected with an ordinary `Err`, which is the expected, uninteresting
//! outcome on almost every trial. The only property under test is that
//! the type-checker itself never panics while getting there -- a
//! robustness guarantee for a kernel meant to reject bad proofs cleanly,
//! not crash the process trying.
//!
//! Deterministic (the same tiny splitmix64 PRNG `compile_fuzz.rs` uses),
//! seed-scanned, bounded generation depth (`MAX_DEPTH`) so a failure is a
//! genuine kernel bug, not just the generator building an implausibly
//! deep tree.

use tatic::kernel::{self, Expr};

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Rng(seed)
    }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: u32) -> u32 {
        (self.next_u64() % n as u64) as u32
    }
}

const MAX_DEPTH: u32 = 6;

/// A leaf `Expr`: a `Var` (sometimes genuinely in `scope`, sometimes
/// deliberately at or past its edge, sometimes wildly out of range) or a
/// `Sort` (occasionally `u32::MAX`, exercising the exact overflow this
/// fuzzer's own first run caught -- see `kernel.rs`'s own
/// `a_maximal_universe_level_is_a_clean_type_error_not_an_overflow_panic`).
fn gen_leaf(rng: &mut Rng, scope: u32) -> Expr {
    match rng.below(4) {
        0 if scope > 0 => Expr::Var(rng.below(scope)),
        0 | 1 => Expr::Var(rng.below(scope.max(1) + 3)), // in range, or just past it
        2 => Expr::Var(rng.below(1000)), // almost always wildly unbound
        _ => {
            if rng.below(20) == 0 {
                Expr::Sort(u32::MAX)
            } else {
                Expr::Sort(rng.below(4))
            }
        }
    }
}

/// `scope` tracks how many binders actually enclose the expression being
/// built (only `Pi`/`Lam`/`W`'s own second child sees one more than its
/// parent -- matching `kernel.rs`'s own `shift`/`subst` cutoff
/// convention exactly), so `gen_leaf`'s "genuinely in scope" `Var` case
/// picks an index that's actually bound somewhere, not just plausible.
fn gen_expr(rng: &mut Rng, scope: u32, depth: u32) -> Expr {
    if depth == 0 || rng.below(4) == 0 {
        return gen_leaf(rng, scope);
    }
    let d = depth - 1;
    match rng.below(9) {
        0 => kernel::pi(gen_expr(rng, scope, d), gen_expr(rng, scope + 1, d)),
        1 => kernel::lam(gen_expr(rng, scope, d), gen_expr(rng, scope + 1, d)),
        2 => kernel::app(gen_expr(rng, scope, d), gen_expr(rng, scope, d)),
        3 => kernel::id(gen_expr(rng, scope, d), gen_expr(rng, scope, d), gen_expr(rng, scope, d)),
        4 => kernel::refl(gen_expr(rng, scope, d)),
        5 => kernel::wty(gen_expr(rng, scope, d), gen_expr(rng, scope + 1, d)),
        6 => kernel::sup(gen_expr(rng, scope, d), gen_expr(rng, scope, d)),
        7 => kernel::jelim(
            gen_expr(rng, scope, d),
            gen_expr(rng, scope, d),
            gen_expr(rng, scope, d),
            gen_expr(rng, scope, d),
            gen_expr(rng, scope, d),
        ),
        _ => kernel::wrec(gen_expr(rng, scope, d), gen_expr(rng, scope + 1, d), gen_expr(rng, scope, d), gen_expr(rng, scope, d)),
    }
}

#[test]
fn kernel_typecheck_never_panics_on_random_expr_trees() {
    const SEEDS: u64 = 5000;
    for seed in 0..SEEDS {
        let mut rng = Rng::new(0xF00D_BABE_u64 ^ seed);
        let e = gen_expr(&mut rng, 0, MAX_DEPTH);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| kernel::typecheck(&e)));
        assert!(result.is_ok(), "kernel::typecheck panicked on seed={seed}: {e:?}");
    }
}

/// `check`'s own top-level `Lam`-against-`Pi` special case (checking the
/// lambda's body one binder deeper, against the `Pi`'s codomain) is a
/// distinct code path from anything `infer`'s own `Lam` case exercises
/// (which never calls `check` against an externally-supplied expected
/// type at all) -- `kernel_typecheck_never_panics_on_random_expr_trees`
/// above, built entirely on `typecheck` (an `infer` call at the root),
/// never reaches it. Fuzzed directly here instead: an independently
/// generated `Lam` checked against an independently generated `Pi`, so
/// domain mismatches and deeper structural mismatches are both common.
#[test]
fn kernel_check_never_panics_on_random_lambda_against_random_pi() {
    const SEEDS: u64 = 5000;
    for seed in 0..SEEDS {
        let mut rng = Rng::new(0xFEED_FACE_u64 ^ seed);
        let dom = gen_expr(&mut rng, 0, MAX_DEPTH);
        let body = gen_expr(&mut rng, 1, MAX_DEPTH);
        let e = kernel::lam(dom, body);
        let expected_dom = gen_expr(&mut rng, 0, MAX_DEPTH);
        let expected_cod = gen_expr(&mut rng, 1, MAX_DEPTH);
        let expected = kernel::pi(expected_dom, expected_cod);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| kernel::check(&Vec::new(), &e, &expected)));
        assert!(result.is_ok(), "kernel::check panicked on seed={seed}: e={e:?} expected={expected:?}");
    }
}
