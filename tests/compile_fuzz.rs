//! Randomized differential testing: generate random terms (with a bias
//! toward the closure/capture/self-recursion interactions that produced
//! two real indexing bugs earlier -- found by hand-deriving the De Bruijn
//! arithmetic, not by any test failure), and confirm `jit::JitEngine`
//! (compiled, when `compile.rs` accepts the term) and `eval::apply_term`
//! (the reference interpreter) always agree, for every generated term and
//! a battery of argument values per term -- not just the fixed, small
//! sample set `jit.rs`'s own internal `verify()` checks before trusting a
//! compile.
//!
//! Every generated term is built to be well-typed on both readings (a
//! closure sub-expression is always fully resolved back to an `Int`
//! before it's used anywhere an `Int` is expected -- see
//! `gen_closure_block`), so a genuine mismatch here means a real
//! divergence between the two readings, not an artifact of feeding one
//! side a value it doesn't know how to interpret.
//!
//! Deterministic (a tiny splitmix64 PRNG, no new dependency) and
//! seed-scanned rather than reliant on one lucky draw -- a failure prints
//! the seed and argument trial that triggered it, enough to reproduce.
//!
//! A second test, `compile_rejects_out_of_scope_terms_cleanly`, checks
//! the complementary property: terms deliberately built *outside* the
//! fragment (over-applying a literal lambda, calling a parameter with
//! inconsistent arities, a genuinely unbound variable) must always come
//! back `None` from `try_compile`, not get silently accepted and
//! miscompiled. The first test alone couldn't catch a regression here --
//! a generator that only ever produces in-fragment terms has nothing to
//! say about what should be rejected.

use tatic::compile;
use tatic::eval;
use tatic::jit::JitEngine;
use tatic::term::{Hash, PrimOp, TermStore};

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

    fn i64_range(&mut self, lo: i64, hi: i64) -> i64 {
        lo + (self.next_u64() % ((hi - lo + 1) as u64)) as i64
    }
}

const MAX_LIT: i64 = 50;

fn random_arith_op(rng: &mut Rng) -> PrimOp {
    // Div/Mod deliberately excluded: a div-by-zero Err on both readings
    // still "agrees" (see the comparison below), but it's noise unrelated
    // to what this fuzzer is actually chasing (closure/capture indexing),
    // and skewing generation toward hitting it wastes trials.
    [PrimOp::Add, PrimOp::Sub, PrimOp::Mul][rng.below(3) as usize]
}

fn random_cmp_op(rng: &mut Rng) -> PrimOp {
    [PrimOp::Lt, PrimOp::Le, PrimOp::Eq][rng.below(3) as usize]
}

fn gen_leaf(rng: &mut Rng, s: &mut TermStore, scope: u32) -> Hash {
    if scope > 0 && rng.below(2) == 0 {
        s.var(rng.below(scope))
    } else {
        s.lit(rng.i64_range(-MAX_LIT, MAX_LIT))
    }
}

fn gen_cond(rng: &mut Rng, s: &mut TermStore, scope: u32, fuel: u32) -> Hash {
    let a = gen_expr(rng, s, scope, fuel);
    let b = gen_expr(rng, s, scope, fuel);
    let op = random_cmp_op(rng);
    s.prim(op, a, b)
}

/// Generates an `Int`-valued expression, referencing any of `scope` bound
/// variables (`Var(0..scope)` all valid), using up to `fuel` further
/// levels of structure. Always denotes an `Int` on both readings --
/// `gen_closure_block` never leaves a bare closure value where an `Int`
/// is expected.
fn gen_expr(rng: &mut Rng, s: &mut TermStore, scope: u32, fuel: u32) -> Hash {
    if fuel == 0 || rng.below(3) == 0 {
        return gen_leaf(rng, s, scope);
    }
    match rng.below(4) {
        0 => {
            let a = gen_expr(rng, s, scope, fuel - 1);
            let b = gen_expr(rng, s, scope, fuel - 1);
            let op = random_arith_op(rng);
            s.prim(op, a, b)
        }
        1 => {
            let c = gen_cond(rng, s, scope, fuel - 1);
            let t = gen_expr(rng, s, scope, fuel - 1);
            let e = gen_expr(rng, s, scope, fuel - 1);
            s.if_(c, t, e)
        }
        _ => gen_closure_block(rng, s, scope, fuel - 1),
    }
}

/// Builds a nested lambda (arity 1 or 2, capturing freely from `scope`),
/// then fully resolves it back to an `Int`: either a direct, fully
/// saturated call, or -- when under-applied -- completed through a
/// wrapper (`\g y1..yk. g(y1,...,yk)`) that calls the resulting partial
/// closure with the remaining arguments, exercising the compile-time
/// partial-application desugaring the same way. Either way the result is
/// always a plain `Int`, safe to embed anywhere `gen_expr` is used.
fn gen_closure_block(rng: &mut Rng, s: &mut TermStore, scope: u32, fuel: u32) -> Hash {
    let inner_arity = 1 + rng.below(2); // 1 or 2
    let inner_scope = scope + inner_arity;
    let inner_body = gen_expr(rng, s, inner_scope, fuel);
    let mut inner = inner_body;
    for _ in 0..inner_arity {
        inner = s.abs(inner);
    }

    let supplied = rng.below(inner_arity + 1); // 0..=inner_arity
    let mut applied = inner;
    for _ in 0..supplied {
        let arg = gen_expr(rng, s, scope, fuel);
        applied = s.app(applied, arg);
    }

    if supplied == inner_arity {
        return applied; // fully applied directly -- an ordinary Int result
    }

    let remaining = inner_arity - supplied;
    let mut remaining_args = Vec::new();
    for _ in 0..remaining {
        remaining_args.push(gen_expr(rng, s, scope, fuel));
    }

    // caller = \g y1..yk. g(y1,...,yk) -- arity 1+remaining, binds nothing
    // captured of its own (Abs is unlabeled, so the wrapping order below
    // doesn't matter, only the count and the indices the body was built
    // against): g = Var(remaining) [outermost/first-applied], y_i (1-based)
    // = Var(remaining - i).
    let g_var = s.var(remaining);
    let mut call_g = g_var;
    for i in 0..remaining {
        let y_i = s.var(remaining - 1 - i);
        call_g = s.app(call_g, y_i);
    }
    let mut caller = call_g;
    for _ in 0..(1 + remaining) {
        caller = s.abs(caller);
    }

    let mut call_caller = s.app(caller, applied);
    for r in remaining_args {
        call_caller = s.app(call_caller, r);
    }
    call_caller
}

/// `\x1..xn. gen_expr(...)` -- not self-recursive, arity 1 or 2.
fn gen_non_recursive(rng: &mut Rng, s: &mut TermStore) -> (Hash, usize) {
    let arity = 1 + rng.below(2) as usize;
    let body = gen_expr(rng, s, arity as u32, 3);
    let mut term = body;
    for _ in 0..arity {
        term = s.abs(term);
    }
    (term, arity)
}

/// `rec f n acc = if n <= 0 then acc else f(n - 1, acc OP payload)` --
/// tail-recursive (loop/br in compile.rs), 2-ary. `payload` can reference
/// both `n` and `acc`, and may itself contain closure blocks capturing
/// either.
fn gen_tail_recursive(rng: &mut Rng, s: &mut TermStore) -> (Hash, usize) {
    let n = s.var(1);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Le, n, zero);
    let base = s.var(0);
    let n2 = s.var(1);
    let one = s.lit(1);
    let n_minus_1 = s.prim(PrimOp::Sub, n2, one);
    let f = s.var(2);
    let payload = gen_expr(rng, s, 2, 3);
    let op = random_arith_op(rng);
    let acc2 = s.var(0);
    let new_acc = s.prim(op, acc2, payload);
    let rec_call = s.app2(f, n_minus_1, new_acc);
    let body = s.if_(cond, base, rec_call);
    let inner = s.abs(body);
    let abs = s.abs(inner);
    (s.rec(abs), 2)
}

/// `rec f n = if n <= 0 then base else payload OP f(n - 1)` -- genuinely
/// non-tail (an ordinary Wasm `call`, not a loop), 1-ary. `payload` (and
/// `base`) can reference `n` and may contain closure blocks capturing
/// it -- exercises a self-recursive combinator that also captures
/// something from its own scope, the exact shape a real bug was found in
/// (`compile_var_read`'s capture-slot formula didn't match `free_vars`'s
/// for a self-recursive function with a genuine outward capture).
fn gen_non_tail_recursive(rng: &mut Rng, s: &mut TermStore) -> (Hash, usize) {
    let n = s.var(0);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Le, n, zero);
    let base = gen_expr(rng, s, 1, 2);
    let n2 = s.var(0);
    let one = s.lit(1);
    let n_minus_1 = s.prim(PrimOp::Sub, n2, one);
    let f = s.var(1);
    let rec_call = s.app(f, n_minus_1);
    let payload = gen_expr(rng, s, 1, 3);
    let op = random_arith_op(rng);
    let else_branch = s.prim(op, payload, rec_call);
    let body = s.if_(cond, base, else_branch);
    let abs = s.abs(body);
    (s.rec(abs), 1)
}

fn gen_program(rng: &mut Rng, s: &mut TermStore) -> (Hash, usize) {
    match rng.below(3) {
        0 => gen_non_recursive(rng, s),
        1 => gen_tail_recursive(rng, s),
        _ => gen_non_tail_recursive(rng, s),
    }
}

#[test]
fn compiled_and_interpreted_agree_on_random_terms() {
    const SEEDS: u64 = 250;
    const TRIALS_PER_SEED: u32 = 12;
    const SAMPLE_VALUES: [i64; 7] = [0, 1, -1, 2, -3, 10, -20];

    let mut compiled_count = 0u32;

    for seed in 0..SEEDS {
        let mut rng = Rng::new(0x00C0_FFEE_1E55_u64 ^ seed);
        let mut s = TermStore::new();
        let (h, arity) = gen_program(&mut rng, &mut s);

        let mut jit = JitEngine::new();
        let mut args = vec![0i64; arity];
        for trial in 0..TRIALS_PER_SEED {
            for a in args.iter_mut() {
                *a = SAMPLE_VALUES[rng.below(SAMPLE_VALUES.len() as u32) as usize];
            }
            let interpreted = eval::apply_term(&s, h, &args);
            let jitted = jit.apply(&s, h, &args);
            let agree = match (&interpreted, &jitted) {
                (Ok(a), Ok(b)) => a == b,
                (Err(_), Err(_)) => true,
                _ => false,
            };
            assert!(
                agree,
                "compiled/interpreted mismatch: seed={seed} trial={trial} arity={arity} args={args:?}\n\
                 interpreted={interpreted:?} jit={jitted:?} compiled={}",
                jit.stats.compiled > 0,
            );
        }
        if jit.stats.compiled > 0 {
            compiled_count += 1;
        }
    }

    eprintln!("compile_fuzz: {compiled_count}/{SEEDS} generated programs actually compiled");
    assert!(
        compiled_count > SEEDS as u32 / 10,
        "hit rate suspiciously low ({compiled_count}/{SEEDS}) -- check the generator itself, \
         not just compile.rs"
    );
}

/// A literal lambda (arity 1 or 2, an arbitrary `gen_expr`-generated body)
/// applied to more arguments than its own arity -- always over-applied,
/// unconditionally outside the fragment (see `compile.rs`'s module docs).
fn gen_over_applied(rng: &mut Rng, s: &mut TermStore) -> Hash {
    let arity = 1 + rng.below(2);
    let body = gen_expr(rng, s, arity, 2);
    let mut lit = body;
    for _ in 0..arity {
        lit = s.abs(lit);
    }
    let extra = 1 + rng.below(2);
    let mut applied = lit;
    for _ in 0..(arity + extra) {
        let arg = s.lit(rng.i64_range(-MAX_LIT, MAX_LIT));
        applied = s.app(applied, arg);
    }
    applied
}

/// `\f. f(a_1..a_k1) OP f(b_1..b_k2)`, `k1 != k2` -- a parameter called
/// with inconsistent arities at two different call sites in the same
/// function. Unlike an under-applied *literal* lambda, there's no fixed
/// arity for a parameter to desugar around, so this stays unconditionally
/// outside the fragment.
fn gen_inconsistent_arity(rng: &mut Rng, s: &mut TermStore) -> Hash {
    let k1 = 1 + rng.below(2);
    let k2 = k1 + 1 + rng.below(2); // always different from k1
    let f1 = s.var(0);
    let mut call1 = f1;
    for _ in 0..k1 {
        let arg = s.lit(rng.i64_range(-MAX_LIT, MAX_LIT));
        call1 = s.app(call1, arg);
    }
    let f2 = s.var(0);
    let mut call2 = f2;
    for _ in 0..k2 {
        let arg = s.lit(rng.i64_range(-MAX_LIT, MAX_LIT));
        call2 = s.app(call2, arg);
    }
    let op = random_arith_op(rng);
    let body = s.prim(op, call1, call2);
    s.abs(body)
}

/// `\x1..xn. Var(k)` with `k` clearly beyond `n` -- genuinely unbound (no
/// enclosing scope at all, since this term *is* the whole top-level
/// entry point), not a capture of anything.
fn gen_unbound_variable(rng: &mut Rng, s: &mut TermStore) -> Hash {
    let arity = 1 + rng.below(2);
    let out_of_range = arity + 1 + rng.below(3);
    let unbound = s.var(out_of_range);
    let mut term = unbound;
    for _ in 0..arity {
        term = s.abs(term);
    }
    term
}

#[test]
fn compile_rejects_out_of_scope_terms_cleanly() {
    const SEEDS: u64 = 300;

    for seed in 0..SEEDS {
        let mut rng = Rng::new(0x00BA_D000_0000_u64 ^ seed);

        let mut s1 = TermStore::new();
        let over_applied = gen_over_applied(&mut rng, &mut s1);
        assert!(
            compile::try_compile(&s1, over_applied).is_none(),
            "seed={seed}: an over-applied literal lambda should be rejected"
        );

        let mut s2 = TermStore::new();
        let inconsistent = gen_inconsistent_arity(&mut rng, &mut s2);
        assert!(
            compile::try_compile(&s2, inconsistent).is_none(),
            "seed={seed}: a parameter called with inconsistent arities should be rejected"
        );

        let mut s3 = TermStore::new();
        let unbound = gen_unbound_variable(&mut rng, &mut s3);
        assert!(
            compile::try_compile(&s3, unbound).is_none(),
            "seed={seed}: a genuinely unbound variable should be rejected"
        );
    }
}
