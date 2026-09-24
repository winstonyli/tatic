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
//! the complementary property: a term deliberately built *outside* the
//! fragment (a genuinely unbound variable) must always come back `None`
//! from `try_compile`, not get silently accepted and miscompiled. The
//! first test alone couldn't catch a regression here -- a generator that
//! only ever produces in-fragment terms has nothing to say about what
//! should be rejected. Over-application of a plain `Int`-returning
//! literal lambda, and a parameter called with inconsistent arities
//! across call sites, both used to belong here too, but neither is
//! unconditionally rejected by `try_compile` anymore -- see
//! `over_applied_ill_typed_terms_still_agree_with_the_interpreter` and
//! `inconsistently_called_parameters_still_agree_with_the_interpreter`,
//! which check the soundness property that actually matters for each
//! (jit.rs's own verification/fallback still agrees with the
//! interpreter) rather than blanket rejection.

use tatic::compile;
use tatic::eval;
use tatic::jit::JitEngine;
use tatic::proof;
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
    match rng.below(5) {
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
        2 | 3 => gen_closure_block(rng, s, scope, fuel - 1),
        _ => gen_over_application_block(rng, s, scope, fuel - 1),
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

/// Builds a literal lambda (arity 1 or 2) whose own body, once saturated,
/// resolves to a *further* closure -- an `If` between two literal lambdas
/// of the same arity, the only shape `compile::peel` can't already fold
/// into one flat combinator (see `lower_wat.rs`'s "Over-application"
/// docs) -- then over-applies it with exactly that closure's own arity of
/// extra arguments, exercising compile.rs's/proof.rs's over-application
/// dispatch (`combinator_return_type` correctly classifying the root as
/// `Clo`-returning) on a genuinely well-typed term, distinct from
/// `gen_over_applied`'s own ill-typed, arithmetic-bodied terms in
/// `compile_rejects_out_of_scope_terms_cleanly`. Both inner closures may
/// capture from the root's own parameters, not just the outer `scope`,
/// matching `gen_closure_block`'s own capturing convention. Always
/// resolves to a plain `Int`, safe to embed anywhere `gen_expr` is used.
fn gen_over_application_block(rng: &mut Rng, s: &mut TermStore, scope: u32, fuel: u32) -> Hash {
    let root_arity = 1 + rng.below(2); // 1 or 2
    let extra_arity = 1 + rng.below(2); // 1 or 2
    let inner_scope = root_arity + extra_arity;

    let inner_body1 = gen_expr(rng, s, inner_scope, fuel);
    let mut closure1 = inner_body1;
    for _ in 0..extra_arity {
        closure1 = s.abs(closure1);
    }

    let inner_body2 = gen_expr(rng, s, inner_scope, fuel);
    let mut closure2 = inner_body2;
    for _ in 0..extra_arity {
        closure2 = s.abs(closure2);
    }

    let cond = gen_cond(rng, s, root_arity, fuel);
    let root_body = s.if_(cond, closure1, closure2);
    let mut root = root_body;
    for _ in 0..root_arity {
        root = s.abs(root);
    }

    let mut applied = root;
    for _ in 0..(root_arity + extra_arity) {
        let arg = gen_expr(rng, s, scope, fuel);
        applied = s.app(applied, arg);
    }
    applied
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
/// (`compile_var_read`'s, now `build_read`'s, capture-slot formula didn't match `free_vars`'s
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

/// `rec f g n x = if n <= 0 then x else f(g, n-1, (g x) OP payload)`,
/// wrapped as `\n2 x2. it(g_init, n2, x2)` -- `g_init` (a fresh,
/// non-capturing `\y. ...`) baked in as the initial closure-typed
/// loop-carried parameter, since there's no way to hand a real `Clo`
/// value in through a plain-`i64` arg the way `n2`/`x2` are.
///
/// This is a recursion *signature* `gen_tail_recursive` never produces
/// (always `(n, acc)`, no closure-typed formal parameter at all), so it's
/// the only generator here that exercises `call_indirect` on a
/// loop-carried closure parameter every iteration -- and, since `payload`
/// can itself be a `gen_closure_block`, sometimes combines that with a
/// *second*, independently created-and-called closure inside the same
/// self-call argument, a shape nothing else here produces either.
///
/// Returns the wrapped, runnable term (`Hash`, arity 2) plus the bare
/// self-recursive `it` on its own -- `jit.rs`'s own `kernel_verify`
/// cascade tries `prove_closure_expr`'s opaque "self-recursive combinator
/// called directly" postulate on the *wrapped* term before ever reaching
/// `prove_tail_recursive_universal` (see `jit::tests::
/// a_closure_typed_loop_carried_parameter_compiles_and_is_kernel_verified`'s
/// own docs for why), so fuzzing the wrapped term alone would never
/// actually exercise `build_universal`'s closure-typed-parameter pipeline
/// at all -- `it` is checked directly against
/// `prove_tail_recursive_universal` instead, below.
fn gen_closure_typed_recursive(rng: &mut Rng, s: &mut TermStore) -> (Hash, usize, Hash) {
    let x = s.var(0);
    let n = s.var(1);
    let g = s.var(2);
    let payload = gen_expr(rng, s, 2, 2); // scope: x=Var(0), n=Var(1) -- g excluded, it's Clo-typed
    let op = random_arith_op(rng);
    let gx = s.app(g, x);
    let new_x = s.prim(op, gx, payload);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Le, n, zero);
    let one = s.lit(1);
    let n_minus_1 = s.prim(PrimOp::Sub, n, one);
    let f = s.var(3);
    let f_g = s.app(f, g);
    let f_g_n1 = s.app(f_g, n_minus_1);
    let rec_call = s.app(f_g_n1, new_x);
    let body = s.if_(cond, x, rec_call);
    let x_abs = s.abs(body);
    let n_abs = s.abs(x_abs);
    let g_abs = s.abs(n_abs);
    let it = s.rec(g_abs);

    // g_init = \y. gen_expr(...) -- non-capturing, matching the `inc` used
    // by benches::closure_typed_loop_carried_parameter_loop and
    // jit::tests::a_closure_typed_loop_carried_parameter_compiles_and_is_kernel_verified.
    let g_body = gen_expr(rng, s, 1, 2);
    let g_init = s.abs(g_body);

    let n2 = s.var(1);
    let x2 = s.var(0);
    let g_n2 = s.app(it, g_init);
    let g_n2_n2 = s.app(g_n2, n2);
    let top_body = s.app(g_n2_n2, x2);
    let x2_abs = s.abs(top_body);
    let top = s.abs(x2_abs);
    (top, 2, it)
}

fn gen_program(rng: &mut Rng, s: &mut TermStore) -> (Hash, usize, Option<Hash>) {
    match rng.below(4) {
        0 => {
            let (h, arity) = gen_non_recursive(rng, s);
            (h, arity, None)
        }
        1 => {
            let (h, arity) = gen_tail_recursive(rng, s);
            (h, arity, None)
        }
        2 => {
            let (h, arity) = gen_non_tail_recursive(rng, s);
            (h, arity, None)
        }
        _ => {
            let (h, arity, it) = gen_closure_typed_recursive(rng, s);
            (h, arity, Some(it))
        }
    }
}

/// These fuzzers run `--release`, where an ill-formed IR from the builder
/// is only a silent rejection (the hit-rate thresholds are too loose to
/// notice it). The counter is process-wide, so any test's failure shows.
fn assert_no_ir_failures() {
    assert_eq!(compile::ir_check_failures(), 0, "the IR builder produced an ill-formed module (ir::check) -- a builder bug");
    assert_eq!(compile::ir_validation_failures(), 0, "try_compile accepted a module that failed translation validation (decompile::decompile) -- a builder bug or a decompiler false alarm");
}

#[test]
fn compiled_and_interpreted_agree_on_random_terms() {
    // Raised from 250: that default silently missed a real push_pap_env
    // clobbering bug (then in src/compile.rs; now Lowering::pap_env) for the entire time it was in the
    // tree -- only a background stress run at 3,000 seeds caught it. The
    // bug itself is now permanently pinned by its own regression test in
    // compile.rs, but this bump is about future, still-unknown bugs: a
    // default four times stronger, without inflating routine `cargo test`
    // runs to the 4-5 minute range 3,000 seeds costs in a debug build.
    const SEEDS: u64 = 1000;
    const TRIALS_PER_SEED: u32 = 12;
    const SAMPLE_VALUES: [i64; 7] = [0, 1, -1, 2, -3, 10, -20];

    let mut compiled_count = 0u32;
    let mut universal_proof_count = 0u32;

    for seed in 0..SEEDS {
        let mut rng = Rng::new(0x00C0_FFEE_1E55_u64 ^ seed);
        let mut s = TermStore::new();
        let (h, arity, closure_typed_recursive) = gen_program(&mut rng, &mut s);

        // Fuzzes proof.rs's own closure-typed-parameter pipeline directly:
        // jit.rs's kernel_verify cascade never reaches
        // prove_tail_recursive_universal for `h` itself here (see
        // gen_closure_typed_recursive's own docs for why), so this is the
        // only way this generator's random bodies ever exercise it.
        // prove_tail_recursive_universal already gates its own result on
        // kernel::check internally (see proof.rs), so `is_some()` here is
        // already a real, independently re-typechecked proof, not just a
        // "didn't crash" check.
        if let Some(it) = closure_typed_recursive {
            assert!(
                proof::prove_tail_recursive_universal(&s, it).is_some(),
                "seed={seed}: a closure-typed loop-carried parameter recursion should always get a universal proof"
            );
            universal_proof_count += 1;
        }

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

    eprintln!("compile_fuzz: {compiled_count}/{SEEDS} generated programs actually compiled ({universal_proof_count} closure-typed-recursive)");
    assert!(
        compiled_count > SEEDS as u32 / 10,
        "hit rate suspiciously low ({compiled_count}/{SEEDS}) -- check the generator itself, \
         not just compile.rs"
    );
    assert!(
        universal_proof_count > 0,
        "no closure-typed loop-carried parameter recursion was ever generated -- check gen_program's own odds"
    );
    assert_no_ir_failures();
}

/// A literal lambda (arity 1 or 2, an arbitrary `gen_expr`-generated body)
/// applied to more arguments than its own arity. `compile.rs` now compiles
/// this shape (see its module docs: a saturated call whose own result is
/// dispatched through `call_indirect`, exactly like calling a closure-typed
/// variable) -- but `gen_expr`'s bodies are always plain arithmetic, never
/// a further closure, so every term this generates is genuinely ill-typed
/// (over-applying an `Int`), still outside what compile.rs can *correctly*
/// compile even though `try_compile` itself no longer rejects the shape
/// outright. Used by `over_applied_ill_typed_terms_still_agree_with_the_interpreter`
/// to confirm `jit.rs`'s own sample verification catches exactly this case
/// and falls back to the interpreter, rather than by
/// `compile_rejects_out_of_scope_terms_cleanly` (which is about `try_compile`
/// alone).
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
/// function. `f` is left as a genuinely free parameter here (not baked
/// in via an enclosing application to a concrete literal lambda), so
/// whatever value it's called with at runtime is essentially always
/// "garbage" as a closure -- this generator is for
/// `inconsistently_called_parameters_still_agree_with_the_interpreter`'s
/// own soundness check (jit.rs's verification/fallback still agrees with
/// the interpreter), not for anything claiming to be well-typed. See
/// `compile::tests` for hand-built, well-typed, runnable versions of this
/// same shape (bound to a real literal lambda, with only one of the two
/// call sites ever actually reached at runtime).
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

        // Over-application is no longer unconditionally rejected here --
        // see `gen_over_applied`'s own docs and
        // `over_applied_ill_typed_terms_still_agree_with_the_interpreter`
        // below, which covers the complementary property for this shape
        // (jit.rs's verification catches the ill-typed case this
        // generator always produces, rather than try_compile rejecting it
        // outright). Still draws from `rng` here, unused, so every other
        // sub-case below keeps drawing the exact same random values per
        // seed it always has.
        let mut s1 = TermStore::new();
        let _ = gen_over_applied(&mut rng, &mut s1);

        // Likewise no longer unconditionally rejected -- see
        // `gen_inconsistent_arity`'s own docs and
        // `inconsistently_called_parameters_still_agree_with_the_interpreter`
        // below.
        let mut s2 = TermStore::new();
        let _ = gen_inconsistent_arity(&mut rng, &mut s2);

        let mut s3 = TermStore::new();
        let unbound = gen_unbound_variable(&mut rng, &mut s3);
        assert!(
            compile::try_compile(&s3, unbound).is_none(),
            "seed={seed}: a genuinely unbound variable should be rejected"
        );
    }
    assert_no_ir_failures();
}

#[test]
fn over_applied_ill_typed_terms_still_agree_with_the_interpreter() {
    // gen_over_applied always produces a genuinely ill-typed term
    // (over-applying a plain Int-returning literal lambda, never one that
    // returns a further closure -- see its own docs). compile.rs now
    // compiles the shape rather than rejecting it outright, so this is
    // the test that actually matters for soundness: jit.rs's own sample
    // verification must catch every one of these (the interpreter
    // type-errors, the compiled form traps or -- vanishingly unlikely --
    // coincidentally produces some value through a garbage
    // `call_indirect` target) and fall back to the interpreter, so
    // `JitEngine::apply` still agrees with `eval::apply_term` regardless.
    const SEEDS: u64 = 300;

    for seed in 0..SEEDS {
        let mut rng = Rng::new(0x00BA_D111_0000_u64 ^ seed);
        let mut s = TermStore::new();
        let over_applied = gen_over_applied(&mut rng, &mut s);

        let interpreted = eval::apply_term(&s, over_applied, &[]);
        let mut jit = JitEngine::new();
        let jitted = jit.apply(&s, over_applied, &[]);
        let agree = match (&interpreted, &jitted) {
            (Ok(a), Ok(b)) => a == b,
            (Err(_), Err(_)) => true,
            _ => false,
        };
        assert!(
            agree,
            "seed={seed}: an ill-typed over-application should still agree via jit.rs's own verification\n\
             interpreted={interpreted:?} jit={jitted:?}"
        );
    }
    assert_no_ir_failures();
}

#[test]
fn inconsistently_called_parameters_still_agree_with_the_interpreter() {
    // gen_inconsistent_arity leaves `f` as a genuinely free parameter,
    // so whatever value it's called with is essentially always garbage
    // as a closure (the interpreter type-errors calling a plain `Int`;
    // the compiled form, now that this shape goes through the curried
    // dispatch mechanism instead of being rejected outright, either
    // traps or -- vanishingly unlikely -- coincidentally produces some
    // value through a garbage `call_indirect` target). Same soundness
    // property, and same reasoning, as
    // `over_applied_ill_typed_terms_still_agree_with_the_interpreter`
    // just above: jit.rs's own verification/fallback must still make
    // `JitEngine::apply` agree with `eval::apply_term` regardless of
    // what `f` happens to be.
    const SEEDS: u64 = 300;
    const SAMPLE_ARGS: [i64; 5] = [0, 1, -1, 12345, -98765];

    for seed in 0..SEEDS {
        let mut rng = Rng::new(0x00BA_D222_0000_u64 ^ seed);
        let mut s = TermStore::new();
        let inconsistent = gen_inconsistent_arity(&mut rng, &mut s);

        for &f_val in &SAMPLE_ARGS {
            let interpreted = eval::apply_term(&s, inconsistent, &[f_val]);
            let mut jit = JitEngine::new();
            let jitted = jit.apply(&s, inconsistent, &[f_val]);
            let agree = match (&interpreted, &jitted) {
                (Ok(a), Ok(b)) => a == b,
                (Err(_), Err(_)) => true,
                _ => false,
            };
            assert!(
                agree,
                "seed={seed} f={f_val}: an inconsistently-called parameter should still agree via jit.rs's own verification\n\
                 interpreted={interpreted:?} jit={jitted:?}"
            );
        }
    }
    assert_no_ir_failures();
}

#[test]
fn over_application_block_terms_compile_and_mostly_get_kernel_checked_proofs() {
    // The complementary, *well-typed* counterpart to `gen_over_applied`:
    // `gen_over_application_block` (woven into `gen_expr`'s own dispatch,
    // so `compiled_and_interpreted_agree_on_random_terms` already
    // exercises it indirectly) is called *directly* here, bypassing the
    // rest of the generator tree, so a regression in over-application's
    // own compile.rs/proof.rs support shows up as a compilation or
    // kernel-verification rate drop rather than being masked by
    // `compiled_and_interpreted_agree_on_random_terms`'s own "agree"
    // check -- which a rejected-and-fallen-back-to-the-interpreter term
    // would trivially satisfy too, so it alone can't tell "compiles
    // correctly" from "never even tries."
    const SEEDS: u64 = 300;
    const TRIALS_PER_SEED: u32 = 12;
    const SAMPLE_VALUES: [i64; 7] = [0, 1, -1, 2, -3, 10, -20];

    let mut compiled_count = 0u32;
    let mut kernel_verified_count = 0u32;

    for seed in 0..SEEDS {
        let mut rng = Rng::new(0x0BE5_7A55_0000_u64 ^ seed);
        let mut s = TermStore::new();
        let arity = 1 + rng.below(2) as usize;
        let body = gen_over_application_block(&mut rng, &mut s, arity as u32, 3);
        let mut term = body;
        for _ in 0..arity {
            term = s.abs(term);
        }

        let mut jit = JitEngine::new();
        let mut args = vec![0i64; arity];
        for trial in 0..TRIALS_PER_SEED {
            for a in args.iter_mut() {
                *a = SAMPLE_VALUES[rng.below(SAMPLE_VALUES.len() as u32) as usize];
            }
            let interpreted = eval::apply_term(&s, term, &args);
            let jitted = jit.apply(&s, term, &args);
            let agree = match (&interpreted, &jitted) {
                (Ok(a), Ok(b)) => a == b,
                (Err(_), Err(_)) => true,
                _ => false,
            };
            assert!(
                agree,
                "seed={seed} trial={trial} args={args:?}: over-application block term mismatch\n\
                 interpreted={interpreted:?} jit={jitted:?}"
            );
        }
        if jit.stats.compiled > 0 {
            compiled_count += 1;
        }
        if jit.is_kernel_verified(term) {
            kernel_verified_count += 1;
        }
    }

    assert!(
        compiled_count > SEEDS as u32 / 2,
        "well-typed over-application terms should mostly compile ({compiled_count}/{SEEDS}) -- check compile.rs's own over-application support, not just this generator"
    );
    assert!(
        kernel_verified_count > 0,
        "at least some well-typed over-application terms should get a kernel-checked proof -- check combinator_return_type/call_ref"
    );
    assert_no_ir_failures();
}
