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
//!
//! `a_branch_that_goes_wrong_off_the_samples_is_never_installed` puts a
//! term that goes wrong behind `if x == OFF_SAMPLE`, where `verify()`'s
//! samples never reach it, so it tests the two static gates themselves
//! (RELATED_WORK.md §41).

use tatic::compile;
use tatic::eval;
use tatic::jit::JitEngine;
use tatic::proof;
use tatic::term::{Hash, PrimOp, Term, TermStore};
use tatic::{spec_check, specialise};

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
    gen_tail_recursive_with(rng, s, |rng, s| gen_expr(rng, s, 2, 3))
}

/// `gen_tail_recursive`, with `payload` (over `n` = `Var(1)` and `acc` =
/// `Var(0)`) generated by the caller.
fn gen_tail_recursive_with(rng: &mut Rng, s: &mut TermStore, payload: impl FnOnce(&mut Rng, &mut TermStore) -> Hash) -> (Hash, usize) {
    let n = s.var(1);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Le, n, zero);
    let base = s.var(0);
    let n2 = s.var(1);
    let one = s.lit(1);
    let n_minus_1 = s.prim(PrimOp::Sub, n2, one);
    let f = s.var(2);
    let payload = payload(rng, s);
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
    gen_non_tail_recursive_with(rng, s, |rng, s| gen_expr(rng, s, 1, 3))
}

/// `gen_non_tail_recursive`, with `payload` (over `n` = `Var(0)`)
/// generated by the caller.
fn gen_non_tail_recursive_with(rng: &mut Rng, s: &mut TermStore, payload: impl FnOnce(&mut Rng, &mut TermStore) -> Hash) -> (Hash, usize) {
    let n = s.var(0);
    let zero = s.lit(0);
    let cond = s.prim(PrimOp::Le, n, zero);
    let base = gen_expr(rng, s, 1, 2);
    let n2 = s.var(0);
    let one = s.lit(1);
    let n_minus_1 = s.prim(PrimOp::Sub, n2, one);
    let f = s.var(1);
    let rec_call = s.app(f, n_minus_1);
    let payload = payload(rng, s);
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
    assert_eq!(compile::spec_check_failures(), 0, "compile_specialised discarded a specialisation because spec_check::check rejected its trace -- a specialiser bug");
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
/// to confirm `jit.rs`'s typing gate declines exactly this case and falls
/// back to the interpreter, rather than by
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
        // (jit.rs's typing gate declines the ill-typed case this
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
    // the test that actually matters for soundness: jit.rs must decline
    // every one of these before installing it (the interpreter
    // type-errors; the compiled form traps or coincidentally produces some
    // value through a garbage `call_indirect` target). It does so
    // statically, since none is simply typed (`typing::well_typed`), so
    // `JitEngine::apply` agrees with `eval::apply_term` on every input,
    // not just the sampled ones.
    const SEEDS: u64 = 300;

    for seed in 0..SEEDS {
        let mut rng = Rng::new(0x00BA_D111_0000_u64 ^ seed);
        let mut s = TermStore::new();
        let over_applied = gen_over_applied(&mut rng, &mut s);

        let interpreted = eval::apply_term(&s, over_applied, &[]);
        let mut jit = JitEngine::new();
        let jitted = jit.apply(&s, over_applied, &[]);
        assert_eq!((jit.stats.compiled, jit.stats.declined_ill_typed), (0, 1), "seed={seed}: not declined as ill-typed");
        let agree = match (&interpreted, &jitted) {
            (Ok(a), Ok(b)) => a == b,
            (Err(_), Err(_)) => true,
            _ => false,
        };
        assert!(
            agree,
            "seed={seed}: an ill-typed over-application should still agree via jit.rs's typing gate\n\
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
    // just above: jit.rs's typing gate must decline it, so
    // `JitEngine::apply` agrees with `eval::apply_term` regardless of
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
            assert_eq!((jit.stats.compiled, jit.stats.declined_ill_typed), (0, 1), "seed={seed}: not declined as ill-typed");
            let agree = match (&interpreted, &jitted) {
                (Ok(a), Ok(b)) => a == b,
                (Err(_), Err(_)) => true,
                _ => false,
            };
            assert!(
                agree,
                "seed={seed} f={f_val}: an inconsistently-called parameter should still agree via jit.rs's typing gate\n\
                 interpreted={interpreted:?} jit={jitted:?}"
            );
        }
    }
    assert_no_ir_failures();
}

/// The one input the off-sample branch below is taken at. `jit.rs`'s
/// `SAMPLE_ARGS` (and the pairs and rotations it builds from them) never
/// reach it, so `verify()` can't see what that branch does.
const OFF_SAMPLE: i64 = 777;

/// A literal or one of the `scope` enclosing parameters, which sit at
/// `Var(skip..skip + scope)` under `skip` further binders.
fn gen_outer_leaf(rng: &mut Rng, s: &mut TermStore, skip: u32, scope: u32) -> Hash {
    if rng.below(2) == 0 {
        s.var(skip + rng.below(scope))
    } else {
        s.lit(rng.i64_range(-MAX_LIT, MAX_LIT))
    }
}

/// An expression that goes wrong, one of four ways. The first three are
/// ill-typed, so `eval` fails on them: a closure where an `Int` is
/// expected, an `Int` called, and a lambda over-applied. The fourth is
/// well typed but passes a two-argument closure where `g` is only ever
/// called with one (RELATED_WORK.md §40):
///
/// ```text
/// (\g. (\k. k e1) (g a) + (\k. k e2) (g b)) (\x. \y. body)
/// ```
///
/// where `body` captures a parameter, so the specialiser keeps `g` (used
/// twice) abstract. `eval` gives an `Int`; the compiled fragment, under
/// `Dispatch::Fast`, traps.
fn gen_goes_wrong(rng: &mut Rng, s: &mut TermStore, scope: u32) -> (Hash, usize) {
    let kind = rng.below(WRONG_KINDS.len() as u32) as usize;
    let h = match kind {
        0 => {
            let body = gen_expr(rng, s, scope + 1, 1);
            let clo = s.abs(body);
            let e = gen_expr(rng, s, scope, 1);
            let op = random_arith_op(rng);
            if rng.below(2) == 0 { s.prim(op, clo, e) } else { s.prim(op, e, clo) }
        }
        1 => {
            // A parameter, since `compile.rs` rejects any other head that
            // isn't a lambda (`Shape::OtherCall`) and the gate never sees it.
            let f = s.var(rng.below(scope));
            let a = gen_expr(rng, s, scope, 1);
            s.app(f, a)
        }
        2 => {
            let body = gen_expr(rng, s, scope + 1, 1);
            let lam = s.abs(body);
            let a = gen_expr(rng, s, scope, 1);
            let b = gen_expr(rng, s, scope, 1);
            let once = s.app(lam, a);
            s.app(once, b)
        }
        _ => {
            // Under `\g` (Var(0)); inside each `\k`, `k` is Var(0) and `g` Var(1).
            let half = |rng: &mut Rng, s: &mut TermStore| {
                let k = s.var(0);
                let e = gen_outer_leaf(rng, s, 2, scope);
                let ke = s.app(k, e);
                let apply_e = s.abs(ke);
                let g = s.var(0);
                let a = gen_outer_leaf(rng, s, 1, scope);
                let ga = s.app(g, a);
                s.app(apply_e, ga)
            };
            let l = half(rng, s);
            let r = half(rng, s);
            let op = random_arith_op(rng);
            let sum = s.prim(op, l, r);
            let wrap = s.abs(sum);
            // Under `\x. \y.`: `y` is Var(0), `x` Var(1), parameters from Var(2).
            let e = gen_expr(rng, s, scope + 2, 1);
            let captured = s.var(2 + rng.below(scope));
            let body = s.prim(PrimOp::Add, e, captured);
            let y = s.abs(body);
            let clo = s.abs(y);
            s.app(wrap, clo)
        }
    };
    (h, kind)
}

/// `gen_goes_wrong`'s kinds, in order.
const WRONG_KINDS: [&str; 4] = ["closure as Int", "Int called", "over-applied", "wrong arity"];

/// Where `gen_wrong_off_sample` puts its guarded branch.
const HOSTS: [&str; 4] = ["function", "tail loop", "non-tail recursion", "called parameter"];

/// `if x == OFF_SAMPLE then <goes wrong> else <gen_expr>`, over `scope`
/// parameters of which `x` is `Var(x)`, placed in one of three hosts: the
/// body of `\x1..xn.`, or the per-iteration payload of
/// `gen_tail_recursive`'s loop or `gen_non_tail_recursive`'s recursion. In
/// the last two, `x` is the counter, so the bad branch runs once the
/// counter reaches `OFF_SAMPLE` on its way down.
///
/// The fourth host is `\x1. \x2. if x2 == OFF_SAMPLE then x1 a else e`,
/// with `a` and `e` over `x2` alone, so `x1` is only ever called. The
/// other hosts almost always use a called parameter as an `Int` somewhere
/// too, and then no proof exists. Here `prove_closure_expr` proves a
/// theorem that types `x1` as a closure, which the JIT, always called
/// with `Int`s, can't rely on (RELATED_WORK.md §41).
///
/// Returns the term, its arity, and indices into `HOSTS` and
/// `WRONG_KINDS`.
fn gen_wrong_off_sample(rng: &mut Rng, s: &mut TermStore) -> (Hash, usize, usize, usize) {
    let mut kind = 0;
    let mut guarded = |rng: &mut Rng, s: &mut TermStore, scope: u32, x: u32| {
        let xv = s.var(x);
        let k = s.lit(OFF_SAMPLE);
        let cond = s.prim(PrimOp::Eq, xv, k);
        let wrong;
        (wrong, kind) = gen_goes_wrong(rng, s, scope);
        let fine = gen_expr(rng, s, scope, 3);
        s.if_(cond, wrong, fine)
    };
    let host = rng.below(HOSTS.len() as u32) as usize;
    let (h, arity) = match host {
        0 => {
            let arity = 1 + rng.below(2);
            let x = rng.below(arity);
            let mut term = guarded(rng, s, arity, x);
            for _ in 0..arity {
                term = s.abs(term);
            }
            (term, arity as usize)
        }
        1 => gen_tail_recursive_with(rng, s, |rng, s| guarded(rng, s, 2, 1)),
        2 => gen_non_tail_recursive_with(rng, s, |rng, s| guarded(rng, s, 1, 0)),
        _ => {
            kind = 1;
            let (x1, x2, k) = (s.var(1), s.var(0), s.lit(OFF_SAMPLE));
            let cond = s.prim(PrimOp::Eq, x2, k);
            let a = gen_expr(rng, s, 1, 1);
            let wrong = s.app(x1, a);
            let fine = gen_expr(rng, s, 1, 3);
            let body = s.if_(cond, wrong, fine);
            let inner = s.abs(body);
            (s.abs(inner), 2)
        }
    };
    (h, arity, host, kind)
}

#[test]
fn a_branch_that_goes_wrong_off_the_samples_is_never_installed() {
    // Every term here passes `verify()`'s samples wherever it compiles,
    // since its bad branch is taken only at `OFF_SAMPLE`. What keeps each
    // compiled form out is one of the two static gates: `typing::well_typed`
    // for the ill-typed branches (§38), the universal-proof gate for the
    // closure of the wrong arity (§40). With either gate disabled, this
    // test fails.
    const SEEDS: u64 = 600;
    const ARGS: [i64; 5] = [0, 1, -1, 7, OFF_SAMPLE];
    // What happened to each term: declined as ill-typed, declined for want
    // of a universal proof, installed, or never compiled at all.
    const OUTCOMES: [&str; 4] = ["ill-typed", "no proof", "installed", "not compiled"];

    let mut tally = [[[0u32; OUTCOMES.len()]; WRONG_KINDS.len()]; HOSTS.len()];
    for seed in 0..SEEDS {
        let mut rng = Rng::new(0x00FF_5A3F_0000_u64 ^ seed);
        let mut s = TermStore::new();
        let (h, arity, host, kind) = gen_wrong_off_sample(&mut rng, &mut s);

        let mut jit = JitEngine::new();
        for i in 0..ARGS.len().pow(arity as u32) {
            let args: Vec<i64> = (0..arity).map(|j| ARGS[i / ARGS.len().pow(j as u32) % ARGS.len()]).collect();
            let interpreted = eval::apply_term(&s, h, &args);
            let jitted = jit.apply(&s, h, &args);
            let agree = match (&interpreted, &jitted) {
                (Ok(a), Ok(b)) => a == b,
                (Err(_), Err(_)) => true,
                _ => false,
            };
            assert!(agree, "seed={seed} args={args:?}: interpreted={interpreted:?} jit={jitted:?} stats={:?}", jit.stats);
        }
        let st = &jit.stats;
        assert_eq!(st.verification_failures, 0, "seed={seed}: a sample reached the bad branch -- check OFF_SAMPLE");
        let outcome = match (st.declined_ill_typed, st.declined_no_universal_proof, st.compiled) {
            (1, 0, 0) => 0,
            (0, 1, 0) => 1,
            (0, 0, 1) => 2,
            (0, 0, 0) => 3,
            _ => panic!("seed={seed}: more than one outcome for one term: {st:?}"),
        };
        tally[host][kind][outcome] += 1;
    }

    for (host, by_kind) in HOSTS.iter().zip(&tally) {
        for (kind, counts) in WRONG_KINDS.iter().zip(by_kind) {
            let counts: Vec<String> = OUTCOMES.iter().zip(counts).map(|(o, n)| format!("{o} {n}")).collect();
            eprintln!("compile_fuzz off-sample: {host}, {kind}: {}", counts.join(", "));
        }
    }
    // Each ill-typed kind reaches the typing gate, and the wrong arity the
    // proof gate, in every host (the called-parameter host builds only
    // "Int called"); otherwise the generator has stopped testing what it
    // is for.
    for (h, host) in HOSTS.iter().enumerate() {
        for (k, kind) in WRONG_KINDS.iter().enumerate() {
            if h == 3 && k != 1 {
                continue;
            }
            let gate = if k == 3 { 1 } else { 0 };
            assert!(tally[h][k][gate] > 0, "{host}, {kind}: never reached the {} gate", OUTCOMES[gate]);
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

/// An Int-valued expression over `scope` variables that is full of βv
/// redexes: literal lambdas applied to values (literals, variables,
/// closed or capturing lambdas), two-argument spines, and redexes whose
/// argument is not a value (which must stay put). `Div`/`Mod` are
/// included so errors are exercised. There's no `Rec` and every applied
/// lambda is fresh, so every term terminates.
fn gen_redex_rich(rng: &mut Rng, s: &mut TermStore, scope: u32, fuel: u32) -> Hash {
    let leaf = |rng: &mut Rng, s: &mut TermStore| {
        if scope > 0 && rng.below(2) == 0 { s.var(rng.below(scope)) } else { s.lit(rng.i64_range(-3, MAX_LIT)) }
    };
    if fuel == 0 {
        return leaf(rng, s);
    }
    match rng.below(8) {
        0 => leaf(rng, s),
        1 => {
            let op = [PrimOp::Add, PrimOp::Sub, PrimOp::Mul, PrimOp::Div, PrimOp::Mod, PrimOp::Lt][rng.below(6) as usize];
            let a = gen_redex_rich(rng, s, scope, fuel - 1);
            let b = gen_redex_rich(rng, s, scope, fuel - 1);
            s.prim(op, a, b)
        }
        2 => {
            let c = gen_redex_rich(rng, s, scope, fuel - 1);
            let t = gen_redex_rich(rng, s, scope, fuel - 1);
            let e = gen_redex_rich(rng, s, scope, fuel - 1);
            s.if_(c, t, e)
        }
        3 => {
            // (\x. e) v, with v a leaf.
            let body = gen_redex_rich(rng, s, scope + 1, fuel - 1);
            let lam = s.abs(body);
            let v = leaf(rng, s);
            s.app(lam, v)
        }
        4 => {
            // (\x. e) a, with a not necessarily a value.
            let body = gen_redex_rich(rng, s, scope + 1, fuel - 1);
            let lam = s.abs(body);
            let a = gen_redex_rich(rng, s, scope, fuel - 1);
            s.app(lam, a)
        }
        5 => {
            // (\g. g e1 + e2) (\y. e3): a closure argument, called once,
            // possibly capturing. Inside \g, Var(0) is g.
            let g = s.var(0);
            let e1 = gen_redex_rich(rng, s, scope + 1, fuel - 1);
            let call = s.app(g, e1);
            let e2 = gen_redex_rich(rng, s, scope + 1, fuel - 1);
            let body = s.prim(PrimOp::Add, call, e2);
            let lam = s.abs(body);
            let fbody = gen_redex_rich(rng, s, scope + 1, fuel - 1);
            let f = s.abs(fbody);
            s.app(lam, f)
        }
        6 => {
            // (\a b. e) v1 v2
            let body = gen_redex_rich(rng, s, scope + 2, fuel - 1);
            let inner = s.abs(body);
            let lam = s.abs(inner);
            let (v1, v2) = (leaf(rng, s), leaf(rng, s));
            s.app2(lam, v1, v2)
        }
        _ => {
            // (\a b. e) v1: a partial application, then applied to v2 via a caller.
            let body = gen_redex_rich(rng, s, scope + 2, fuel - 1);
            let inner = s.abs(body);
            let add_like = s.abs(inner);
            let v1 = leaf(rng, s);
            let partial = s.app(add_like, v1);
            let (g, z) = (s.var(1), s.var(0));
            let gz = s.app(g, z);
            let c_inner = s.abs(gz);
            let caller = s.abs(c_inner);
            let v2 = leaf(rng, s);
            s.app2(caller, partial, v2)
        }
    }
}

/// Runs a compiled fragment directly, with no `verify()` or proof gate in
/// between, the way `jit.rs` calls it: a fresh bump allocator per call
/// (`hp` reset to 0) and a trap mapped to `Err`.
fn load_fragment(engine: &wasmtime::Engine, frag: &compile::CompiledFragment) -> wasmtime::Module {
    let bytes = wat::parse_str(&frag.wat).expect("compile.rs emits valid wat");
    wasmtime::Module::new(engine, &bytes).expect("compile.rs emits a valid module")
}

fn run_fragment(engine: &wasmtime::Engine, module: &wasmtime::Module, args: &[i64]) -> Result<i64, ()> {
    let mut store = wasmtime::Store::new(engine, ());
    let instance = wasmtime::Instance::new(&mut store, module, &[]).expect("the module has no imports");
    if let Some(hp) = instance.get_global(&mut store, "hp") {
        hp.set(&mut store, wasmtime::Val::I32(0)).unwrap();
    }
    let f = instance.get_func(&mut store, "f").expect("the entry point is exported as f");
    let wargs: Vec<wasmtime::Val> = args.iter().map(|&a| wasmtime::Val::I64(a)).collect();
    let mut out = [wasmtime::Val::I64(0)];
    f.call(&mut store, &wargs, &mut out).map_err(|_| ())?;
    Ok(out[0].unwrap_i64())
}

#[test]
fn specialisation_is_checked_and_preserves_meaning_on_random_terms() {
    const SEEDS: u64 = 1000;
    const SAMPLE_VALUES: [i64; 7] = [0, 1, -1, 2, -3, 10, -20];
    let engine = wasmtime::Engine::default();
    let (mut specialised, mut compiled, mut compiled_specialised, mut ran, mut declined) = (0u32, 0u32, 0u32, 0u32, 0u32);
    for seed in 0..SEEDS {
        let mut rng = Rng::new(0x5BEC_1A11_u64 ^ seed);
        let mut s = TermStore::new();
        // Mostly redex-rich terms and the existing programs (recursion,
        // closures), plus some open terms, which the checker rejects.
        let (h, arity, open) = match seed % 5 {
            0 | 2 => {
                let e = gen_redex_rich(&mut rng, &mut s, 2, 4);
                let inner = s.abs(e);
                (s.abs(inner), 2, false)
            }
            4 => {
                // `\x1..xn. v`, with `v` unbound. On odd rounds, `v` is put
                // under a redex, `\x1..xn. (\y. 0) v`: contracting it would
                // hide the UnboundVariable error, so the open-source guard
                // has something to refuse.
                let unbound = gen_unbound_variable(&mut rng, &mut s);
                let (mut arity, mut body) = (0, unbound);
                while let Term::Abs(b) = *s.resolve(body) {
                    arity += 1;
                    body = b;
                }
                let h = if (seed / 5) % 2 == 0 {
                    unbound
                } else {
                    let zero = s.lit(0);
                    let k0 = s.abs(zero);
                    let mut h = s.app(k0, body);
                    for _ in 0..arity {
                        h = s.abs(h);
                    }
                    h
                };
                (h, arity, true)
            }
            _ => {
                let (h, arity, _) = gen_program(&mut rng, &mut s);
                (h, arity, false)
            }
        };
        let sp = specialise::specialise(&s, h);
        if open {
            assert!(sp.trace.is_empty(), "seed={seed}: an open source was specialised: {:?}", sp.trace);
            assert_eq!(spec_check::check(&s, h, &sp.trace, sp.term).unwrap_err().reason, "source term has free variables", "seed={seed}");
        } else {
            assert_eq!(spec_check::check(&s, h, &sp.trace, sp.term), Ok(()), "seed={seed}: the checker rejected the specialiser's trace");
        }
        if !sp.trace.is_empty() {
            specialised += 1;
        }
        let c = compile::compile_specialised(&s, h);
        if let Some(c) = &c {
            compiled += 1;
            if c.specialised.is_some() {
                compiled_specialised += 1;
            }
            assert_eq!(c.frag.arity, arity, "seed={seed}");
        }
        let module = c.as_ref().map(|c| load_fragment(&engine, &c.frag));
        let typed = tatic::typing::well_typed(&s, h, arity);
        if c.is_some() && !typed {
            declined += 1;
        }
        let mut jit = JitEngine::new();
        let mut args = vec![0i64; arity];
        for trial in 0..8 {
            for a in args.iter_mut() {
                *a = SAMPLE_VALUES[rng.below(SAMPLE_VALUES.len() as u32) as usize];
            }
            let interpreted = eval::apply_term(&s, h, &args);
            // Exact equality, including which error: βv moves only values,
            // which have no effects, so it can't reorder or remove an error.
            assert_eq!(eval::apply_term(&sp.store, sp.term, &args), interpreted, "seed={seed} trial={trial} args={args:?}");
            // The JIT, gate and all, whether or not the term is typed.
            let jitted = jit.apply(&s, h, &args);
            assert_eq!(jitted.as_ref().ok(), interpreted.as_ref().ok(), "seed={seed} trial={trial} args={args:?}: JIT disagrees");
            // Type safety: a simply typed term can't go wrong.
            if typed {
                assert!(
                    !matches!(
                        interpreted,
                        Err(eval::EvalError::TypeError | eval::EvalError::NotAFunction | eval::EvalError::UnboundVariable)
                    ),
                    "seed={seed} trial={trial} args={args:?}: well_typed accepted a term that goes wrong: {interpreted:?} h={}",
                    tatic::syntax::print(&s, h)
                );
            }
            // The compiled output, with nothing between it and the caller.
            // Errors are compared as errors: a compiled one is a trap. Only
            // for a simply typed term: `gen_redex_rich` can use a closure as
            // an `Int` (case 5 puts `g` in scope), and compiled code can't
            // tell them apart (seed 95: `try_compile(h)` returns 310 where
            // `eval` is a TypeError). `jit.rs` declines such terms with the
            // same `typing::well_typed` check.
            if let (Some(c), Some(module)) = (&c, &module)
                && typed
            {
                ran += 1;
                assert_eq!(
                    run_fragment(&engine, module, &args).ok(),
                    interpreted.as_ref().ok().copied(),
                    "seed={seed} trial={trial} args={args:?} specialised={} interpreted={interpreted:?} h={}",
                    c.specialised.is_some(),
                    tatic::syntax::print(&s, h)
                );
            }
        }
    }
    eprintln!("specialisation fuzz: {specialised}/{SEEDS} terms specialised, {compiled} compiled ({compiled_specialised} from h'), {ran} compiled runs compared, {declined} compiled but ill-typed");
    assert!(declined > 0, "no ill-typed term compiled, so the typing gate went untested");
    assert!(specialised > SEEDS as u32 / 4, "too few terms specialised ({specialised}/{SEEDS}); check gen_redex_rich");
    assert!(compiled_specialised > SEEDS as u32 / 10, "too few specialised terms compiled ({compiled_specialised}/{SEEDS})");
    assert_no_ir_failures();
}
