//! Fuzzes `kernel.rs` for an actual *soundness* violation -- not just
//! crash-safety (`kernel_fuzz.rs`'s own, narrower property: `infer`/
//! `check`/`typecheck` never panic on garbage). The property under test
//! here is sharper and closer to what the whole project's "kernel-checked
//! equivalence proof" claim actually rests on: given two postulated
//! constants of the same type with *no* axiom in the context relating
//! them, `kernel::check` must never accept *any* term as a proof that
//! they're propositionally equal (`Id(A, a, b)`).
//!
//! This is deliberately not "is `a` `def_eq` `b`" -- a *postulated*
//! equality (e.g. one of `proof.rs`'s own `ArithPostulates` axioms) is
//! legitimately `Id`-provable without being computationally/
//! definitionally equal at all; that's the entire point of postulating
//! axioms rather than deriving everything from nothing (see
//! `kernel.rs`'s own `Postulates` docs). The soundness question this file
//! asks is narrower and sharper: can the kernel be tricked into accepting
//! `Id(A, a, b)` for a pair that *nothing* in the context actually
//! relates? If it ever can, that's a genuine soundness bug -- the kernel
//! would have derived a false proposition from nothing, the exact failure
//! mode that would make every kernel-checked proof this project produces
//! worthless regardless of how much proof-coverage work sits on top of it.
//!
//! Two complementary strategies, both checked against the same unrelated
//! pair's `Id`-claim:
//! - Pure random generation (`gen_expr`, adapted from `kernel_fuzz.rs`'s
//!   own generator, widened to reference the richer postulated context
//!   built here) of a candidate proof term.
//! - Mutation (`mutate_once`, a random single-node substitution or
//!   subtree swap) of a proof that's genuinely valid for a *different*,
//!   actually-related pair -- far more likely to land near a checker bug
//!   than blind generation, since it starts from a well-typed skeleton
//!   instead of an almost-certainly-ill-formed random tree.
//!
//! Deterministic (the same splitmix64 PRNG the other fuzz files use),
//! seed-scanned, bounded generation depth.

use tatic::kernel::{self, Expr, Node, Postulates};

struct Rng {
    state: u64,
    consts: bool,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Rng { state: seed, consts: false }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: u32) -> u32 {
        (self.next_u64() % n as u64) as u32
    }
}

const MAX_DEPTH: u32 = 5;
const GLOBALS: u32 = 7;

/// With `rng.consts` set, one leaf in three names a constant instead --
/// in the constant-form context's range, or just past it -- so generated
/// terms can reach `Const`s at all; the branch draws no random number
/// when `consts` is false, so the existing tests' streams are untouched.
fn gen_leaf(rng: &mut Rng, scope: u32) -> Expr {
    if rng.consts && rng.below(3) == 0 {
        return kernel::mk(Node::Const(rng.below(GLOBALS + 2)));
    }
    match rng.below(4) {
        0 if scope > 0 => kernel::var(rng.below(scope)),
        0 | 1 => kernel::var(rng.below(scope.max(1) + 3)),
        2 => kernel::var(rng.below(1000)),
        _ => {
            if rng.below(20) == 0 {
                kernel::sort(u32::MAX)
            } else {
                kernel::sort(rng.below(4))
            }
        }
    }
}

/// Same shape as `kernel_fuzz.rs`'s own generator -- duplicated rather
/// than shared, matching this codebase's existing per-fuzz-file
/// convention (each fuzz file is a standalone `tests/*.rs` binary; see
/// `compile_fuzz.rs`'s own note on why the PRNG itself isn't shared
/// either).
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

// --- generic subterm access, for mutation -------------------------------

/// Total node count of `e` (itself included), pre-order.
fn count_nodes(e: &Expr) -> u32 {
    let mut n = 1;
    e.node().for_kids(|c, _| n += count_nodes(c));
    n
}

/// The subterm at pre-order position `target` (same numbering
/// `count_nodes` implies) -- `target` must be `< count_nodes(e)`.
fn nth_subterm(e: &Expr, target: u32, counter: &mut u32) -> Expr {
    let my_idx = *counter;
    *counter += 1;
    if my_idx == target {
        return e.clone();
    }
    let mut kids = Vec::new();
    e.node().for_kids(|c, _| kids.push(c.clone()));
    for child in &kids {
        let nc = count_nodes(child);
        if target < *counter + nc {
            return nth_subterm(child, target, counter);
        }
        *counter += nc;
    }
    unreachable!("target out of range")
}

/// Rebuilds `e`, replacing the subterm at pre-order position `target`
/// with `replacement` -- everything else copied unchanged. `target` must
/// be `< count_nodes(e)`.
fn replace_nth(e: &Expr, target: u32, counter: &mut u32, replacement: &Expr) -> Expr {
    let my_idx = *counter;
    *counter += 1;
    if my_idx == target {
        return replacement.clone();
    }
    match e.node() {
        Node::Var(_) | Node::Sort(_) | Node::Const(_) | Node::Free(_) => e.clone(),
        n => kernel::mk(n.map_kids(|c, _| replace_nth(&c, target, counter, replacement))),
    }
}

/// One random single-point mutation of `e`: either a structural swap
/// (replace one subterm with another subterm already present somewhere
/// in `e`) or a leaf substitution (a wildly different `Var`/`Sort`).
/// `scope` bounds the fresh `Var`/`Sort` alternatives to plausible-ish
/// values, matching `gen_leaf`'s own convention.
fn mutate_once(rng: &mut Rng, e: &Expr, scope: u32) -> Expr {
    let total = count_nodes(e);
    let target = rng.below(total);
    let replacement = match rng.below(3) {
        0 => {
            let other = rng.below(total);
            let mut c = 0;
            nth_subterm(e, other, &mut c)
        }
        1 => kernel::var(rng.below(scope.max(1) + 5)),
        _ => kernel::sort(rng.below(5)),
    };
    let mut c = 0;
    replace_nth(e, target, &mut c, &replacement)
}

/// `e` with its references to an `n`-entry context turned into constants.
/// Under `d` binders, `Var(d + i)` for `i < n` is entry `n - 1 - i`, so it
/// becomes `Const(n - 1 - i)`. A `Var` past the context drops by `n`,
/// still unbound. Bound variables stay.
fn to_consts(e: &Expr, n: u32, d: u32) -> Expr {
    match e.node() {
        Node::Var(k) if k < d => e.clone(),
        Node::Var(k) if k - d < n => kernel::mk(Node::Const(n - 1 - (k - d))),
        Node::Var(k) => kernel::var(k - n),
        Node::Sort(_) | Node::Const(_) | Node::Free(_) => e.clone(),
        m => kernel::mk(m.map_kids(|c, under| to_consts(&c, n, d + under as u32))),
    }
}

/// The context's postulates as globals: entry `i` was written under `i`
/// earlier entries. Since stage 3a, `ctx.p.globals` is already in `Const` form
/// (`push` bakes it in through the new `get`), so this conversion is now
/// the identity on every caller here; kept as a guard in case that ever
/// changes back.
fn to_globals(globals: &kernel::Globals) -> kernel::Globals {
    globals.iter().enumerate().map(|(i, ty)| kernel::persist(to_consts(&ty.get(), i as u32, 0))).collect()
}

/// The inverse of `to_consts`: `e` with references to the `n`-entry
/// constant environment turned back into references to an `n`-entry local
/// context, as if `d` binders were already pushed on top of it.
fn to_vars(e: &Expr, n: u32, d: u32) -> Expr {
    match e.node() {
        Node::Const(l) if l < n => kernel::var(d + (n - 1 - l)),
        Node::Var(_) | Node::Sort(_) | Node::Const(_) | Node::Free(_) => e.clone(),
        m => kernel::mk(m.map_kids(|c, under| to_vars(&c, n, d + under as u32))),
    }
}

/// `build_ctx`'s seven postulates as a plain `Var`-based local context --
/// exactly what `Postulates::push`/`get` produced here before postulates
/// became `Const`s (stage 3a). `to_consts`/`to_globals` already convert
/// *from* this shape; `the_global_environment_agrees_with_the_context`
/// needs the shape itself, since `build_ctx`'s own `ctx.p.globals` no longer
/// stores it -- `push`ing through the new `get` bakes `Const`s into it
/// instead.
fn build_var_ctx() -> kernel::Ctx {
    let mut ctx = kernel::Ctx::new();
    ctx.push_back(kernel::sort(0)); // 0: A : Type0
    ctx.push_back(kernel::sort(0)); // 1: B : Type0
    ctx.push_back(kernel::var(1)); // 2: a : A
    ctx.push_back(kernel::var(2)); // 3: b : A
    ctx.push_back(kernel::var(3)); // 4: c : A
    ctx.push_back(kernel::id(kernel::var(4), kernel::var(2), kernel::var(0))); // 5: pac : Id(A, a, c)
    ctx.push_back(kernel::arrow(kernel::var(5), kernel::var(4))); // 6: f : A -> B
    ctx
}

/// A moderately rich postulated context: a base type `A`, three of its
/// elements `a`/`b`/`c` (only `a`/`c` related, via `pac`; `a`/`b` and
/// `b`/`c` are *not* related by anything in the context), and a function
/// `f : A -> B` into a second base type -- enough surface for `sym`/
/// `trans_proof`/`cong1` to each have something genuine to build from,
/// while keeping `a`/`b` themselves deliberately unrelated: that pair is
/// this file's own target claim throughout.
struct Ctx {
    p: Postulates,
    a_ty: Expr,
    b_ty: Expr,
    a: Expr,
    b: Expr,
    c: Expr,
    pac: Expr, // : Id(A, a, c)
    f: Expr,   // : A -> B
}

fn build_ctx() -> Ctx {
    let mut p = Postulates::new();
    let a_ty_pos = p.push(kernel::sort(0));
    let b_ty_pos = p.push(kernel::sort(0));
    let a_pos = p.push(p.get(a_ty_pos));
    let b_pos = p.push(p.get(a_ty_pos));
    let c_pos = p.push(p.get(a_ty_pos));
    let pac_pos = p.push(kernel::id(p.get(a_ty_pos), p.get(a_pos), p.get(c_pos)));
    let f_pos = p.push(kernel::arrow(p.get(a_ty_pos), p.get(b_ty_pos)));

    Ctx {
        a_ty: p.get(a_ty_pos),
        b_ty: p.get(b_ty_pos),
        a: p.get(a_pos),
        b: p.get(b_pos),
        c: p.get(c_pos),
        pac: p.get(pac_pos),
        f: p.get(f_pos),
        p,
    }
}

/// A pool of proof terms genuinely valid for *some* claim this context's
/// own postulates actually back -- each paired with that claim, purely as
/// a sanity check that the pool itself is real (not a fuzzer bug), never
/// used as the target claim itself (that's always `Id(A, a, b)` below,
/// the one pair nothing here relates).
fn valid_seed_pool(ctx: &Ctx) -> Vec<Expr> {
    vec![
        kernel::refl(ctx.a.clone()),
        ctx.pac.clone(),
        kernel::sym(&ctx.a_ty, &ctx.a, &ctx.c, ctx.pac.clone()),
        kernel::trans_proof(&ctx.a_ty, &ctx.a, &ctx.c, &ctx.a, ctx.pac.clone(), kernel::sym(&ctx.a_ty, &ctx.a, &ctx.c, ctx.pac.clone())),
        kernel::cong1(&ctx.a_ty, &ctx.b_ty, &ctx.f, ctx.a.clone(), ctx.c.clone(), ctx.pac.clone()),
    ]
}

#[test]
fn the_seed_pool_itself_is_genuinely_valid() {
    // Not a soundness check -- just confirms this file's own fixtures
    // aren't accidentally ill-typed, which would make every other test
    // here vacuous (a fuzzer whose "valid" seeds don't even typecheck
    // proves nothing about mutations of them).
    let ctx = build_ctx();
    ctx.p.check(&kernel::refl(ctx.a.clone()), &kernel::id(ctx.a_ty.clone(), ctx.a.clone(), ctx.a.clone())).expect("refl(a) : Id(A,a,a)");
    ctx.p.check(&ctx.pac, &kernel::id(ctx.a_ty.clone(), ctx.a.clone(), ctx.c.clone())).expect("the postulate itself should check against its own type");
    ctx.p.check(
        &kernel::sym(&ctx.a_ty, &ctx.a, &ctx.c, ctx.pac.clone()),
        &kernel::id(ctx.a_ty.clone(), ctx.c.clone(), ctx.a.clone()),
    )
    .expect("sym(pac) : Id(A,c,a)");
    ctx.p.check(
        &kernel::cong1(&ctx.a_ty, &ctx.b_ty, &ctx.f, ctx.a.clone(), ctx.c.clone(), ctx.pac.clone()),
        &kernel::id(ctx.b_ty.clone(), kernel::app(ctx.f.clone(), ctx.a.clone()), kernel::app(ctx.f.clone(), ctx.c.clone())),
    )
    .expect("cong1(f, pac) : Id(B, f a, f c)");
}

/// The core soundness property, exercised via pure random generation: no
/// randomly generated term, however it's shaped, should ever check
/// against `Id(A, a, b)` -- nothing in the context relates `a` and `b`,
/// so any `Ok` here is a genuine false-equality acceptance.
#[test]
fn kernel_never_accepts_a_random_term_as_proving_an_unrelated_equality() {
    const SEEDS: u64 = 20_000;
    let ctx = build_ctx();
    let claim = kernel::id(ctx.a_ty.clone(), ctx.a.clone(), ctx.b.clone());
    for seed in 0..SEEDS {
        let mut rng = Rng::new(0xC0FF_EE00_u64 ^ seed);
        let candidate = gen_expr(&mut rng, ctx.p.globals.len() as u32, MAX_DEPTH);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| ctx.p.check(&candidate, &claim)));
        match result {
            Ok(Err(_)) => {} // expected: declined
            Ok(Ok(())) => panic!("SOUNDNESS BUG: seed={seed} kernel accepted a random term as proof of {claim:?} (nothing relates a and b): {candidate:?}"),
            Err(_) => panic!("kernel::check panicked on seed={seed}: candidate={candidate:?}"),
        }
    }
}

/// The sharper version: mutate a proof that's genuinely valid for some
/// *other*, actually-related claim, and re-check it against `Id(A, a,
/// b)`. Starting from a well-typed skeleton is far more likely to land
/// near a real checker bug (a missed shift, a substitution applied at
/// the wrong depth, `J`'s motive-substitution logic, `WRec`'s own
/// reduction) than blind random generation, which almost always produces
/// something `infer` rejects immediately on totally unrelated grounds.
#[test]
fn mutating_a_genuinely_valid_proof_never_fools_the_kernel_into_an_unrelated_equality() {
    const SEEDS: u64 = 20_000;
    let ctx = build_ctx();
    let claim = kernel::id(ctx.a_ty.clone(), ctx.a.clone(), ctx.b.clone());
    let pool = valid_seed_pool(&ctx);
    for seed in 0..SEEDS {
        let mut rng = Rng::new(0xBAD_C0DE_u64 ^ seed);
        let base = &pool[rng.below(pool.len() as u32) as usize];
        // One or two rounds of mutation -- deeper corruption than a
        // single point change, without drifting all the way back to
        // pure random generation (the other test's own job).
        let rounds = 1 + rng.below(2);
        let mut mutant = base.clone();
        for _ in 0..rounds {
            mutant = mutate_once(&mut rng, &mutant, ctx.p.globals.len() as u32);
        }
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| ctx.p.check(&mutant, &claim)));
        match result {
            Ok(Err(_)) => {}
            Ok(Ok(())) => panic!(
                "SOUNDNESS BUG: seed={seed} a mutation of a genuinely valid proof was accepted as proof of {claim:?} (nothing relates a and b): base={base:?} mutant={mutant:?}"
            ),
            Err(_) => panic!("kernel::check panicked on seed={seed}: base={base:?} mutant={mutant:?}"),
        }
    }
}

/// Moving the context's postulates into the global environment changes no
/// answer: every candidate, random or a mutant of a valid proof, checks
/// against the claim in constant form exactly when it checks against the
/// same claim in the original, plain-`Var` local context (`build_var_ctx`).
/// `ctx.p` no longer holds that original shape itself -- with postulates
/// as `Const`s (stage 3a) `ctx.p.check` already *is* the constant-form
/// side, so both sides are built explicitly here instead of one borrowing
/// `ctx.p`.
#[test]
fn the_global_environment_agrees_with_the_context() {
    const SEEDS: u64 = 20_000;
    let ctx = build_ctx();
    let n = ctx.p.globals.len() as u32;
    let g = to_globals(&ctx.p.globals);
    let var_ctx = build_var_ctx();
    let pool = valid_seed_pool(&ctx);
    let (mut agreed_ok, mut agreed_err) = (0, 0);
    for seed in 0..SEEDS {
        let mut rng = Rng::new(0xD1FF_u64 ^ seed);
        let claim = if seed % 2 == 0 { kernel::id(ctx.a_ty.clone(), ctx.a.clone(), ctx.c.clone()) } else { kernel::id(ctx.a_ty.clone(), ctx.a.clone(), ctx.a.clone()) };
        let candidate = if seed % 3 == 0 {
            gen_expr(&mut rng, n, MAX_DEPTH)
        } else {
            let base = &pool[rng.below(pool.len() as u32) as usize];
            mutate_once(&mut rng, base, n)
        };
        let by_vars = kernel::check(&var_ctx, &to_vars(&candidate, n, 0), &to_vars(&claim, n, 0)).is_ok();
        let by_consts = kernel::check_in(&g, &kernel::Ctx::new(), &to_consts(&candidate, n, 0), &claim).is_ok();
        assert_eq!(by_vars, by_consts, "seed={seed}: {candidate:?} against {claim:?}");
        if by_vars { agreed_ok += 1 } else { agreed_err += 1 }
    }
    assert!(agreed_ok > 200, "only {agreed_ok} candidates checked; the differential has too few positive cases");
    assert!(agreed_err > 200, "only {agreed_err} candidates were rejected");
}

/// The core soundness property in constant form: with the postulates as
/// globals and candidates free to name any constant (or one past the
/// environment), nothing proves `Id(A, a, b)`.
#[test]
fn kernel_never_accepts_a_random_term_as_proving_an_unrelated_equality_in_constant_form() {
    const SEEDS: u64 = 20_000;
    let ctx = build_ctx();
    let n = ctx.p.globals.len() as u32;
    let g = to_globals(&ctx.p.globals);
    let claim = to_consts(&kernel::id(ctx.a_ty.clone(), ctx.a.clone(), ctx.b.clone()), n, 0);
    for seed in 0..SEEDS {
        let mut rng = Rng::new(0xC0DE_C0DE_u64 ^ seed);
        rng.consts = true;
        let candidate = gen_expr(&mut rng, 0, MAX_DEPTH);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| kernel::check_in(&g, &kernel::Ctx::new(), &candidate, &claim)));
        match result {
            Ok(Err(_)) => {}
            Ok(Ok(())) => panic!("SOUNDNESS BUG: seed={seed} accepted {candidate:?} as proof of {claim:?}"),
            Err(_) => panic!("kernel::check_in panicked on seed={seed}: {candidate:?}"),
        }
    }
}

/// A `Free` never checks: mutants of valid proofs (in constant form) with
/// a `Free` spliced in are rejected against their own true claims, which
/// they'd otherwise often still prove.
#[test]
fn a_term_with_a_free_never_checks() {
    const SEEDS: u64 = 20_000;
    let ctx = build_ctx();
    let n = ctx.p.globals.len() as u32;
    let g = to_globals(&ctx.p.globals);
    let claims = [
        kernel::id(ctx.a_ty.clone(), ctx.a.clone(), ctx.a.clone()),
        kernel::id(ctx.a_ty.clone(), ctx.a.clone(), ctx.c.clone()),
        kernel::id(ctx.a_ty.clone(), ctx.c.clone(), ctx.a.clone()),
        kernel::id(ctx.a_ty.clone(), ctx.a.clone(), ctx.a.clone()),
        kernel::id(ctx.b_ty.clone(), kernel::app(ctx.f.clone(), ctx.a.clone()), kernel::app(ctx.f.clone(), ctx.c.clone())),
    ];
    let pool = valid_seed_pool(&ctx);
    assert_eq!(claims.len(), pool.len(), "claims[i] must be the claim pool[i] proves");
    for (i, claim) in claims.iter().enumerate() {
        let proof = to_consts(&pool[i], n, 0);
        let claim_c = to_consts(claim, n, 0);
        kernel::check_in(&g, &kernel::Ctx::new(), &proof, &claim_c).unwrap_or_else(|e| panic!("pool[{i}] should check against claims[{i}] in constant form: {e}"));
    }
    for seed in 0..SEEDS {
        let mut rng = Rng::new(0xF3EE_u64 ^ seed);
        let i = rng.below(pool.len() as u32) as usize;
        let proof = to_consts(&pool[i], n, 0);
        let claim = to_consts(&claims[i], n, 0);
        let total = count_nodes(&proof);
        let mut c = 0;
        let mutant = replace_nth(&proof, rng.below(total), &mut c, &kernel::mk(Node::Free(rng.below(3))));
        let result = kernel::check_in(&g, &kernel::Ctx::new(), &mutant, &claim);
        assert!(result.is_err(), "seed={seed}: {mutant:?} with a Free checked against {claim:?}");
    }
}
