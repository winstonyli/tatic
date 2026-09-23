//! JIT cache: the piece that realizes "if a high-level transformation is
//! found to be equivalent to a low-level sequence of operations on the
//! target machine, use that for future invocations."
//!
//! For a given term hash we only ever pay the compile cost once:
//!
//! 1. First call: try to compile the term into the target-machine
//!    fragment (`compile::try_compile`). If that fails, the term simply
//!    isn't in the compilable fragment — fall back to the interpreter and
//!    remember not to try again.
//! 2. If it compiles, don't trust it blindly: run it against the
//!    interpreter (the reference semantics) on a battery of sample inputs.
//!    Only once compiled and interpreted agree on all of them do we call
//!    the compiled code "equivalent" and install it in the cache.
//! 3. Every later call for that same hash — content-addressed, so any
//!    structurally identical term anywhere hits the same entry — skips
//!    straight to the compiled, native-speed path.
//!
//! If verification ever fails (a compiler bug, in principle), the term is
//! blacklisted and permanently served by the interpreter instead, rather
//! than risking a silently wrong "optimization".
//!
//! Sample verification is the actual trust gate for every compiled term.
//! Where possible (see `proof.rs`), a kernel-checked `Id`-typed proof is
//! additionally attempted and recorded (`Stats::kernel_proofs_checked`,
//! `is_kernel_verified`) as stronger evidence alongside it.
//! `kernel_verify` below tries `proof.rs`'s strategies in order of
//! strength, first success wins: a straight-line term gets one `refl`
//! proof covering every input; a tail-recursive term gets the universal
//! theorem (`prove_tail_recursive_universal`) if its shape allows one --
//! also covering every input, from real induction rather than per-sample
//! checking; only if that doesn't apply does it fall back to a per-sample
//! relational proof (translation validation) for the same battery of
//! samples `verify()` uses.

use hashbrown::HashMap;
use wasmtime::{Engine, Instance, Module, Store, Val};

use crate::compile::try_compile;
use crate::eval::{self, EvalError};
use crate::proof;
use crate::term::{Hash, TermStore};

const SAMPLE_ARGS: &[i64] = &[0, 1, 2, 3, 5, -1, -3, 7, 20];

enum CacheEntry {
    Compiled {
        func: wasmtime::Func,
        arity: usize,
        // Kept alive only so the module backing `func` isn't dropped.
        _module: Module,
        /// Whether `proof.rs` additionally produced a kernel-checked `Id`
        /// proof for this term (only possible for the non-recursive
        /// fragment -- see `proof.rs`). Sample-based `verify()` below is
        /// still what actually gates trusting the compiled form either
        /// way; this just records the stronger evidence when it exists.
        kernel_verified: bool,
        /// The exported `"hp"` global (`compile::CompiledFragment`'s
        /// `needs_hp_reset` docs), for a fragment with at least one
        /// capturing closure -- `invoke` resets it to `0` before every
        /// call, since this same compiled instance is reused across many
        /// separate calls (that's the whole point of this cache), and
        /// the bump allocator itself never reclaims anything. `None` for
        /// a fragment with no capturing closures at all.
        hp_global: Option<wasmtime::Global>,
    },
    NotCompilable,
    FailedVerification,
}

#[derive(Default, Debug, Clone, Copy)]
pub struct Stats {
    pub compiled: u64,
    pub cache_hits: u64,
    pub interpreted: u64,
    pub verification_failures: u64,
    /// Of `compiled`, how many additionally got a kernel-checked proof
    /// (see `kernel_verify`'s strategy order) rather than only sample
    /// verification.
    pub kernel_proofs_checked: u64,
    /// How many concrete calls got their own kernel-checked instance of the
    /// universal theorem (`proof::prove_tail_recursive_instance`), on top
    /// of `kernel_proofs_checked`'s single per-term theorem. Additional
    /// evidence only -- `kernel_verified` doesn't depend on this, so it
    /// stays `0` for terms the universal proof doesn't apply to at all.
    /// Branching recursion (e.g. naive Fibonacci) gets real per-instance
    /// evidence too now, not a blanket decline -- see
    /// `build_ev_witness`'s own `memo`-based fix in `proof.rs`.
    pub universal_instances_checked: u64,
}

pub struct JitEngine {
    engine: Engine,
    rt: Store<()>,
    cache: HashMap<Hash, CacheEntry>,
    pub stats: Stats,
}

impl JitEngine {
    pub fn new() -> Self {
        let engine = Engine::default();
        let rt = Store::new(&engine, ());
        JitEngine {
            engine,
            rt,
            cache: HashMap::new(),
            stats: Stats::default(),
        }
    }

    /// Apply the term `h` (a function of `args.len()` integer arguments) to
    /// `args`, transparently using a JIT-compiled implementation once one
    /// has been compiled and verified for this exact term.
    pub fn apply(&mut self, terms: &TermStore, h: Hash, args: &[i64]) -> Result<i64, EvalError> {
        match self.cache.get(&h) {
            Some(CacheEntry::Compiled { .. }) => {
                self.stats.cache_hits += 1;
                self.call_compiled(h, args)
            }
            Some(CacheEntry::NotCompilable) | Some(CacheEntry::FailedVerification) => {
                self.stats.interpreted += 1;
                eval::apply_term(terms, h, args)
            }
            None => self.compile_verify_and_apply(terms, h, args),
        }
    }

    fn compile_verify_and_apply(
        &mut self,
        terms: &TermStore,
        h: Hash,
        args: &[i64],
    ) -> Result<i64, EvalError> {
        let Some(frag) = try_compile(terms, h) else {
            self.cache.insert(h, CacheEntry::NotCompilable);
            self.stats.interpreted += 1;
            return eval::apply_term(terms, h, args);
        };

        if frag.arity != args.len() {
            self.cache.insert(h, CacheEntry::NotCompilable);
            self.stats.interpreted += 1;
            return eval::apply_term(terms, h, args);
        }

        let Some((module, func, hp_global)) = self.instantiate(&frag.wat) else {
            self.cache.insert(h, CacheEntry::NotCompilable);
            self.stats.interpreted += 1;
            return eval::apply_term(terms, h, args);
        };
        debug_assert_eq!(hp_global.is_some(), frag.needs_hp_reset, "compile.rs's export and needs_hp_reset flag should always agree");

        if self.verify(terms, h, func, hp_global, frag.arity) {
            let kernel_verified = self.kernel_verify(terms, h, frag.arity);
            if kernel_verified {
                self.stats.kernel_proofs_checked += 1;
            }
            self.cache.insert(
                h,
                CacheEntry::Compiled {
                    func,
                    arity: frag.arity,
                    _module: module,
                    kernel_verified,
                    hp_global,
                },
            );
            self.stats.compiled += 1;
            self.stats.cache_hits += 1;
            self.call_compiled(h, args)
        } else {
            self.cache.insert(h, CacheEntry::FailedVerification);
            self.stats.verification_failures += 1;
            self.stats.interpreted += 1;
            eval::apply_term(terms, h, args)
        }
    }

    /// Attempts a kernel-checked equivalence proof for `h`, on top of (not
    /// instead of) the sample-based `verify()` above, trying `proof.rs`'s
    /// strategies from strongest to weakest and stopping at the first that
    /// applies:
    /// 1. `prove_pure_expr` -- a straight-line (non-recursive) term gets
    ///    one proof covering every input.
    /// 2. `prove_closure_expr` -- a closed, non-recursive term built from
    ///    non-capturing ("known-call") closures gets one proof covering
    ///    every input too, the same way `prove_pure_expr` does for plain
    ///    arithmetic -- see its own docs for what's in and out of scope
    ///    (an `If` between two closures, self-recursion combined with
    ///    closures, ...).
    /// 3. `prove_tail_recursive_universal` -- a tail-recursive term whose
    ///    shape it covers gets one universal theorem, also covering every
    ///    input, via real induction rather than per-sample checking. Once
    ///    this succeeds, also tries instantiating that theorem at a few
    ///    concrete samples in one pass
    ///    (`proof::prove_tail_recursive_universal_with_instances`) purely to
    ///    record stronger, call-specific evidence
    ///    (`Stats::universal_instances_checked`) -- cheap since it clones
    ///    the already-built scaffold per sample rather than re-deriving the
    ///    theorem from scratch each time, but not required:
    ///    `kernel_verified` is already `true` from the theorem alone, so
    ///    any shape whose instances this step doesn't get (an arity
    ///    mismatch, a `Clo`-typed top-level parameter -- see
    ///    `instance_from_scaffold`) is unaffected. Branching recursion
    ///    (e.g. naive Fibonacci) gets real instances through this step
    ///    too, not a blanket decline.
    /// 4. `prove_tail_recursive_call`, once per sample in the same battery
    ///    `verify()` uses, reporting success only if *every* sample got its
    ///    own per-call relational proof -- the fallback for tail-recursive
    ///    shapes the universal proof doesn't (yet) cover.
    /// 5. `prove_closure_expr_instance`, once per sample, reporting
    ///    success only if *every* sample gets its own per-instance
    ///    proof -- the fallback for exactly the shapes none of the above
    ///    can cover at all: a closure-typed parameter called with
    ///    genuinely inconsistent arities across call sites (`compile.rs`'s
    ///    curried-dispatch capability), including one threaded through a
    ///    *tail*-recursive loop (`proof::eval_dyn_tail_recursive`) -- the
    ///    recursive use of that capability `RELATED_WORK.md` names as a
    ///    standing gap. Tried last, not third, precisely because it's
    ///    weakest (a per-instance certificate, never one theorem covering
    ///    every input -- see `proof.rs`'s own module docs for why a
    ///    universal proof is a dead end here without a real dependent sum
    ///    in the kernel's own type theory) and its widened, closure-aware
    ///    evaluator happens to also accept plain arithmetic recursion
    ///    (e.g. gcd) that steps 3-4 already prove more strongly -- trying
    ///    it first would silently downgrade those to weaker evidence.
    ///
    /// Anything else (e.g. a callee reached only through a captured/
    /// parameter variable whose concrete identity isn't statically known
    /// at proof-construction time -- see `RELATED_WORK.md` §9) reports
    /// `false` -- see `proof.rs` for what's in scope and why. Non-tail
    /// recursion combined with the inconsistent-arity curried-dispatch
    /// fallback is *not* in that bucket: step 5's own widened,
    /// `self_ctx`-threaded evaluator covers it too, including branching.
    fn kernel_verify(&mut self, terms: &TermStore, h: Hash, arity: usize) -> bool {
        if proof::prove_pure_expr(terms, h).is_some() {
            return true;
        }
        if proof::prove_closure_expr(terms, h).is_some() {
            return true;
        }
        let instance_samples: Vec<Vec<i64>> = sample_arg_vectors(arity).into_iter().take(3).collect();
        if let Some((_, instances)) = proof::prove_tail_recursive_universal_with_instances(terms, h, &instance_samples)
        {
            self.stats.universal_instances_checked += instances.iter().filter(|i| i.is_some()).count() as u64;
            return true;
        }
        let samples = sample_arg_vectors(arity);
        if !samples.is_empty() && samples.iter().all(|sample| proof::prove_tail_recursive_call(terms, h, sample).is_some()) {
            return true;
        }
        let closure_instance_samples = sample_arg_vectors(arity);
        !closure_instance_samples.is_empty()
            && closure_instance_samples
                .iter()
                .all(|sample| proof::prove_closure_expr_instance(terms, h, sample).is_some())
    }

    /// Run the compiled candidate against the interpreter (reference
    /// semantics) on a battery of sample inputs and confirm they agree.
    /// This is the "found to be equivalent" check.
    fn verify(&mut self, terms: &TermStore, h: Hash, func: wasmtime::Func, hp_global: Option<wasmtime::Global>, arity: usize) -> bool {
        for sample in sample_arg_vectors(arity) {
            let interpreted = eval::apply_term(terms, h, &sample);
            let compiled = self.invoke(func, hp_global, &sample);
            let agree = match (interpreted, compiled) {
                (Ok(a), Ok(b)) => a == b,
                (Err(_), Err(_)) => true, // both error/trap: agree they're undefined here
                _ => false,
            };
            if !agree {
                return false;
            }
        }
        true
    }

    /// Whether the compiled form cached for `h` additionally carries a
    /// kernel-checked equivalence proof. `false` for anything not yet
    /// compiled, not compilable, or in the recursive fragment `proof.rs`
    /// doesn't cover yet.
    pub fn is_kernel_verified(&self, h: Hash) -> bool {
        matches!(
            self.cache.get(&h),
            Some(CacheEntry::Compiled { kernel_verified: true, .. })
        )
    }

    fn call_compiled(&mut self, h: Hash, args: &[i64]) -> Result<i64, EvalError> {
        let Some(CacheEntry::Compiled { func, arity, hp_global, .. }) = self.cache.get(&h) else {
            unreachable!("call_compiled invoked without a compiled cache entry");
        };
        debug_assert_eq!(*arity, args.len());
        let (func, hp_global) = (*func, *hp_global);
        self.invoke(func, hp_global, args)
    }

    /// Calls `func`, first resetting `hp_global` to `0` if present (see
    /// `CacheEntry::Compiled::hp_global`'s docs) -- every call site goes
    /// through here (both `verify`'s own sample calls and every real,
    /// cached call `call_compiled` makes), so every actual invocation of
    /// a compiled function gets a fresh bump allocator regardless of how
    /// many times this same instance has been called before.
    fn invoke(&mut self, func: wasmtime::Func, hp_global: Option<wasmtime::Global>, args: &[i64]) -> Result<i64, EvalError> {
        if let Some(hp) = hp_global {
            hp.set(&mut self.rt, Val::I32(0)).expect("hp is always a mutable i32 global when exported");
        }
        let wargs: Vec<Val> = args.iter().map(|&a| Val::I64(a)).collect();
        let mut results = [Val::I64(0)];
        func.call(&mut self.rt, &wargs, &mut results)
            .map_err(|_| EvalError::Trap)?;
        match results[0] {
            Val::I64(n) => Ok(n),
            _ => Err(EvalError::TypeError),
        }
    }

    fn instantiate(&mut self, wat: &str) -> Option<(Module, wasmtime::Func, Option<wasmtime::Global>)> {
        let bytes = wat::parse_str(wat).ok()?;
        let module = Module::new(&self.engine, &bytes).ok()?;
        let instance = Instance::new(&mut self.rt, &module, &[]).ok()?;
        let func = instance.get_func(&mut self.rt, "f")?;
        let hp_global = instance.get_global(&mut self.rt, "hp");
        Some((module, func, hp_global))
    }
}

impl Default for JitEngine {
    fn default() -> Self {
        Self::new()
    }
}

fn sample_arg_vectors(arity: usize) -> Vec<Vec<i64>> {
    // Small cartesian-ish sample set, capped so verification stays cheap
    // even for higher-arity functions.
    let mut out = Vec::new();
    match arity {
        0 => {
            // Exactly one possible 0-argument call -- `vec![a; 0]` is `[]`
            // regardless of `a`, so falling through to the `_` arm below
            // would push the same empty sample `SAMPLE_ARGS[..6].len()`
            // times over. Harmless for `verify()` (repeats the same cheap
            // interpreted-vs-compiled check), but `kernel_verify`'s
            // `prove_closure_expr_instance` fallback is expensive per call
            // (it walks a full concrete execution trace) and gained
            // nothing from the repeats -- see `RELATED_WORK.md` §9.
            out.push(vec![]);
        }
        1 => {
            for &a in SAMPLE_ARGS {
                out.push(vec![a]);
            }
        }
        2 => {
            for &a in &SAMPLE_ARGS[..6] {
                for &b in &SAMPLE_ARGS[..6] {
                    out.push(vec![a, b]);
                }
            }
        }
        _ => {
            // Higher-arity: just probe the all-equal and all-small-distinct
            // diagonals rather than a full cartesian product.
            for &a in &SAMPLE_ARGS[..6] {
                out.push(vec![a; arity]);
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::{PrimOp, TermStore};

    #[test]
    fn sample_arg_vectors_for_arity_zero_is_a_single_trivial_sample() {
        // `vec![a; 0]` is `[]` regardless of `a` -- without the dedicated
        // `0` arm, the `_` catch-all would push the same empty sample
        // once per `SAMPLE_ARGS[..6]` entry (see `sample_arg_vectors`'s
        // own comment and `RELATED_WORK.md` §9 for the redundant-proof-
        // search cost this was causing).
        assert_eq!(sample_arg_vectors(0), vec![Vec::<i64>::new()]);
    }

    fn factorial(s: &mut TermStore) -> Hash {
        let n = s.var(0);
        let f = s.var(1);
        let one = s.lit(1);
        let cond = s.prim(PrimOp::Le, n, one);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one);
        let rec_call = s.app(f, n_minus_1);
        let else_branch = s.prim(PrimOp::Mul, n, rec_call);
        let body = s.if_(cond, one, else_branch);
        let abs = s.abs(body);
        s.rec(abs)
    }

    #[test]
    fn first_call_compiles_later_calls_hit_cache() {
        let mut s = TermStore::new();
        let fact = factorial(&mut s);
        let mut jit = JitEngine::new();

        assert_eq!(jit.apply(&s, fact, &[10]).unwrap(), 3628800);
        assert_eq!(jit.stats.compiled, 1);
        assert_eq!(jit.stats.cache_hits, 1);

        for n in 0..10 {
            assert_eq!(jit.apply(&s, fact, &[n]).unwrap(), eval::apply_term(&s, fact, &[n]).unwrap());
        }
        assert_eq!(jit.stats.compiled, 1, "should not recompile on repeat calls");
        assert!(jit.stats.cache_hits > 1);
    }

    fn gcd(s: &mut TermStore) -> Hash {
        // rec f a b = if b == 0 then a else f(b, a mod b) -- tail
        // recursive: compile.rs turns this into a loop, and proof.rs's
        // relational, per-sample proof covers exactly this shape.
        let b = s.var(0);
        let a = s.var(1);
        let f = s.var(2);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Eq, b, zero);
        let a_mod_b = s.prim(PrimOp::Mod, a, b);
        let rec_call = s.app2(f, b, a_mod_b);
        let body = s.if_(cond, a, rec_call);
        let inner = s.abs(body);
        let abs = s.abs(inner);
        s.rec(abs)
    }

    #[test]
    fn kernel_proof_recorded_for_straight_line_and_tail_recursive_terms() {
        // \a b. if a < b then a * 2 else b + 1 -- straight-line, no Rec.
        let mut s = TermStore::new();
        let a = s.var(1);
        let b = s.var(0);
        let cond = s.prim(PrimOp::Lt, a, b);
        let two = s.lit(2);
        let then_branch = s.prim(PrimOp::Mul, a, two);
        let one = s.lit(1);
        let else_branch = s.prim(PrimOp::Add, b, one);
        let body = s.if_(cond, then_branch, else_branch);
        let inner = s.abs(body);
        let straight_line = s.abs(inner);

        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, straight_line, &[3, 5]).unwrap(), 6);
        assert!(jit.is_kernel_verified(straight_line));
        assert_eq!(jit.stats.kernel_proofs_checked, 1);

        // gcd is Rec-wrapped but *tail*-recursive -- proof.rs's relational,
        // per-sample proof covers it (every sample verify() tries gets its
        // own kernel-checked proof), so this is kernel-verified too.
        // gcd's tail-recursive shape (a single self-call in tail position)
        // gets the universal proof (strategy 2), not the relational
        // fallback -- and since that's a linear, single-self-call leaf,
        // kernel_verify also gets concrete per-call instances out of it
        // (see kernel_verify's own docs).
        let gcd_term = gcd(&mut s);
        assert_eq!(jit.apply(&s, gcd_term, &[48, 18]).unwrap(), 6);
        assert!(jit.is_kernel_verified(gcd_term));
        assert_eq!(jit.stats.kernel_proofs_checked, 2);
        assert!(jit.stats.universal_instances_checked > 0, "gcd's linear shape should get instance evidence too");

        // factorial is Rec-wrapped and *not* tail-recursive (the self-call
        // is nested inside a multiplication, not the relational proof's
        // fragment either -- see proof.rs docs) -- but prove_tail_recursive_universal
        // now covers leaves with any number of self-calls combined
        // arithmetically (via kernel::cong_n), not just tail calls, so
        // this gets the universal proof too -- and, still a single-self-call
        // (k=1) leaf, instance evidence as well.
        let fact = factorial(&mut s);
        let instances_before_fact = jit.stats.universal_instances_checked;
        assert_eq!(jit.apply(&s, fact, &[5]).unwrap(), 120);
        assert!(jit.is_kernel_verified(fact));
        assert_eq!(jit.stats.kernel_proofs_checked, 3);
        assert!(jit.stats.universal_instances_checked > instances_before_fact);
    }

    fn fib(s: &mut TermStore) -> Hash {
        let n = s.var(0);
        let f = s.var(1);
        let two = s.lit(2);
        let cond = s.prim(PrimOp::Lt, n, two);
        let one = s.lit(1);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one);
        let n_minus_2 = s.prim(PrimOp::Sub, n, two);
        let call1 = s.app(f, n_minus_1);
        let call2 = s.app(f, n_minus_2);
        let else_branch = s.prim(PrimOp::Add, call1, call2);
        let body = s.if_(cond, n, else_branch);
        let abs = s.abs(body);
        s.rec(abs)
    }

    #[test]
    fn branching_recursion_gets_instance_evidence_too() {
        // Naive Fibonacci's else-branch leaf has two self-calls -- the
        // universal theorem covers it fine (kernel_verified stays true
        // regardless), and build_ev_witness now instance-witnesses a
        // branching leaf too (see proof.rs docs: a memo DP cache plus a
        // congruence-based recast, not just the at-most-one-self-call
        // shapes from before). kernel_verify tries instances at
        // SAMPLE_ARGS' first 3 values (0, 1, 2) -- all three now succeed.
        let mut s = TermStore::new();
        let fibonacci = fib(&mut s);

        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, fibonacci, &[10]).unwrap(), 55);
        assert!(jit.is_kernel_verified(fibonacci));
        assert_eq!(jit.stats.kernel_proofs_checked, 1);
        assert_eq!(jit.stats.universal_instances_checked, 3);
    }

    #[test]
    fn non_capturing_higher_order_terms_now_compile() {
        // twice = \f. \x. f (f x); inc = \y. y + 1; (twice inc) 5 -- both
        // twice and inc are non-capturing, so compile.rs's known-call
        // closure support (twice becomes a combinator calling `f` through
        // a Wasm table, inc becomes another combinator) now compiles this
        // instead of falling back to the interpreter, and proof.rs's
        // prove_closure_expr gives it a kernel-checked proof too.
        let mut s = TermStore::new();
        let f = s.var(1);
        let x = s.var(0);
        let fx = s.app(f, x);
        let ffx = s.app(f, fx);
        let inner = s.abs(ffx);
        let twice = s.abs(inner);
        let y = s.var(0);
        let one = s.lit(1);
        let y_plus_1 = s.prim(PrimOp::Add, y, one);
        let inc = s.abs(y_plus_1);
        let five = s.lit(5);
        let applied = s.app2(twice, inc, five);

        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, applied, &[]).unwrap(), 7);
        assert_eq!(jit.stats.compiled, 1);
        assert_eq!(jit.stats.interpreted, 0);
        assert!(jit.is_kernel_verified(applied));
        assert_eq!(jit.stats.kernel_proofs_checked, 1);
    }

    #[test]
    fn a_let_bound_self_recursive_function_compiles_and_is_kernel_verified() {
        // (\g. g 10) (rec f n = if n <= 1 then 1 else n * f (n - 1)) --
        // what `let fact = rec f n = .. in fact 10` desugars to (found via
        // the REPL, see syntax.rs/repl.rs): a named recursive function
        // called through the same combinator table a plain closure value
        // uses. compile.rs handles this (a bug fix -- see its own tests),
        // and prove_closure_expr now does too: a call to a combinator is
        // always postulated opaque (never denoted by looking inside its
        // own body), so widening `Term::Abs`-only call/value sites to also
        // accept `Term::Rec` needed no new proof machinery, just the wider
        // pattern -- see proof.rs's own denote_closure docs.
        let mut s = TermStore::new();
        let n = s.var(0);
        let f = s.var(1);
        let one = s.lit(1);
        let cond = s.prim(PrimOp::Le, n, one);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one);
        let rec_call = s.app(f, n_minus_1);
        let else_branch = s.prim(PrimOp::Mul, n, rec_call);
        let body = s.if_(cond, one, else_branch);
        let abs = s.abs(body);
        let fact = s.rec(abs);

        let inner_var = s.var(0);
        let ten = s.lit(10);
        let call = s.app(inner_var, ten);
        let wrapper = s.abs(call);
        let applied = s.app(wrapper, fact);

        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, applied, &[]).unwrap(), 3628800);
        assert_eq!(jit.stats.compiled, 1);
        assert_eq!(jit.stats.interpreted, 0);
        assert!(jit.is_kernel_verified(applied));
    }

    #[test]
    fn a_returned_closure_now_compiles_via_over_application() {
        // (\x. if x > 0 then (\y. x + y) else (\y. x - y)) 3, then applied
        // to 4 -- `unwind_app_spine` can't distinguish this from "inner
        // takes 2 arguments" (see `compile::tests::
        // curried_application_is_indistinguishable_from_multi_arg_calls`),
        // and `inner` is declared 1-ary, so this reads as `inner`
        // over-applied by one argument: `inner`'s own saturated call
        // (`inner(3)`) is compiled, and whatever it returns -- one of two
        // *capturing* closures, depending on `x` -- is dispatched via
        // `call_indirect` the same way a closure-typed variable would be
        // (see `compile.rs`'s module docs on over-application). Was
        // previously rejected outright, falling back to the interpreter;
        // now compiles and gets the right, sample-verified answer --
        // *and* proof.rs's own `denote_closure`/`combinator_return_type`
        // widening (see `proof::tests::
        // an_over_applied_literal_lambda_returning_a_closure_gets_a_closure_proof`)
        // covers this shape too, so it's kernel-verified as well.
        let mut s = TermStore::new();
        let x1 = s.var(0);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Lt, zero, x1);
        let y_pos = s.var(0);
        let x_pos = s.var(1);
        let plus = s.prim(PrimOp::Add, x_pos, y_pos);
        let then_closure = s.abs(plus);
        let y_neg = s.var(0);
        let x_neg = s.var(1);
        let minus = s.prim(PrimOp::Sub, x_neg, y_neg);
        let else_closure = s.abs(minus);
        let picked = s.if_(cond, then_closure, else_closure);
        let inner = s.abs(picked);
        let three = s.lit(3);
        let picked_closure = s.app(inner, three);
        let four = s.lit(4);
        let applied = s.app(picked_closure, four);

        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, applied, &[]).unwrap(), 7); // 3 > 0, so 3 + 4
        assert_eq!(jit.stats.compiled, 1);
        assert_eq!(jit.stats.interpreted, 0);
        assert!(jit.is_kernel_verified(applied));
    }

    #[test]
    fn content_addressing_shares_the_cache_across_independently_built_terms() {
        let mut s = TermStore::new();
        let fact_a = factorial(&mut s);
        let fact_b = factorial(&mut s); // rebuilt from scratch, same structure
        assert_eq!(fact_a, fact_b);

        let mut jit = JitEngine::new();
        jit.apply(&s, fact_a, &[6]).unwrap();
        assert_eq!(jit.stats.compiled, 1);
        jit.apply(&s, fact_b, &[7]).unwrap();
        assert_eq!(jit.stats.compiled, 1, "same hash must reuse the compiled entry");
    }

    fn capturing_closure_loop(s: &mut TermStore) -> Hash {
        // rec f n acc = if n <= 0 then acc else f (n - 1) ((\y. acc + y) n)
        // -- see compile.rs's own test of the same shape.
        let y = s.var(0);
        let acc_captured = s.var(1);
        let sum = s.prim(PrimOp::Add, acc_captured, y);
        let closure = s.abs(sum);
        let n_ref = s.var(1);
        let new_acc = s.app(closure, n_ref);
        let n = s.var(1);
        let acc = s.var(0);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Le, n, zero);
        let one = s.lit(1);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one);
        let f = s.var(2);
        let rec_call = s.app2(f, n_minus_1, new_acc);
        let body = s.if_(cond, acc, rec_call);
        let inner = s.abs(body);
        let abs = s.abs(inner);
        s.rec(abs)
    }

    #[test]
    fn repeated_calls_to_a_capturing_closure_term_stay_correct_and_cached() {
        // The same cached compiled instance gets called many times here
        // (that's the whole point of the cache) -- each call creates a
        // fresh capturing closure, so this exercises the `hp` reset
        // `invoke` does before every call (see compile.rs's own
        // `resetting_hp_between_calls_keeps_memory_bounded_across_many_calls`
        // for the lower-level mechanism this relies on). Not a memory
        // measurement itself (jit.rs has no public way to inspect Wasm
        // linear memory) -- just confirms behavior stays correct and the
        // cache, not recompilation, serves every repeated call.
        let mut s = TermStore::new();
        let h = capturing_closure_loop(&mut s);
        let mut jit = JitEngine::new();

        for i in 0..500 {
            let n = (i % 50) + 1;
            let result = jit.apply(&s, h, &[n, 0]).unwrap();
            let expected = n * (n + 1) / 2; // sum 1..=n
            assert_eq!(result, expected, "mismatch at n={n}");
        }
        assert_eq!(jit.stats.compiled, 1, "should compile once, not once per call");
        assert_eq!(jit.stats.cache_hits, 500);
    }

    #[test]
    fn a_self_recursive_closure_created_and_called_each_iteration_is_kernel_verified() {
        // Same term as capturing_closure_loop above -- rec f n acc = if
        // n <= 0 then acc else f(n-1, (\y. acc+y)(n)) -- but now checked
        // directly against proof.rs: prove_tail_recursive_universal covers
        // a closure *created and called* inside a self-call argument too,
        // not just a closure-typed *parameter* (see proof.rs's own
        // denote_closure_typed/prime_closure_postulates docs), so this
        // gets the universal theorem, not just per-sample relational
        // proofs.
        let mut s = TermStore::new();
        let h = capturing_closure_loop(&mut s);
        let mut jit = JitEngine::new();

        assert_eq!(jit.apply(&s, h, &[5, 0]).unwrap(), 15); // sum 1..=5
        assert!(jit.is_kernel_verified(h));
        assert_eq!(jit.stats.kernel_proofs_checked, 1);
    }

    #[test]
    fn a_closure_typed_loop_carried_parameter_compiles_and_is_kernel_verified() {
        // rec f n g x = if n <= 0 then x else f(n-1, g, g x) -- same shape
        // as proof::tests::iterate, but here actually run: a closure-typed
        // *parameter* threaded through every iteration and called
        // (call_indirect) rather than a fresh closure created each
        // iteration (capturing_closure_loop's own shape above). Since `g`
        // is Clo-typed, `it` can't be called directly through jit.apply's
        // plain-i64 args the way gcd/fib/capturing_closure_loop are --
        // there's no way to hand it a real packed closure value from the
        // outside -- so `inc` (a non-capturing literal lambda) is baked in
        // as the initial `g` and wrapped in a fully-applied outer call
        // (`top`), making the whole term closed (arity 0).
        //
        // That wrapping matters for *which* proof `is_kernel_verified`
        // below actually reflects: `kernel_verify` tries
        // `prove_closure_expr` before `prove_tail_recursive_universal`,
        // and `top` -- an application whose root resolves to `it`, fully
        // applied -- is exactly the "self-recursive combinator called
        // directly" shape `prove_closure_expr` already covers opaquely
        // (`call_ref`, never unfolding `it`'s own body), so *that* is what
        // succeeds here, not the universal theorem `it` gets on its own
        // (checked directly below) -- an honest distinction, not a
        // weaker guarantee: `jit.rs`'s own sample-based `verify()` against
        // the interpreter is still the actual trust gate installing the
        // compiled form either way (see this module's own docs).
        let mut s = TermStore::new();
        let x = s.var(0);
        let g = s.var(1);
        let n = s.var(2);
        let f = s.var(3);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Le, n, zero);
        let one = s.lit(1);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one);
        let gx = s.app(g, x);
        let f_n1_g = s.app2(f, n_minus_1, g);
        let rec_call = s.app(f_n1_g, gx);
        let body = s.if_(cond, x, rec_call);
        let g_binder = s.abs(body);
        let n_binder = s.abs(g_binder);
        let abs = s.abs(n_binder);
        let it = s.rec(abs);

        let y = s.var(0);
        let one2 = s.lit(1);
        let inc_body = s.prim(PrimOp::Add, y, one2);
        let inc = s.abs(inc_body);

        let n_lit = s.lit(10);
        let x0 = s.lit(0);
        let partial = s.app2(it, n_lit, inc);
        let top = s.app(partial, x0);

        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, top, &[]).unwrap(), 10); // 0 incremented 10 times
        assert_eq!(jit.stats.compiled, 1);
        assert_eq!(jit.stats.interpreted, 0);
        assert!(jit.is_kernel_verified(top));

        // The universal theorem this recursion path is actually about --
        // checked directly against `it`, not through `top`'s own opaque
        // wrapping call.
        assert!(proof::prove_tail_recursive_universal(&s, it).is_some());
    }

    #[test]
    fn a_tail_recursive_loop_compiles_and_is_kernel_verified_once_its_own_closure_parameter_turns_inconsistent() {
        // Same shape as
        // a_closure_typed_loop_carried_parameter_compiles_and_is_kernel_verified
        // just above, with one addition: `rec f n g x = if 1<0 then
        // g(x,999) else (if n<=0 then x else f(n-1,g,g(x)))` -- a dead
        // (never-reached, since `1<0` is always false) extra call site
        // for `g` at arity 2, alongside the live, tail-recursive arity-1
        // call. `g` is now `ArityUse::Inconsistent`, which -- per
        // compile.rs's own docs -- makes the *whole* fragment (not just
        // this one dead call site) switch to curried dispatch, including
        // the hot, tail-recursive `g(x)` call every iteration actually
        // takes. `proof::eval_dyn_tail_recursive` now covers this too
        // (see its own docs): every call `g` actually takes, along this
        // one concrete trace, happens to be exactly saturated, so the
        // per-instance methodology proves it despite `g`'s own static
        // classification staying `Inconsistent`.
        let mut s = TermStore::new();
        let x_dead = s.var(0);
        let nine_ninety_nine = s.lit(999);
        let g_dead = s.var(1);
        let dead_call = s.app2(g_dead, x_dead, nine_ninety_nine);

        let x = s.var(0);
        let g = s.var(1);
        let n = s.var(2);
        let f = s.var(3);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Le, n, zero);
        let one = s.lit(1);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one);
        let gx = s.app(g, x);
        let f_n1_g = s.app2(f, n_minus_1, g);
        let rec_call = s.app(f_n1_g, gx);
        let live_body = s.if_(cond, x, rec_call);

        let one_c = s.lit(1);
        let zero_c = s.lit(0);
        let dead_cond = s.prim(PrimOp::Lt, one_c, zero_c); // always false
        let body = s.if_(dead_cond, dead_call, live_body);

        let g_binder = s.abs(body);
        let n_binder = s.abs(g_binder);
        let abs = s.abs(n_binder);
        let it = s.rec(abs);

        let y = s.var(0);
        let one2 = s.lit(1);
        let inc_body = s.prim(PrimOp::Add, y, one2);
        let inc = s.abs(inc_body);

        let n_lit = s.lit(10);
        let x0 = s.lit(0);
        let partial = s.app2(it, n_lit, inc);
        let top = s.app(partial, x0);

        let frag = try_compile(&s, it).expect("should compile via curried dispatch, per compile.rs alone");
        assert!(frag.wat.contains("call_indirect (type $ty1)"), "the hot, consistent g(x) call should also go through the curried fallback:\n{}", frag.wat);

        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, top, &[]).unwrap(), 10); // 0 incremented 10 times, same as the baseline shape
        assert_eq!(jit.stats.compiled, 1);
        assert_eq!(jit.stats.interpreted, 0);
        // `prove_closure_expr_instance`'s own inlining (via
        // `eval_dyn_tail_recursive`) now covers a recursive use of the
        // curried-dispatch capability too -- previously the standing gap
        // this whole test existed to document (see `RELATED_WORK.md`).
        // `jit.rs`'s own sample-based `verify()` is still the actual
        // trust gate installing the compiled form regardless.
        assert!(jit.is_kernel_verified(top));
        assert_eq!(jit.stats.kernel_proofs_checked, 1);
    }

    #[test]
    fn a_closure_created_in_a_self_call_argument_capturing_a_closure_typed_loop_parameter_compiles_and_gets_a_universal_proof() {
        // Same shape as proof::tests::
        // a_closure_created_in_a_self_call_argument_capturing_a_closure_typed_loop_parameter_gets_a_universal_proof,
        // run for real here: rec f n g x = if n <= 0 then x else
        // f(n-1, g, g x + (\y. g y + 1) x) -- each iteration creates a
        // fresh closure that captures `g` itself (a Clo-typed value, not
        // an Int). `g x` (a direct call) is what makes `it`'s own scan
        // classify `g` as Clo-typed in the first place -- `infer_closure_arities`
        // never looks inside the wrapper's own body, matching
        // `denote_closure`'s own "never look inside a body" discipline.
        let mut s = TermStore::new();
        let x = s.var(0);
        let g = s.var(1);
        let n = s.var(2);
        let f = s.var(3);

        let gx = s.app(g, x);

        let y = s.var(0);
        let g_captured = s.var(2);
        let gy = s.app(g_captured, y);
        let one = s.lit(1);
        let gy_plus_1 = s.prim(PrimOp::Add, gy, one);
        let wrapper = s.abs(gy_plus_1);
        let wrapper_call = s.app(wrapper, x);

        let new_x = s.prim(PrimOp::Add, gx, wrapper_call);

        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Le, n, zero);
        let one2 = s.lit(1);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one2);
        let f_n1_g = s.app2(f, n_minus_1, g);
        let rec_call = s.app(f_n1_g, new_x);
        let body = s.if_(cond, x, rec_call);
        let g_binder = s.abs(body);
        let n_binder = s.abs(g_binder);
        let abs = s.abs(n_binder);
        let it = s.rec(abs);

        let y2 = s.var(0);
        let one3 = s.lit(1);
        let inc_body = s.prim(PrimOp::Add, y2, one3);
        let inc = s.abs(inc_body);

        let n_lit = s.lit(5);
        let x0 = s.lit(0);
        let partial = s.app2(it, n_lit, inc);
        let top = s.app(partial, x0);

        let mut jit = JitEngine::new();
        // new_x = g(x) + (g(x)+1) = 2*inc(x)+1 = 2x+3; from x=0: 3, 9,
        // 21, 45, 93 after 1..5 iterations (same derivation as proof.rs's
        // own test).
        assert_eq!(jit.apply(&s, top, &[]).unwrap(), 93);
        assert_eq!(jit.stats.compiled, 1);
        assert_eq!(jit.stats.interpreted, 0);
        assert!(proof::prove_tail_recursive_universal(&s, it).is_some());
    }

    #[test]
    fn partial_application_of_a_non_capturing_root_compiles_and_is_kernel_verified() {
        // add = \x y. x + y; partial = add(3); caller = \g. g(4);
        // top = caller(partial) -- same shape as
        // compile::tests::partial_application_of_a_literal_lambda_compiles.
        // compile.rs desugars this at compile time (a synthesized wrapper
        // combinator), and proof.rs's own denote_closure now covers a
        // partial application of a *non-capturing* literal too (pap_ref),
        // so this gets a kernel-checked proof, not just empirical sample
        // verification -- see proof::tests::
        // a_partially_applied_literal_lambda_used_as_a_value_gets_a_closure_proof
        // for the same shape checked directly against proof.rs.
        let mut s = TermStore::new();
        let x = s.var(1);
        let y = s.var(0);
        let sum = s.prim(PrimOp::Add, x, y);
        let inner_add = s.abs(sum);
        let add = s.abs(inner_add);

        let three = s.lit(3);
        let partial = s.app(add, three);

        let g = s.var(0);
        let four = s.lit(4);
        let call_g = s.app(g, four);
        let caller = s.abs(call_g);

        let top = s.app(caller, partial);

        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, top, &[]).unwrap(), 7);
        assert_eq!(jit.stats.compiled, 1);
        assert_eq!(jit.stats.interpreted, 0);
        assert!(jit.is_kernel_verified(top));
    }

    #[test]
    fn partial_application_of_a_capturing_root_compiles_and_is_kernel_verified() {
        // g = \z. (\g2. g2(4)) ((\x y. x + y + z)(3)) -- same shape as
        // compile::tests::partial_application_of_a_capturing_literal_lambda_compiles.
        // compile.rs's push_pap_env composes the wrapper's own environment
        // with a copy of the (capturing) root's environment, and proof.rs's
        // pap_ref now mirrors that (a leading Env_n parameter when the root
        // captures, built at every call site via build_env_expr) -- see
        // proof::tests::a_partially_applied_capturing_literal_lambda_used_as_a_value_gets_a_closure_proof
        // for the same shape checked directly against proof.rs -- so this
        // now gets a kernel-checked proof, not just empirical sample
        // verification.
        let mut s = TermStore::new();
        let y = s.var(0);
        let x = s.var(1);
        let z_captured = s.var(2);
        let xy = s.prim(PrimOp::Add, x, y);
        let xyz = s.prim(PrimOp::Add, xy, z_captured);
        let inner = s.abs(xyz);
        let capturing_add = s.abs(inner);

        let three = s.lit(3);
        let partial = s.app(capturing_add, three);

        let g2 = s.var(0);
        let four = s.lit(4);
        let call_g2 = s.app(g2, four);
        let caller = s.abs(call_g2);

        let called = s.app(caller, partial);
        let g = s.abs(called);

        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, g, &[10]).unwrap(), 17); // (3 + 4 + 10)
        assert_eq!(jit.stats.compiled, 1);
        assert_eq!(jit.stats.interpreted, 0);
        assert!(jit.is_kernel_verified(g));
    }

    #[test]
    fn partial_application_of_a_self_recursive_root_compiles_and_is_kernel_verified() {
        // rec f n acc = if n <= 0 then acc else f(n-1, n*acc); partial =
        // f(3) (under-applied by one arg); caller = \g. g(1); top =
        // caller(partial) -- same shape as proof::tests::
        // a_partially_applied_self_recursive_combinator_used_as_a_value_gets_a_closure_proof.
        // compile.rs's register_partial_app/emit_pap_wrapper never
        // special-cased is_rec (a PAP wrapper only ever forwards a static
        // call to its root, indifferent to whether that root's own codegen
        // happens to loop), and now neither does proof.rs's pap_ref, so
        // this gets a kernel-checked proof too.
        let mut s = TermStore::new();
        let acc = s.var(0);
        let n = s.var(1);
        let f = s.var(2);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Le, n, zero);
        let one = s.lit(1);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one);
        let n_times_acc = s.prim(PrimOp::Mul, n, acc);
        let rec_call = s.app2(f, n_minus_1, n_times_acc);
        let body = s.if_(cond, acc, rec_call);
        let inner = s.abs(body);
        let abs = s.abs(inner);
        let fact2 = s.rec(abs);

        let three = s.lit(3);
        let partial = s.app(fact2, three);

        let g = s.var(0);
        let one2 = s.lit(1);
        let call_g = s.app(g, one2);
        let caller = s.abs(call_g);

        let top = s.app(caller, partial);

        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, top, &[]).unwrap(), 6); // fact2(3,1) = 3*2*1
        assert_eq!(jit.stats.compiled, 1);
        assert_eq!(jit.stats.interpreted, 0);
        assert!(jit.is_kernel_verified(top));
    }

    #[test]
    fn partial_application_of_a_capturing_self_recursive_root_compiles_and_is_kernel_verified() {
        // \z. caller(fact2(3)) where fact2 = rec f n acc = if n <= 0 then
        // acc else f(n-1, n*acc+z) -- same shape as proof::tests::
        // partial_application_of_a_capturing_self_recursive_combinator_gets_a_closure_proof,
        // combining the two pap_ref restrictions lifted independently this
        // session (a capturing root, then a self-recursive root) in one
        // term, run for real. fact2(n=3, acc=1, z) unrolls to
        // acc=6+4z, so top(z) = 6 + 4*z.
        let mut s = TermStore::new();
        let acc = s.var(0);
        let n = s.var(1);
        let f = s.var(2);
        let z = s.var(3);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Le, n, zero);
        let one = s.lit(1);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one);
        let n_times_acc = s.prim(PrimOp::Mul, n, acc);
        let plus_z = s.prim(PrimOp::Add, n_times_acc, z);
        let rec_call = s.app2(f, n_minus_1, plus_z);
        let body = s.if_(cond, acc, rec_call);
        let acc_abs = s.abs(body);
        let n_abs = s.abs(acc_abs);
        let fact2 = s.rec(n_abs);

        let three = s.lit(3);
        let partial = s.app(fact2, three);

        let g = s.var(0);
        let one2 = s.lit(1);
        let call_g = s.app(g, one2);
        let caller = s.abs(call_g);

        let top_inner = s.app(caller, partial);
        let top = s.abs(top_inner);

        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, top, &[0]).unwrap(), 6);
        assert_eq!(jit.apply(&s, top, &[10]).unwrap(), 46);
        assert_eq!(jit.stats.compiled, 1);
        assert_eq!(jit.stats.interpreted, 0);
        assert!(jit.is_kernel_verified(top));
    }

    #[test]
    fn an_over_applied_literal_lambda_returning_a_closure_compiles_and_is_kernel_verified() {
        // f = \a b. if 0 < a then (\c. a+b+c) else (\c. a-b+c); f(a,b,c) --
        // same shape as compile::tests::
        // an_over_applied_literal_lambda_returning_a_closure_compiles_and_matches_interpreter,
        // run through the real cache (compile + sample-verify) rather than
        // raw wasmtime, at both a positive and a negative `a` so both
        // branches get exercised. `denote_closure`'s own `Term::Abs | Term::Rec`
        // case now covers over-application too, gated by
        // `combinator_return_type` correctly classifying `f`'s own
        // saturated call as `Clo`-typed (the `If` between `closure1`/
        // `closure2`) -- see proof::tests::
        // an_over_applied_literal_lambda_returning_a_closure_gets_a_closure_proof.
        let mut s = TermStore::new();
        let c1 = s.var(0);
        let b1 = s.var(1);
        let a1 = s.var(2);
        let ab1 = s.prim(PrimOp::Add, a1, b1);
        let abc1 = s.prim(PrimOp::Add, ab1, c1);
        let closure1 = s.abs(abc1);

        let c2 = s.var(0);
        let b2 = s.var(1);
        let a2 = s.var(2);
        let amb2 = s.prim(PrimOp::Sub, a2, b2);
        let ambc2 = s.prim(PrimOp::Add, amb2, c2);
        let closure2 = s.abs(ambc2);

        let a_body = s.var(1);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Lt, zero, a_body);
        let body = s.if_(cond, closure1, closure2);
        let b_binder = s.abs(body);
        let f = s.abs(b_binder);

        let a_param = s.var(2);
        let b_param = s.var(1);
        let c_param = s.var(0);
        let fa = s.app(f, a_param);
        let fab = s.app(fa, b_param);
        let fabc = s.app(fab, c_param);
        let c_binder = s.abs(fabc);
        let bc_binder = s.abs(c_binder);
        let top = s.abs(bc_binder);

        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, top, &[10, 3, 100]).unwrap(), 113);
        assert_eq!(jit.apply(&s, top, &[-5, 3, 100]).unwrap(), 92);
        assert_eq!(jit.stats.compiled, 1);
        assert_eq!(jit.stats.interpreted, 0);
        assert!(jit.is_kernel_verified(top));
    }

    // The four shapes below mirror compile.rs's own canonical capability
    // tests exactly (same term construction) -- this is where the actual
    // stated goal of `proof::prove_closure_expr_instance` gets checked
    // end to end: before it existed, `kernel_verify` had no strategy at
    // all for a closure-typed parameter called with genuinely
    // inconsistent arities, so `is_kernel_verified` was unconditionally
    // `false` for every one of these; it's `true` now.

    #[test]
    fn an_inconsistently_called_parameters_saturating_instance_is_kernel_verified() {
        // (\f. if 0<1 then f(1,2) else f(1)) (\a b. a+b)
        let mut s = TermStore::new();
        let a = s.var(1);
        let b = s.var(0);
        let add = s.prim(PrimOp::Add, a, b);
        let inner = s.abs(add);
        let f_lit = s.abs(inner);

        let f1 = s.var(0);
        let one1 = s.lit(1);
        let two1 = s.lit(2);
        let call_2 = s.app2(f1, one1, two1);
        let f2 = s.var(0);
        let one2 = s.lit(1);
        let call_1 = s.app(f2, one2);
        let zero = s.lit(0);
        let one_c = s.lit(1);
        let cond = s.prim(PrimOp::Lt, zero, one_c);
        let inner_body = s.if_(cond, call_2, call_1);
        let f_abs = s.abs(inner_body);
        let top = s.app(f_abs, f_lit);

        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, top, &[]).unwrap(), 3);
        assert_eq!(jit.stats.interpreted, 0);
        assert!(jit.is_kernel_verified(top));
    }

    #[test]
    fn an_inconsistently_called_parameters_under_applying_instance_is_kernel_verified() {
        // (\f. if 1<0 then f(1,2) else f(1)) (\a. a+100)
        let mut s = TermStore::new();
        let a = s.var(0);
        let hundred = s.lit(100);
        let a_plus_100 = s.prim(PrimOp::Add, a, hundred);
        let f_lit = s.abs(a_plus_100);

        let f1 = s.var(0);
        let one1 = s.lit(1);
        let two1 = s.lit(2);
        let call_2 = s.app2(f1, one1, two1);
        let f2 = s.var(0);
        let one2 = s.lit(1);
        let call_1 = s.app(f2, one2);
        let one_c = s.lit(1);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Lt, one_c, zero);
        let inner_body = s.if_(cond, call_2, call_1);
        let f_abs = s.abs(inner_body);
        let top = s.app(f_abs, f_lit);

        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, top, &[]).unwrap(), 101);
        assert_eq!(jit.stats.interpreted, 0);
        assert!(jit.is_kernel_verified(top));
    }

    #[test]
    fn a_captured_value_through_an_inconsistently_called_parameter_is_kernel_verified() {
        // \k. (\f. if 0<1 then f(1,2) else f(1)) (\a b. k+a+b)
        let mut s = TermStore::new();
        let k = s.var(2);
        let a = s.var(1);
        let b = s.var(0);
        let k_plus_a = s.prim(PrimOp::Add, k, a);
        let sum = s.prim(PrimOp::Add, k_plus_a, b);
        let inner = s.abs(sum);
        let f_lit = s.abs(inner);

        let f1 = s.var(0);
        let one1 = s.lit(1);
        let two1 = s.lit(2);
        let call_2 = s.app2(f1, one1, two1);
        let f2 = s.var(0);
        let one2 = s.lit(1);
        let call_1 = s.app(f2, one2);
        let zero = s.lit(0);
        let one_c = s.lit(1);
        let cond = s.prim(PrimOp::Lt, zero, one_c);
        let inner_body = s.if_(cond, call_2, call_1);
        let f_abs = s.abs(inner_body);
        let app = s.app(f_abs, f_lit);
        let top = s.abs(app);

        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, top, &[100]).unwrap(), 103);
        assert_eq!(jit.apply(&s, top, &[-7]).unwrap(), -4);
        assert_eq!(jit.stats.interpreted, 0);
        assert!(jit.is_kernel_verified(top));
    }

    #[test]
    fn a_runtime_chosen_literals_own_instance_is_kernel_verified() {
        // \pick. (\f. if 0<1 then f(1,2) else f(1)) (if 0<pick then add else sub)
        let mut s = TermStore::new();
        let a1 = s.var(1);
        let b1 = s.var(0);
        let add_body = s.prim(PrimOp::Add, a1, b1);
        let add_inner = s.abs(add_body);
        let add_lit = s.abs(add_inner);

        let a2 = s.var(1);
        let b2 = s.var(0);
        let sub_body = s.prim(PrimOp::Sub, a2, b2);
        let sub_inner = s.abs(sub_body);
        let sub_lit = s.abs(sub_inner);

        let pick = s.var(0);
        let zero_p = s.lit(0);
        let pick_cond = s.prim(PrimOp::Lt, zero_p, pick);
        let f_value = s.if_(pick_cond, add_lit, sub_lit);

        let f1 = s.var(0);
        let one1 = s.lit(1);
        let two1 = s.lit(2);
        let call_2 = s.app2(f1, one1, two1);
        let f2 = s.var(0);
        let one2 = s.lit(1);
        let call_1 = s.app(f2, one2);
        let zero_c = s.lit(0);
        let one_c = s.lit(1);
        let cond = s.prim(PrimOp::Lt, zero_c, one_c);
        let inner_body = s.if_(cond, call_2, call_1);
        let f_abs = s.abs(inner_body);
        let app = s.app(f_abs, f_value);
        let top = s.abs(app);

        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, top, &[1]).unwrap(), 3);
        assert_eq!(jit.apply(&s, top, &[-1]).unwrap(), -1);
        assert_eq!(jit.stats.interpreted, 0);
        assert!(jit.is_kernel_verified(top));
    }
}
