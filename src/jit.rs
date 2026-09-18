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

        let Some((module, func)) = self.instantiate(&frag.wat) else {
            self.cache.insert(h, CacheEntry::NotCompilable);
            self.stats.interpreted += 1;
            return eval::apply_term(terms, h, args);
        };

        if self.verify(terms, h, func, frag.arity) {
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
    /// 2. `prove_tail_recursive_universal` -- a tail-recursive term whose
    ///    shape it covers gets one universal theorem, also covering every
    ///    input, via real induction rather than per-sample checking.
    /// 3. `prove_tail_recursive_call`, once per sample in the same battery
    ///    `verify()` uses, reporting success only if *every* sample got its
    ///    own per-call relational proof -- the fallback for tail-recursive
    ///    shapes the universal proof doesn't (yet) cover.
    ///
    /// Anything else (non-tail recursion, genuinely higher-order terms)
    /// reports `false` -- see `proof.rs` for what's in scope and why.
    fn kernel_verify(&self, terms: &TermStore, h: Hash, arity: usize) -> bool {
        if proof::prove_pure_expr(terms, h).is_some() {
            return true;
        }
        if proof::prove_tail_recursive_universal(terms, h).is_some() {
            return true;
        }
        let samples = sample_arg_vectors(arity);
        !samples.is_empty()
            && samples
                .iter()
                .all(|sample| proof::prove_tail_recursive_call(terms, h, sample).is_some())
    }

    /// Run the compiled candidate against the interpreter (reference
    /// semantics) on a battery of sample inputs and confirm they agree.
    /// This is the "found to be equivalent" check.
    fn verify(&mut self, terms: &TermStore, h: Hash, func: wasmtime::Func, arity: usize) -> bool {
        for sample in sample_arg_vectors(arity) {
            let interpreted = eval::apply_term(terms, h, &sample);
            let compiled = self.invoke(func, &sample);
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
        let Some(CacheEntry::Compiled { func, arity, .. }) = self.cache.get(&h) else {
            unreachable!("call_compiled invoked without a compiled cache entry");
        };
        debug_assert_eq!(*arity, args.len());
        let func = *func;
        self.invoke(func, args)
    }

    fn invoke(&mut self, func: wasmtime::Func, args: &[i64]) -> Result<i64, EvalError> {
        let wargs: Vec<Val> = args.iter().map(|&a| Val::I64(a)).collect();
        let mut results = [Val::I64(0)];
        func.call(&mut self.rt, &wargs, &mut results)
            .map_err(|_| EvalError::Trap)?;
        match results[0] {
            Val::I64(n) => Ok(n),
            _ => Err(EvalError::TypeError),
        }
    }

    fn instantiate(&mut self, wat: &str) -> Option<(Module, wasmtime::Func)> {
        let bytes = wat::parse_str(wat).ok()?;
        let module = Module::new(&self.engine, &bytes).ok()?;
        let instance = Instance::new(&mut self.rt, &module, &[]).ok()?;
        let func = instance.get_func(&mut self.rt, "f")?;
        Some((module, func))
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
        let gcd_term = gcd(&mut s);
        assert_eq!(jit.apply(&s, gcd_term, &[48, 18]).unwrap(), 6);
        assert!(jit.is_kernel_verified(gcd_term));
        assert_eq!(jit.stats.kernel_proofs_checked, 2);

        // factorial is Rec-wrapped but *not* tail-recursive (the self-call
        // is nested inside a multiplication) -- outside proof.rs's
        // fragment (needs induction over an unbounded call stack, not
        // covered by the relational per-iteration proof either -- see
        // proof.rs docs), so it's compiled and sample-verified as before,
        // but not kernel-proof-verified.
        let fact = factorial(&mut s);
        assert_eq!(jit.apply(&s, fact, &[5]).unwrap(), 120);
        assert!(!jit.is_kernel_verified(fact));
        assert_eq!(jit.stats.kernel_proofs_checked, 2, "unchanged");
    }

    #[test]
    fn non_compilable_terms_still_produce_correct_results() {
        // twice = \f. \x. f (f x); inc = \y. y + 1; (twice inc) applied with no int args.
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
        assert_eq!(jit.stats.compiled, 0);
        assert_eq!(jit.stats.interpreted, 1);
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
}
