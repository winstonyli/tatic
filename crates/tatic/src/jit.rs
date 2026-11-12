//! JIT cache: the piece that realizes "if a high-level transformation is
//! found to be equivalent to a low-level sequence of operations on the
//! target machine, use that for future invocations."
//!
//! For a given term hash we only ever pay the compile cost once:
//!
//! 1. First call: try to compile the term into the target-machine
//!    fragment (`compile::compile_specialised`, which specialises `h`
//!    first, then compiles with `try_compile` — the certificate-checked
//!    specialisation `h' ≡ h` itself is not kernel-checked, see
//!    `docs/related-work/` §37). If that fails, the term simply isn't in the
//!    compilable fragment — fall back to the interpreter and remember not
//!    to try again.
//! 2. If it compiles, don't trust it blindly. Three things must hold before
//!    it is installed: it is simply typed as `Int -> ... -> Int`
//!    (`typing::well_typed`: compiled code can't tell an `Int` from a
//!    closure, see `docs/related-work/` §38), it agrees with the interpreter
//!    (the reference semantics) on a battery of sample inputs, *and*
//!    the kernel checked a theorem covering every input
//!    (`prove_install`). Every input means every `Int`: a
//!    theorem that types a parameter as a closure doesn't count (§42). A term that passes only the samples is
//!    cached as `NoUniversalProof` and served by the interpreter forever
//!    after -- see `compile_verify_and_apply` for why per-sample
//!    certificates don't substitute.
//! 3. Every later call for that same hash — content-addressed, so any
//!    structurally identical term anywhere hits the same entry — skips
//!    straight to the compiled, native-speed path.
//!
//! If verification ever fails (a compiler bug, in principle), the term is
//! blacklisted and permanently served by the interpreter instead, rather
//! than risking a silently wrong "optimization".
//!
//! Installation takes both halves of that gate, and neither is redundant.
//! The sample battery runs the WAT wasmtime actually runs; the kernel
//! theorem is the only check that says anything about inputs outside the
//! battery. For a term in the straight-line fragment
//! the gate covers (`proof::gate::Verdict`) that theorem is about the emitted
//! instruction list itself, run on `tatic_wasm`'s machine at n = 64
//! (`proof::gate`), and its verdict is final. For every other term it is
//! stated over `proof.rs`'s model of the compiler (`compile::build_node`
//! and the `lower_wat` templates) rather than its output, so there the
//! pair is strictly stronger than either alone and still short of
//! end-to-end soundness (`docs/related-work/` 28). Neither half says
//! anything about types, which is what the typing check is for.
//! `kernel_verify` below tries `proof.rs`'s strategies in order, first
//! success wins: a closure term gets one `refl` proof covering every
//! input; a tail-recursive term gets the universal theorem
//! (`prove_tail_recursive_universal`) if its shape allows one -- also
//! covering every input, from real induction rather than per-sample
//! checking. A term of arity 0 has exactly one possible call, so a
//! per-execution certificate for it (`prove_closure_expr_instance`)
//! covers every input too. Above arity 0
//! those certificates reach exactly as far as `verify()`'s samples
//! already do, so the gate doesn't build them. (Per *execution*, not per
//! compilation: that's why they aren't translation validation in the
//! sense the literature means, which would cover every input. See
//! `proof.rs`'s own module docs.)

pub mod compile;
pub(crate) mod ir;
pub(crate) mod lower_wat;
#[cfg(test)]
mod op_table_tests;
#[cfg(test)]
mod tail_rule_tests;
pub(crate) mod shape;
pub mod specialise;

use hashbrown::HashMap;
use wasmtime::{Engine, Instance, Module, Store, Val};

use crate::lang::eval::{self, EvalError};
use crate::proof;
use crate::lang::term::{Hash, TermStore};

// The largest is 12, not 20: `verify` interprets every sample, and `fib(20)`
// alone was 4.6 of a 15.5 ms cold-call total (docs/related-work/ §71).
const SAMPLE_ARGS: &[i64] = &[0, 1, 2, 3, 5, -1, -3, 7, 12];

enum CacheEntry {
    Compiled {
        func: wasmtime::Func,
        arity: usize,
        // Kept alive only so the module backing `func` isn't dropped.
        _module: Module,
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
    /// Compiled, but not simply typed as `Int -> ... -> Int`
    /// (`typing::well_typed`). Compiled code can't tell an `Int` from a
    /// closure, so it is never installed; see `compile_verify_and_apply`.
    IllTyped,
    FailedVerification,
    /// Compiled cleanly and agreed with the interpreter on every sample,
    /// but carries no universal theorem -- so it is deliberately *not*
    /// installed, and this term is served by the interpreter from here
    /// on.
    NoUniversalProof,
}

#[derive(Default, Debug, Clone, Copy)]
pub struct Stats {
    pub compiled: u64,
    pub cache_hits: u64,
    pub interpreted: u64,
    pub verification_failures: u64,
    /// Terms that compiled and passed `verify()` but were declined
    /// installation for lack of a universal theorem (see
    /// `compile_verify_and_apply`). These are served by the interpreter,
    /// so they also count toward `interpreted` on every call.
    pub declined_no_universal_proof: u64,
    /// Terms that compiled but were declined because they aren't simply
    /// typed (`typing::well_typed`). Served by the interpreter, so they
    /// also count toward `interpreted` on every call.
    pub declined_ill_typed: u64,
    /// Of `compiled`, how many were compiled from a certificate-checked
    /// specialisation (`compile::compile_specialised`) rather than from the
    /// term itself.
    pub specialised: u64,
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
            Some(CacheEntry::Compiled { arity, .. }) if *arity == args.len() => {
                self.stats.cache_hits += 1;
                self.call_compiled(h, args)
            }
            Some(CacheEntry::Compiled { .. }) => {
                // This call's arg count doesn't match the arity `h` was
                // actually compiled for. `eval::apply_term` is fully
                // generic over arg count (applies one at a time), so a
                // mismatched call here is a legitimate shape this cache
                // entry just can't serve -- fall back rather than
                // feeding the compiled function's fixed Wasm signature
                // the wrong number of arguments (a debug-build panic via
                // `call_compiled`'s own assertion, or a spurious `Trap`
                // in release).
                self.stats.interpreted += 1;
                eval::apply_term(terms, h, args)
            }
            Some(CacheEntry::NotCompilable)
            | Some(CacheEntry::IllTyped)
            | Some(CacheEntry::FailedVerification)
            | Some(CacheEntry::NoUniversalProof) => {
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
        match self.try_install(terms, h, args.len()) {
            Ok(()) => {
                self.stats.cache_hits += 1;
                self.call_compiled(h, args)
            }
            Err(declined) => {
                if let Some(entry) = declined {
                    match entry {
                        CacheEntry::IllTyped => self.stats.declined_ill_typed += 1,
                        CacheEntry::NoUniversalProof => self.stats.declined_no_universal_proof += 1,
                        CacheEntry::FailedVerification => self.stats.verification_failures += 1,
                        _ => {}
                    }
                    self.cache.insert(h, entry);
                }
                self.stats.interpreted += 1;
                eval::apply_term(terms, h, args)
            }
        }
    }

    /// Compiles, checks and installs `h` for calls of `nargs` arguments, or the entry that caches why not (`None`: this
    /// call's argument count is not `h`'s arity, which says nothing about `h`).
    fn try_install(&mut self, terms: &TermStore, h: Hash, nargs: usize) -> Result<(), Option<CacheEntry>> {
        let Some(crate::jit::compile::Compiled { frag, specialised }) = crate::jit::compile::compile_specialised(terms, h) else {
            return Err(Some(CacheEntry::NotCompilable));
        };

        if frag.arity != nargs {
            // Don't cache this as `NotCompilable` -- that would conflate
            // "is `h` compilable at all" (a property of `h` alone) with
            // "did this one call's arg count match `h`'s own arity" (a
            // property of this call), permanently defeating compilation
            // for `h` even once a later, correctly-sized call comes in.
            // Just interpret this one call and leave the cache untouched.
            return Err(None);
        }

        // Compiled code is untyped: an `Int` and a closure are the same
        // `i64`. Code that confuses them returns garbage where `eval` fails,
        // and neither half of the gate below sees it unless a sample reaches
        // that code (the kernel theorem is over postulated symbols with no
        // types). So only a simply typed term is installed; see `typing.rs`
        // and `docs/related-work/` §38. The check is on `h`: a specialisation
        // `h'` is βv-equivalent to it, and βv preserves types.
        if !crate::verify::typing::well_typed(terms, h, frag.arity) {
            return Err(Some(CacheEntry::IllTyped));
        }

        let Some((module, func, hp_global)) = self.instantiate(&frag.wat()) else {
            return Err(Some(CacheEntry::NotCompilable));
        };
        debug_assert_eq!(hp_global.is_some(), frag.needs_hp_reset, "compile.rs's export and needs_hp_reset flag should always agree");

        if !self.verify(terms, h, func, hp_global, frag.arity) {
            return Err(Some(CacheEntry::FailedVerification));
        }
        // The kernel theorems are about the term that was compiled, so for
        // a specialised fragment they are proved about `h'`. `h' ≡ h`
        // itself is certificate-checked, not kernel-checked
        // (docs/related-work/ §37).
        let (proof_store, proof_term) = specialised.as_ref().map_or((terms, h), |(s, t)| (s, *t));
        // The installation gate. `verify()` agreeing on the sample
        // battery is necessary but not sufficient: it is a finite
        // probe of an `i64` domain, and a compiled form installed on
        // that alone goes on to serve arbitrary arguments no evidence
        // ever covered, so only a theorem covering every input earns
        // installation (`prove_install`).
        if !Self::prove_install(proof_store, proof_term, &frag) {
            return Err(Some(CacheEntry::NoUniversalProof));
        }
        self.cache.insert(
            h,
            CacheEntry::Compiled {
                func,
                arity: frag.arity,
                _module: module,
                hp_global,
            },
        );
        self.stats.compiled += 1;
        if specialised.is_some() {
            self.stats.specialised += 1;
        }
        Ok(())
    }

    /// Whether the kernel proves `h` equal to its compiled form for every
    /// input, on top of (not instead of) the sample-based `verify()` above.
    /// A term the gate covers (`Verdict::Accepted` or `Rejected`) is decided
    /// by the gate alone, which reads the fragment's records, the instruction
    /// lists that run: its verdict is final, so a wrong body is refused even where a
    /// theorem about `h`'s model would hold. Every other term goes to
    /// `kernel_verify`, whose theorems are about `proof.rs`'s model of the
    /// compiler, not the code that runs (`docs/related-work/` 28).
    pub(crate) fn prove_install(terms: &TermStore, h: Hash, frag: &compile::CompiledFragment) -> bool {
        match proof::gate::gate(shape::wasm_table(), terms, h, frag) {
            proof::gate::Verdict::Accepted => true,
            proof::gate::Verdict::Rejected(..) => false,
            proof::gate::Verdict::NotCovered(_) => Self::kernel_verify(terms, h, frag.arity),
        }
    }

    /// Whether `proof.rs` proves `h` equivalent to the model of its compiled
    /// form for *every* input (the model is the recursion's inductive reading, `Ev` and `loop_val`; it does not
    /// read the emitted text). Tries the strategies in order and stops at
    /// the first that applies:
    /// 1. `prove_closure_expr` -- a closed, non-recursive term built from
    ///    non-capturing ("known-call") closures gets one proof covering
    ///    every input -- see its own docs for what's in and out of
    ///    scope (an `If` between two closures, self-recursion combined with
    ///    closures, ...).
    /// 2. `prove_tail_recursive_universal` -- a recursive term whose shape
    ///    it covers gets one universal theorem, via real induction rather
    ///    than per-sample checking. Branching recursion (e.g. naive
    ///    Fibonacci) included.
    /// 3. At arity 0 only, where the one possible call is the whole input
    ///    space, a per-execution certificate for that call,
    ///    `prove_closure_expr_instance` (recursive shapes step 2 doesn't
    ///    cover, such as a closure-typed parameter called with inconsistent arities across call sites,
    ///    `compile.rs`'s curried-dispatch capability, including one threaded
    ///    through a recursive loop). Above arity 0 such certificates reach
    ///    only `verify()`'s own samples, so they aren't built
    ///    (`docs/related-work/` 28).
    ///
    /// Anything else (e.g. a callee reached only through a captured/
    /// parameter variable whose concrete identity isn't statically known
    /// at proof-construction time -- see `docs/related-work/` §9) is `false`
    /// -- see `proof.rs` for what's in scope and why.
    fn kernel_verify(terms: &TermStore, h: Hash, arity: usize) -> bool {
        // The compiled entry point is only ever passed `Int`s. The provers
        // type a called parameter as a closure (`Clo_k`), so their theorem
        // for such a term covers no call the JIT makes (docs/related-work/ §42).
        if calls_a_parameter(terms, h) {
            return false;
        }
        if proof::prove_closure_expr(terms, h).is_some()
            || proof::prove_tail_recursive_universal(terms, h).is_some()
        {
            return true;
        }
        arity == 0 && proof::prove_closure_expr_instance(terms, h, &[]).is_some()
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

    /// Whether `h` is installed: compiled, and carrying a kernel-checked
    /// equivalence theorem covering *every* input (`kernel_verify`).
    /// `false` for anything not yet compiled, not compilable, or declined.
    pub fn is_kernel_verified(&self, h: Hash) -> bool {
        matches!(self.cache.get(&h), Some(CacheEntry::Compiled { .. }))
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
        // `Val` is `Copy`, so the common case (every combinator arity this
        // project's own demo/bench/test corpus ever reaches is well under
        // this) needs no heap allocation at all -- only an arity this rare
        // falls back to a per-call `Vec`.
        const STACK_ARGS: usize = 8;
        let mut stack_buf = [Val::I64(0); STACK_ARGS];
        let heap_buf;
        let wargs: &[Val] = if args.len() <= STACK_ARGS {
            for (slot, &a) in stack_buf.iter_mut().zip(args) {
                *slot = Val::I64(a);
            }
            &stack_buf[..args.len()]
        } else {
            heap_buf = args.iter().map(|&a| Val::I64(a)).collect::<Vec<_>>();
            &heap_buf
        };
        let mut results = [Val::I64(0)];
        func.call(&mut self.rt, wargs, &mut results)
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

/// Whether `h` calls one of its own parameters, which the JIT only ever
/// binds to `Int`s. A callee shape the scan can't classify counts as a
/// call; no prover covers it anyway.
fn calls_a_parameter(terms: &TermStore, h: Hash) -> bool {
    let Some((arity, body, is_rec)) = crate::jit::shape::peel(terms, h) else {
        return false;
    };
    match crate::jit::shape::infer_closure_arities(terms, body, arity, is_rec.then_some(arity as u32)) {
        Some(found) => found.keys().any(|&i| (i as usize) < arity),
        None => true,
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
            // times over, repeating the same check (`docs/related-work/` §9).
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
            // Higher-arity: probe two diagonals rather than a full
            // cartesian product -- all-equal (every position gets the
            // same sampled value) and several rotations of an
            // all-small-distinct assignment (every position gets a
            // different one). The all-equal diagonal alone is
            // structurally blind to a compiled-code bug that swaps or
            // misindexes two argument positions, since swapping equal
            // values changes nothing observable -- this was a real,
            // previously-unfuzzed verification-coverage gap for every
            // arity->=3 term (see docs/related-work/ §17).
            for &a in &SAMPLE_ARGS[..6] {
                out.push(vec![a; arity]);
            }
            for offset in 0..SAMPLE_ARGS.len().min(6) {
                out.push((0..arity).map(|i| SAMPLE_ARGS[(i + offset) % SAMPLE_ARGS.len()]).collect());
            }
        }
    }
    out
}

#[cfg(test)]
mod tests;
