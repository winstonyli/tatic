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
//!    `RELATED_WORK.md` §37). If that fails, the term simply isn't in the
//!    compilable fragment — fall back to the interpreter and remember not
//!    to try again.
//! 2. If it compiles, don't trust it blindly. Three things must hold before
//!    it is installed: it is simply typed as `Int -> ... -> Int`
//!    (`typing::well_typed`: compiled code can't tell an `Int` from a
//!    closure, see `RELATED_WORK.md` §38), it agrees with the interpreter
//!    (the reference semantics) on a battery of sample inputs, *and*
//!    `proof.rs` produced
//!    a kernel-checked theorem covering every input
//!    (`kernel_verify`). Every input means every `Int`: a
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
//! The sample battery is the only check that touches the WAT wasmtime
//! actually runs; the kernel theorem is the only one that says anything
//! about inputs outside the battery -- but it is stated over `proof.rs`'s
//! `denote`, which *models* the compiler (`compile::build_node` and the
//! `lower_wat` templates) rather than reading its
//! output. So the pair is strictly stronger than either alone and still
//! short of end-to-end soundness (`RELATED_WORK.md` 28). Neither half
//! says anything about types, which is what the typing check is for.
//! `kernel_verify` below tries `proof.rs`'s strategies in order, first
//! success wins: a straight-line term gets one `refl` proof covering every
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

use hashbrown::HashMap;
use wasmtime::{Engine, Instance, Module, Store, Val};

use crate::eval::{self, EvalError};
use crate::proof;
use crate::term::{Hash, TermStore};

// The largest is 12, not 20: `verify` interprets every sample, and `fib(20)`
// alone was 4.6 of a 15.5 ms cold-call total (RELATED_WORK.md §71).
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
        let Some(crate::compile::Compiled { frag, specialised }) = crate::compile::compile_specialised(terms, h) else {
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
        // and `RELATED_WORK.md` §38. The check is on `h`: a specialisation
        // `h'` is βv-equivalent to it, and βv preserves types.
        if !crate::typing::well_typed(terms, h, frag.arity) {
            return Err(Some(CacheEntry::IllTyped));
        }

        let Some((module, func, hp_global)) = self.instantiate(&frag.wat) else {
            return Err(Some(CacheEntry::NotCompilable));
        };
        debug_assert_eq!(hp_global.is_some(), frag.needs_hp_reset, "compile.rs's export and needs_hp_reset flag should always agree");

        if !self.verify(terms, h, func, hp_global, frag.arity) {
            return Err(Some(CacheEntry::FailedVerification));
        }
        // The kernel theorems model the structure of the term that was
        // compiled, so for a specialised fragment they are proved about
        // `h'`. `h' ≡ h` itself is certificate-checked, not
        // kernel-checked (RELATED_WORK.md §37).
        let (proof_store, proof_term) = specialised.as_ref().map_or((terms, h), |(s, t)| (s, *t));
        // The installation gate. `verify()` agreeing on the sample
        // battery is necessary but not sufficient: it is a finite
        // probe of an `i64` domain, and a compiled form installed on
        // that alone goes on to serve arbitrary arguments no evidence
        // ever covered, so only a theorem covering every input earns
        // installation.
        //
        // Note this does *not* make the JIT sound end to end: the
        // theorem is about `proof.rs`'s `denote`, which models
        // the compiler (`build_node`, the `lower_wat` templates) rather
        // than reading the WAT that actually
        // runs. `verify()` remains the only check touching emitted
        // code, which is why it stays as the first half of this gate
        // rather than being replaced by the proof. See
        // `RELATED_WORK.md` 28.
        if !Self::kernel_verify(proof_store, proof_term, frag.arity) {
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

    /// Whether `proof.rs` proves `h` equivalent to its compiled form for
    /// *every* input, on top of (not instead of) the sample-based `verify()`
    /// above. Tries the strategies in order and stops at the first that
    /// applies:
    /// 1. `prove_pure_expr` -- a straight-line (non-recursive) term gets
    ///    one proof covering every input.
    /// 2. `prove_closure_expr` -- a closed, non-recursive term built from
    ///    non-capturing ("known-call") closures gets one proof covering
    ///    every input too -- see its own docs for what's in and out of
    ///    scope (an `If` between two closures, self-recursion combined with
    ///    closures, ...).
    /// 3. `prove_tail_recursive_universal` -- a recursive term whose shape
    ///    it covers gets one universal theorem, via real induction rather
    ///    than per-sample checking. Branching recursion (e.g. naive
    ///    Fibonacci) included.
    /// 4. At arity 0 only, where the one possible call is the whole input
    ///    space, a per-execution certificate for that call,
    ///    `prove_closure_expr_instance` (recursive shapes step 3 doesn't
    ///    cover, such as a closure-typed parameter called with inconsistent arities across call sites,
    ///    `compile.rs`'s curried-dispatch capability, including one threaded
    ///    through a recursive loop). Above arity 0 such certificates reach
    ///    only `verify()`'s own samples, so they aren't built
    ///    (`RELATED_WORK.md` 28).
    ///
    /// Anything else (e.g. a callee reached only through a captured/
    /// parameter variable whose concrete identity isn't statically known
    /// at proof-construction time -- see `RELATED_WORK.md` §9) is `false`
    /// -- see `proof.rs` for what's in scope and why.
    fn kernel_verify(terms: &TermStore, h: Hash, arity: usize) -> bool {
        // The compiled entry point is only ever passed `Int`s. The provers
        // type a called parameter as a closure (`Clo_k`), so their theorem
        // for such a term covers no call the JIT makes (RELATED_WORK.md §42).
        if calls_a_parameter(terms, h) {
            return false;
        }
        if proof::prove_pure_expr(terms, h).is_some()
            || proof::prove_closure_expr(terms, h).is_some()
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
    let Some((arity, body, is_rec)) = crate::compile::peel(terms, h) else {
        return false;
    };
    match crate::compile::infer_closure_arities(terms, body, arity, is_rec.then_some(arity as u32)) {
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
            // times over, repeating the same check (`RELATED_WORK.md` §9).
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
            // arity->=3 term (see RELATED_WORK.md).
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
mod tests {

    #[test]
    fn the_verify_battery_probes_zero_negatives_and_a_loop_that_runs_many_times() {
        // What `verify` is the only check of (the emitted code) depends on the
        // battery reaching these; the cap at 12 (RELATED_WORK.md §71) must not
        // shrink it below them.
        let samples: Vec<i64> = sample_arg_vectors(1).into_iter().map(|v| v[0]).collect();
        assert!(samples.contains(&0), "no zero");
        assert!(samples.iter().any(|&a| a < 0), "no negative");
        assert!(samples.iter().any(|&a| a >= 10), "no input that iterates 10+ times");
    }
    use super::*;
    use crate::samples::{
        a_pap_capturing, a_pap_non_capturing, capturing_closure_loop, closure_typed_loop_carried_parameter_loop,
        factorial, fib, gcd, inc, inconsistent_arity_loop_carried_parameter_loop, iterate, source, twice_inc_5,
    };
    use crate::test_corpus::{
        a_pap_of_a_capturing_self_recursive_combinator, a_pap_of_a_self_recursive_combinator,
        inconsistent_arity_capturing_instance, inconsistent_arity_iterate, inconsistent_arity_runtime_chosen_instance,
        inconsistent_arity_saturating_instance, inconsistent_arity_under_applying_instance,
        iterate_creating_a_closure_over_g, let_bound_factorial_10, over_application_if_between_closures_of_params,
    };
    use crate::term::TermStore;

    #[test]
    fn a_closure_of_the_wrong_arity_off_the_samples_is_not_installed() {
        let mut s = TermStore::new();
        let h = source(
            &mut s,
            r"\n. (\g. if n == 777 then (\k. k n) (g 1) + (\k. k n) (g 2) else n) (\x y. x + y + n)",
        );
        // Well typed, but `g` is called with one argument everywhere and
        // bound to a two-argument closure, so the fragment dispatches at the
        // wrong arity: it traps at n = 777, which no sample reaches. Types
        // don't see arity, so typing.rs accepts it. What keeps it out is the
        // universal-proof gate: the kernel types a closure by its exact
        // arity (`Clo_k`), so no proof can exist (RELATED_WORK.md §40).
        assert!(crate::typing::well_typed(&s, h, 1));
        let c = crate::compile::compile_specialised(&s, h).unwrap();
        assert!(c.specialised.is_none());
        let mut raw = JitEngine::new();
        let (_module, f, hp) = raw.instantiate(&c.frag.wat).unwrap();
        assert_eq!(raw.invoke(f, hp, &[777]), Err(EvalError::Trap));
        let mut jit = JitEngine::new();
        for n in [0, 1, 776, 777, 778] {
            assert_eq!(jit.apply(&s, h, &[n]), eval::apply_term(&s, h, &[n]), "n={n}");
        }
        assert_eq!((jit.stats.compiled, jit.stats.declined_no_universal_proof), (0, 1));
    }

    #[test]
    fn a_parameter_that_is_only_called_gets_no_universal_proof() {
        // The JIT passes only `Int`s, so a theorem that types a called
        // parameter as a closure covers none of its calls
        // (RELATED_WORK.md §42). Both provers produced one: the closure
        // prover for the first term, the tail-recursive one for the second.
        for src in [
            r"\a. \f. if a == 777 then f 5 else a",
            r"rec go g n x = if n <= 0 then x else go g (n - 1) (g x)",
        ] {
            let mut s = TermStore::new();
            let h = crate::syntax::parse(&mut s, src).unwrap();
            let arity = crate::compile::peel(&s, h).unwrap().0;
            assert!(!JitEngine::kernel_verify(&s, h, arity), "{src}");
        }
    }

    #[test]
    fn an_ill_typed_branch_off_the_samples_is_not_miscompiled() {
        // `g 1 + g` adds a closure to an Int: `eval` fails with TypeError
        // at n = 777, which no sample hits.
        let mut s = TermStore::new();
        let h = source(&mut s, r"\n. (\g. if n == 777 then g 1 + g else n) (\x. x + n)");
        let mut jit = JitEngine::new();
        for n in [0, 1, 776, 777, 778] {
            assert_eq!(jit.apply(&s, h, &[n]), eval::apply_term(&s, h, &[n]), "n={n}");
        }
        assert_eq!((jit.stats.compiled, jit.stats.declined_ill_typed), (0, 1));
    }

    #[test]
    fn a_closure_argument_of_the_wrong_arity_gets_no_proof() {
        let mut s = TermStore::new();
        let h = source(&mut s, r"\n. (\g. g 1) (\x y. x + y) n");
        // `\g. g 1` gives `g : Clo_1`, but the argument is a `Clo_2`. The
        // proof walkers used to compose them anyway, which the kernel
        // rejects (and a debug build panicked on).
        let mut jit = JitEngine::new();
        assert!(!JitEngine::kernel_verify(&s, h, 1));
        // The gate skips the per-execution prover above arity 0, so ask it directly.
        for sample in sample_arg_vectors(1) {
            assert!(proof::prove_closure_expr_instance(&s, h, &sample).is_none());
        }
        // The JIT proves the specialisation `\n. 1 + n` instead.
        assert_eq!(jit.apply(&s, h, &[4]), Ok(5));
        assert_eq!(jit.stats.specialised, 1);
    }

    #[test]
    fn an_open_redex_is_not_contracted_away_by_the_jit() {
        // Final review's probe: before the checker required a closed
        // source, `(\x. 0) v5` was contracted to `0`, `h'` compiled, no
        // sample hit 777, the universal proof on `h'` installed it, and
        // the JIT returned Ok(0) where `eval` fails. Whatever the JIT does
        // with this term, it must agree with `eval`.
        let mut s = TermStore::new();
        let h = crate::test_corpus::open_redex_probe(&mut s);
        let mut jit = JitEngine::new();
        for n in [0, 1, 776, 777, 778, -777] {
            assert_eq!(jit.apply(&s, h, &[n]), eval::apply_term(&s, h, &[n]), "n={n}");
        }
        assert_eq!(eval::apply_term(&s, h, &[777]), Err(EvalError::UnboundVariable));
    }

    #[test]
    fn the_installation_proof_is_about_the_specialised_term() {
        // No `kernel_verify` strategy proves `(\g. g) (\x. x + 1) n`
        // universally (asserted below), but its specialisation `n + 1` is
        // plain arithmetic. So installing it at all depends on proving
        // `h'`, not `h`.
        let mut s = TermStore::new();
        let h = crate::syntax::parse(&mut s, r"\n. (\g. g) (\x. x + 1) n").unwrap();
        let sp = crate::specialise::specialise(&s, h);
        let mut jit = JitEngine::new();
        assert!(!JitEngine::kernel_verify(&s, h, 1));
        assert!(JitEngine::kernel_verify(&sp.store, sp.term, 1));
        for n in [0, 5, -7] {
            assert_eq!(jit.apply(&s, h, &[n]), Ok(n + 1));
        }
        assert_eq!((jit.stats.compiled, jit.stats.specialised, jit.stats.declined_no_universal_proof), (1, 1, 0));
    }

    #[test]
    fn sample_arg_vectors_for_arity_zero_is_a_single_trivial_sample() {
        // `vec![a; 0]` is `[]` regardless of `a` -- without the dedicated
        // `0` arm, the `_` catch-all would push the same empty sample
        // once per `SAMPLE_ARGS[..6]` entry (see `sample_arg_vectors`'s
        // own comment and `RELATED_WORK.md` §9 for the redundant-proof-
        // search cost this was causing).
        assert_eq!(sample_arg_vectors(0), vec![Vec::<i64>::new()]);
    }

    #[test]
    fn sample_arg_vectors_for_higher_arity_includes_a_genuinely_distinct_sample() {
        // Before this fix, the `_` (arity >= 3) arm only ever generated
        // `vec![a; arity]` -- every position the *same* value -- despite
        // its own comment claiming an "all-small-distinct" diagonal too.
        // A compiled-code bug that swaps or misindexes two argument
        // positions is structurally invisible to an all-equal sample
        // (swapping equal values changes nothing), so `verify()` would
        // have missed
        // exactly that bug class for every arity->=3 term. Confirm at
        // least one generated sample now has genuinely different values
        // at different positions, for a couple of arities.
        for arity in [3, 4, 5] {
            let samples = sample_arg_vectors(arity);
            assert!(
                samples.iter().any(|s| s.iter().collect::<hashbrown::HashSet<_>>().len() > 1),
                "arity {arity}: no sample has distinct argument values: {samples:?}"
            );
        }
    }

    #[test]
    fn invoke_agrees_with_the_interpreter_past_the_stack_buffer_threshold() {
        // `invoke`'s own `STACK_ARGS` bound (8) is meant to be transparent:
        // a call with more arguments than that must still agree with the
        // interpreter via the heap-`Vec` fallback, not just avoid crashing.
        // A 10-ary sum is the simplest term whose arity exceeds the bound.
        let mut s = TermStore::new();
        let top = source(&mut s, r"\a b c d e f g h i j. j + i + h + g + f + e + d + c + b + a");
        let args: Vec<i64> = (1..=10).collect();

        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, top, &args).unwrap(), eval::apply_term(&s, top, &args).unwrap());
        // Without this, a broken `invoke` wouldn't necessarily show up as a
        // wrong *value* here: `verify()` itself calls `invoke` on its own
        // sample battery, so a corrupted heap-fallback call would just make
        // verification disagree and safely blacklist the term to the
        // interpreter (confirmed directly: a deliberately truncated
        // heap-fallback buffer made this assertion fail with compiled=0,
        // not a wrong sum) -- this assertion is what actually forces the
        // comparison above through the compiled path.
        assert_eq!(jit.stats.compiled, 1, "must actually exercise the compiled path, not silently fall back to the interpreter");
    }

    #[test]
    fn a_mismatched_arg_count_does_not_poison_the_cache_and_is_served_by_the_interpreter() {
        // `eval::apply_term` is fully generic over arg count -- under-
        // applying `factorial` (arity 1) with 0 args is a legitimate
        // shape it handles (evaluates to an unapplied closure, then
        // fails the final `Value::Int` match with a clean `TypeError`,
        // not a panic). This call's arity not matching `h`'s own must
        // not get cached as permanently `NotCompilable`, conflating "is
        // `h` compilable at all" with "did this one call's arg count
        // match".
        let mut s = TermStore::new();
        let fact = factorial(&mut s);
        let mut jit = JitEngine::new();

        assert!(jit.apply(&s, fact, &[]).is_err());
        assert_eq!(jit.stats.compiled, 0, "a mismatched call must not poison the cache");

        // A later, correctly-sized call must still compile normally.
        assert_eq!(jit.apply(&s, fact, &[5]).unwrap(), 120);
        assert_eq!(jit.stats.compiled, 1);

        // A further mismatched call against the now-cached, *compiled*
        // entry must fall back to the interpreter cleanly too, not
        // panic via `call_compiled`'s own debug_assert or return a
        // spurious `Trap` from feeding the compiled function's fixed
        // Wasm signature the wrong number of arguments.
        assert_eq!(jit.apply(&s, fact, &[]).unwrap_err(), eval::apply_term(&s, fact, &[]).unwrap_err());
    }

    #[test]
    fn a_term_too_big_as_a_tree_is_interpreted() {
        // Past `compile.rs`'s `MAX_TREE_NODES` as a tree.
        let mut s = TermStore::new();
        let h = crate::test_corpus::doubling(&mut s, 16);
        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, h, &[3]).unwrap(), 3 << 16);
        assert_eq!((jit.stats.compiled, jit.stats.interpreted), (0, 1));
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

    #[test]
    fn division_agrees_with_the_interpreter_at_i64_min_over_negative_one() {
        // `i64::MIN / -1` is the one input where `i64.div_s` traps per
        // the WebAssembly spec (the mathematical quotient overflows
        // `i64`), while `eval.rs`'s own `wrapping_div` silently wraps
        // back to `i64::MIN` -- the same non-trapping convention
        // `Add`/`Sub`/`Mul` already use uniformly. `compile.rs`'s
        // `emit_wrapping_div` special-cases exactly this combination so
        // the compiled fragment doesn't disagree with the interpreter on
        // an input `SAMPLE_ARGS` doesn't happen to include.
        let mut s = TermStore::new();
        let div = source(&mut s, r"\a b. a / b");

        let mut jit = JitEngine::new();
        let args = [i64::MIN, -1];
        let interpreted = eval::apply_term(&s, div, &args).unwrap();
        let compiled = jit.apply(&s, div, &args).unwrap();
        assert_eq!(interpreted, i64::MIN);
        assert_eq!(compiled, interpreted, "compiled and interpreted must agree on i64::MIN / -1");
        assert_eq!(jit.stats.compiled, 1, "should have compiled, not fallen back to the interpreter");
    }

    #[test]
    fn kernel_proof_recorded_for_straight_line_and_tail_recursive_terms() {
        // Straight-line, no Rec.
        let mut s = TermStore::new();
        let straight_line = crate::samples::straight_line(&mut s);

        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, straight_line, &[3, 5]).unwrap(), 6);
        assert!(jit.is_kernel_verified(straight_line));
        assert_eq!(jit.stats.compiled, 1);

        // gcd is Rec-wrapped and tail-recursive (a single self-call in tail
        // position): it gets the universal theorem.
        let gcd_term = gcd(&mut s);
        assert_eq!(jit.apply(&s, gcd_term, &[48, 18]).unwrap(), 6);
        assert!(jit.is_kernel_verified(gcd_term));
        assert_eq!(jit.stats.compiled, 2);

        // factorial is Rec-wrapped and *not* tail-recursive (the self-call
        // is nested inside a multiplication), but prove_tail_recursive_universal
        // covers leaves with any number of self-calls combined
        // arithmetically (via kernel::cong_n), so it gets the universal
        // theorem too.
        let fact = factorial(&mut s);
        assert_eq!(jit.apply(&s, fact, &[5]).unwrap(), 120);
        assert!(jit.is_kernel_verified(fact));
        assert_eq!(jit.stats.compiled, 3);
    }

    #[test]
    fn branching_recursion_gets_the_universal_theorem() {
        // Naive Fibonacci's else-branch leaf has two self-calls; the
        // universal theorem covers it. Its per-call instances are
        // proof::tests::fibonacci_branching_leaves_get_per_instance_proofs.
        let mut s = TermStore::new();
        let fibonacci = fib(&mut s);

        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, fibonacci, &[10]).unwrap(), 55);
        assert!(jit.is_kernel_verified(fibonacci));
        assert_eq!(jit.stats.compiled, 1);
    }

    #[test]
    fn non_capturing_higher_order_terms_now_compile() {
        // Both twice and inc are non-capturing, so compile.rs's known-call
        // closure support (twice becomes a combinator calling `f` through
        // a Wasm table, inc becomes another combinator) now compiles this
        // instead of falling back to the interpreter, and proof.rs's
        // prove_closure_expr gives it a kernel-checked proof too.
        let mut s = TermStore::new();
        let applied = twice_inc_5(&mut s);

        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, applied, &[]).unwrap(), 7);
        assert_eq!(jit.stats.compiled, 1);
        assert_eq!(jit.stats.interpreted, 0);
        assert!(jit.is_kernel_verified(applied));
        assert_eq!(jit.stats.compiled, 1);
    }

    #[test]
    fn a_let_bound_self_recursive_function_compiles_and_is_kernel_verified() {
        // `let fact = rec f n = .. in fact 10` desugars to
        // `(\g. g 10) (rec f n = ..)` (found via the REPL, see
        // syntax.rs/repl.rs): a named recursive function
        // called through the same combinator table a plain closure value
        // uses. compile.rs handles this (a bug fix -- see its own tests),
        // and prove_closure_expr now does too: a call to a combinator is
        // always postulated opaque (never denoted by looking inside its
        // own body), so widening `Term::Abs`-only call/value sites to also
        // accept `Term::Rec` needed no new proof machinery, just the wider
        // pattern -- see proof.rs's own denote_closure docs.
        let mut s = TermStore::new();
        let applied = let_bound_factorial_10(&mut s);

        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, applied, &[]).unwrap(), 3628800);
        assert_eq!(jit.stats.compiled, 1);
        assert_eq!(jit.stats.interpreted, 0);
        assert!(jit.is_kernel_verified(applied));
    }

    #[test]
    fn a_returned_closure_now_compiles_via_over_application() {
        // The literal lambda `\x. ...` applied to 3, then 4:
        // `unwind_app_spine` can't distinguish this from "the lambda takes
        // 2 arguments" (see `compile::tests::
        // curried_application_is_indistinguishable_from_multi_arg_calls`),
        // and the lambda is declared 1-ary, so this reads as it
        // over-applied by one argument: its own saturated call (on 3) is
        // compiled, and whatever it returns -- one of two
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
        let applied = source(&mut s, r"(\x. if 0 < x then (\y. x + y) else (\y. x - y)) 3 4");

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
        // denote_closure/prime_closure_postulates docs), so this
        // gets the universal theorem, not just per-sample relational
        // proofs.
        let mut s = TermStore::new();
        let h = capturing_closure_loop(&mut s);
        let mut jit = JitEngine::new();

        assert_eq!(jit.apply(&s, h, &[5, 0]).unwrap(), 15); // sum 1..=5
        assert!(jit.is_kernel_verified(h));
        assert_eq!(jit.stats.compiled, 1);
    }

    #[test]
    fn a_closure_typed_loop_carried_parameter_compiles_and_is_kernel_verified() {
        // `it` is `samples::iterate`, here actually run: a closure-typed
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
        let it = iterate(&mut s);
        let top = closure_typed_loop_carried_parameter_loop(&mut s, 10);

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
        // just above, with one addition: a dead (never-reached, since
        // `1 < 0` is always false) extra call site `g x 999` for `g` at
        // arity 2, alongside the live, tail-recursive arity-1
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
        let it = inconsistent_arity_iterate(&mut s);
        let top = inconsistent_arity_loop_carried_parameter_loop(&mut s, 10);

        let frag = crate::compile::try_compile(&s, it).expect("should compile via curried dispatch, per compile.rs alone");
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
        assert_eq!(jit.stats.compiled, 1);
    }

    #[test]
    fn a_closure_created_in_a_self_call_argument_capturing_a_closure_typed_loop_parameter_compiles_and_gets_a_universal_proof() {
        // Same shape as proof::tests::
        // a_closure_created_in_a_self_call_argument_capturing_a_closure_typed_loop_parameter_gets_a_universal_proof,
        // run for real here: each iteration creates a
        // fresh closure that captures `g` itself (a Clo-typed value, not
        // an Int). `g x` (a direct call) is what makes `it`'s own scan
        // classify `g` as Clo-typed in the first place -- `infer_closure_arities`
        // never looks inside the wrapper's own body, matching
        // `denote_closure`'s own "never look inside a body" discipline.
        let mut s = TermStore::new();
        let it = iterate_creating_a_closure_over_g(&mut s);
        let inc = inc(&mut s);
        let (five, zero) = (source(&mut s, "5"), source(&mut s, "0"));
        let partial = s.app2(it, five, inc);
        let top = s.app(partial, zero);

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
        // compile.rs desugars this at compile time (a synthesized wrapper
        // combinator), and proof.rs's own denote_closure now covers a
        // partial application of a *non-capturing* literal too (pap_ref),
        // so this gets a kernel-checked proof, not just empirical sample
        // verification -- see proof::tests::
        // a_partially_applied_literal_lambda_used_as_a_value_gets_a_closure_proof
        // for the same shape checked directly against proof.rs.
        let mut s = TermStore::new();
        let top = a_pap_non_capturing(&mut s);

        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, top, &[]).unwrap(), 7);
        assert_eq!(jit.stats.compiled, 1);
        assert_eq!(jit.stats.interpreted, 0);
        assert!(jit.is_kernel_verified(top));
    }

    #[test]
    fn partial_application_of_a_capturing_root_compiles_and_is_kernel_verified() {
        // lower_wat.rs's Lowering::pap_env composes the wrapper's own environment
        // with a copy of the (capturing) root's environment, and proof.rs's
        // pap_ref now mirrors that (a leading Env_n parameter when the root
        // captures, built at every call site via build_env_expr) -- see
        // proof::tests::a_partially_applied_capturing_literal_lambda_used_as_a_value_gets_a_closure_proof
        // for the same shape checked directly against proof.rs -- so this
        // now gets a kernel-checked proof, not just empirical sample
        // verification.
        let mut s = TermStore::new();
        let g = a_pap_capturing(&mut s);

        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, g, &[10]).unwrap(), 17); // (3 + 4 + 10)
        assert_eq!(jit.stats.compiled, 1);
        assert_eq!(jit.stats.interpreted, 0);
        assert!(jit.is_kernel_verified(g));
    }

    #[test]
    fn partial_application_of_a_self_recursive_root_compiles_and_is_kernel_verified() {
        // The combinator is partially applied: under-applied by one argument.
        // compile.rs's register_partial_app/lower_wat.rs's emit_pap_wrapper
        // never special-cased is_rec (a PAP wrapper only ever forwards a static
        // call to its root, indifferent to whether that root's own codegen
        // happens to loop), and now neither does proof.rs's pap_ref, so
        // this gets a kernel-checked proof too.
        let mut s = TermStore::new();
        let top = a_pap_of_a_self_recursive_combinator(&mut s);

        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, top, &[]).unwrap(), 6); // 3*2*1
        assert_eq!(jit.stats.compiled, 1);
        assert_eq!(jit.stats.interpreted, 0);
        assert!(jit.is_kernel_verified(top));
    }

    #[test]
    fn partial_application_of_a_capturing_self_recursive_root_compiles_and_is_kernel_verified() {
        // Combines the two pap_ref restrictions lifted independently this
        // session (a capturing root, then a self-recursive root) in one
        // term, run for real. The combinator at n=3, acc=1 unrolls to
        // acc=6+4z, so top(z) = 6 + 4*z.
        let mut s = TermStore::new();
        let top = a_pap_of_a_capturing_self_recursive_combinator(&mut s);

        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, top, &[0]).unwrap(), 6);
        assert_eq!(jit.apply(&s, top, &[10]).unwrap(), 46);
        assert_eq!(jit.stats.compiled, 1);
        assert_eq!(jit.stats.interpreted, 0);
        assert!(jit.is_kernel_verified(top));
    }

    #[test]
    fn an_over_applied_literal_lambda_returning_a_closure_compiles_and_is_kernel_verified() {
        // Same shape as compile::tests::
        // an_over_applied_literal_lambda_returning_a_closure_compiles_and_matches_interpreter,
        // run through the real cache (compile + sample-verify) rather than
        // raw wasmtime, at both a positive and a negative `a` so both
        // branches get exercised. `denote_closure`'s own `Term::Abs | Term::Rec`
        // case now covers over-application too, gated by
        // `combinator_return_type` correctly classifying `f`'s own
        // saturated call as `Clo`-typed (the `If` between the two
        // `\c. ...` closures) -- see proof::tests::
        // an_over_applied_literal_lambda_returning_a_closure_gets_a_closure_proof.
        let mut s = TermStore::new();
        let top = over_application_if_between_closures_of_params(&mut s);

        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, top, &[10, 3, 100]).unwrap(), 113);
        assert_eq!(jit.apply(&s, top, &[-5, 3, 100]).unwrap(), 92);
        assert_eq!(jit.stats.compiled, 1);
        assert_eq!(jit.stats.interpreted, 0);
        assert!(jit.is_kernel_verified(top));
    }

    // The four shapes below are the `samples::inconsistent_arity_*_instance`
    // terms that compile.rs's own canonical capability tests use too -- this is where the actual
    // stated goal of `proof::prove_closure_expr_instance` gets checked
    // end to end: before it existed, `kernel_verify` had no strategy at
    // all for a closure-typed parameter called with genuinely
    // inconsistent arities, so `is_kernel_verified` was unconditionally
    // `false` for every one of these; it's `true` now.

    #[test]
    fn an_inconsistently_called_parameters_saturating_instance_is_kernel_verified() {
        let mut s = TermStore::new();
        let top = inconsistent_arity_saturating_instance(&mut s);

        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, top, &[]).unwrap(), 3);
        assert_eq!(jit.stats.interpreted, 0);
        assert!(jit.is_kernel_verified(top));
    }

    #[test]
    fn an_inconsistently_called_parameters_under_applying_instance_is_kernel_verified() {
        let mut s = TermStore::new();
        let top = inconsistent_arity_under_applying_instance(&mut s);

        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, top, &[]).unwrap(), 101);
        assert_eq!(jit.stats.interpreted, 0);
        assert!(jit.is_kernel_verified(top));
    }

    #[test]
    fn a_captured_value_through_an_inconsistently_called_parameter_is_declined_for_want_of_a_universal_proof() {
        let mut s = TermStore::new();
        let top = inconsistent_arity_capturing_instance(&mut s);

        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, top, &[100]).unwrap(), 103);
        assert_eq!(jit.apply(&s, top, &[-7]).unwrap(), -4);
        // Those answers came from the interpreter. `prove_closure_expr_
        // instance` is a per-call certificate, and at arity 1 the battery
        // it runs on is a finite probe of `i64`, so the installation gate
        // declines this term outright and every call falls back. `100`
        // isn't even in `SAMPLE_ARGS`: before the gate it was served by
        // compiled code on the strength of `verify()`'s agreement at nine
        // *other* points, which is exactly what the gate exists to stop.
        assert!(!jit.is_kernel_verified(top));
        assert_eq!(jit.stats.declined_no_universal_proof, 1);
        assert_eq!(jit.stats.compiled, 0);
        assert_eq!(jit.stats.interpreted, 2);
    }

    #[test]
    fn a_runtime_chosen_literals_own_instance_is_declined_for_want_of_a_universal_proof() {
        let mut s = TermStore::new();
        let top = inconsistent_arity_runtime_chosen_instance(&mut s);

        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, top, &[1]).unwrap(), 3);
        assert_eq!(jit.apply(&s, top, &[-1]).unwrap(), -1);
        // Per-call certificates at arity 1, so the gate declines it and
        // the interpreter answers both calls -- see the sibling test
        // above for why that's `Samples` rather than `Universal`. Note
        // both arguments here *are* in `SAMPLE_ARGS`; the gate is a
        // property of the term, not of which arguments happen to show up.
        assert!(!jit.is_kernel_verified(top));
        assert_eq!(jit.stats.declined_no_universal_proof, 1);
        assert_eq!(jit.stats.compiled, 0);
        assert_eq!(jit.stats.interpreted, 2);
    }

    #[test]
    fn a_known_partial_application_is_installed_specialised_with_a_universal_proof() {
        let (_, s, h) = crate::samples::corpus().into_iter().find(|(n, ..)| *n == "partial_application_loop").unwrap();
        let mut jit = JitEngine::new();
        for args in [[0, 0], [1, 0], [5, 3], [100, -7]] {
            assert_eq!(jit.apply(&s, h, &args), eval::apply_term(&s, h, &args), "args={args:?}");
        }
        assert_eq!((jit.stats.compiled, jit.stats.specialised), (1, 1));
        assert!(jit.is_kernel_verified(h));
    }
}
