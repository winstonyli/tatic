# tatic

An efficient implementation of an expressive higher-order language where,
once a high-level transformation is *found to be equivalent* to a low-level
sequence of operations on a formalized target machine, that low-level form
is used as a JIT-compiled implementation for future invocations of the same
transformation.

Concretely: terms are content-addressed (hash-consed), so structurally
identical transformations anywhere share one cache key. The first call for
a given term tries to compile it to WebAssembly and JIT it via `wasmtime`
(Cranelift); every later call for that same content hash skips straight to
the compiled, native-speed path. The compile step is
`compile::compile_specialised`: it first βv-reduces known closures
(`specialise.rs`, untrusted) and has an independent checker replay every
step (`spec_check.rs`), and when the checker accepts and the reduced `h'`
compiles, the fragment is built from `h'`, so for it `h' ≡ h` is
certificate-checked rather than kernel-checked (§37 of `docs/related-work/`).
"Found to be equivalent" is not just
asserted — it's checked, in two layers: sample verification against a
reference interpreter, then an actual **kernel-checked proof**, covering
every input, that the compiled and interpreted readings agree. Compiled code
is installed only when both pass; a term without such a proof stays
interpreted.

## Scope

tatic is a research prototype, not a production compiler. The compilable
fragment is small (simply typed `Int -> ... -> Int` terms with closures);
anything else is served by the interpreter. Kernel-checked equivalence proofs
cover only the terms in the proof fragment, and a term runs compiled only
with a proof covering every input (the installation gate, [docs/proven.md](docs/proven.md)). Alongside the JIT, the
repository holds a Church-encoded bit-vector library and a rewrite-rule miner
(`crates/church-bv/src/`), which are research experiments and are
not needed to use the JIT.

## Requirements

- A recent stable Rust toolchain: the crate uses edition 2024, and its
  dependencies declare a minimum of Rust 1.91 (the crate itself declares no
  `rust-version`).
- Development and measurements were done on Windows 11. The Rust code is not
  Windows-specific, but several helper scripts under `scripts/` use bash and
  PowerShell, the gate and timing tool `tools/runs` uses Windows job objects,
  and the recorded timings come from one laptop.

## License and development notes

Licensed under the Apache License, Version 2.0 (see `LICENSE`; copyright 2026
Winston Li).

This project was developed with substantial AI assistance: over 90% of the
commits (500 of 536 when this note was written) carry a `Co-Authored-By:
Claude` trailer, and the design notes in `docs/related-work/` were written the
same way. Treat the measurements and proofs as claims to re-run, not as
audited results. The design specs and implementation plans behind the work are
in `docs/superpowers/` (each starts with its `status:`); the experiment scripts
that some commits and `docs/related-work/` refer to (`scripts/experiments/`) are
not part of this repository.

## Quick start

```sh
cargo run --release             # runs the demo in crates/tatic/src/bin/demo.rs
cargo run --release --bin repl  # an interactive REPL (crates/tatic/src/bin/repl.rs)
cargo test                      # unit tests across all modules
cargo bench                     # criterion benchmarks (crates/tatic/benches/) -- see docs/benchmarks.md
cargo test --profile sweep -p church-bv --lib --no-run  # fat-LTO build for sweeps and timing (Cargo.toml)
cargo build --release --manifest-path tools/runs/Cargo.toml  # gates and timings of sweeps (Windows), tools/runs
```

The demo starts by parsing a real source string (`syntax.rs`) into a term,
then builds a few more example terms by hand (factorial, gcd, a naive
Fibonacci, a non-capturing higher-order term, a genuinely capturing
closure, a straight-line arithmetic function), runs them all through the
JIT, and prints timing plus which ones got a kernel-checked equivalence
proof. (Two capturing-closure terms appear side by side, compiled via
*different* dispatch paths: one reached by over-applying a literal
lambda's saturated-call result, the other by calling a closure-typed
*parameter* — see `lower_wat.rs`'s module docs and `crates/tatic/src/bin/demo.rs`'s comments on
each.)

## Architecture

```
 term.rs -----> eval.rs (reference semantics)
    |               ^
    |               | compared against
    v               |
 compile.rs ---> jit.rs ---> wasmtime (Cranelift JIT)
    |               ^
    |               | additional evidence
    v               |
 proof.rs <----> tatic-kernel (Pi/Sort/Id/W/Sigma type theory)
```

Files are under `crates/tatic/src/lang/`, `crates/tatic/src/jit/`, `crates/tatic/src/verify/`, `crates/tatic/src/support/` and `crates/tatic/src/testing/` (layers in `docs/TOUR.md`); `jit.rs` and `proof.rs` sit at the top; the kernel is the crate `crates/tatic-kernel`.

| Module | Role |
|---|---|
| `term.rs` | Content-addressed term store. Hash-conses a small higher-order language (`Var`/`Lit`/`Prim`/`If`/`Abs`/`App`/`Rec`) by BLAKE3 content hash, so structurally identical terms — however independently constructed — always share one hash and one cache entry. |
| `syntax.rs` | A real, parseable surface syntax for that language, so a term doesn't have to be hand-built through `term.rs`'s De Bruijn-index builders. A small recursive-descent parser (no separate AST — each grammar production interns directly via `TermStore`) with ordinary named-variable scoping (`\x y. x + y`, `let`, `rec f x = ...`), translating names to De Bruijn indices as it parses; `print` is the reverse direction, a precedence-aware pretty-printer back to source text. |
| `samples.rs` | The sample terms, written as source: the benchmarks', the demo's, the corpus unit tests and `crates/tatic/tests/golden_wat.rs` run over. Terms only unit tests use are in `test_corpus.rs`. |
| `test_corpus.rs` (test-only) | Terms only unit tests use: the shapes that unit tests in several files share (as source, through `samples::source`), and three terms the parser can't express (one with a free variable, one built past `spec_check::MAX_NODES`, and a doubled DAG whose text is exponentially long). |
| `eval.rs` | The reference interpreter (call-by-value). Defines correctness: everything else is judged against this. Supports the *full* language, including arbitrary higher-order closures. Trampolined for its own tail positions (an `If`'s chosen branch, and applying a value that resolves the current call), mirroring `lower_wat.rs`'s own `loop`/`br` lowering at the interpreter level: a tail-recursive term runs at any depth without growing the native stack, while a genuinely non-tail-recursive one (naive `fib`, say) still grows it, exactly as it would grow a Wasm `call` chain in the compiled reading. |
| `compile.rs` | Term analysis and the IR builder. Decides which terms fall in the compilable "first-order arithmetic with self-recursion and closures" fragment (`classify`, shared with `proof.rs`; `free_vars`; closure-arity inference; the combinator registry, including compile-time partial-application wrappers) and builds `ir.rs`'s IR for them (`build`). `try_compile` is a tree-size gate (§47), then build, then `ir::check`, then `lower_wat::lower`. Anything outside the fragment is rejected -- the compiler only needs to be sound, not complete. `compile_specialised` is the pipeline driver: it runs `specialise.rs`, checks the result with `spec_check.rs`, then calls `try_compile` on the specialised `h'` whenever the checker accepted its trace and `h'` compiles, and on `h` otherwise (no trace, a rejected trace, or an `h'` outside the fragment). For a specialised fragment the claim is: compiles `h'`, which decompiles to itself (§35) and is certificate-checked ≡ `h`, not kernel-checked -- see §37 of `docs/related-work/`. |
| `specialise.rs` (untrusted) | βv-reduces known closures before compilation (`caller (add acc) n` -> `acc+n`), emitting the result plus a trace of steps. Nothing here is trusted: a bug here produces a trace `spec_check.rs` rejects, or a slower program. Soundness rests on `spec_check.rs` alone -- see §37 of `docs/related-work/`. |
| `spec_check.rs` (trusted, independent) | Replays `specialise.rs`'s trace from the original term with its own `shift`/`subst`, step by step, and accepts only if it lands on exactly the claimed result. Its own independence allowlist (checked by a test, reusing `decompile.rs`'s import-scanner) permits importing only `crate::term` and `std` -- see §37 of `docs/related-work/`. |
| `ir.rs` | The JIT's IR: closure-converted, representation-neutral; well-formedness checker. |
| `lower_wat.rs` | Lowers the IR to WAT; one template per node, plus closure representation, allocator and curried stages. Its module docs describe the closure representation (a packed `i64` of table index and environment pointer), partial application, over-application and the curried fallback for inconsistent arities. |
| `jit.rs` | The cache. On first use of a term, tries to compile it, then verifies the compiled code against the interpreter on a battery of sample inputs before trusting it; only then is the compiled form installed for future calls under that hash. A verification failure permanently blacklists that hash to the interpreter rather than risking a silently wrong optimization. For a fragment with capturing closures, `invoke` also resets the bump allocator's pointer before *every* call (not just the first) — caught by benchmarking the closure-conversion path, not by any unit test: since this cache reuses *one* compiled instance across many separate calls, every capturing closure any call created was leaking its environment forever, growing that instance's linear memory unboundedly over its whole cached lifetime. The reset can't happen inside the compiled function itself (at `$f`'s own entry, say) — a non-tail self-recursive call is an ordinary `call $f`, re-entering the whole function from the top, which would reset mid-computation and corrupt a closure created earlier in the same call that's still needed after the recursive call returns. From the host, once per top-level call, there's no such hazard: nothing outside one call ever reads a closure value `$f` itself returned. |
| `typing.rs` (trusted, independent) | Simple (monomorphic) type inference over `Term`, with a closed-constant-condition rule for dead branches. `jit.rs` installs a compiled term only if it has type `Int -> ... -> Int`: compiled code stores `Int`s and closures as the same untagged `i64`, so ill-typed code returns garbage where `eval` fails, and the sample battery only notices when a sample reaches that code -- see §38 of `docs/related-work/`. Linear in shared subterms whose type is ground, and its type-safety claim is fuzzed (§45). |
| `crates/tatic-kernel` | A free-standing, minimal predicative dependent type theory: `Pi` + a stratified universe hierarchy (`Type₀:Type₁:...`) + `Id`/`Refl`/`J` (equality) + `W`/`Sup`/`WRec` (general inductive types) + `Sigma`/`Pair`/`SigRec` (dependent sums) — five primitives. The first four are provably the minimum needed for *definitional* computation of user-defined recursive functions in a predicative system (see doc comments for why weaker combinations don't work); `Sigma` is a separate addition for a different reason — `W`'s own children function maps back into `W` itself, so it can't stand in for an arbitrary, independently-chosen payload type the way a general dependent sum needs, and (as with `W` over Church-encoding) the usual `Pi`-alone encoding was rejected because it doesn't reduce by `refl`. Has a real bidirectional typechecker and normalizer. Every recursive traversal (and `Expr`'s `Drop`) runs through a `stacker`-backed `grow`, so term depth is bounded by heap, not native stack -- see §31 of `docs/related-work/`. |
| `proof.rs` | Connects `tatic-kernel` to the JIT. For terms in scope, builds an actual `Id`-typed proof — checked by `tatic-kernel`'s typechecker, not just asserted — that the compiled and interpreted readings of a term agree, and records it as additional evidence in `jit.rs`'s cache. Every walker here dispatches on `compile::classify`, the same case analysis `build_node` uses, so the proofs and the compiler cannot disagree about which case a term falls into -- see §33 of `docs/related-work/`. |
| `decompile.rs` | Translation validation: rebuilds the term an IR module implements, from the IR alone; `try_compile` requires the rebuilt term's content hash to match the source's before accepting the module -- see §35 of `docs/related-work/`. |
| `ir_fuzz.rs` (test-only) | Differential tests of the lowering templates against `decompile.rs` + `eval.rs`: each template, and random well-typed IR, run through both `lower_wat`+wasmtime and `decompile`+`eval`, and must agree -- see §35 of `docs/related-work/`. |

The closures fragment's `Int`/`Clo` type system is written down in [`docs/types.md`](docs/types.md).

## Where to read next

- [`ROADMAP.md`](ROADMAP.md): the goals, and [`PARKED.md`](PARKED.md): the deferred work.
- [`docs/TOUR.md`](docs/TOUR.md): the map of the codebase and its vocabulary.
- [`docs/proven.md`](docs/proven.md): the validation routine, exactly what is proven and what isn't, and the fuzzers.
- [`docs/syntax.md`](docs/syntax.md): the surface syntax. [`docs/design-notes.md`](docs/design-notes.md): why the code is shaped as it is.
- [`docs/benchmarks.md`](docs/benchmarks.md): the benchmarks and the `church-bv` entry points.
- [`docs/loop-experiment.md`](docs/loop-experiment.md): the rule-mining loop; its findings are in [`docs/tier-cycle/`](docs/tier-cycle/README.md).
- [`docs/related-work/`](docs/related-work/README.md): the survey and the implementation notes, cited by `§`.
