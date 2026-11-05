## 35. Translation validation: every compilation is decompiled back

Step 2 and 3 of the IR design (§34; `docs/superpowers/specs/2026-09-23-jit-ir-design.md`).

**The gate.** `try_compile` now accepts a module only if
`decompile::decompile` rebuilds, from the IR alone, a term with the
source's content hash -- meaning it exactly, up to a `Dispatch::Fast`
arity trap (a `call_indirect` type mismatch), a runtime distinction the
term semantics doesn't model and which `jit.rs`'s sample verification
still catches on real inputs. Hashes are store-independent, so the rebuild
goes into a scratch store and never reads the source. The decompiler
shares nothing with the compiler but the IR and term types (enforced by a
test -- an allowlist on every `crate::` path, not just a denylist on
`compile`/`lower_wat`), so a bug in `classify`/`peel`/`local_index`/
`free_vars` cannot be mirrored by it and cancel out -- the pitfall the Œuf
and CompCert-validator work warns about. A mismatch is loud in debug and
counted (`compile::builder_bugs(BuilderBug::Untranslated)`) and rejected in release; the
whole suite and the release fuzzers run with zero failures, i.e. no false
alarms on anything the fragment compiles. `ir::check` also gained a rule
the decompiler needed: the combinator reference graph (`CallKnown.f`,
`MakeClosure.f`, `MakePap.wrapper` resolved through its `Pap.root`) must be
acyclic, because a cyclic one made `decompile` recurse forever instead of
being rejected cleanly.

**Not vacuous.** Mutation tests apply every single-point change -- swapped
arguments, environment slots or branches, shifted reads, changed
operators, retargeted combinators (both a call/closure site's own target
and, separately, a `Pap` wrapper's `root`) -- to every built corpus
module; every well-formed mutant (214 of them) fails validation. Flipping
a self-call's `tail` flag, which is meaning-preserving (field-parity class
2), passes. The two bugs injected directly into the decompiler while
building it (a wrong Wasm-local-to-de-Bruijn mapping, and a dropped
self-binder offset on recursive captures) were caught not by the mutation
test but by round-trip tests: the corpus and fixture checks, and for the
offset a dedicated recursive-capture test, since no corpus term exercises
that path; the mutation test's own evidence is its 214 rejections.
Injected builder bugs (swapped `If` branches, a reversed
environment-capture order, a mis-split over-application argument list) are
caught across the suite.

**What the decompiler cannot see -- and step 3.** It reads the IR, not the
WAT, so a wrong template is invisible to it. `ir_fuzz.rs` closes that gap
differentially: each template, and random well-typed IR under both
dispatch modes, runs through `lower`+wasmtime and through
`decompile`+`eval`, and must agree, a division by zero matching a trap.
The per-template tests cover closure arity 1 through 4 -- the spec's whole
range, including the top of `Dispatch::Curried`'s stage chain -- and the
random generator reaches the same ceiling. Injected template bugs (the
`MIN / -1` sequence, dynamic-apply operand order, PAP slot order) are
caught. A ceiling assert on the fraction of runs where both sides merely
agree by both erroring (measured 5.8% at 150 seeds, 9.8% at 5000 seeds;
asserted below 20%) guards against the fuzzer quietly degenerating into
mostly-trapping, mostly-uninformative runs. What remains trusted: the
templates on inputs no test reached, wasmtime, and -- since the random
generator builds only non-recursive IR (self-calls are covered separately
by the fixed per-template test) -- any interaction between the generator's
shapes and recursion.

**Cost.** Cold-compile medians (`jit_cold_compile_and_verify`, `0aaa7de`
-- no gate -- vs this branch, median of five interleaved runs per build
after the machine proved noisy): fib_30 314 → 302 ms, gcd 165 → 127 ms,
capturing_closure_loop 86.6 → 102 ms, partial_application_loop 103 → 103
ms, closure_typed_loop_carried_parameter_loop 28.4 → 26.1 ms,
inconsistent_arity_loop_carried_parameter_loop 7.41 → 6.19 ms. This
machine was shared with unrelated heavy processes throughout measurement
(individual runs for the same build swung by up to 5x); three of the six
fixtures land within about 10% and the other three move in both
directions with no consistent regression, so
the decompile-and-compare pass adds no cost distinguishable from this
machine's run-to-run spread.

**Deviations from the spec.** The decompiler lives in its own file and
takes the target `TermStore` (so step 3 can evaluate what it builds); the
failure count is a process-wide counter like `builder_bugs`, not a
`jit::Stats` field -- every caller of `try_compile`, not only the JIT, is
covered that way.

