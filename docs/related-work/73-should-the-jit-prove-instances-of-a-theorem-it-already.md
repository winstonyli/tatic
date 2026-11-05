## 73. Should the JIT prove instances of a theorem it already checked?

§71 found that `kernel_verify` spends ~34% of a cold call proving the
universal theorem at inputs 0, 1 and 2 (`jit.rs`, step 3). The install
decision ignores them: step 3 returns `Universal` from the theorem alone,
and the instances only raise `Stats::universal_instances_checked`.

**What an instance adds.** The theorem is conditional: for every input
and every evaluation trace `e : Ev(params, v)`, `loop_val(params, v, e) =
v`. It says nothing about an input whose trace doesn't exist (a call that
doesn't terminate). `instance_from_scaffold` builds the trace for one
input by stepping through the recursion in the kernel, then applies the
theorem to it. So an instance adds a kernel-checked fact that the call
terminates, with value `v`, at that one input. Nothing compares `v` with
the interpreter or the compiled code. `verify()` already runs the compiled
code against the interpreter at the same inputs (and six more), so it
covers the same points by execution, and it stays.

**What related systems do.**
- Certifying compilers check one certificate per compiled unit and never
  re-prove concrete instances on the hot path: CompCert, Jitk, and the
  verified speculative JIT of Barrière et al. (POPL 2021). Extra assurance
  is a separate, non-blocking layer: CompCert's Valex checks the emitted
  binary, and the POPL JIT leaves native code generation to testing. Both
  check an artefact the proof doesn't model, which our instances don't.
- Lean's `decide +kernel` exists to reduce a proposition once instead of
  twice: re-deriving a proven fact is treated as waste.
- Toolchains ship redundant self-checks off by default: LLVM's
  `EXPENSIVE_CHECKS` is opt-in and runs on dedicated bots (dropping one
  needless `-verify-machineinstrs` cut a test suite 22%), and GCC's
  release checking keeps only the cheap checks.
- Background work (V8, HotSpot, Coq's async `Qed`, Lean's parallel kernel
  checking, §71) is for work that must happen. The instances needn't, and
  our `Rc` proof terms can't cross threads.

**Decision.** The instances move behind an opt-in engine flag, off by
default. Tests turn it on, and `proof.rs` keeps the builder and its own
tests, including the fib16 probe. Dropping them outright was the
alternative; one sample instead of three keeps two-thirds of a cost that
buys nothing. Built as `JitEngine::prove_instances` (ba66f11).

**Cost.** A/B of bf52ba4 vs ba66f11 (`target/ab5`, `jit_cold_compile_and_verify`,
5 pairs, RTP off, 2026-09-28; best-of): `gcd` 2194 → 875 µs (−60%),
`capturing_closure_loop` 2057 → 955 µs (−54%), `partial_application_loop`
2138 → 1052 µs (−51%), `fib_30` 13,721 → 12,079 µs (−12%). The two
closure-typed loops, which get no instances, moved −2% and +3%. That is
more than §71's 34% for the first three, presumably because the theorem
and instances are most of what such a term does on a cold call (not
profiled); `fib_30` is dominated by `verify()` running `fib` on the
samples (§71), so the saving is a smaller share.

