## 71. Where a cold JIT call's time goes

The question was whether any of the cold path could run in parallel or
on the GPU. A throwaway probe (fe36eaf, release, pinned, Defender RTP
off, 2026-09-27) timed each phase of `compile_verify_and_apply` on a
fresh engine for every `test_corpus` term, best of 7. Summed over the 21
terms (35.6 ms):

| Phase | ms | Share |
|---|---|---|
| `kernel_verify` | 18.8 | 53% |
| - the universal theorem (`build_universal`, built and checked) | 5.7 | 16% |
| - its instances at 3 samples | 12.1 | 34% |
| wasmtime `instantiate` (Cranelift) | 8.4 | 24% |
| `verify` (interpreter vs compiled on the samples) | 7.2 | 20%, 6.5 of it `fib` |
| `compile`, `typing`, the other provers | 1.5 | 4% |

- **Per-sample provers barely run.** Only one term reached steps 4-5 of
  the cascade, with one sample each (0.4 ms). Every recursive term is
  proved universally at step 3, and the rest at steps 1-2 in under
  0.05 ms. Proving samples in parallel would save nothing.
- **Instances cost twice the theorem.** Step 3 instantiates the theorem
  at 3 samples. That only raises `Stats::universal_instances_checked`;
  installation needs the theorem alone. It is 0.9-1.9 ms per recursive
  term.
- **Cranelift is one function per module,** 0.25-0.9 ms each, so
  wasmtime's parallel compilation (per function) has nothing to split.
  It doesn't depend on the proof, so it could run beside it.
- **GPU:** nothing fits. The work is small, sequential and pointer-heavy,
  and no GPU type-theory kernel exists: Pareas does front-end passes,
  HVM2 is slower single-threaded.

What would pay, in order: drop or defer the instances (-34%, no
thread); prove in the background while the first calls run interpreted,
as V8, Lean's parallel kernel checking and Coq's proof workers do
(hides the remaining ~0.5-1 ms of theorem per recursive term); run
Cranelift beside the proof (saves the shorter of the two).

### Re-profile at fbc988b (stage 4, prelude cache, `prove_instances` off)

Same probe shape as above (throwaway ignored test in `jit.rs`, fresh `JitEngine` per run, best of 7 per term, summed over the 21 `test_corpus` terms; pinned, BelowNormal, RTP off, CPU 6% before). Total 15.5 ms:

| phase | ms | share |
|---|---|---|
| `instantiate` (wasm parse + Cranelift + instance) | 5.41 | 35% |
| `verify` (compiled vs interpreter on `SAMPLE_ARGS`) | 5.02 | 32% |
| universal theorem (`prove_tail_recursive_universal`) | 4.01 | 26% |
| compile + typing | 0.83 | 5% |
| pure / closure provers, fallback | 0.36 | 2% |

Two findings. (1) `verify` is 4.6 of its 5.0 ms on `fib` alone: the interpreter evaluating `fib(20)`. Every other term costs under 0.08 ms. Dropping or capping the large sample for non-tail recursion is the cheapest cold-path saving (about 30% of this total), and it needs no design. (2) The theorem does not depend on the compiled module, so it could run in parallel with `instantiate` + `verify` (14.4 ms serial vs a critical path of about 10.4 ms, at most 28%). That needs a thread and a per-thread kernel/prelude; not built. Change (1) was then made: the largest `SAMPLE_ARGS` entry is 12 instead of 20. The full release suite passes unchanged, and `fib_30`'s cold call went 12.8 to 6.1 ms (-52%; the other cold benches moved 1-25% but the fbc988b baseline ran at 29% CPU, so only the `fib` figure is attributable (§74)). Change (2) was not built.

Re-profile with the cap in (same probe, CPU 39% before from other load, RTP off, so read shares rather than absolutes): 12.4 ms total over the 21 terms. `instantiate` 6.3 ms (51%), universal theorem 4.4 (36%), compile + typing 0.9 (8%), `verify` 0.6 (5%), everything else 0.4. `fib`'s `verify` fell from 4.6 ms to 0.13. Cranelift is now the largest slice; the theorem is second, and it alone is what running it beside `instantiate` + `verify` could hide (a 35% ceiling).

