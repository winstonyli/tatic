### The generator on tatic's terms and the lowering's code: a spike (2026-11-10)

The question: does the generator above carry real inputs, the specialised `Term` through `Source::cps` on one side and
the instruction list `lower_wat.rs` emits on the other, with no per-function case? Throwaway; patch
`docs/superpowers/spikes/2026-11-10-gen-real-spike.patch`, which applies to `f9ec5e5` on its own and contains the
generator spike's patch; reverted.

**What changed.** `Source::cps` takes the kernel context and a continuation over it, holds parameters as binders, gains
a self-call case (a spine headed by the fixpoint variable: arguments left to right, then `g args (\res. k res)`) and
uses the generator's `choose` hook; the v0.7 gate calls the same `cps` with no hook, and its tests pass. The
generator's one interface change replaced its mirror source language with a source-builder closure; it was then
hashed and not edited again. The lowering's `local.get`/`local.set` of `$p{k}` and `$t{k}` map to slots `k` and
`arity + k` (its real index order), `call $f` maps to `call` only at arity 1, and any line left `Raw` stops the attempt
before a proof is built.

Run `2026-11-10-f1-real-terms-4` (untimed, about 40% load), build + check at n = 64, ms; n = 4 and 24 give the same
verdicts:

| target (census) | specialised term | n = 64 |
|---|---|---|
| sum loop A (`capturing_closure_loop`) | `rec f n acc = if n <= 0 then acc else f (n-1) (acc+n)` | 15.9 + 45.6 |
| sum loop B (`partial_application_loop`) | the same term | 13.9 + 42.2 |
| factorial | `if n <= 1 then 1 else n * f (n-1)` | 17.0 + 83.8 |
| `redundant_arithmetic_recursion` | `if n <= 0 then 0 else n*8 + 0 + f (n-1)` | 17.3 + 78.9 |
| fib | `if n < 2 then n else f (n-1) + f (n-2)` | 15.0 + 52.9 |
| direct call 13 (`twice_inc_5`) | `(\x. x+1) (5+1)` | no proof: `i32.const 0`, `call $c0` have no `Ins` |
| direct call 34 (`let_bound_factorial_10`) | `(rec ...) 10` | no proof: the same two lines |

Six terms written after the hash, parsed and lowered for real (a triangle loop, `dbl`, a multiply loop, nested
`f (f (n-2))`, a three-parameter loop, an `==`-guarded loop), prove at 28-99 ms of check; a seventh, a two-parameter
non-tail self-call, stops on `call $f` (calls take one argument). Rejected at n = 4 and 24: three operator swaps,
factorial's `<=` as `<`, two call arguments off by one or two, two branch swaps, a wrong `local.set`, a wrong base case
(each by the walk), the call replaced by a push (by the shape check), and factorial's proof against fib's statement
(by the kernel). The existing gate tests (run `-5`) and the whole `tatic-wasm` library (run `-6`) pass on the patch.

What it settles, and what stays open:

- **Real terms carry.** The five loop and self-recursion targets of the census install from emitted code through one
  unchanged generator; what blocks the rest is the machine's vocabulary, not the proof procedure.
- **The direct calls need a module.** 13 and 34 call another function with an `i32` environment pointer: a call that
  names its callee, a callee's law as a hypothesis, more than one argument, and an `i32` kind (the machine has words and
  bits only). Lines the lowering emits with no `Ins` yet, read from the lowering, not run: `i64.rem_s`, the wrapping
  division's scratch locals, `$envtmp`, `$papenv`, `call_indirect`.
- **The printer** names every slot `$p{i}`, so a temporary at `arity + k` would print as a parameter that does not
  exist; nothing emits these yet.

