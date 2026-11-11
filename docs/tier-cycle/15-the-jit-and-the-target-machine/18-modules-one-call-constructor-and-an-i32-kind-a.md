### Modules, one call constructor and an `i32` kind: a spike (2026-11-10)

The question: the S3 rung of the v0.8 decision. Do direct calls 13 and 34 install from emitted code through the
generator once a call names its callee, the callee's law is a hypothesis, one constructor covers every arity and an
`i32` kind carries the environment pointer? Throwaway; patch `docs/superpowers/spikes/2026-11-10-modules-i32-spike.patch`
(applies to `28975c2`, with the no-loop patch inside); reverted.

**What changed.** `Ins::Call(callee, kinds)` and `Ins::ReturnCall(callee, kinds)` are one constructor each whatever
the arity, taking the state sort as an explicit operand (needed for the levels; no universe change); the per-arity
constructors go. All functions share the fuel `N`; a callee's law enters the caller's proof as a hypothesis,
discharged once by the callee's own closed proof. `K::I` with `ConstI`/`GetI` is an `i32` word told apart only by
the shape rule; the environment sits at slot `arity`. `gen_module` and the gate's `sim_module` lift emitted `$c0..`
and `$f` bodies.

Runs `2026-11-10-s3-real2`, `-s3-real3`, `-s3-reg`, `-s3-reg2` and the checker's `-chk-j4-a` to `-c`, `-chk-j4-base`;
build + check at n = 24, ms: term 13 (`twice_inc_5`) 3.2 + 6.8; term 34 (`let_bound_factorial_10`) 7.7 + 15.2; term
23 (the pap self-call loop) 9.7 + 24.1; both sum loops, factorial, `redundant_arithmetic_recursion`, fib and seven
unseen terms still prove. Rejected by the generator: the wrong callee with kinds kept (13, 34, 23), arguments swapped
(23), a false callee law (13, 34); the wrong callee by name only by the stack check. The kernel rejects a module proof
against another callee. The real-term tests print their verdicts and do not assert them; the checker read the output.

What it settles, and what stays open:

- **Settled:** one call constructor for every arity fits the kernel's levels; callee laws as hypotheses carry 13, 23
  and 34. `fragment_bodies_contain_no_raw` and `gate_rejects_mutations` fail with the patch (they pass at clean HEAD;
  the entry is no longer a `Loop`, as in the no-loop spike).
- **Open:** callees are paired with `$cK` by order and arity, unverified (a swap gives a spurious rejection, never a
  false accept); no real term with two callees ran; a callee calling another callee is rejected; whether the state
  sort operand can be derived. The first two are answered in "Callees paired by the lowering's registry: a spike".

