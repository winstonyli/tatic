## 42. Proofs about closure arguments the JIT never passes -- found and fixed

§41's fourth host found a term the proof gate installed although it goes
wrong:

```
\a. \f. if a == 777 then f 5 else a
```

`prove_closure_expr` sees `f` called with one argument, gives it the
kernel type `Clo_1`, and proves that the compiled function equals its
denotation for every `Int` `a` and every one-argument closure `f`. The
theorem is true. But the JIT's entry point is only ever passed `Int`s, so
`f` is always an `Int`, and the theorem covers none of the calls the
fragment is installed for. At `a = 777` the compiled code calls through
whatever table entry the `Int` names (`Ok(10)` in §41's seed 7, with the
typing gate disabled), where
`eval` gives `NotAFunction`. The tail-recursive prover does the same for a
loop-carried closure parameter at the top level:
`rec go g n x = if n <= 0 then x else go g (n - 1) (g x)` got a universal
proof with `g : Clo_1`.

The typing gate (§38) already declined both, since calling an `Int` is a
type error, so nothing wrong was installed. But the proof gate's claim,
that the theorem covers every input the fragment will see, was false for
them. That was the case §38 warned of: the kernel's parameters are typed
by how the term uses them, not by how the JIT calls it.

**Fix.** `kernel_verify` returns `ProofStrength::None` for a term that
calls one of its own parameters (`calls_a_parameter`, from
`compile::infer_closure_arities`), before trying any prover. That's the
one place every prover's theorem meets the JIT's calling convention.

The provers are unchanged. A theorem over closure-typed parameters is
still a theorem, and the benches and `compile_fuzz` prove such terms (the
bare `it` of `gen_closure_typed_recursive`) directly. What changed is
which theorems the JIT counts. Where the fix belongs was a choice:

- **In `kernel_verify` (chosen).** One check covers every prover. It is
  syntactic: it asks whether a parameter is called, not what the
  theorem's context says, so it relies on every prover typing a called
  parameter as a closure. They must, since the kernel can't apply an
  `Int`.
- **In each prover.** This needs an "entry point" flag on
  `prove_closure_expr` and the tail provers, which also serve callers
  that want the closure-typed theorem.
- **Record parameter types on each proof and check them.** This is the
  most exact: the gate would read the theorem's own context. It means
  changing `EquivalenceProof` and `UniversalTailProof`, for no case the
  syntactic check misses.

**Tests.** `jit.rs`'s `a_parameter_that_is_only_called_gets_no_universal_proof`
checks both terms above, and each was seen to get `Universal` with the
check removed. In §41's fuzz, each static defence now keeps out every
ill-typed term on its own. With the typing gate disabled, there are no
mismatches. With the typing gate and this check both disabled, there are
91, all "Int called", 89 of them in the called-parameter host.

