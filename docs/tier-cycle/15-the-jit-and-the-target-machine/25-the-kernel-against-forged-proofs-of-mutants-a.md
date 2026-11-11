### The kernel against forged proofs of mutants: a spike (2026-11-11)

The question: every heap control so far was refused by the generator's walk, before the kernel ran. Does the kernel
reject a forged proof of a mutant? Throwaway; patch `docs/superpowers/spikes/2026-11-11-kernel-controls-spike.patch`
(applies to `fb2a284`, with the heap-on-frame code inside; its test-only flag is always compiled and must not ship);
reverted.

Each mutant's statement comes from the same builder as the positive case, and each is attacked three ways: the
positive case's proof checked against the mutant's statement; the term the generator builds with the checks the
kernel would repeat switched off; and that term with every remaining walk failure replaced by `refl`. The kernel
rejected every forgery (runs `2026-11-11-w4-heap-kernel`, `-w4-real-kernel3`, the checker's `-v6-w4-all`,
`-v6-w4-suites`): the six heap mutants at n = 4, 24 and 64, and factorial `Mul` to `Add`, fib `Add` to `Sub` and two
wrong callee indices on term 13 at n = 4 and 24.

- **Settled:** no soundness finding; the walk's value, branch, slot and callee-frame checks only fail early, since
  the kernel rejects the same mutants without them.
- **Guarding what the kernel cannot see:** `check_code` (without it there is no statement for a wrong callee index),
  the gate's fragment, arity and registry checks, and the heap spec, which is an input to the statement. The
  forgeries show proofs do not transfer between statements; that the builder's statement is faithful to the code is
  trusted, not tested.
