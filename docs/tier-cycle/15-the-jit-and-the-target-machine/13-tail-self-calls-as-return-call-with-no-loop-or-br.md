### Tail self-calls as `return_call`, with no `loop` or `br`: a spike (2026-11-10)

The question: `br` and `call` are one edge in the generator, and the lowering's only `loop` wraps a function for its
tail self-calls. Can tail self-calls lower to `return_call $f`, so the machine needs no `loop` or `br`? Throwaway;
patch `docs/superpowers/spikes/2026-11-10-no-loop-spike.patch`, which applies to `b092e5c` on its own and contains the
previous spike's patch; reverted.

**What changed.** The lowering emits a self-call's arguments and then `return_call $f` in tail position or `call $f`
otherwise, with no loop wrapper, staging temporaries, copy-back or `br` (`lower_wat.rs` +7 -22). The machine's `call`
takes the callee's arity (a fresh frame, parameter `i` in local `i`), and `return_call` calls the environment with the
activation's own return continuation, a new hook; one constructor per arity up to 3. The generator's walk did not
change; its one edit, before the first run, passes that hook. wasmtime 42.0.1 accepts `return_call` with its default
configuration (the repo sets none).

Run `2026-11-10-i1-no-loop-gen-real-3` (untimed, 27% load), build + check at n = 64, ms:

| case | n = 64 | case | n = 64 |
|---|---|---|---|
| sum loop A | 5.9 + 11.8 | tri | 4.9 + 13.3 |
| sum loop B | 6.1 + 13.3 | dbl | 6.3 + 17.9 |
| factorial | 7.6 + 68.0 | mulloop | 8.9 + 21.0 |
| `redundant_arithmetic_recursion` | 7.6 + 22.0 | mixed | 11.8 + 26.5 |
| fib | 6.4 + 16.6 | pow2sum (3 parameters) | 9.8 + 18.5 |
| `==`-guarded loop | 6.2 + 10.7 | two parameters, non-tail self-call | 7.0 + 13.7 |

Every case also proves at n = 4 and 24. The two-parameter non-tail self-call, which stopped on `call $f` in the
previous spike, now proves; 13 and 34 still stop on `i32.const 0`, `call $c0`. The test prints a failure list
instead of asserting; its only entries are 13 and 34, and a case is printed as proved only after the kernel accepts
it. Rejected at n = 4 and 24: operator swaps, `<=` as `<`, call arguments off by one or two, a dropped call, swapped
branches, a wrong `local.get` in the condition and in the call's argument, a wrong base case, `return_call` put for a
non-tail `call` in factorial, fib and tri, and factorial's proof against fib's statement (by the kernel). `call` put
for a tail `return_call` proves, as it should: the code is equivalent.

Run against the emitted code: the differential compile fuzz passes 7 of 7 (`-compile-fuzz`); a tail loop of 10^6
iterations returns `n(n+1)/2` (`-deep`), while the same WAT with `call` for `return_call` traps on the stack;
`tatic-wasm` passes (`-wasm-lib`). What fails until updated: all three golden WAT tests (29 files: 23 corpus, 4
fragment, 2 specialised; `-golden`), and two `tatic` tests that expect a `loop` wrapper,
`fragment_bodies_contain_no_raw` and `gate_rejects_mutations` (`-tatic-lib`).

What it settles: one recursion edge suffices, so z5's D1 (what `loop` means) can be removed instead of decided. Gone
with `loop` and `br` (grepped, not deleted): the two constructors, `shape`'s loop stack, the restart hook, `laws.rs`'s
`loop_law` and countdown checks, the printer's arms, and `strip_loop`. Fuel stays: it moves from the machine's
`meaning` into the generator's induction. Open: calls of any arity need a family of constructors or one constructor
over a frame (the spike capped arity at 3).

