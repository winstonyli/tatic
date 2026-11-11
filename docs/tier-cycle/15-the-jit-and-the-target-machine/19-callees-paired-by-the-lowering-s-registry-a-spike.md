### Callees paired by the lowering's registry: a spike (2026-11-10)

The question: the modules spike paired callees with `$cK` by order of first appearance and arity. Does a real term
with several same-arity callees, called out of registration order, install, and is a swapped pairing rejected?
Throwaway; patch `docs/superpowers/spikes/2026-11-10-callee-registry-spike.patch` (applies to `b76ba93`, with the
modules patch inside); reverted.

**What changed.** `compile.rs#build` exposes the registry it already keeps: the source function term at each
combinator index, stored in `CompiledFragment`. The gate reads the pairing from it instead of guessing; each
function's callees come from its own body, so a callee calling another callee needs no new rule, and the old
rejection of that case goes. A copy of the registry's order in the gate would be wrong: it numbers head first, then
callee bodies last in, first out. The real-term tests now assert their verdicts.

Runs `2026-11-10-m2-gen-real`, `-m2-kernel4`, `-m2-full2` and the checker's `-chk-m2` (10 passed); all four terms
below have arity-1 callees and prove at n = 4 and 24 (build + check at n = 24, ms):

| term | calls in `$f` | n = 24 |
|---|---|---|
| two callees, called `$c1` then `$c0` | `$c1 $c0` | 14.4 + 30.4 |
| roles exchanged | `$c1 $c0` | 14.9 + 31.5 |
| both callees at two sites | `$c1 $c0 $c0 $c1` | 25.2 + 50.8 |
| a callee that calls another callee | `$c0 $c2 $c0 $c1` | 38.4 + 86.8 |

The checker's rerun was 3-8 times slower on a machine at 92% CPU. Every modules-spike target still proves. A swap is
refused by the generator in all 24 cases: machine calls exchanged, registry entries exchanged, or callee bodies
exchanged. Against the right proof, the kernel rejects the first and third on all four terms; it accepts the registry
swap on the three flat terms, where the statement is the same proposition (the source names its callees by their
functions, not positions), so only the generator refuses it. The specialiser inlines a pure lambda argument, so a
callee survives only when its argument holds a self-call; all four terms are shaped that way.

- **Settled:** pairing by construction from the registry, for entry-to-callee and callee-to-callee calls.
- **Open:** pap wrappers and capturing callees are refused; mutual recursion is untested (the IR check is assumed to
  exclude cycles); the full suite's 5 failures (3 golden files and the 2 tests the no-loop spike already lists) were
  not rerun on the base alone.

