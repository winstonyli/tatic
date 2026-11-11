### Calls by index proved against a source recursion: a spike (2026-11-10)

The question: does a call fit the machine's universe levels, and can a non-tail recursion be proved against its
source? It was the open risk of a v0.8 with calls (`docs/decisions/2026-11-10-v08-shape-and-any-backend.md`, option
z3). Throwaway; patch at `docs/superpowers/spikes/2026-11-10-call-ctor-spike.patch`, reverted.

**A constructor that takes a program does not fit** (reasoning from the sort rules; not run). `Prog S T` quantifies
over `F : Sort2 -> Sort2`, so it lives at Sort3. A constructor with a `Prog` argument makes a new type `Prog'` that can
call `Prog` programs but not `Prog'` ones, since the Church encoding has no recursive type. Each layer adds one call
depth, so this form cannot express recursion.

**Calls by index into an environment fixpoint do fit, and they prove.** The callee's meaning is
`H = V -> Heap -> (V -> Heap -> R) -> R` (argument, heap, return continuation), at Sort2 like the existing `G A`. The
module's meaning is `N H (\x h k. z) B`, the same fuel fixpoint the loop uses. A `call` therefore needs no program
argument, so its constructor type would sit at the level of `bin` (inference; the spike built meanings by hand, below; the next
section builds it, with load's type).
The bodies are written in direct style. Locals are bound variables of the meaning, with no frame in the heap, so the sum
spike's "continuations must ignore the frame" restriction does not arise here. A machine built from `Ins` keeps its
locals in a frame. Whether per-activation frames, dropped at return, remove the restriction there too is untested. The
heap is passed through and never read or written, so only pure callees were covered.

The statement is relational in the continuations: for every fuel `N` with `GoodNat N`, every `R`, `z`, `x`, heap `h`,
machine continuation `km` and source continuation `ks`, `(Pi a h. km a h = ks a) -> M_N x h km = S_N x ks`, with
`M_N = N H (\x h k. z) Bm` and `S_N = N Hs (\x k. z) Bs`. The source is the same body with no heap. The types already force a relation, because
`km` takes a heap and `ks` does not. Fib also needs it to be a hypothesis rather than an equality the kernel computes
(reasoning; not tried another way). After the first call, the machine's continuation runs the second call on the machine
and the source's runs it on the source. The two are equal only by the induction hypothesis.

The proof is one fuel induction. In the step, the `then` branch is `rel` at the answer. The `else` branch is the
hypothesis at the call, with continuations and relation built from the outer ones. For fib, the outer call's relation
is the hypothesis at the inner call. Two J's push both equalities through the shared `choose`. Run
`2026-11-10-call-spike-2` (untimed, one run, 36% load):

| check | n = 4 | n = 24 | n = 64 |
|---|---|---|---|
| factorial law (proved) | 0.6 ms | 3.3 ms | 10.4 ms |
| fib law (proved) | 0.7 ms | 1.1 ms | 3.8 ms |
| factorial, machine base 0 (rejected) | 0.2 ms | 1.5 ms | 10.0 ms |
| fib, machine `sub` for `add` in the sum (rejected) | 0.4 ms | 0.7 ms | 2.2 ms |
| run by `refl`: fact 3, fuel 3, answers `k0 6` | 0.9 ms | 15.4 ms | 161 ms |
| run by `refl`: fact 3, fuel 2, times out | 0.2 ms | 1.8 ms | 9.1 ms |
| run by `refl`: fib 5, fuel 5, answers `k0 5` | 1.9 ms | 16.2 ms | 48.9 ms |
| run by `refl`: fib 5, fuel 4, times out | 0.2 ms | 0.4 ms | 1.9 ms |

The run answering 4 for fib 5 is rejected too. The two controls each change one value at a leaf (a base case, an
operator), and their proof terms come from the same builder as the proved laws. They do not test call structure: a
wrong argument, a dropped or reordered call, or a wrong continuation. The first attempt (`2026-11-10-call-spike`) failed on a de Bruijn bug in
the spike's own term building: a type built outside a binder was reused under it. It was not a kernel result.

What it settles for a calls milestone:

- **The universe risk is gone at the meaning level** for calls by index. The environment and the module's fixpoint
  check at Sort2. Whether `call`'s constructor slot fits the program type is untested here (see the limit below; the
  next section tests it), and the argument against a constructor that takes a program is reasoning only.
- **Still open, beyond size:** callees that read or write the heap, where the relation must link machine heap to source
  state (7 of the 26 class C terms keep closure records in memory; the next section tests a fixed cell only); the
  table; and the calling convention for closures.
- **The law is a simulation with a continuation relation**, the sum loop's statement generalised. It needs one
  hypothesis application per call site and one J per branch. The spike wrote each proof by hand for its function. A
  general law needs the per-call-site continuations derived from the instruction list, which was not tried.
- **Limit:** the machine meanings were written by hand at the meaning level. They were not derived from `Ins` through
  `prog` and `ctors`, so the constructor type of `call` and its `seq_step` row are untested. (The next section tests
  both.)

