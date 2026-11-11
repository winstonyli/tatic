### A loop calling a closure through a fixed record, and one composed theorem: a spike (2026-11-10)

The question: the closure-relation spike did not build a loop that calls a closure each iteration, nor compose the
per-function proofs into one theorem. Throwaway; patch `docs/superpowers/spikes/2026-11-10-closure-loop-spike.patch`
(applies to `b76ba93`, with the closure-relation and heap-state patches inside); reverted.

**Term 37 is not that shape.** Its emitted code (run `2026-11-10-m3-t37-dump`) is a self-loop that re-reads the
captured cell (the heap-state spike's shape), a pap thunk, one `call_indirect` on a packed closure word and an
allocating entry: lifting it needs calls, an `i32` kind and bit rows for the word split. The spike hand-wrote the
asked shape instead, `iter p n acc = if n <= 0 then acc else iter p (n - 1) (clo acc)`.

Run `2026-11-10-m3-full3` and the checker's `-chk-m3`, `-chk-m3-wasm` (tatic-wasm 42 passed); single runs, shared
machine, build + check in ms:

| case | n = 8 | n = 24 | n = 64 |
|---|---|---|---|
| loop, abstract record invariant | 8.4 + 23.0 | 10.8 + 25.3 | 21.9 + 62.8 |
| loop, concrete cell | 6.3 + 19.4 | 12.2 + 19.1 | 22.1 + 41.0 |
| loop, a fresh record each iteration | 12.2 + 27.6 | 17.3 + 50.5 | 37.7 + 93.0 |
| the composed theorem (build + kernel inference) | 7.6 + 21.9 | 8.5 + 16.5 | 13.6 + 31.7 |

The loop proved against the abstract invariant composes with the closure body proved against the concrete cell into
one theorem the kernel types, once the abstract invariant is declared at Sort2 (a concrete cell lives in Type2,
because a word is a Church type, and the kernel has no cumulativity). Rejected at n = 8 and 24, asserted: a wrong
captured value, the loop clobbering the record before or after the call, the closure called on the wrong argument,
the call dropped; the kernel rejects four composition mutants (a wrong body, a wrong source, the invariant at the
wrong offset, a body that writes the record).

- **Settled:** the closure relation carries the record across iterations, and the separate proofs compose.
- **Corrected:** a store to a cell the invariant does not name, after the call, is rejected with the concrete cell
  too ("a cell's heap is neither the statement's heap nor a store over it"): the walk follows a store chain only down
  to the statement's own heap, not a heap a callee returned. The closure-relation spike's "A can store" holds only
  before a call.
- **Open:** term 37 as emitted; a callee that calls back, several records, a type-indexed relation; the composed
  statement is inferred, not written independently.

