### Fresh addresses by construction: the allocation pointer in the state, a spike (2026-11-10)

The question: callees that allocate or read records need a relation between heaps before and after a call (the
decision file's open heap relation). Does making the allocation pointer part of the state, so fresh addresses are
fresh by construction, avoid order reasoning on 64-bit words? Throwaway; patch
`docs/superpowers/spikes/2026-11-10-heap-state-spike.patch` (applies to `b092e5c` on its own, with the generator-on-
real-terms patch inside); reverted. Machine code is hand-written in the lowering's shape, not emitted.

**What changed.** The state is `(locals, hp, heap)`; `alloc k` returns `hp` and bumps it. The generator gained general
rules, not cases: a stuck heap read at a declared cell is rewritten by that cell's hypothesis (as rule 3 does for a
local); a store chain is walked down to the heap, deciding each address test by conversion, the region lemma or
cancellation; a test only the machine makes on an address is decided and walked down the branch it picks. Cells are
declared per function as hypotheses `h (p + off) K = K v` with the source taking `v` as a parameter; the variant with
the record's cells inside the closure relation was not built.

Run `2026-11-10-i3-heap-state-final` (untimed), build + check at n = 64, ms:

| case | n = 64 |
|---|---|
| a read at `p + 8` | 1.0 + 5.5 |
| a loop re-reading a captured cell each iteration (term 37's shape) | 8.7 + 12.1 |
| `alloc 24`, two stores, a call on the record; the callee reads it | 81.1 + 65.1 |
| the same with a header store at `q` | 111.0 + 64.2 |
| the record updated in place and passed again | 74.2 + 52.8 |
| two allocations, cells at `q` and `q + 8` | 97.3 + 58.6 |

All prove at n = 8 and 24 too, with the heap and `hp` symbolic. At n = 4 the header and two-allocation cases fail
(addresses alias in four bits); the others pass. Rejected at n = 8 and 24: a read at the wrong offset, a cell
overwritten before its read, a condition on the wrong offset, swapped store offsets, a stored value one too large,
an overwrite before a read, and a stale `hp` with two allocations. A stale `hp` with one allocation is accepted:
nothing reads the aliased cell, so nothing differs.

What it settles, and what stays open:

- **No order reasoning was needed** for addresses of the form `hp + k`, `p + k`, `hp` or `p`: the region and
  cancellation lemmas decide them. Nested sums like `(hp + 16) + 8` are not normalised and give "cannot tell".
- **Open:** a non-tail call whose continuation reads the heap (the walk after the call has no cell hypotheses), and
  reading an older record after a later allocation or store with no relation to it: both need a callee
  heap-preservation relation or order facts. Cells are declared per function by hand.

