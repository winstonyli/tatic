### The heap across a non-tail call, and an older record: a spike (2026-11-10)

The question: the heap-state spike left two cases open, a non-tail call whose continuation reads the heap and an older
record read after a later allocation. Do they prove with the allocation pointer in the state, and can the per-function
cell declarations be derived? Throwaway; patch `docs/superpowers/spikes/2026-11-10-heap-continuation-spike.patch`
(applies to `28975c2`, with the heap-state patch inside); reverted. Machine code is hand-written, not emitted.

**What changed, all general.** An associativity lemma `eq ((p + i) + j) t = eq (p + (i + j)) t` (same bit-chain
technique as cancellation) lets address decisions normalise nested sums first. The closure relation `rel` gains a
premise per preserved cell: the returned heap still holds it; a return proves the premise, and a call pushes it as a
fact while the continuation is walked. `HeapSpec::derive(code, arity)` reads cells (loads at `param + literal`),
pointer parameters and preserved cells (never stored, with code after a call) off the machine code.

Runs `2026-11-10-j2a-wasm-all` (tatic-wasm 40 passed) and the checker's `-chk-j2a`, `-chk-j2a-all`, `-chk-j2a-tatic`
(76 `proof::` tests pass); build + check in ms:

| case | n = 8 | n = 24 | n = 64 |
|---|---|---|---|
| alloc r1, alloc r2, read r1's field | | | check 183 |
| three records, r1 read under `((hp + 16) + 24) + 8` | 21.5 + 74.3 | 65.3 + 464.7 | 319.4 + 9607.0 |
| non-tail call, the continuation reads a cell the callee preserves | 7.8 + 16.4 | 31.2 + 41.0 | |

Rejected at n = 8 and 24 by the generator: the non-tail call with no preserved-cell premise; the continuation reading
a cell the callee wrote; a callee overwriting the preserved cell; reading the wrong record. `derive` matches the hand
declarations in 9 of 10 cases (two of them declare nothing, so match vacuously); the exception is a pointer never
dereferenced.

What it settles, and what stays open:

- **Settled:** nested address sums need one lemma, no order facts (tested to a three-term sum; deeper is reasoning).
  A callee's preserved cells cross a non-tail call as a premise of the closure relation, the same rule as the
  statement's own cells. Cells come from the machine code, not the source term: which source values live at which
  offsets is the lowering's layout.
- **Cost:** the three-term address checks in 9.6 s at n = 64 against 0.18 s for one level; the lemma's proof size is
  what to watch.
- **Open:** a cell the callee writes and the continuation reads (needs a postcondition naming the callee's result); a
  record allocated before the call and read after it (the callee moves `hp`; reasoned route: `hp = p + D` plus
  associativity, not run).

