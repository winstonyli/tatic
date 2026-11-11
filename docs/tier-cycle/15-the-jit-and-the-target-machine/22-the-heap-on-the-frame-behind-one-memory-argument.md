### The heap on the frame, behind one memory argument: a spike (2026-11-10)

The question: the state-shape choice turned on one untested claim. With locals in a frame passed in and the memory as
one opaque argument (the frame spike's l3), does the heap's return leave the machine's types, the call row and the
class interpreters unchanged? The counter-evidence: the heap spikes bind the heap's parts separately, because a
projection of a variable state is stuck without eta. Throwaway; patch
`docs/superpowers/spikes/2026-11-10-heap-on-frame-spike.patch` (applies to `31fecf2`, with the l3 frame code inside);
reverted.

The memory became a product, `Mem = V x Heap` (the allocation pointer and the heap), and the heap-continuation
spike's case was ported onto the frame: a cell preserved across a non-tail self-call, read after it, under the
preserved-cell premise. It proves through `tatic_kernel::check` at n = 4, 24 and 64 (build + check 19 + 24 ms at 24,
98 + 62 ms at 64; shared machine); six controls are rejected at every n (no premise, the wrong cell, the cell
clobbered before or after the call, the store dropped, the wrong address), each by the generator's walk, not by the
kernel. gen_real (10 passed) and the tatic-wasm lib (38 passed, 4 ignored) keep every base verdict. Runs
`2026-11-10-s1-p-all2`, the checker's `2026-11-11-s1-chk-genreal` and `-s1-chk-wasm`.

- **Settled, the machine side:** against l3, `wasm.rs` changes only in the memory's definition, three helpers to build
  and split it, and the load and store rows; the answer-typed `G`, `Ret` and `H`, `unpack`, the table entry type, the
  call row and every other class interpreter are byte-identical (the checker diffed the two patches).
- **The exception, the generator side:** `rel` and the statement bind the memory's parts separately, and the walk
  destructures the concrete state at return, recursion and call (`parts`, `split_mu`), as the counter-evidence said.
  Most of the generator's growth (`sim.rs` 744 to 1271 lines, a new 510-line `addr.rs` of address lemmas) is heap
  modelling copied from the heap spikes, which any arm with a heap needs; only the destructuring and the
  component-wise `rel` belong to the product.
- **Open:** the allocation pointer is carried but never read (no allocation tested); only a self-call, not a call
  through the module's call row; the controls show the generator refuses, not that the kernel rejects a forged proof.

