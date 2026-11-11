### A caller's cell across a call to another function: a spike (2026-11-11)

The question: the heap-on-frame spike carried a cell across a self-call only. Can a caller's cell survive a call
through the module's call row, with the memory still opaque in the machine? Throwaway; patch
`docs/superpowers/spikes/2026-11-11-callee-cell-spike.patch` (applies to `fb2a284`, with the heap-on-frame code
inside); reverted.

Two routes prove at n = 4 and 24 through `tatic_kernel::check` (runs `2026-11-11-w3-framed-2` to `-4`,
`-w3-wasm-lib`, `-w3-genreal`, and the checker's `-w3chk-wasm-lib`, `-w3chk-genreal`; tatic-wasm 42 passed, gen_real
10 passed, every base verdict kept):

- **The callee names the cell:** the existing post-cell premise already crosses a registry call with no generator
  change, for a pure callee and for one that writes another cell. It couples the callee to the caller's layout.
- **A footprint premise:** the callee law declares the addresses it may store to, and `rel` gains one premise: every
  address outside the footprint reads the same after the call as before. The callee's own proof checks its stores
  against the footprint; the caller rewrites a read of the returned heap to a read of the heap it called with, once
  the address is shown apart from each footprint address. It covers a callee that knows nothing of the cell, and a
  cell the caller stored itself.

Controls rejected, asserted: the callee writes the cell (with its footprint understated or honest), the caller reads
the callee's cell, the law without the premise; the kernel itself rejects one module's proof against another's
statement. `wasm.rs`, `laws.rs` and `gate.rs` are untouched against the heap-on-frame patch: the machine side stays
byte-identical, and the change is all in the generator.

- **Open:** a recursion inside a function with a footprint is refused (the premise needs transitivity); a callee
  that itself calls cannot discharge its footprint; the footprint is declared and checked, not inferred; only
  constant offsets from one base are decided; n = 64 not run.

