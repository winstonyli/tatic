## 26. term.rs's content_hash under-sized its scratch buffer -- found and fixed

`Term::content_hash` built its serialization scratch buffer with
`Vec::with_capacity(64)`, but `write_bytes`'s own worst case (`If`,
carrying three `Hash`es) needs `1 + 3*32 = 97` bytes -- past 64, forcing
`Vec` to grow (doubling to 128) partway through every single `If` node
interned. `Prim` (`1 + 1 + 2*32 = 66`) and even `App` (`1 + 2*32 = 65`)
both exceed 64 too, so in practice almost every non-leaf node hit this
same unnecessary reallocation. Fixed by starting at 128 directly, which
comfortably covers every variant with no growth needed at all.

This closes out the last item on the audit's punch list (`docs/related-work/`
sections 16 through 26 above cover items #2-13: five soundness/
correctness fixes, three performance fixes, three doc-staleness sweeps,
and this one) -- worked one by one, each with its own implement/verify/
validate/document/commit/push cycle.

