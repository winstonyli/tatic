### One call rule for self-calls and callees: a spike (2026-11-11)

The question: the frame spike's walk has four rules, and its self-call rule (through the fuel induction's hypothesis)
and its callee rule (through a callee law taken as a hypothesis) looked like one condition. Throwaway; patch
`docs/superpowers/spikes/2026-11-11-merge-call-rules-spike.patch` (applies to `fb2a284`, with the l3 frame code
inside); reverted.

They merge. A table of call entries replaces the separate fields: the function itself is entry 0, headed by the
induction's variable with its hypothesis as the law, and each callee follows, headed by the outer fuel with its law.
One branch finds the entry by head, reads the frame's spine, checks each parameter slot, the environment slot and the
padding, and applies the entry's law. The walk is three rules (return, branch, call); `sim.rs` goes from 744 to 710
lines, with only `sim.rs` changed; every verdict of the tatic-wasm lib (37 passed, 4 ignored) and gen_real (10
passed) is unchanged, reproduced by a checker (runs `2026-11-11-w2-wasm-full`, `-w2-gen-real`, `-w2chk-wasm`,
`-w2chk-genreal`).

- **Settled:** one call rule. Every law now quantifies over the temporaries, as the self-call already did, and the
  proof already covered them, so the entry's statement changes shape but no verdict does.
- **Kept, `d`:** dropping the leading numeral binder made the kernel reject every proof ("inferred Type2, expected
  Type3", run `2026-11-11-w2-wasm-lib`): the induction's motive must live a level up and the kernel has no
  cumulativity. It stays as a uniform first binder of every law, vestigial for callees.

