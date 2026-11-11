### What a signed remainder costs the gate: a probe (2026-11-10)

The question: gcd needs `rem_s`, which the machine lacks (`Op` has no row for it, and the lowering printed
`i64.rem_s` as `Raw`). What would a 64-bit remainder circuit cost the straight-line gate? Throwaway; patch
`docs/superpowers/spikes/2026-11-10-rem-cost-spike.patch`, reverted.

**The circuit.** `Op::RemS`: both operands made non-negative by `(x ^ s) + s`, then `n` rows of restoring division,
most significant bit first, each a ripple-borrow subtract and an `n`-wide `mux`; the result takes the dividend's sign.
`Mod` got an `op_of` row, so `\a b. a % b` enters the gate. It matches `eval.rs` (`wrapping_rem`, so `MIN % -1 = 0`)
on every n = 8 pair (all 65,536, by `def_eq`) and on about 200 edge and random n = 64 pairs; the op-table test against
eval and wasmtime passes with `b = 0` skipped.

**Division by zero has no meaning yet.** `eval` returns `DivByZero` there and wasm traps; the circuit answers `x`. The
gate builds both sides from the one table, so it would accept `rem_s` by construction at `b = 0` too, and the table
test cannot check that row because neither reference has a value. Installing `Mod` needs a trap or partial-domain
story first (the machine has no trap channel; `docs/decisions/2026-11-10-v08-shape-and-any-backend.md` already notes
it for gcd).

Measured on the gate, build + check in ms (n = 8 to 32 and the first n = 64 row best of 3 in plain runs, load not
recorded; the second n = 64 row is run `2026-11-10-e4-rem-cost-2`, 74% load; `-cost`, the first attempt, failed to
launch):

| n | `a % b` | `a * b` | distinct nodes, rem / mul |
|---|---|---|---|
| 8 | 0.08 + 0.40 | 0.06 + 0.25 | 1,288 / 650 |
| 16 | 0.19 + 1.53 | 0.14 + 1.03 | 4,440 / 2,590 |
| 32 | 0.84 + 3.82 | 0.60 + 2.52 | 16,504 / 10,502 |
| 64 | 5.5 + 16.0 | 3.3 + 8.7 | 63,672 / 42,454 |
| 64 (recorded) | 3.5 + 16.2 | 4.4 + 13.1 | same |

- **It fits.** At n = 64 a remainder costs about 20 ms, 5% of the JIT path's 0.4 s, and 1.3-1.8 times a product's check;
  in an `if` arm about 29 ms against 17 ms for `*`. Two runs of the same test moved `mul` by half, so the ratio is rough.
- **Both grow quadratically**, about 4 times per doubling in nodes and check time; the remainder's `n` subtract rows
  set its size. Not profiled.
- **So gcd's cost is not the circuit.** What it lacks is the meaning at `b = 0` above, and loops through the gate.

