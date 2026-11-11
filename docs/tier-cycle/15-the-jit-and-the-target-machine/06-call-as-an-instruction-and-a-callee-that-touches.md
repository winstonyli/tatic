### `call` as an instruction, and a callee that touches the heap: a spike (2026-11-10)

The questions, left open by the section above: does `call` fit as a constructor of the program type, built through
`prog`; and can the relation link the machine's heap to the source's state when a callee writes memory and its caller
reads it after the call? Throwaway; patch at `docs/superpowers/spikes/2026-11-10-call-ins-spike.patch`, reverted.

**The machine change.** `Ins::Call` is a ninth constructor (index 8, after load at 7) with load's type,
`Pi A. F (V, A) -> F (V, A)`: it pops the argument and pushes the answer. Its meaning splits the stack and runs
`env x mu (\y mu'. rest (y, s) mu')`, with `env : H = V -> Mem -> (V -> Mem -> R) -> R` a new parameter of the
interpreter (`meaning_env`). Without an environment it answers the timeout. `Prog` keeps its level (Sort3). The change
touched `Ins`, `shape`, the constructor count, `seq_step`, `interp` and the printer (only its never-emitted panic list:
there is no `call` lowering to WAT); `ctor_ty` needed no new arm, since `call` falls into load's. With nine
constructors, the 31 existing tatic-wasm tests pass, plus the spike's own (run `2026-11-10-call-ins-regress-wasm`:
32 passed); its 4 ignored tests, `wasm_scaling` among them, were not run, so what the extra constructor costs existing
programs is unmeasured here (`wasm_scaling` is counted two sections down: about 1.1% more work). The `tatic` run was filtered to `gate`, `fragment` and `wasm` (`2026-11-10-call-ins-regress`:
10 gate tests, 1 fragment test and 6 tatic-wasm tests pass; 3 ignored `measure_*` tests not run).

The callee's body is a program built by `prog` from `[x]` to `[answer]` over a dummy base. Its argument and result
pass on the stack, and it has no locals: the bodies use `Dup`. A module's meaning is `N H (\x h k. z) Bm` with
`Bm = \env x h k. M_env (prog body) (x, 0) h`, and the answer is passed to `k` with its heap.

**The statement carries a state.** The source threads the cell's value `st` explicitly. Its continuation takes the
answer and the state. The heap and the state are linked by `Inv h st = Pi kk. h A kk = kk st` for the one cell `A`.
For every fuel `N` with `GoodNat N`, and every `R`, `z`, `x`, `h`, `st`, `km`, `ks`:
`(Pi a h st. Inv h st -> km a h = ks a st) -> Inv h st -> M_N x h km = S_N x st ks`. Three functions, each with
a call that has work after it:

- **sum:** `s x = x <= 0 ? x : x + s (x - 1)` (one call);
- **nest:** `d x = x <= 0 ? x : d (d (x - 1))` (the first call's continuation is the second call, which is in tail
  position; the machine treats it like any other call);
- **counter:** `c x = x <= 0 ? x : (mem[A] += 1; c (x - 1) + mem[A])` (it writes before the call and reads after).

Each proof is one fuel induction, still written by hand per function. The `then` branch is `rel`. The `else` branch
applies the hypothesis at each call. For the counter it also uses:

- `inv` at the read before the call, then one transitivity step;
- the hypothesis at the updated heap `upd A (st + 1) h`, whose `Inv` is `refl`, because conversion evaluates `upd` at
  the literal address;
- for the continuation, `inv` at the read after the call, composed with `rel` by transitivity.

**Conversion has no eta** (inferred here; the next section tests it directly). The machine's continuation for an inner call is `\y mu. km y mu`,
not `km`. The first nest proof passed `km` and was rejected with a type mismatch (run `2026-11-10-call-ins-spike-2`,
which stopped there, so the counter law has no result in it); passing the eta-expanded form made it check. A proof generated from the instruction list must follow the machine's continuations as
they are built. The first run (`2026-11-10-call-ins-spike`) failed to compile.

Run `2026-11-10-call-ins-spike-3` (untimed, one run, 22% load):

| check | n = 4 | n = 24 | n = 64 |
|---|---|---|---|
| sum law (proved) | 1.7 ms | 2.3 ms | 6.2 ms |
| nest law (proved) | 1.5 ms | 1.9 ms | 5.1 ms |
| counter law (proved) | 1.7 ms | 2.7 ms | 4.9 ms |
| sum, the call's argument `x - 2` (rejected) | 0.8 ms | 1.2 ms | 4.6 ms |
| sum, the call dropped (rejected) | 0.7 ms | 1.2 ms | 3.2 ms |
| nest, one call instead of two (rejected) | 0.9 ms | 1.3 ms | 3.3 ms |
| counter, no store (rejected) | 1.1 ms | 2.1 ms | 3.4 ms |
| counter, reads cell `A + 1` after the call (rejected) | 1.2 ms | 2.7 ms | 4.0 ms |
| run by `refl`: sum 3, fuel 4, answers `k0 6` | 1.2 ms | 2.4 ms | 7.5 ms |
| run by `refl`: nest 2, fuel 3, answers `k0 0` | 0.9 ms | 1.5 ms | 4.2 ms |
| run by `refl`: counter 3 from a zero cell, fuel 4, answers `k0 9` | 1.0 ms | 1.9 ms | 5.5 ms |

The same runs one fuel short time out, and the counter run answering 8 is rejected. Each of the five rejected law
controls changes only the machine's code; the source and the proof term stay those of the intended function. All five
fail with the same type-mismatch prefix, and the reason was not inspected further.

What it settles, and what stays open:

- **`call` fits the program type** as a constructor by index, with load's type and the program type's level
  unchanged. This answers the open part of the section above.
- **A heap through calls works for a fixed cell.** A state invariant joins the continuation relation. A write before a
  call and a read after it each cost one transitivity step.
- **Open:**
  - `Inv` names one literal address. Closure records allocated at addresses computed at run time need an invariant
    over a region, a separation-style statement, which was not tried here (the next section tests its first step).
  - Locals: the bodies avoid them, and per-activation frames are untested.
  - The table and `call_indirect`, and the calling convention for closures.
  - Proofs derived from the instruction list. Every proof here was written by hand per function, and the eta finding
    above constrains a generated one.

