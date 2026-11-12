### The proved loop form: measurements (2026-11-12)

What the build of the loop form measured (spec `docs/superpowers/specs/2026-11-12-proved-loop-form-design.md`, plan
`docs/superpowers/plans/2026-11-12-proved-loop-form.md`, tasks 1 to 5; the spikes it came from are in "v0.8's build:
measurements and checks"). A tail self call now lowers to `local.set`s of the parameter slots (last argument first)
and `Br`, printed `br $top` inside `loop $top (result i64)`. The gate proves `Br` as a restart of the function's own
entry on the current frame, so the loop is proved, not assumed. Run ids are in `docs/runs.md`; raw output is under
`%LOCALAPPDATA%\claude-runs\tatic\`.

**The bench (A B A, T5).** The `execution` bench's `jit` rows for the closure loop and gcd, main (`7ad2f0a`) against
the branch, each arm a copy of its exe (`docs/runs/2026-11-12/scripts/pfl-bench.sh`, criterion's 1 s warm-up and 3 s
measurement). A1 and B1 ran timed on CPU 8 (`pfl-bench-a1`, `-b1`). A2 was refused twice by the quiet check (CPU 8 at
12.5% and 28.1%; `pfl-bench-a2`, `-a2b`), so it ran untimed on `CFF` (`pfl-bench-a2-untimed`), then timed on a later
try (`pfl-bench-a2-timed1`).

| row | A1 main (timed) | B1 loop form (timed) | A2 main (timed) | A2 main (untimed) |
|---|---|---|---|---|
| closure loop, warm | 25.89 us | 4.416 us | 25.57 us | 27.19 us |
| closure loop, cold | 4.763 ms | 4.717 ms | 4.380 ms | 5.856 ms |
| gcd, warm | 126.4 ns | 127.2 ns | 125.8 ns | 146.3 ns |
| gcd, cold | 598.7 us | 557.9 us | 550.2 us | 657.7 us |

- The closure loop's warm call is back at the v0.7 loop's 4.4 us (4.357 us before v0.8), 5.9 times faster than
  `return_call`. Every A run reads 25.6 to 27.2 us, so the gap is the form, not the machine. This meets the ROADMAP v0.9
  check.
- Cold compile and verify is unchanged (4.72 against 4.76 and 4.38 ms; the plan's bound was 1.5 times main's). The cold rows
  are about 4.7 ms, not the 604 us of v0.8's S2b table, on both arms, while gcd's still match it; the cause is not
  established (not checked).
- gcd's warm call does not move (126 against 127 ns). Inference: its few iterations make the 1.25 ns per iteration
  that `return_call` costs invisible beside the call into the module; confirming it would take a gcd input with many
  steps.

**Correctness checks.**
- Goldens: 11 WAT files change, each a tail self `return_call` turned into `local.set`s and `br $top` inside the loop
  wrapper (`capturing_closure_loop` and its specialised form, `closure_typed_loop_carried_parameter_loop`, `gcd`,
  `gcd_with_two_base_cases`, `inconsistent_arity_loop_carried_parameter_loop`, `iterate`, `partial_application_loop`
  and its specialised form, and the two `tail_recursive_loop_with_*_self_call_arg` modules). `baseline.rs`'s verdicts
  do not change.
- The six loop-form targets are `Accepted` and the O3 spike's 54 mutants are rejected, each at its recorded layer
  (`proof/tests/loop_form.rs`). The shipped `capturing_closure_loop` and `held_out_b`, compiled as the lowering emits
  them, gate `Accepted` with `br $top` and no self `return_call`.
- `compile_fuzz` (1000 seeds, 12 trials each): all 1000 programs agree with eval through `jit.apply`. A temporary
  count (`t4-fuzz-loop-count-2`, reverted) found `br $top` in the compiled text of 482 of the 983 that compile. The
  test does not tell an installed loop from an interpreter fallback.
- A function with env words loops correctly through both env forms (`Params(1)` and `Pointer`), matching eval. It
  still pushes its env words before the `Set`s, and the `Br` drops them (`PARKED.md`, "Dead env pushes before a
  loop-form `br`").
- The workspace suite after T4 (`cargo test --workspace`, run `t4-suite`): 819 passed, 0 failed.
