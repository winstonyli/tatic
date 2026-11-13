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
  are about 4.7 ms, not the 604 us of v0.8's S2b table, on both arms, while gcd's still match it. A probe that rebuilt
  the bench at six commits (`cold-probe`, untimed on `CFF`, `docs/runs/2026-11-12/scripts/cold-probe.sh`) puts the
  step at `c46cfe6`: 632 and 607 us at `0f97e17` and `59810fd`, then 4.70, 5.07, 5.02 and 4.86 ms at `c46cfe6`,
  `d4e54b3`, `64d1689` and `7ad2f0a`. That commit brought self calls into the gate, so the cold path now includes the
  closure loop's kernel proof, and most of it is the kernel check, not the build. A probe timed `build` and `holds`
  apart, 20 runs each, untimed on `CFF` (`cold-gap-release`, patch `docs/runs/2026-11-12/patches/cold-gap-probe.patch`,
  reverted). In release, build took 0.67 to 0.70 ms (kernel work 6804) and check 3.49 to 3.82 ms (work 23552). These
  hold on a `CHECK_STACK` thread and on a 1 MiB one like criterion's main thread, with one store reused or a fresh
  store and compile per run, as the bench does. So the O3 spike's 0.70 ms build stands in a release test exe. That
  exe is not the bench: its whole cold `jit.apply` read 5.84 and 6.12 ms (the two threads), against the bench's
  timed 4.4 to 4.8 ms, and the probe was untimed at 16 to 19% CPU load. At the test profile's opt-level 1 with debug
  assertions (`cold-gap-debug`), build is 0.85 to 1.05 ms and check 4.4 to 5.7 ms. The spike's 0.70 and 3.70 ms were
  taken at that profile too, on its own tree and machine state. On the 1 MiB thread the check, and not the build,
  moves onto one `CHECK_SEGMENT` stacker segment. In release that costs 0.24 to 0.29 ms more; at opt-level 1 it costs
  0.57 and 1.29 ms more.
- A samply profile of the cold row (`cold-prof`, table `docs/runs/2026-11-12/cold-prof/named.txt`) seemed to say the
  reverse: of the samples under `compile_verify_and_apply`, `gate::build` was 56% and the check 24%. That split
  disagrees with the direct timings above, and the profile's stacks show why. On the bench's main thread
  (`docs/runs/2026-11-12/scripts/profile-roots.py`), 3364 busy stacks walk back to the thread's start, and 1503 of
  those hold `gate::build`. Another 3423 end at an ntdll root that is not the thread's start; 3416 of them hold
  `on_segment` and a kernel frame, so they ran on a stacker fiber. A further 3079 reach samply's 256 frames, and all of
  them are in the kernel; their roots cannot be seen. None of the last two groups reaches a gate frame. Inference: these
  are mostly the check's samples. The probe shows that only the check takes a segment, and the counts fit:
  1503 build samples at about 0.7 ms put about 7500 at the check's 3.5 ms, against the roughly 6500 here. That the
  truncated stacks are not the build's is not shown, since `holds` is inlined and their roots are cut off. A build with
  `holds` kept out of line, or a deeper samply stack limit, would confirm it. In this profile, then, the share of a
  caller of kernel work reads low, because its samples on a segment or deeper than 256 frames never reach the
  caller's frame. The leaf shares are not affected.
- Where the check's 23552 units of work go (a survey with counters added to the kernel, test profile; patch
  `docs/runs/2026-11-12/patches/check-breakdown-probe.patch`, never merged). Shift is 10918 and instantiate 8838, so 84% is
  re-indexing and substituting terms with loose variables under the statement's 11 leading binders and the proof's
  lambdas. Infer is 3205, whnf 364 and full conversion 227; 16154 of the conversion attempts are pointer-equal. By
  phase: definitional equality 12618, instantiating application types 4829, the statement's own inference 1695. A
  check memo would save little: 16130 check calls cover 6377 distinct keys, but repeated calls hold only 46 units.
  Checking the instance closed, with the 11 binders opened onto postulated constants, took 13081 units plus 537 to
  infer the binder types, against 23552 open. That figure leaves out building the opened instance. The same
  opening on v0.7's encoding gate at doubling d = 13 saved only 6.5% and built more nodes (`docs/tier-cycle/`, "v0.7's build: measurements
  and checks", its "Closed parameters, the falsifier"), on a different proof shape. Persisting memos across gate calls
  saved nothing (26926 units), because each call is a fresh region. Only 42 of the 3205 inferred nodes are closed.
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
