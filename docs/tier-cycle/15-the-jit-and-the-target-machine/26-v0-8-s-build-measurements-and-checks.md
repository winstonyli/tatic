### v0.8's build: measurements and checks (2026-11-11)

What S0 to S2c measured while building (plan `docs/superpowers/plans/2026-11-11-v08-recursion-once.md`, tasks 4 to 13).
Run ids are in `docs/runs.md`; raw output is under `%LOCALAPPDATA%\claude-runs\tatic\`. Where a timed run was refused
(the machine was busy), the number is an untimed run on CPUs `CFF` with its comparison arm interleaved in the same
script, as the long-runs rule allows for a verdict that does not need a quiet machine; those are marked untimed.

**S0, the dispatch check (T4).** Row dispatch against the old constructor match, by retired instructions (rotated
arms, 12 runs per batch; runs `v08-s0-icount-*`). The first B missed on `gate_build_work_is_linear_in_the_tree`
(361.9 M against A's 358.9 M, +0.8%; A/A 0.14%). The cause was not the row lookup: `ctor_idx` rebuilt `ctor_list()` as
a `Vec` per instruction. With `ctor_list` a `[Ctor; 7]` array, the rerun read `gate_build` 358.5 M (-0.1%), `gate_check`
889.2 M (-0.1%) and `wasm_scaling` 197.28 M (+0.03%) against A's 358.9, 890.2 and 197.22 M; B's batch spread on
`gate_build` was 0.9%. Two batches with the wrong test filter ran nothing (27 M, start-up sized) and were discarded
(`v08-s0-icount-wasm-a1`, `-gcheck-a0`).

**S2a, the empty-`rest` call probe (T5).** Run `s2a-empty-rest3`: 10 of 10 `gen_real` tests pass; the eight targets prove
at n = 4, 24 and 64 and every control is rejected, with one exception that is not a gap: a tail call's continuation is
the activation's own up to beta, so a wrong `rel` on the sum loop is accepted (proving the same statement), and the
tail-position `rel` is therefore not a mutant for T10 and T11. Wrong `rel` on factorial and fib (non-tail calls) is
rejected, as are wrong `km` and `ks` on the sum loop.

**S2b, the benches (T5 before, T7 after).** `execution` bench, same machine, runs `v08-s2b-bench-before(-ccl)` and
`-after(-ccl)`:

| term | interpreter | cold JIT | warm |
|---|---|---|---|
| gcd, before | 2.894 us | 533 us | 120 ns |
| gcd, after | 2.918 us | 603 us | 134.5 ns |
| capturing_closure_loop, before | 7.573 ms | 564 us | 4.357 us |
| capturing_closure_loop, after | 7.673 ms | 604 us | 25.24 us |

`return_call` per iteration in place of `loop` costs the closure loop's warm call +480% (4.4 to 25 us), and gcd's +12%.
Both stay far under the interpreter (7.7 ms). The spec makes a slowdown a finding, not a gate; this is the finding.

**The go/no-go (T9) and its rerun with `Call` (T10 Step 4b).** The relational build and check of `doubling(12)` against
the refl path, untimed (5 interleaved runs per arm, `CFF`, BelowNormal; a timed run was refused for 45 minutes): relational
median 0.360 s against refl 0.399 s (0.90x), limit 0.57 s (1.5x). With `Call` in the machine (runs
`v08-s2c-call-doubling12-u1` to `-u5`, and `-d12-c1` to `-c5` against `-refl-d12-c*`; untimed again, a game held
CPU 8): call median 0.408 s (338.6, 366.6, 408.2, 450.5, 463.3 ms), refl median 0.496 s, under the 0.57 s cap. The
`Const` operand is CPS (`Fr -> Pi R:Sort0. (V -> R) -> R`): the spec's `Fr -> V` left an unreduced redex in every stack
value and made conversion about d^2 * 2^d (`doubling(7)` 3.0 M work; `doubling(10)` 49 ms with the CPS form).

**The `Call` weight fit (T12).** Run `v08-s2c-weight-fit-u1` (untimed, `doubling(12)` interleaved; the timed row
`v08-s2c-weight-fit` was refused): build and check of `rec f n = if n <= 0 then 0 else f (n-1) + .. + f (n-1)` with k
call sites, medians for k = 1, 2, 4, 8, 16, 32, 64: 12.5, 17.4, 27.2, 48.3, 123.4, 366.9, 1549 ms. The check is about
quadratic in k. `doubling(12)` took 439.8 ms in the same session; the crossing is at k about 35, tree about 215, so
`CALL_WEIGHT` is 228. A timed rerun on a quiet machine could move it (it is a plain constant).

**The targets' times (T13 Step 3).** Run `v08-s2c-targets-u1` (untimed, `CFF`; the timed row `v08-s2c-targets` was refused:
total CPU 53%, CPU 8 at 33%, a game running). `time_targets` prints `name cost build_ms check_ms`, best of 3:

| term | cost | build ms | check ms |
|---|---|---|---|
| capturing_closure_loop | 245 | 2.9 | 7.0 |
| partial_application_loop | 245 | 1.9 | 5.3 |
| factorial | 242 | 4.9 | 23.2 |
| redundant_arithmetic_recursion | 246 | 4.4 | 18.7 |
| fib | 474 | 1.9 | 8.6 |
| held_out_a | 484 | 2.9 | 18.2 |
| held_out_b | 247 | 4.1 | 19.9 |
| doubling(12) | 8192 | 163.7 | 175.1 |
| inc, doubling(4), straight_line, a_capturing_closure_call, a_pap_capturing | 4 to 32 | 0.4 to 5.9 | 1.5 to 19.5 |

Every Goal 1 target is far under `MAX_GATE_TREE` (8192) and under 55 ms for build and check together, against
`doubling(12)`'s 0.34 s here.

**The verdict column.** `proof/tests/baseline.rs#VERDICTS` holds the gate's verdict kind for every census and held-out
row, measured on the form `try_install` proves. Goal 1's five targets and both held-out terms are `Accepted`; no row is
`Rejected`; the rest (closures, `Div`/`Mod`, curried dispatch, modules with callees, the oversized term) are
`NotCovered` and keep going to `kernel_verify`. `verdicts_match` also fails if a fragment holding a `Raw` line or a
pointer-reached environment is anything but `NotCovered` (Goal 5).

**Guard: none added.** The items deleted by S0 to S2c (`loop`, `strip_loop`, `gate_with`, `in_fragment`, `upd`, the memory
rows) are code symbols, so the compiler fails on any use; the docs grep (`in_fragment`, `loop $L`, `countdown`, `Store`,
`Load`, `LocalGet`, `EnvAccess::None` over the roadmap, parked list, tour, proven and decision docs) covers the prose.
