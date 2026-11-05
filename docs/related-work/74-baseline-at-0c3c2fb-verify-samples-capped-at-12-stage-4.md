## 74. Baseline at 0c3c2fb (verify samples capped at 12, stage 4, prelude cache, `prove_instances` off)

Criterion, `--warm-up-time 3 --measurement-time 8`, pinned to 12 cores at BelowNormal, Defender RTP off, whole-machine CPU 18.6% before and 7.4% after. Raw output: `target/baseline/{proofs,execution}.txt` (untracked). Medians:

| bench | median |
|---|---|
| straight_line_refl_proof | 3.4 us |
| gcd_relational_proof_single_call | 5.1 us |
| universal_proof_one_time gcd 2 / 3 leaves | 446 us / 724 us |
| gcd_relational x1 / x5 / x10 | 4.2 / 26 / 48 us |
| gcd universal x1 | 452 us |
| closures_fragment_proof (4 variants) | 4.0-7.9 us |
| closure_typed_loop_carried universal | 659 us |
| over_application instance proofs | 1.2-1.5 ms |
| non_tail_closure_recursion instance proofs | 8.4-8.6 us |
| fib_30 interpreter / jit cold / jit warm | 621 ms / 6.0 ms / 4.5 ms |
| gcd loop interpreter / cold / warm | 2.6 us / 810 us / 122 ns |
| capturing_closure_loop cold / warm | 880 us / 4.4 us |
| partial_application_loop cold / warm | 969 us / 4.5 us |
| closure_typed_loop_carried cold / warm | 10.0 ms / 32.5 us |

A first pass at fbc988b ran with the machine at 29% CPU and read 15-25% slower across the board, *including the interpreter benches whose code did not change* (fib_30 interpreter 668 vs 621 ms). That is the size of the load effect: compare A/Bs only within one run, and treat this table, not that pass, as the reference. The only code change between the two is the sample cap, so `fib_30`'s cold call (12.8 to 6.0 ms) is the one figure it explains; the other cold benches' 10-20% are load.

