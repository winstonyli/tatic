## 66. An idle re-baseline, and mimalloc

Both measured 2026-09-25, 18:04 to 19:21, with Defender's real-time
protection off (it had been on through §65's runs; the log shows it
turned off at 17:20 and has no record of when it turned on) and, from
re-baseline round 2 on, total CPU sampled every 10 s. Each is 3 rounds of `scripts/gate/bench_ab.sh
--bench proofs`, best of the rounds per bench, then 3 interleaved rounds
of `fib16_instance_proof_cost`. The machine wasn't idle throughout: a
game and other sessions' jobs held the CPU at 14 to 90% through
re-baseline round 3 and mimalloc round 1 (round 1 of the re-baseline ran
before sampling began), and those rounds' noise
columns (base rerun against base) reach -63%. Mimalloc rounds 2 and 3
were quiet, with noise within -19% to +11%, and only they are used
below.

**Stage 1 against 43b5e15, again.** Best of 3, candidate against base:
`gcd_2_leaves` and `gcd_3_leaves` -28% and -29%,
`closure_typed_loop_carried_parameter_universal_proof` -24%,
`pap_producing_root` -21%, the closure fragment and non-tail proofs -11%
to -18%, and the rest within ±5% except `relational_x10`, +21%. That
one was +4% in §65 and its per-round changes swing from -37% to +31%, so
it's unresolved, not a regression shown. The `fib(16)` probe ran
contended (16 to 34% CPU): build +4%, check -6%, against -12% and -16%
in §65's idle rerun. The same unchanged code's `fib(16)` build ranged
from 297 to 414 ms across the evening, so these single-probe numbers
move by 30% with the machine's state.

**mimalloc.** The `mimalloc` crate (0.1.52) as `#[global_allocator]` in
`benches/proofs.rs` and, under `cfg(test)`, in `src/lib.rs`, against
HEAD (6cf2c67) with the system allocator. The shipped binary was left
alone. Best of rounds 2 and 3:

| bench | system | mimalloc | change |
|---|---|---|---|
| `straight_line_refl_proof` | 7.8 µs | 4.3 µs | -45% |
| `gcd_relational_proof_single_call` | 10.7 µs | 5.7 µs | -47% |
| `gcd_2_leaves` | 1.24 ms | 0.63 ms | -49% |
| `gcd_3_leaves` | 2.36 ms | 1.16 ms | -51% |
| `relational_x10` | 101.7 µs | 55.0 µs | -46% |
| `universal_x1` | 1.38 ms | 0.67 ms | -52% |
| closure fragment proofs (4) | 8.2 to 13.9 µs | 4.1 to 7.9 µs | -43 to -50% |
| `closure_typed_loop_carried_parameter_universal_proof` | 1.79 ms | 1.07 ms | -40% |
| `if_between_closures_self_call_arg` | 5.82 ms | 3.59 ms | -38% |
| `pap_producing_root_self_call_arg` | 4.47 ms | 2.62 ms | -41% |
| non-tail proofs (2) | 14.9 to 15.2 µs | 8.4 to 8.5 µs | -44% |

`fib(16)`, 3 quiet rounds (CPU 1 to 3% before each): build 297 to
150 ms (-49%), check 256 to 144 ms (-44%), best of 3.

Every proof bench roughly halves, far past the noise, and the effect is
uniform across them, as an allocator's should be: the kernel's cost is
dominated by allocating and freeing nodes. That's three to four times what
stage 1 bought, from one dependency. It says nothing yet about the rest
of the program: the JIT (Cranelift, which also allocates heavily) and
wasmtime would run on it too once it's set in `main.rs`, and neither
was measured. `libmimalloc-sys` compiles C through `cc`, which the
build already uses.

**Measuring through contention (2026-09-26).** Another session's
selfplay jobs run back to back, about 40 s each with 15 s gaps, so a
quiet check before a run passes in a gap and the run lands in the next
job; the first attempt at the runs below ran at a median 88% CPU. The
runner used here (`scripts/quiet_ab/`) samples total CPU every 2 s alongside the runs,
alternates A and B in ABBA order, and keeps a pair only if both runs saw
no selfplay process and averaged under 20% CPU from other processes.
Defender's real-time protection was off throughout. "Other processes" is
the total minus the run's own CPU: for the benches, which run for
minutes, from sampling the bench process; for the demo and probes, which
run for about a second, from the process's exact CPU time at exit. The
first cut of the runner looked only at samples wholly inside a run,
found none for a 1 s run, and so kept no demo runs at all. Per-process
counters can't stand in for the subtraction: a non-elevated
`Get-Process` reads no CPU time for 129 of 348 processes (services), and
the `\Process(*)` counters, which do read them, still accounted for only
86% of the machine. The rest is processes that start and exit between
samples, such as other sessions' shell commands and our own short runs.

**`relational_x10`, settled.** 5 clean pairs of the proofs bench, 43b5e15
against HEAD (stage 1), other processes at 5 to 17%:

| bench | best | median |
|---|---|---|
| `relational_x1` | +0.8% | +0.5% |
| `relational_x5` | -2.1% | +1.4% |
| `relational_x10` | -0.4% | +7.1% |
| `universal_x1` | -9.9% | -10.4% |

`relational_x10`'s median comes from one +17% pair; its best is
unchanged, and the base alone spread 13 to 24% across its own rounds.
Stage 1 costs nothing on the small proofs, and the +21% above was
contention.

**mimalloc for the whole program.** The allocator is now set in
`src/main.rs`, `benches/execution.rs` and `benches/proofs.rs`; library
tests keep the system allocator. The execution bench, 3 clean pairs,
best of, mimalloc against system:
- the interpreter, -13 to -28% (`fib(30)` -13%, gcd -18%, factorial
  -15%, the closure benches -17 to -28%);
- `jit_cold_compile_and_verify` (Cranelift, wasmtime and the kernel
  check), -19 to -35%;
- `jit_warm_cache_hit`, within ±1%: compiled code barely allocates.

The demo binary (`cargo run --release`), 12 clean pairs, other
processes at 10 to 20%, best of: interpreted `fib(30)` 737 to 641 ms
(-13%), cold JIT 19.7 to 15.7 ms (-21%), warm JIT 4.37 to 4.38 ms. The
system allocator's own runs spread 10 to 19%. Peak memory was 17 MB with the system allocator and 19 MB with
mimalloc. Nothing measured got slower, so it's adopted.

**`fib(16)` baseline for stage 2.** Library tests now use mimalloc too
(`#[cfg(test)]` in `src/lib.rs`), so `fib16_instance_proof_cost`
measures the shipped allocator. At HEAD (stage 1), 10 clean pairs of the
same binary against itself (22 clean runs, other processes at 11 to
20%): build 128 ms best, 134 ms median; check 127 ms best, 139 ms median;
DAG 227,157 nodes every run. The slowest clean run was 24% (build) and
28% (check) above the best, so single `fib(16)` runs differing by less
than that say nothing; compare bests over many runs.

