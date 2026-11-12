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

Why (2026-11-11, `docs/runs/2026-11-11/scripts/rc_probe.rs`, a quick unrecorded probe): it is wasmtime's, not tatic's.
The same body on a default `Engine`, as `return_call` and as `loop`, runs 1.50 and 0.25 ns per iteration (best of 30
at n = 20 000 and 2 000 000; the bench's 25 and 4.4 us for 20 000). Cranelift does not turn a self tail call into a
jump inside the function: each `return_call` re-enters through the prologue (push and pop of `rbp` and the stack-limit
check, two dependent loads from the vmctx and a compare) before the `jmp`, where the `loop` body is the four
arithmetic instructions and a back edge. So the cost is a fixed few cycles per call, the same in any self tail
recursion, and cannot be removed by changing tatic's emitted wasm short of emitting `loop` again.

Newer wasmtime does not fix it (checked 2026-11-12). On 50.0.1, the latest stable release, and on 51.0.0-rc.1, the same
probe gives the same per-iteration costs: about 1.5 against 0.26 ns. The prologue is the same, except that the stack
limit is read from vmctx field `+0x18`. In all three versions, `translate_return_call` emits a plain Cranelift
`return_call`, with no special case when a function calls itself. No `Config` option removes the stack check, which
is emitted on entry to every function and skipped only on Pulley.
- `cranelift_opt_level`, `enable_probestack(false)` and `preserve_frame_pointers(false)` leave the function body
  byte-identical.
- `signals_based_traps(false)` moves the check but keeps it.
- `compiler_inlining(Inlining::Yes)` on 50.0.1 also leaves the body byte-identical, at the same speed (1.25 against
  0.21 ns, run `wp/2026-11-12-wasmtime-inline-probe-3` for the build). Its source never inlines a function into its
  own call graph cycle ("we never inline recursion", `compile.rs#should_inline`).

Replacing these explicit checks with guard pages is upstream issue bytecodealliance/wasmtime#8135, open since
2024-03, with an unmerged work-in-progress branch. The probe's run records are under `claude-runs\wp`.

**A spike of the printer-only fix (h4, 2026-11-12; patch `docs/runs/2026-11-12/patches/h4-printer-loop.patch`,
reverted).** The kernel, the machine, the statement, the generator and the gate are unchanged, so the proved list still
ends in `Call(own)`. Only the trusted printer changes: it prints a self call in tail position as `local.set` of each
parameter in reverse order and then `br $top`, and `print_func` wraps the body in `loop $top (result i64)` when it holds
such a call.

The workspace suite (`h4-spike-suite`) fails 5 tests, all of them checks on the printed text:
- the two golden tests, `every_benchmark_term_lowers_to_its_golden_wat` and
  `specialised_benchmark_terms_lower_to_their_golden_wat`;
- `print::call_prints_by_the_tail_rule`;
- `tail_rule_prints_both_forms_in_one_body`;
- `a_tail_loop_of_a_million_iterations_installs_and_runs`, which asserts `return_call $f` in the text after its run of a
  million iterations has returned the right sum.

Every behavioural test passes: the differential compile fuzz, the tail-rule differential, the gate tests and the JIT
tests.

The `jit_warm_cache_hit` bench, with two interleaved rounds per arm, ran on a busy machine (55-75% CPU) and is not
timed. `capturing_closure_loop` takes 34.6 and 33.7 us on main against 9.5 and 7.9 us with the spike, about 4x. gcd
moves within noise (201 and 225 ns on main against 230 and 240 ns), since its few iterations are swamped by the call
overhead.

The fix works and is small: 15 lines in `print.rs`. Its cost is trust: the printed text of a self tail call is no
longer the near-identity form of the proved `Call`.

**A spike of the proved loop form (Set and Br, 2026-11-12; patch `docs/runs/2026-11-12/patches/setbr-spike.patch`,
reverted).** It tests whether the loop that h4 prints can instead be proved by the gate. The machine gains a leaf class
`Set` (pops one word, writes parameter slot i, passes the new frame on; printed `local.set $p{i}`) and a terminal `Br`
(meaning `restart fr mu`, where `G::bm` fills a new `MeaningEnv.restart` with `\fr mu. env fr mu k`: the entry's own
previous-fuel step with the activation's own continuation; printed `br $top`). `print_func` wraps the body in
`loop $top (result i64)` when it holds a `Br`. `shape` returns `None` for a path that ends in `Br`, which must be last in
its sequence, and `shape_check`'s slot bound now covers `local.set` too.
- `sim.rs`, `gate.rs` and the kernel are unchanged. After a `Br` the machine term is `j hm tm bm fr mu km`, the same
  head the call rule matches, so the walk proves it with no new rule.
- With the tail `Call(own)` replaced by `[Set(k-1) .. Set(0), Br]`, five lists are `Accepted`: the specialised
  `capturing_closure_loop`, `partial_application_loop`, both sum loops, and a two-function module whose loop argument
  comes from a callee. The printed text is byte-identical to h4's for all five. It validates and runs under wasmtime:
  100 000 iterations return 5000050000 with a constant stack.
- All 54 hand-written mutants are rejected, each at its expected layer. Walk: Sets in forward order, a dropped Set,
  both Sets to one slot, Br for a non-tail call in factorial and fib, Br with a callee call skipped or put in the wrong
  arm, the loop unrolled by two, a dead `if` guarding a Br. Shape: a Set to a slot at or above the arity (including
  the padding slot of a width-2 frame), a Br not last, a body made only of Br. Pairing: a callee call dropped.
- A sound but incomplete case: `+ 0` after the `if` is rejected, since `add acc 0` and `acc` are not definitionally
  equal.
- Suite on the spike: 810 passed, 0 failed (`setbr-suite2`).
- Untimed gate cost on `capturing_closure_loop` (median of 20 interleaved runs, debug profile): Set/Br 0.70 ms build,
  3.70 ms check, against 1.14 and 2.92 ms for the `Call` list.
- An adversarial review (`setbr-review1`) found no accepted list whose wasm validates but computes something else. It
  did find that the gate accepts some lists whose printed wasm fails to validate. Example: an `If` arm that leaves the
  outer stack untouched, as in `[get1, get0, const0, le, If([], [..])]`, prints an empty `then` arm that wasm rejects
  ("expected i64 but nothing on stack"). The class predates the spike: `If([], [])` with neither `Set` nor `Br` is accepted too (the review's
`review_preexisting_outer_stack_arms`, run on the spike tree, whose rule for two arms that do not end in `Br` is main's). The failure
  is safe, since `Module::new` refuses the module and the JIT falls back, but `Accepted` does not imply the wasm
  validates. `Br` adds a new way into it (an arm that ends in `Br`). Fixed on main the same day (q2): `shape` now runs each arm from an
  empty stack and requires one word (`machine.rs#if_arms_start_empty_and_leave_one_word`); suite 807 passed, 0 failed
  (`q2-arm-check-suite`).
- Not tested: a direct `prove` that skips `shape_check`, and a `Br` inside a callee whose source is itself a loop (no
  sample module has one).
- Gaps a build would close: the mutation generator (`testing/ins_mutate.rs`) has no `Set` or `Br` case; `Class::Set`'s
  `kind()` returns `W` though it pushes nothing.

So the loop form needs no change to the proof generator. The trusted code grows by two constructors (about 130 lines in
`machine.rs`, `statement.rs`, `ops.rs`, `wasm.rs` and `print.rs`, by the patch), and the printed loop is proved rather
than assumed.

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

**Timed reruns (2026-11-11).** Run `v08-timed-reruns` (`run.ps1 -Timed`, total CPU 5%, each measurement on the exe its
untimed run used; script `docs/runs/2026-11-11/scripts/v08-timed-reruns.sh`). Everything ran about 2.4x faster than
untimed and every verdict holds. Go/no-go, `doubling(12)` build and check, medians of 5 interleaved rounds: relational
182.6 ms, refl 237.9 ms (0.77x), with `Call` 180.6 ms, against the 0.57 s cap. Weight fit, medians for k = 1 .. 64:
5.8, 6.1, 8.8, 18.6, 41.8, 134.0, 570.1 ms, `doubling(12)` 185.4 ms: the crossing is at k about 36, tree about 221, a
weight of about 223, within 3% of the untimed 228, which stays (the larger weight is the safer side). Targets, best of
3: Goal 1 at most 14.5 ms (`redundant_arithmetic_recursion`, build plus check), Goal 2 at most 16.2 ms (`let_bound_factorial_10`), held-out at
most 14.9 ms, `doubling(12)` 176.1 ms.

**The verdict column.** `proof/tests/baseline.rs#VERDICTS` holds the gate's verdict kind for every census and held-out
row, measured on the form `try_install` proves. Goal 1's five targets and both held-out terms are `Accepted`; no row is
`Rejected`; the rest (closures, `Div`/`Mod`, curried dispatch, modules with callees, the oversized term) are
`NotCovered` and keep going to `kernel_verify`. `verdicts_match` also fails if a fragment holding a `Raw` line or a
pointer-reached environment is anything but `NotCovered` (Goal 5).

**Guard: none added.** The items deleted by S0 to S2c (`loop`, `strip_loop`, `gate_with`, `in_fragment`, `upd`, the memory
rows) are code symbols, so the compiler fails on any use; the docs grep (`in_fragment`, `loop $L`, `countdown`, `Store`,
`Load`, `LocalGet`, `EnvAccess::None` over the roadmap, parked list, tour, proven and decision docs) covers the prose.
