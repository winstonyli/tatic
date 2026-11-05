## 30. `cargo bench --bench execution` died of a stack overflow -- found and fixed

Found while checking (belatedly) whether §29's installation gate changed
any benchmark. It didn't. But the benchmark suite did not complete:

```
Benchmarking inconsistent_arity_loop_carried_parameter_loop/jit_cold_compile_and_verify
thread 'main' has overflowed its stack
error: bench failed  (exit code 0xc00000fd, STATUS_STACK_OVERFLOW)
```

**Pre-existing, not caused by the gate.** Confirmed by checking out
`src/jit.rs` from the commit before §29's change and re-running: it
overflows identically.

**Why nothing caught it.** Benchmarks were not in the standing validation
routine. `--all-targets` *builds* them, which is presumably why this
looked covered. Building a target proves nothing about running it. The
routine is now written down in `docs/proven.md`, "Validation",
with `cargo bench` in it.

### Isolation

A throwaway harness ran each stage of a cold compile separately on the
same term, at varying loop counts and thread stack sizes:

- `eval::apply_term` -- fine at 20,000 iterations. Not the interpreter.
- `compile::try_compile` -- fine. Not the compiler.
- `proof::prove_closure_expr_instance` -- overflows.
- The same call on a 1 GB thread **returns `None`**, correctly, at
  n=20,000 (its budget is exhausted). So the logic was right all along;
  it simply needed more stack than it had to reach the decline.
- Instrumenting the expression handed to `kernel::check`: depth 101 at
  n=50, 201 at n=100, 401 at n=200. Depth grows at ~2 levels per trace
  step, exactly as the per-*execution* proof design implies.
- `prove_tail_recursive_call` -- the purely arithmetic sibling, no
  closures anywhere -- overflows too, at an even lower loop count. So
  this was never closure-specific; it is a property of both per-execution
  strategies.

### Two distinct overflow sites

1. **`kernel::check`.** `infer`, `whnf`, `def_eq` and `nf` are mutually
   recursive over `Expr` structure. Release build: depth ~400 survives,
   ~500 takes the process down. Debug is far worse -- a `refl` tower
   overflows a debug main thread somewhere between depth 50 and 100.
2. **Recursive `Drop`.** When the step budget runs out, the accumulated
   `Rc<Expr>` chain is discarded unproved, and dropping it recurses one
   frame per level. Measured: depth ~8,000 survives, ~12,000 does not.
   This is the one that actually killed the benchmark -- with
   `tail_steps: 10_000` a 20,000-iteration loop built a ~20,000-level
   expression, never reached `check` at all, and died on the way out.
   (`Clone` is unaffected: `#[derive(Clone)]` over `Rc` fields is
   shallow.)

### Fix

Both step budgets drop from 10,000 to **200** --
`prove_tail_recursive_call`'s `MAX_STEPS` and `DynBudget::tail_steps` --
sized to sit between the two ceilings rather than at whatever number
looked generous. Above them, nothing past ~100 steps could ever produce
an acceptable proof anyway; below them, 200 steps cannot build anything
within two orders of magnitude of the drop cliff.

Second, `kernel::depth_within` (iterative, explicit stack, early-exit)
plus `kernel::MAX_CHECK_DEPTH = 128`, checked once in `proof::finish` --
the single point where every strategy that can build an unbounded
expression hands it to the kernel. Over-deep means `None`, the same
graceful failure an exhausted budget already produces.

**Why the guard is not inside `kernel::check`, where it belongs.** That
was tried first, and measured: a 50-160% slowdown across every single
proof benchmark. The lib test suite makes **184,785** `check` calls, and
`depth_within` must visit every node to answer "no". `check` is too hot
to afford it. `typecheck` -- cold, and the other public entry that
accepts or rejects a term -- is guarded.

**The constant, measured rather than guessed.** Instrumenting all 184,785
`check` calls, the deepest expression any real proof passes is **64**
levels (57 on the `expected` side). 128 is double the observed maximum
and far below the release cliff.

**Known gap, recorded rather than papered over.** `kernel::check` stays
unguarded, and a debug build overflows at depths inside
`MAX_CHECK_DEPTH`. Lowering the constant to fit debug would start
rejecting proofs the project actually builds; the real fix is making the
kernel's traversals iterative, which is its own project. What stops the
crash today is the step budgets -- the guard is a backstop for anything
that gets past them.

*Since closed by §31*, with `stacker` rather than a hand conversion, and
the guard removed.

### A benchmark consequence worth stating

`inconsistent_arity_loop_carried_parameter_loop` runs 20,000 iterations,
so its trace now exhausts the 200-step budget, `prove_closure_expr_
instance` declines, and §29's gate therefore refuses to install it. Its
`jit_warm_cache_hit` bar now measures the interpreter (~18 ms against the
interpreter's ~23 ms), not curried dispatch. That bar was the whole point
of the group -- its own docs say so -- so the benchmark needs either a
loop short enough to stay provable or an explicit note that it is
measuring the declined path. Not done here.

This also corrects §29 a second time. The gate *did* change this
benchmark: before, the term compiled and was served fast; now it is
interpreted. That was invisible earlier only because the benchmark
crashed before reaching the point where you could see it.

**Since resolved.** Two changes to `benches/execution.rs`:

- *The pair now runs at 150 iterations, side by side in one group.* The
  inconsistent term's only proof is `prove_closure_expr_instance`'s
  trace, one step per iteration against the 200-step budget. Measured
  ceiling: 199 iterations install, 200 are declined -- the budget binds,
  not `MAX_CHECK_DEPTH`. Shortening only the inconsistent term would
  have broken the comparison, and the companion group's 20,000 feeds its
  own README comparison with `capturing_closure_loop`. So both builders
  now take an iteration count, and the inconsistent group benches a
  `consistent_baseline_jit_warm_cache_hit` bar at the same 150. I
  initially wrote that no provable length would work, because fixed
  per-call overhead would dominate. Measurement says otherwise. A
  1-iteration loop costs ~220 ns warm, so at 150 the loop is most of the
  call. Result: **~1.01 µs curried vs ~0.73 µs baseline (~1.37×)**.
  Subtract the fixed overhead and the loop itself is ~1.55× slower,
  consistent with the ~1.56× §9 recorded at 20,000 before the gate.
  Criterion's spread on the baseline was wide this run (523-898 ns), so
  the ratio is approximate.
- *Every warm bar now asserts the path it measures.* A shared `warm`
  helper replaces each group's warm-up call and fails the run unless
  `stats.compiled` matches the group's stated expectation (all seven
  expect compiled). The class of bug here was a bar that silently
  changed meaning; now a change to the gate or a budget that uninstalls
  any benchmarked term stops `cargo bench` instead. Verify-teeth:
  expecting compiled at 20,000 iterations, and running the pair at
  200, both panic in `warm` naming the declined stats.

### Tests and verification

- `proof::tests::a_long_running_trace_declines_instead_of_overflowing_the_stack`
  -- a 20,000-step arithmetic loop must return `None`, and a 10-step one
  must still prove. Verify-teeth: restoring `MAX_STEPS` to 10,000 makes
  it overflow the test process exactly as described.
- `kernel::tests::an_over_deep_expression_is_measurable_and_refused_by_typecheck`
  -- `depth_within` measures, `typecheck` refuses, and a shallow term of
  the same shape still typechecks. It deliberately never calls `check` on
  the deep term, since `check` is unguarded and doing so *is* the crash.
  Verify-teeth: raising `MAX_CHECK_DEPTH` to 10,000,000 makes the test
  overflow.

Full validation green afterwards: build, 193/193 lib tests, all four
fuzzers at release, `cargo bench` (both suites, to completion), and the
release demo. The proof benchmarks are back within noise of their
pre-guard numbers.

