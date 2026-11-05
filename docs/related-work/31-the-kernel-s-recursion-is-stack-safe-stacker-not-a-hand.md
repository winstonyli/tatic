## 31. The kernel's recursion is stack-safe -- `stacker`, not a hand conversion

§30 left one gap open: `kernel::check` had no guard, and its traversals
recurse over `Expr` (and `whnf`/`nf` once per reduction step too), so a
deep enough term took the process down instead of returning a verdict.

**Measured first, and narrower than §30 said.** Survivable depth of two
shapes (a `refl` tower, and `(\x:Type0. x)` applied n-fold), bisected per
build and thread size:

| build | 1 MB (Windows main thread) | 2 MB (test threads) |
|---|---|---|
| debug | ~90-100 | ~185-205 |
| release | ~450-570 | ~900-1,120 |

So "a debug build overflows inside `MAX_CHECK_DEPTH` (128)" was only true
on a 1 MB thread -- `cargo run` and the REPL in debug, not the test
suite.

**The choice.** Hand-converting every traversal into an explicit worklist
would turn `infer`/`check` into a defunctionalized continuation machine
of about 20 states: hundreds of new lines inside the trusted kernel, no
longer reading like the typing rules they implement, where a de Bruijn
off-by-one is a soundness bug rather than a crash. `stacker` instead
spills onto a heap-allocated stack segment when the current one runs
low. It is what rustc does (`ensure_sufficient_stack`, whose constants
this copies: 100 KB red zone, 1 MB segments). The cost is `unsafe`
platform assembly in `psm` added to what must be trusted not to crash --
though not to what must be trusted for soundness. Chosen: `stacker`.

**What had to be covered.** Every recursive function body in
`kernel.rs` (`infer`, `check`, `whnf_impl`, `nf_impl`, `shift`, `subst`,
`is_var_free`) runs through `kernel::grow`, and so do `PartialEq` (now
written out rather than derived, since `def_eq` compares two full normal
forms with it) and `Debug` (error messages print whole terms). The
surprise was `Drop`. With every traversal wrapped, a 1,000-deep check
still crashed, because the compiler-generated drop glue is recursive and
`whnf` discards a full intermediate term at every beta step -- on
whatever segment is current, with only the red zone guaranteed. `Drop
for Expr` now checks the stack at each level, and only when it runs low
moves the children it would free onto a fresh segment. Implementing
`Drop` forbids moving fields out of an `Expr` by value (E0509), which
touched ~20 match sites; they now bind by reference and clone the `Rc`.

**The cost, and a fix to it.** The first version used
`stacker::maybe_grow` directly and made every proof benchmark 80-100%
slower. One `stacker::remaining_stack` call measured **8.9 ns** on
Windows -- a lazily-initialized thread-local plus a non-inlined assembly
call -- against ~1 ns for reading a local's address, and the kernel
checks at every `shift`/`==`/`Drop` node. So `grow` now compares a
local's address against a const thread-local floor (`FLOOR`) and calls
stacker only when genuinely low, or to learn the floor once per thread.
The floor tracks whichever segment is current, restored by a guard on
the way out, so unwinding restores it too. The first draft of that got
the "unknown" sentinel wrong (`0`, which every check *passes*, so
nothing was ever protected); it is `usize::MAX`, which every check
fails.

This machine was at 100% CPU from unrelated work throughout, so
one-shot criterion comparisons swung ±25% run to run, and the same
binary ranged 12.9-44 ms on `gcd_2_leaves` across rounds. The numbers
that count are from an interleaved A/B -- the pre-change commit built in
a separate worktree, both binaries alternated, minimum and median over
ten rounds: **+4-7%** on the two slowest-affected benches
(`gcd_2_leaves`, `relational_x10`), and within about ±5% on the other
four sampled. Against the 50-160% the depth guard cost inside `check`
(§30), that is the price of safety at every depth.

**What it removed.** `MAX_CHECK_DEPTH`, `depth_within`, and their guards
in `typecheck` and `proof::finish`: their only stated purpose was
surviving the native stack. `DynBudget::tail_steps` and `MAX_STEPS` stay
at 200, but both ceilings they were sized against are gone -- they are
now cost bounds that nobody has re-measured.

**Corrections to §30's record, found while doing this.** `DynBudget`'s
docs gave `MAX_CHECK_DEPTH` as 200 (it was 128), and said a trace past
roughly a hundred steps "cannot produce a provable result". The
inconsistent-arity benchmark measured otherwise just before this: 199
steps install.

### Tests and verification

- `kernel::tests::check_survives_a_term_far_deeper_than_the_native_stack_allows`
  replaces the old guard test. It runs `check` on 1,000-deep terms of
  both shapes on a 1 MB thread in a debug build, through beta reduction,
  a two-tree `==` and a `Debug`-formatted error. Written first, and it
  overflowed. Verify-teeth: making `Drop`'s check always pass crashes it
  with an access violation (an overflow on a stacker segment), and making
  every check pass overflows the native stack.
- Outside the suite: depth 20,000 checks and drops cleanly on a 1 MB
  thread in release, and 5,000 in debug.

Full validation green: build, 193/193 lib tests, clippy (only the four
upstream `entity_impl!` warnings), all four fuzzers at release, and the
release demo (`compiled: 9, declined_no_universal_proof: 0`).

### Open

- **Re-measure the step budgets as cost bounds.** Raising `tail_steps`
  could bring `inconsistent_arity_loop_carried_parameter_loop` back to
  20,000 iterations. Its per-step cost grows with the expression, so
  measure before choosing.
- **`eval_dyn` is still native-recursive.** `DynBudget::recursion_depth`
  (50) and `inline_call_depth` (25) were tuned against a debug thread's
  stack, and the `#[inline(never)]` extractions throughout `kernel.rs`
  exist to shrink frames for that budget. Routing `eval_dyn` through the
  same `grow` would make both limits purely cost bounds, and the
  extractions removable.
  *Since done:* §32.

