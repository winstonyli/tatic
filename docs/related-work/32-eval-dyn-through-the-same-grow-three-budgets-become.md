## 32. `eval_dyn` through the same `grow`; three budgets become one

§31's second open item. `eval_dyn`'s per-instance proof search recurses
through the native stack in two ways: an embedded (non-tail) self-call
re-enters `eval_dyn_tail_recursive`, and a closure call can be inlined
into another combinator's body (`eval_dyn_direct_call` →
`eval_dyn_inline_call`). Each path had its own depth counter,
`recursion_depth` (50) and `inline_call_depth` (25), tuned against a
debug test thread's stack. The second was measured to overflow at the
43rd-45th level, so it got a smaller bound than the first.

**The change.** Every cycle in that mutual recursion passes back through
`eval_dyn`, so one `kernel::grow` there bounds the whole family's depth
by heap (`grow` is now `pub(crate)`). What was left of the two counters
was a *termination* bound, not a stack one, and it turned out not to
need separate counters. A self-application reached only through a
captured closure (a plain `\g n. .. g(g, n-1)`, not `Rec`-wrapped)
consumes no step of the tail loop, so without `inline_call_depth` it
would never stop. So `DynBudget` is now one `steps` counter (200, the
old `tail_steps`), charged once per descent into a body:
- each iteration of the tail loop, which an embedded self-call also
  enters, so `recursion_depth` was redundant;
- plus `eval_dyn_inline_call` inlining a non-`Rec` body, the one
  descent the loop never sees.

**Behaviour change.** Per-instance proofs can now follow up to ~200
levels of embedded or inlined recursion instead of 50 / 25. Both
existing depth tests now also require n=100 to prove, past both old
bounds and the measured debug crash at ~45. That extension was written
first and failed, declined by the old bounds. Verify-teeth: with the
`grow` removed, the tests overflow the stack. The `n = 1,000,000` halves
of both tests still decline cleanly, now on `steps`.

**The frame-size extractions are kept.** The `#[inline(never)]` helpers
in `kernel.rs` (`infer_sigma`/`infer_pair`/`infer_sigrec`/`infer_sup`,
the `*_sigma_family` arms, `whnf_sigrec`) and `eval_dyn_inline_call`
existed to fit that debug-thread budget. Nothing depends on them now --
frame size only decides how soon a deep walk moves to a new segment --
but they cost nothing, and removing them is a codegen change I could not
measure reliably on a machine running at 100% CPU from unrelated work.
Their docs no longer claim a stack budget that no longer exists
(`infer_sigma` carries the one full explanation).

