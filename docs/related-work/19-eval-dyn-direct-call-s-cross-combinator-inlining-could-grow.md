## 19. `eval_dyn_direct_call`'s cross-combinator inlining could grow the native stack without bound -- found and fixed

`proof.rs`'s per-instance proof machinery bounds two distinct kinds of
native-stack recursion through `DynBudget`: `eval_dyn_tail_recursive`'s
own flat loop (`tail_steps`, generous, since the loop itself never
recurses through Rust's call stack) and `eval_dyn`'s recognition of an
*embedded* (non-tail) self-call (`recursion_depth`, deliberately much
smaller, since each one is a genuine Rust stack frame). A third path
through the same machinery had no bound at all:
`eval_dyn_direct_call`'s own `needs_inline` branch -- reached whenever a
call's callee concretely returns a further `Clo`, or some argument's
concrete value is a `Clo` that the callee's own static classification
declined to type as one -- inlines into a *different* combinator's body
(reached only through an ordinary captured closure value, `Rec`-wrapped
or not) by recursing straight back into `eval_dyn`/`eval_dyn_tail_recursive`,
with no check against either counter. Two or more combinators calling
each other only through captured closures (never a direct self-call
`eval_dyn`'s own recognition would catch) could therefore recurse the
native Rust stack without any bound at all -- a crash/DoS risk, not a
soundness one, since a term that got this far without declining could
still only ever be trusted once `kernel::check` verifies the resulting
proof term.

Fixed by checking and decrementing a budget counter on this path too,
before recursing -- but *not* by reusing `recursion_depth` directly.
Measured directly (a term built specifically to drive this path: `step =
\g n. if 1<0 then g(999) else (if n<=0 then n else g(g, n-1))`, called as
`step(step, n0)` -- a plain, non-`Rec` Y-combinator-style self-application
that reaches `step` again only via an ordinary captured `Clo` value, never
via `eval_dyn`'s own `self_ctx`-based recognition, since inlining always
hands the callee a *fresh* `None` self_ctx; the dead `g(999)` call site
forces `g` to classify as `Inconsistent`, so every level takes the
`needs_inline` branch), reusing `recursion_depth`'s existing bound of 50
reliably overflowed the native stack in an unoptimized debug-build test
thread at roughly the 43rd-45th level -- comfortably *inside* that bound.
`eval_dyn_direct_call` itself carries substantially more live state per
frame than the embedded-self-call case `recursion_depth` was tuned for
(`param_types_for`, `combinator_return_type`, and each argument's own
`eval_dyn` call, all evaluated before dispatch is even decided), so the
same numeric bound isn't safe for both paths.

The first fix attempted was out-of-lining the continuation into its own
`#[inline(never)]` function (`eval_dyn_inline_call`), mirroring `kernel.rs`'s
own `infer_sup` precedent (§3/inline note above) exactly. Unlike that
precedent, this alone did *not* resolve the overflow: `infer_sup` worked
because the *caller*'s own locals were what was marginal; here,
`eval_dyn_direct_call`'s own prologue stays live on the stack for the
whole nested call regardless of what's extracted out of its tail, since
it's still waiting on that call to return. The actual fix is `DynBudget`
gaining a third, dedicated counter -- `inline_call_depth`, set to 25,
comfortably below the measured (40 safe / 45 overflowing) boundary --
checked and decremented in `eval_dyn_direct_call`'s `needs_inline` branch
independently of `recursion_depth`, so `eval_dyn`'s own embedded-self-call
recognition keeps its existing, already-validated bound unchanged.
Verify-teeth: removing the `inline_call_depth` check reliably reproduces
the stack overflow on
`proof::tests::a_self_application_reached_only_through_a_captured_closure_is_bounded_by_recursion_depth`'s
own `n=1_000_000` case; restoring it declines cleanly (a graceful `None`)
instead, while `n` in `{0, 1, 3, 10}` still get correct, kernel-checked
per-instance proofs agreeing with the interpreter.

Worth remembering alongside the `infer_sup` episode: an out-of-line
extraction shrinks a *caller's* stack cost, not a callee's own prologue
that stays resident across the recursive call -- when the latter is what's
marginal, the fix is a smaller, honestly-scoped budget for that
specific path, not restructuring the code around the existing one.

