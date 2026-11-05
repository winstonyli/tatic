## 20. `eval_dyn_direct_call` wastefully evaluated arguments before a cheap, args-independent scoping check -- found to be a crash risk, not just a performance one

`eval_dyn_direct_call` always evaluated every argument (`arg_vals`, each
its own, possibly expensive, recursive `eval_dyn` call building up a
kernel proof term) *before* deciding `needs_inline` and, inside
`eval_dyn_inline_call`, checking whether `root`'s own captures are
non-empty (out of this whole per-instance methodology's scope -- it only
ever inlines a non-capturing `root`). Whenever `return_ty.is_some()` --
a fact about `root`'s own static structure alone, entirely independent
of what the arguments evaluate to -- `needs_inline` is already
unconditionally about to be `true`, so if `root`'s captures also turn
out non-empty, every bit of work spent evaluating the arguments was for
nothing: the call was always going to decline.

Measured directly, not just reasoned about: `compile::free_vars` (the
captures check) is a pure, cheap function of `root`'s own body/arity/
`is_rec` alone, so it can just as well run *before* evaluating any
argument. Doing so isn't merely faster in the case it fires -- reverting
it and constructing a term specifically to hit this path (a capturing
closure that itself returns a further `Clo`, reached via a `let`-bound
call whose argument is a deliberately expensive, genuinely non-tail
300-deep `Prim` chain) reliably **overflowed the native stack** in an
unoptimized debug-build test thread, rather than just running slowly.
`eval_dyn`'s own non-tail `Prim` evaluation has no `DynBudget` counter
bounding it at all (unlike the self-call and inline-call paths, which
do) -- it's assumed to stay shallow in practice, an assumption this path
could silently violate by wastefully evaluating an argument that was
never going to matter.

Fixed by computing `captures` once, immediately after `root`'s arity/
body/`is_rec`/`param_types`/`return_ty`, and returning `None` right away
when `return_ty.is_some() && !captures.is_empty()` -- before the
argument-evaluation loop, not after. `captures` is then threaded through
to both `eval_dyn_inline_call` (which no longer needs to recompute
`free_vars` itself) and the opaque-call path below (which already needed
the same value as its own `captures` local) -- a genuine simplification
alongside the fix, not just a reordering. Since the whole `combinators`
context (including anything an argument's own evaluation might have
pushed into it) is discarded unconditionally whenever `eval_dyn_direct_call`
returns `None` -- `prove_closure_expr_instance`'s own `?`-propagation
never looks at partial state on failure -- skipping the wasted evaluation
changes no observable output, only whether it's paid for.
`proof::tests::a_capturing_clo_returning_root_declines_without_evaluating_its_own_argument`
covers it: reverting the hoisted check back to its original position
(checked only after every argument is evaluated) reproduces the stack
overflow on this exact term; restoring it declines cleanly instead.

