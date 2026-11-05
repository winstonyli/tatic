## 10. Making `kernel::with_shift_cache` automatic — and why locally-nameless wasn't the fix

*Superseded: the reshifts this cache recovered came from eager
substitution. §53 fixed that, and §54 removed the cache.*

`with_shift_cache` (`src/kernel.rs`) was opt-in because wrapping every
`instance_from_scaffold` call regressed the common case: `fib(30)`'s
cold-compile time going from ~120ms to ~220ms, a real `HashMap` grown
across a construction and dropped, on top of routine small samples that
never needed it. Made automatic now, via `proof::instance_visit_count` —
a cheap, exact, `Expr`-free dry run of `build_ev_witness`'s own memoized
recursion (plain `i64` arithmetic, no term construction at all) that
counts how many distinct nodes *this concrete instance* actually visits,
engaging the cache only once that crosses a small threshold (`6`,
calibrated so `fib(8)`'s own proven ~2x win clears it while `jit.rs`'s
own routine samples, `0, 1, 2, 3, -1, -3, ...`, don't).

Considered first, and rejected: gating on the function's own *shape*
alone (does any leaf have more than one self-call), reusing data
`build_universal` already computes with no new analysis pass at all.
This looked like the ideal answer — free, structural, no prediction
needed — but measurably regressed the exact case it was meant to fix:
`sample_arg_vectors`'s own small samples still only visit a handful of
`build_ev_witness` nodes even for a branching-shaped function, so shape
alone re-triggered the original regression (confirmed: `fib(30)`'s
cold-compile time went to ~350ms), just now scoped to branching
functions instead of every function. The dry run fixes this by measuring
the actual concrete cost instead of only the syntactic possibility of
one.

**Also investigated, and deliberately not pursued: a locally-nameless
representation**, so postulate references never need reshifting at all.
Turns out to require two pieces working together, not one: (1) a
distinct `Free`-style constructor for postulate references, immune to
`shift`/`subst` — but `Var` is already a leaf, O(1) to shift regardless,
so this alone buys nothing, since the actual cost is recursively
*descending into* composite subtrees, not adjusting individual leaves;
and (2) a per-node cached "loose bound-variable range" letting `shift`
skip recursing into a subtree once `cutoff` already exceeds everything
adjustable inside it (the technique some kernels, e.g. Lean 4's, use this
exact metadata for) — but `proof.rs`'s own `Anchored::at`, the dominant
caller per the profiling above, always shifts at `cutoff = 0`, where
*every* ordinary `Var` needs touching, so this piece alone helps only
subtrees nested deep enough locally to matter, not top-level postulate
references. Only combined — postulate references as `Free`, plus the
range check able to see that a subtree built purely from `Free`s and
closed structure needs nothing touched *regardless* of cutoff — would
this plausibly hit the actual redundancy pattern. The blast radius is
smaller than it first looks (confined to `kernel.rs`'s `Expr`
representation and its constructors; `proof.rs`'s ~180 `Anchored`
call sites are untouched, since `shift` just gets cheaper underneath
them), but it's still a real change to `Expr` itself, and — the
disqualifying difference from the cache-based fix — a *correctness*-risk
one: a hand-derived range formula that's off by one binder would make
`shift` *silently* skip adjusting a variable that needed it, in the one
piece of machinery every proof in this kernel depends on, with no
sample-verification-style backstop the way the JIT has. Rejected in
favor of the dry-run heuristic above, which can only ever be *slow* when
wrong, never *wrong*.

