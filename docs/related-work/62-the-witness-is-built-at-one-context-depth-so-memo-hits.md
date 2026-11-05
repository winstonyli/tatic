## 62. The witness is built at one context depth, so memo hits share

§60 found that an instance proof has almost no sharing. `fib(8)`'s
proof had 53,524 nodes as a tree and 52,380 as a DAG, although
`build_ev_witness` memoises each call's witness. Postulates are
de Bruijn variables of the context, so a term built at one depth has to
be shifted wherever the context has grown since. The witness pushes its
postulates lazily: each concrete arithmetic fact is postulated the first
time `eval_and_prove` needs it. By the time a memo entry is reused, the
context has grown, so `Anchored::at` returned a shifted copy, and every
reuse was a fresh tree.

**How other checkers avoid it.** Lean and Coq refer to global constants
by name, so adding to the environment never shifts an existing term.
Here the postulates live in the local context, so any push does.

**Options.**
- *A. Postulates by name or by de Bruijn level.*
  - Pros: no push ever shifts anything, anywhere.
  - Cons: a new `Expr` variant, with rules in `infer`, `shift`,
    `instantiate` and `ctx_lookup`. A large change to the trusted kernel.
- *B. Build the witness twice*, keeping the second. The first build
  pushes every postulate, and the pushes are memoised (`fact_pos` and
  its siblings), so the second grows nothing.
  - Pros: a few lines, and exact.
  - Cons: the first build is the old, copying one, so the witness costs
    more than it does today.
- *C. A prepass over the call trace.* Walk the calls
  `build_ev_witness` will make, and run `eval_and_prove` on each
  condition and self-call argument, discarding the results.
  - Pros: it pushes through the same function that the build uses, so
    nothing about which facts are needed is duplicated. It costs one
    `eval_and_prove` per condition and argument of each distinct call,
    not a witness. A push it misses only costs sharing: `Anchored` still
    shifts correctly, and the kernel checks the result either way.
  - Cons: a second walk of the trace, which has to stay in step with
    `build_ev_witness`'s.

**Built: C.** `push_ev_facts` runs before `build_ev_witness` in
`instance_from_scaffold`. It is bounded by `WITNESS_NODE_BUDGET` like
the build. The leaf lookup and canonical params it shares with the
build are now `trace_leaf` and `canonical_params`. It's untrusted code:
the kernel checks the proof exactly as before.

**Result.** During the build, the context no longer grows, and memo hits
return the stored term unshifted, so they share. Two kinds of shift are
left: the scaffold's small `combines` terms, and `v` under
`params_and_close`'s binder (next paragraph).

| | before | after |
|---|---|---|
| `fib(8)` proof, DAG nodes | 52,380 | 13,942 |
| `fib(12)` proof, DAG nodes | 424,656 | 48,154 |
| `fib(8)` instance proof | 49.8 ms | 30.8 ms |
| `fib(12)` instance proof | 384 ms | 192 ms |
| `if`-between-closures instance proof, `n = 4` | 7.9 ms | 7.1 ms |

The times are best of 16 interleaved rounds of an in-process toggle
(reverted), on an idle machine. A criterion A/B was attempted too, but
another session's job started during it, and benches this change doesn't
touch moved by up to +749%. `kernel::infer` still walks the proof as
a tree, so what's saved is the shifting while the witness is built and
freeing those copies afterwards.

**What still copies.** Recasting each child's witness to the caller's
arguments builds `λ params. Ev(params, v)` with `params_and_close`, so
`v` is shifted under the binders. `v` is a shared DAG whose tree is
exponential (`v(n)` combines `v(n-1)` and `v(n-2)`), and `kernel::shift`
has no memo, so it returns a tree. That's why `fib(12)`'s DAG is still
3.4 times `fib(8)`'s rather than about 1.4 times. The kernel's
`instantiate` does the same when it substitutes a shared argument. A
shift that preserves sharing is the prerequisite for §50 B's `infer`
memo to make these proofs linear, and it belongs with that design.

**Test.** `a_fibonacci_instance_proof_shares_its_repeated_witnesses`
counts the proof's DAG nodes. It requires `fib(12)`'s to be under 4
times `fib(8)`'s. Without the prepass the ratio is 8.1, and the test
fails.

