## 63. `infer` memoises shared nodes by (node, context id)

This builds §50's option B. §50 held it back because the corpus had no
sharing. §62 created some: `fib(12)`'s instance proof now has 48k DAG
nodes, but `infer` still walked it as a tree.

**How other checkers do it.** Lean 4's kernel caches inferred types by
expression. Its bound variables become named free variables when it
goes under a binder, so the context isn't part of the key. With
de Bruijn indices here, the same node under two different binders can
have two types, so the key needs the context too.

**Design** (as §50 set out):
- *Key:* `(PtrKey, context id)`. `PtrKey` holds the `Rc`, so an address
  isn't reused within the call.
- *Context ids:* 0 is the caller's context. Entering a binder whose type
  is the `Rc` `a` from context `cid` gives the id interned for
  `(cid, a)`, and the context pushed is `a`'s content. So equal ids mean
  equal binder sequences. `infer_pair` pushes an inferred type, not an
  `Rc` of the term, and takes a fresh id, which is always sound.
- *Scope:* one `InferCache` per public `infer` or `check` call, passed
  explicitly. The private `infer_rc`, `infer_node`, `check_rc` and the
  four out-of-line arms take `(ic, ctx, cid, e: &Rc<Expr>)`. The public
  functions wrap their `&Expr` in a new `Rc`, a shallow copy.
- *What's stored:* only successes, and only for nodes with
  `strong_count > 1`. A node referenced once is reached twice only
  through a shared ancestor, which is memoised instead. So unshared
  terms pay no hashing.
- *Not memoised:* `check`'s `Lam` rule, which checks a body against the
  expected codomain rather than inferring it. `def_eq` still runs at
  every occurrence, but its equal-sides fast path (§56) makes a repeat
  cheap.

**Why it's exact.** `infer` is a pure function of the node's content and
the context's content. Both are immutable behind the keys, which keep
them alive.

**Tests.**
- `infer_is_linear_in_the_dag_of_a_shared_term`: `d(k+1) = f d(k) d(k)`
  at depth 20, a million leaves as a tree, under 500 ms in a debug
  build. It took 4.8 s before, and 4.1 s with the memo disabled.
- `infer_memo_keeps_same_length_contexts_apart`: one `Pi` shared under
  binders `Type0` and `Type0 -> Type0`. The first is well typed and the
  second isn't. Keying on context length accepts the pair; the test
  catches that mutation.
- `infer_memo_changes_no_answer`: 20,000 random terms, 1,508 of them
  well typed, built from a pool of shared nodes. Each gets the same
  result, `Ok` or `Err` with the same message, as a copy with no sharing
  (`shift` by 1 and back), which the memo never engages on. It also
  fails under the length-keyed mutation.

**Measured.** An interleaved in-process toggle (reverted), best of 16
rounds, on an idle machine (CPU 3 to 6%):

| instance proof | memo off | memo on | change |
|---|---|---|---|
| `fib(8)` | 41.6 ms | 19.8 ms | -52% |
| `fib(12)` | 282 ms | 76 ms | -73% |
| `fib(16)` | 2.66 s | 0.55 s | -79% |
| `if`-between-closures, `n = 4` | 9.8 ms | 9.8 ms | 0% |
| partial-application root, `n = 4` | 8.0 ms | 7.6 ms | -5% |
| non-tail branching | 17 us | 18 us | +4% |

The unshared proofs don't move, as the `strong_count` filter intends.
With §62, `fib(12)`'s instance proof went from 384 ms to 76 ms.

**What's left.** `fib(16)` is still well over 7 times `fib(12)`. `v` is
still copied as a tree wherever it's shifted under a binder, both in
`params_and_close` (§62) and in the kernel's `instantiate`, since
`shift` has no memo. A `shift` that preserves sharing, memoised by
pointer within one call, is the next step.

