## 60. Where an instance proof's time goes after §56 to §59

A re-profile after §56 to §59, again with throwaway counters and timers
(reverted). The machine was idle this time, so the times are best of
three and fairly stable. The call and node counts are exact.

| phase | `fib(8)` | `fib(12)` | `if`-between-closures | partial-application root |
|---|---|---|---|---|
| whole proof | 51 to 53 ms | 378 to 423 ms | 8 ms | 6 ms |
| `build_universal` | 3 ms | 3 ms | 1.5 ms | 1.3 ms |
| evaluating the witness | 10 ms | 96 to 120 ms | 1.1 ms | 0.6 ms |
| kernel `infer` | 34 ms | 235 to 246 ms | 5 ms | 3.6 ms |
| dropping the witness memo | 5 to 7 ms | 52 ms | 0 | 0 |

The last two terms are the `if`-between-closures over-application and a
partial application at the root, both at `n = 4`.

Inside `fib(8)`'s `infer` (48.8k calls):
- `def_eq`: 19.6k calls, 7.6 ms. It was about half of `infer` in §55,
  and is now under a quarter.
- `subst_top`: 18.3k calls, 9 ms. `instantiate` visits about 14 nodes
  per call.
- `whnf`: 23k calls, 5 ms. `ctx_lookup`: 26k calls, 2 ms.
- The rest is `infer`'s own per-node work.

**Findings.**
- *No quadratic is left on these terms.* Every cost is a per-node
  constant times the proof's size. `fib(8)`'s proof has 53.5k nodes,
  about 800 for each of `fib`'s 67 calls. `fib(12)`'s is about 8 times
  larger, close to its 7 times as many calls, although the memo means
  only 13 distinct witnesses are built.
- *Spines are short.* The longest application spine `infer` meets has 6
  arguments, so batching `instantiate` across a spine wouldn't help.
- *The proof has almost no sharing.* Its tree has 53,524 nodes and its
  DAG 52,380, so an `infer` memo keyed by node (§50 B) would find almost
  nothing to reuse. The cause is in `build_ev_witness`, not the kernel.
  Its memo stores each sub-call's witness as an `Anchored`, and a memo
  hit returns `Anchored::at`, a `kernel::shift` copy at the current
  context depth. Each reuse is a fresh tree.
- *The same copies explain the unaccounted time.* Dropping the memo
  frees an unshifted second copy of every sub-witness. It's 11 to 14% of
  the whole proof for both `fib` terms.

**Where to go next.**
- *Keep the witness's sharing.* `Anchored::at` copies only because the
  context grows while the witness is built (`combinators.lit` adds
  literals). If every literal and combinator the witness needs were
  added before `build_ev_witness` starts, each memo entry would already
  be at the final depth, and a hit could return its `Rc` unchanged. That
  would remove the memo's copies and their drop, and give §50 B's memo
  real sharing to reuse. It's untrusted code, in `proof.rs`.
- *Per-node constants in `infer`.* These are now the bulk. There is no
  single hot spot, so any gain would come from many small ones.

