## 55. Where an instance proof's time goes after §53 and §54

A re-profile of the same two terms as §52, with throwaway counters and
timers in `kernel.rs` and `proof.rs` (reverted). These are the `fib(8)`
branching instance and the `if`-between-closures over-application at
`n = 4`. Another session's job held most cores, so treat the times as
rough. The call and node counts are exact.

| phase | `fib(8)` | `if`-between-closures |
|---|---|---|
| whole proof | 166 to 260 ms | 43 to 48 ms |
| `build_universal` | 13 to 21 ms | 4 to 5 ms |
| evaluating the witness | 32 to 40 ms | 4 to 18 ms |
| kernel `infer` | 110 to 193 ms | 16 to 36 ms |

Inside `fib(8)`'s `infer` (47.6k `infer` calls, context depth 48):
- **`def_eq`: 18,864 calls, 59 to 118 ms, about half of `infer`.** Each
  call builds a fresh `ReductionCache` and normalises both sides in full.
  - 17,951 of the calls (95%) get two syntactically equal sides. They
    still cost 11 to 12 ms of normalisation. The `==` pre-check that
    would skip it costs 2 to 3 ms over all calls.
  - The other 913 calls, where a real conversion is needed, take the
    rest: about 45 ms, or 50 us each.
  - Comparing the normal forms costs only about 1 ms in total.
- `subst_top`: 26k calls, 31 to 40 ms. `is_var_free` visits 235k nodes
  and `instantiate` 231k, so the guard's pre-pass doubles the walk of
  each body.
- `ctx_lookup`: 25k lookups shifting 48k nodes. `whnf` itself is
  negligible.

The `if`-between-closures term has the same shape at a smaller scale:
3,164 `def_eq` calls (3,013 equal, 151 not) take 7 to 8 ms of its
16 to 22 ms `infer`, and `subst_top` takes 3.5 ms.

**Where to go next** (each is a trusted-kernel change):
- *Equal sides first.* `def_eq` returns `true` when `a == b` before
  normalising. It's exact, since `nf` is a function, and saves the
  equal calls' normalisation: about 10 ms, or 15% of `def_eq`, here.
  A pointer check first would make most of the `==` free too.
- *The 913 real conversions.* These dominate, and each normalises both
  sides in full. Options are one `ReductionCache` shared across a
  top-level `infer`'s `def_eq`s (§50 B notes it's sound, since reduction
  doesn't read the context), or a lazy check that compares weak head
  normal forms and recurses only into arguments that differ. Neither has
  been measured.
- *Fuse `is_var_free` into `instantiate`.* One walk instead of two, by
  returning whether the variable was seen, and reusing the original
  node when it wasn't. At most about a third of `subst_top`'s time.

