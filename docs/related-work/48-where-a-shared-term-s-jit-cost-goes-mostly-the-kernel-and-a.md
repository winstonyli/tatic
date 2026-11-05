## 48. Where a shared term's JIT cost goes: mostly the kernel, and a lost pointer cache

§47 put a tree-size gate on `try_compile` rather than sharing in the IR,
on the grounds that compilation was a small part of the cost. This
section times each stage separately, to see what sharing everywhere
would take. The term is again `\x. t_d` with `t_{i+1} = t_i + t_i`
(release build, one run each):

| `d` | WAT | compile | typing | wasmtime | `eval` battery | prove |
|---|---|---|---|---|---|---|
| 7 | 4 KB | 0.3 ms | 0.02 ms | 2.7 ms | 0.1 ms | 1.2 ms |
| 9 | 17 KB | 0.5 ms | 0.01 ms | 0.7 ms | 0.2 ms | 4.5 ms |
| 11 | 68 KB | 2.0 ms | 0.01 ms | 2.1 ms | 0.9 ms | 24.5 ms |
| 13 | 272 KB | 6.4 ms | 0.02 ms | 5.6 ms | 3.5 ms | 217 ms |

At `d = 13` the proof (`prove_pure_expr`) is 93% of the total, and it
grows faster than the tree: 8.8 times per two levels, where the tree
grows 4 times. Sharing in the IR would remove about 5% of the cost.

**Inside the proof.** `denote` builds the denotation in 3 ms. The kernel
does the rest: `infer` on the denotation takes 74 to 79 ms and
`check(refl d : Id(Int, d, d))` 221 to 258 ms (two runs). `check` infers
`d` and then runs `def_eq`, which normalises both sides of the `Id` in
full.

**A pointer cache that never hits.** `whnf` and `nf` already cache by
pointer (`ReductionCache`, keyed by `Rc` identity), so on a denotation
built with sharing they should be linear. They aren't. Built with each
level shared, `nf` still took 26 ms at `d = 13`, and `def_eq(e, e)` took
57 ms. The cause is `whnf_impl`'s stuck-application case:

```
other => app(other, (**a).clone()),
```

`app` wraps its argument in a new `Rc`, so the result's argument is a
new allocation. `nf` then recurses into it, misses the cache, and
normalises the whole subtree again, at every application. Reusing the
`Rc` (`Expr::App(Rc::new(other), a.clone())`) is the same term. As an
experiment, with that one line changed:

| | before | after |
|---|---|---|
| shared denotation, `nf` | 26 ms | 0.03 ms |
| shared denotation, `def_eq(e, e)` | 57 ms | 0.02 ms |
| today's unshared denotation, `check` | 221 ms | 60 ms |

The change was reverted at first, because it is in the trusted
kernel. It affects every proof, not just this term: any `nf` over an
application spine re-normalises its arguments. It landed in §49.

**What sharing end to end would take**, in order of payoff:

1. **The `whnf` fix above.** One line. It speeds up every proof, and
   makes `nf` and `def_eq` linear on a shared denotation.
2. **Memoise `denote` by term hash.** The pure fragment has no binders
   (parameters are postulates in the context), so a subterm's
   denotation depends only on its hash. This is outside the kernel, and
   untrusted.
3. **Memoise `infer`.** With 1 and 2, `infer` is the remaining tree walk
   (36 ms at `d = 13` on a shared denotation). Keyed by pointer and
   context, like `ReductionCache`, but inside `infer`, so it enlarges
   the trusted code. Soundness needs the same care as `ReductionCache`
   (the key keeps its `Rc` alive, so an address can't be reused).
4. **Sharing in the IR and the WAT** (§45's first option): compile and
   wasmtime, 12 ms at `d = 13`.
5. **Memoise `eval`** on pure subterms, as typing does (§45). This also
   speeds up the terms §47's gate hands to the interpreter.

Only 1 is small and pays off on every proof; 2 and 3 matter only for
terms with heavy sharing, which the corpus doesn't have. Until 2 to 5
are all done, some stage is still linear in the tree, so §47's gate
stays.

