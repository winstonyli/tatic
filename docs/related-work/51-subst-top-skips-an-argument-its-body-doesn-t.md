## 51. `subst_top` skips an argument its body doesn't use

This is §50's A1. `subst_top(body, s)` now returns `shift(body, 0, -1)`
when `Var(0)` isn't free in `body`, and only otherwise shifts `s` and
substitutes. The two agree, since `subst` is the identity on a body
without the variable. All 22 callers in the kernel get the change.

**Tests.**
- `subst_top_is_substituting_then_shifting` compares the new function
  with the old formula on 20000 random pairs of `Expr`s, covering every
  variant, with more than 2000 cases each where the body uses `Var(0)`
  and where it doesn't. It fails if the guard returns `body` unshifted,
  or if `shift` or `subst` is mutated in the `Pair` or `W` case.
- `subst_top_leaves_an_unused_argument_alone` substitutes a 20-level
  doubling tree into `Pi(Var(3), Var(4))`. That took 972 ms before
  and must now take under 50 ms.

**Effect.** `prove_pure_expr` on `\x. t_d` from §48 (release, one run
each):

| `d` | §49 | §51 |
|---|---|---|
| 13 | 56 ms | 9.4 ms |
| 16 | 0.7 s | 66.5 ms |
| 20 | 11.5 s | 1.07 s |

It still doubles per level, because `infer` walks the tree (§50's B).
On the benches, against a saved baseline of the parent commit:

| bench | before | after | noise re-run |
|---|---|---|---|
| `gcd_2_leaves` | 12.7 ms | 4.1 ms | 10.4 ms |
| `gcd_3_leaves` | 32.3 ms | 7.5 ms | 25.5 ms |
| `universal_x1` | 8.8 ms | 4.1 ms | 19.1 ms |
| `closure_typed_loop_carried_parameter_universal_proof` | 17.2 ms | 7.0 ms | 31.1 ms |

The last column re-runs the unchanged parent afterwards. The universal
proofs, which apply operators to large arguments, got 2 to 4 times
faster, well outside the noise. The microsecond benches moved by -43%
to +23%, while the noise run moved them by -25% to +73%, so they're
unchanged within what this laptop can resolve.

