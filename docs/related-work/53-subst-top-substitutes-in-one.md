## 53. `subst_top` substitutes in one pass

This lands §52's first proposal (§50's A2). When `body` uses `Var(0)`,
`subst_top` now calls `instantiate(body, s, 0)`. Under `d` of `body`'s
binders, `Var(d)` becomes `shift(s, 0, d)`, higher indices drop by one,
and nothing else changes. So `s` is shifted once per use, not again at
every binder crossed and then in the result. `subst` had no other
caller, and moved into the test module as the reference formula.

**Tests.**
- `subst_top_is_substituting_then_shifting` (§51) now checks
  `instantiate` against the old formula on 20000 random pairs.
- `subst_top_shifts_a_used_argument_once` puts a 14-level doubling
  argument under 30 binders. It must take under 4 times one shift of the
  argument, plus 5 ms. Before the change it took 266 ms against 3 ms.
- Each of these mutations fails a test: `Var(d)` becoming `s` unshifted,
  higher indices not dropping, and a missing `d + 1` under `Pair`'s
  family, `WRec`'s children type or `Sigma`'s family.

**Effect.** fib(30)'s cold compile in `cargo run --release` took 40.6 ms,
where the README had about 140 ms. The full bench A/B ran while another
session's job held about 18 cores. Benches this change can't affect,
such as the interpreter and warm cache hits, came out 2 to 7 times
slower in the candidate run, so only large effects mean anything:

| bench | before | after |
|---|---|---|
| `over_application_instance_proof/if_between_closures_self_call_arg` | 230 ms | 27 ms |
| `over_application_instance_proof/pap_producing_root_self_call_arg` | 220 ms | 34 ms |
| `closure_typed_loop_carried_parameter_universal_proof` | 19.3 ms | 5.7 ms |
| `universal_proof_one_time_by_leaf_count/gcd_3_leaves` | 7.6 ms | 4.8 ms |

These agree with §52's spike. The shift cache is still in place; §54
removes it.

