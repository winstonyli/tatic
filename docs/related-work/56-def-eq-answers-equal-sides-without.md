## 56. `def_eq` answers equal sides without normalising

This lands §55's first proposal: `def_eq` returns `true` when its sides
are the same pointer or syntactically equal (`==`), before building a
`ReductionCache` and normalising either side.

**Survey.** Every mature kernel does this first.
- Lean 4's `is_def_eq_core` starts with `quick_is_def_eq`: pointer
  equality (`is_eqp`), then a union-find cache of pairs already proved
  equal. Hash-consing makes its structural `==` cheap too.
- Coq's `gen_conv` tries `eq_constr_univs` (syntactic, up to universes)
  before calling the lazy conversion machine.
- Agda's `compareTerm` runs `checkSyntacticEquality` first.

**Why it's exact.** `nf` is a function, so `a == b` implies
`nf(a) == nf(b)`. The only behaviour change is that `def_eq(t, t)` now
answers for a `t` with no normal form, where it used to loop. That is
reflexivity of definitional equality, which all three kernels above rely
on too.

**Options considered.**
- *Pointer check only.* Free, but `infer` passes freshly built types
  (from `subst_top` and `ctx_lookup`), so it almost never hits.
- *Structural `==`* (chosen, with the pointer check in front). `Expr`'s
  `==` already short-circuits on `Rc::ptr_eq` at every child, and stops
  at the first difference. §55 measured it at 2 to 3 ms over all 18.9k
  calls of `fib(8)`, against 11 to 12 ms of normalisation saved.

**Test.** `def_eq_answers_equal_sides_without_normalising`: two
separately built copies of `d (d (... (d x)))`, 14 deep, with
`d = \x. x x`. The normal form is 2^14 nodes as a tree. The test must
finish in 5 ms. It took 0.26 s with only the pointer check (the
mutation) and 6 s at 18 deep before the change.

**Measured against §55** (bench A/B, while another session's job held
most cores). A full `proofs` run was too noisy to read, so the benches
it flagged were run again on their own:

| bench | candidate | noise re-run |
|---|---|---|
| `over_application_instance_proof/if_between_closures_self_call_arg` | -49% | +31% |
| `over_application_instance_proof/pap_producing_root_self_call_arg` | -66% | -13% |
| `gcd_relational_scaling_vs_universal/universal_x1` | -18% | +21% |
| `universal_proof_one_time_by_leaf_count/gcd_2_leaves` (full run) | -65% | +9% |

The full run's +276% on `universal_x1` and +115 to +166% on the closure
fragments didn't reproduce. The closure fragments are too noisy under
this load to read either way.

