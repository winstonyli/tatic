## 49. Keeping `whnf`'s arguments, and denoting shared subterms once

This does §48's first two steps.

**`whnf`.** Four places rebuilt an application from an argument they
already held as an `Rc`, copying it into a new one: the stuck case,
and the `J`, `WRec` and `SigRec` reductions. Each now reuses the `Rc`,
which gives the same term. §48 found the stuck case; the other three
are the same mistake, and the reduction results feed `whnf` again, so
they lose the cache the same way. `whnf_keeps_the_arguments_it_was_given`
checks pointer identity for all four, and each one-site reversion fails
it.

**`denote`.** It now memoises by term hash within one call. That is
exact, since the fragment has no binders: `classify` reads only the hash
and the parameter count, and the postulate lookups (`lit_ref`, `op_ref`,
`ite_ref`) are pure. `a_shared_subterm_is_denoted_once` checks that the
two operands of `a + a` share their children, and fails without the
memo.

**Effect.** `prove_pure_expr` on §48's `\x. t_13` went from 217 ms to
56 ms. It still doubles per level (0.7 s at `d = 16`, 11.5 s at 20),
because `infer` walks the tree, which is §48's step 3. On the benches,
an A/B against a saved baseline gave `straight_line_refl_proof` 29%
faster. Everything else was within noise. Re-running unchanged `HEAD`
against the same baseline moved benches by -13% to +34%, on a laptop
that slows over a run, so single percentages from one `cargo bench` on
this machine don't mean much. The full run's proof benches moved 5% to
50% faster, and the ones that moved slower include paths the change
doesn't touch, such as the interpreter.

§47's gate stays. `infer` is still a tree walk.

