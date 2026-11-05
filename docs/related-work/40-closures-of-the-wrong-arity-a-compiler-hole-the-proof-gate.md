## 40. Closures of the wrong arity: a compiler hole the proof gate closes

§38's type check doesn't see arity. `\x. \y. x + y` and `\x. (\y. x + y)`
have the same simple type, but in compiled code one is a two-argument
table entry and the other a one-argument one. Under `Dispatch::Fast`,
a variable called with one argument everywhere is called through a
one-argument `call_indirect`, whatever closure it holds. So a well-typed
term can reach a mismatched `call_indirect`:

```
\n. (\g. if n == 777 then (\k. k n) (g 1) + (\k. k n) (g 2) else n)
    (\x. \y. x + y + n)
```

`typing::well_typed` accepts it, the specialiser leaves it alone (`g` is
used twice and captures `n`), and the compiled fragment traps at
`n = 777`, where `eval` gives 3111. No sample reaches 777.

The JIT still gets it right, because the fragment gets no universal
proof. That is by construction, not by luck, but the construction is the
provers', not the kernel's. `Clo_k` is a curried chain of `k` arrows
ending in `Int`, so the kernel can't tell `\x. \y. e` from
`\x. (\y. e)`. Both are `Clo_2`, and `g` above, used as
`Int -> (Int -> Int)`, has that type too. What declines the term is that
the prover types each closure parameter as `Clo_k` for the number of
arguments at its call sites (`g 1`: `Clo_1`), and then refuses an
argument whose root has another arity (§44 has more on this). The proof
walkers do that up front: `denote_*` through §39's `arg_denotation`, and
`eval_dyn`, whose closure values carry their concrete root, by comparing
that root's arity with the parameter's. §39 had missed `eval_dyn`, and
this test hit its debug panic there; a release build was sound either
way.

So this hole is closed by §29's universal-proof gate, not by the sample
battery the comments in `compile.rs` credited. The test
`a_closure_of_the_wrong_arity_off_the_samples_is_not_installed` runs the
fragment directly to show it traps, and requires the JIT to agree with
`eval` and to decline the term for want of a proof. With the gate relaxed
to install proof-less terms, it fails at `n = 777`.

A static check in the compile path would make this independent of the
proof gate: simple types extended with arity, where an arrow records how
many arguments it takes at once, as in "Kinds are calling conventions"
(Downen et al., ICFP 2020). That isn't done here. It is the natural next
step if the proof gate is ever relaxed (§29's "widen the universal
fragment"). §43 surveys what other compilers do instead.

