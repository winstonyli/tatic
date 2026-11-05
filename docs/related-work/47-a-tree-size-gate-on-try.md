## 47. A tree-size gate on `try_compile`

§45 left three options for `try_compile`'s blowup on shared subterms.
This takes the size gate.

**Why not sharing in the IR.** Compilation is a small part of what a
compiled term costs. Timing the whole JIT path on `\x. t_d`, with
`t_{i+1} = t_i + t_i`:

| `d` | `compile_specialised` | whole JIT call |
|---|---|---|
| 10 | 0.9 ms | 19.6 ms |
| 12 | 2.8 ms | 75 ms |
| 14 | 13 ms | 365 ms |

The rest is wasmtime compiling the module, the sample battery (`eval`)
and the provers, and each of those walks the tree too. A `let` in the IR
would make `try_compile` linear and leave about 96% of the cost, so it
would have to be followed by sharing in `lower_wat.rs`'s output and in
every prover walk. That is a large change for terms the corpus doesn't
have.

**The gate.** `try_compile` now starts by counting the term as a tree
(`tree_size`: one post-order pass over the DAG with a memo, saturating
just past the bound) and declines anything over `MAX_TREE_NODES` =
16384. The interpreter runs it. Every caller goes through `try_compile`,
including `compile_specialised` on the specialised term, and
`specialise.rs` is already bounded in distinct nodes (§37). The bound is
about 20 times the largest term the corpus compiles (838 nodes), and the
whole JIT path costs about 0.4 s there.

`a_term_is_compiled_only_up_to_a_tree_size` pins the boundary: `\x.
t_13` is exactly 16384 nodes and compiles, and `\x. t_14` doesn't.
`t_200` is counted without overflow. `a_term_too_big_as_a_tree_is_interpreted`
calls the JIT on `\x. t_16`: it is interpreted and agrees with `eval`,
in 0.06 s. Without the gate it compiles, in 5.3 s (debug build), and
both tests fail.

**What it doesn't fix.** `eval` walks the tree too, so such a term is
still exponential to run. The gate only stops the compiler costing
far more than the run. §48 times each stage: the kernel, not the IR, is
most of the cost.

