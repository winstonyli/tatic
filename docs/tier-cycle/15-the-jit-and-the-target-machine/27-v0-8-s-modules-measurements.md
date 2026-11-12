### v0.8's modules: measurements (2026-11-11)

What S3's first task measured (plan `docs/superpowers/plans/2026-11-11-v08-recursion-once.md`, task 14). The gate now
reads a module of several records: each record's source is the term the compile registry holds at its position
(`CompiledFragment::sources`), a call of a closed literal combinator at its exact arity is a call at that position, and
the trusted registry pairing (`gate.rs#pairing`) checks that each source has its record's arity and calls the positions
its code calls other than its own. Run ids are in `docs/runs.md`.

**Verdicts.** Re-filling `proof/tests/baseline.rs#VERDICTS` from `print_verdict_rows` moved exactly three rows,
`NotCovered` to `Accepted`: `twice_inc_5`, `let_bound_factorial_10` and
`tail_recursive_loop_with_pap_producing_root_self_call_arg`, the three Goal 2 targets (each module holds a record other
than the entry). No row became `Rejected`, no `Raw`-bearing row became `Accepted`, and the other rows (closures,
`Div`/`Mod`, curried dispatch, partial applications, the oversized term) stay `NotCovered`. The goldens are unchanged.

**Times.** Run `v08-s3-targets-u1` (untimed on CPUs `CFF`; the timed request `v08-s3-targets` was refused, exit 3,
total 94% with a game and another session's python on CPUs 8 and 9). `cost` is `gate.rs#module_cost`: the tree plus
`CALL_WEIGHT` per call site of the entry and of the registry's callee terms.

| term | cost | build ms | check ms |
|---|---|---|---|
| twice_inc_5 | 236 | 3.9 | 5.1 |
| let_bound_factorial_10 | 472 | 16.8 | 40.9 |
| tail_recursive_loop_with_pap_producing_root_self_call_arg | 474 | 5.3 | 19.6 |

The Goal 1 targets' costs are unchanged (245, 245, 242, 246, 474, their modules hold one record), so the callee call
sites added nothing there. Every Goal 2 target is far under `MAX_GATE_TREE` and under 60 ms for build and check
together; none leaves the goal.

**A callee's tail loop (Review Focus 5).** `a_callee_tail_loop_runs_a_million_iterations`: the callee `$c0` of
`\n. (rec g n acc = ..) n 0` is printed with `return_call $c0`, the gate `Accepts` it, and `jit.apply` at 10^6 returns
`n(n+1)/2` with one compile.

**Mutants of modules (T15, Goal 4).** `proof/tests/modules.rs` edits every call site of every callee in every record of
the three Goal 2 modules (5 wrong-index, 5 dropped, 5 added argument, 1 swapped) and the registry itself. Observed
layers, pinned in the tests: a wrong callee, a dropped or added argument and the padding read are `Rejected(Shape)`;
swapped arguments and a false callee law (the callee's body edited under its unchanged source) are `Rejected(Walk)`,
and the kernel rejects the positive proof against each such mutant's statement; swapped `Call` indices and swapped
registry entries are `Walk` except where the callee calls a callee, which is `Pairing`; a cyclic registry is
`Rejected(Pairing)` on all four modules. No mutant is `Accepted`. A swapped registry entry states the same proposition,
so its test asserts the layer only. Workspace suite `v08-s3-workspace`: 803 passed, 0 failed, goldens unchanged.

**The toy second table (T16, S4, Goal 7).** `proof/tests/toy_table.rs` hands `gate` a table whose `sub` means
`x y. (y - x) + 1`, beside wasm's `const`, `local.get` and `lt`. The unchanged gate accepts `a - b` and
`if a < b then a - b else b` under it and rejects the same `a - b` with the operands loaded in the other order, so the
source reading and the machine read the table given, not wasm's. The toy has no runtime, so "installs" is the gate's
verdict (an inference from the roadmap's wording; the user confirms). No change to `gate.rs`, `machine/` or `machine.rs`.
