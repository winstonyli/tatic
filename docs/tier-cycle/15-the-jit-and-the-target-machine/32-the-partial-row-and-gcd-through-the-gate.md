### The partial row and gcd through the gate (2026-11-13)

The question: with the `mod` row (`rem_s`, domain `y != 0`) and every Word site guarded on both sides
(`docs/superpowers/specs/2026-11-13-partial-row-and-gcd-design.md`), does gcd install through the gate, and do the
costs the spike measured hold on the build? Branch `partial-row`, plan
`docs/superpowers/plans/2026-11-13-partial-row-and-gcd.md`.

- **Verdicts.** `gcd` and `gcd_with_two_base_cases` go from `NotCovered` to `Accepted`; no other row of
  `proof/tests/baseline.rs#VERDICTS` moves (run `2026-11-13-t4-verdicts` diffed exactly those two rows). Also accepted:
  `\a b. if a % b == 0 then a else b`, a module whose callee holds `%`, and a `%` in a proved loop
  (`proof/tests/loop_form.rs#shipped`). The mutants `factorial: mul -> mod` and `gcd: mod -> add` are rejected at the
  walk ("branch conditions differ").
- **The guard's controls** (`machine/sim/tests.rs`): a source whose guard differs from the table's (always taken, or with
  `k(op x y)` in place of `z` as its else) is refused by the walk, and outside the domain both sides answer `z` (`out_of_domain_answers_z`; it failed with the
  source's guard dropped).
- **Cost against the spike.** `p1_probe` (the spike patch's probe, run once and removed; run `2026-11-13-t6-p1`)
  reproduces the spec's "Cost" table (its section 7) exactly, check/build work: `capturing_closure_loop` 9288/7275,
  `straight_line` 29241/4530, `held_out_b` 31449/7568, `doubling(6)` 26170/19762, `doubling(12)` 1346914/1074514,
  gcd 61609/7037, `gcd_with_two_base_cases` 62100/7613.
- **`%` chains are linear** (`proof/tests/gate.rs#gate_work_is_linear_in_a_mod_chain`, check and build under 2.2x per
  doubling, as the `if` chain). Check/build work at depths 16, 32, 64: `a % (b % (a % .. b))` 64944/8322,
  71432/13618, 84408/24210; `((b % a) % b) % ..` 63983/7893, 69303/12669, 79943/22221. The check is nearly flat
  (1.10x, 1.18x right; 1.08x, 1.15x left) on a large fixed part; the build grows 1.6x to 1.8x. The `if` chain's numbers
  are unchanged by the refactor that shares the test's body (`assert_linear`).
- **Eval reads the domain through the row** (`lang/eval.rs#apply_prim`). Retired instructions for eval on fib 26
  (`lib` test exe, CPU 4, best of 3, each median within 0.25% of its best): looking the row up by name searched the table on every
  operator, +7.2% in debug (1,745,589,358 to 1,871,743,781) and +9.6% in release (1,241,236,505 to 1,360,653,723;
  start-up is 26.1 M), about 120 instructions per operator in both builds. Indexing rows by operator once
  (`lang/term.rs#PrimOp::row`, picked h1) brings it to +1.0% debug (1,763,137,400) and +1.3% release (1,256,837,375),
  under the plan's 2% line. Runs `2026-11-13-t7-icount-before`, `-after`, `i1-icount-{before,after}-release-3`,
  `i1-icount-startup-release`, `icount-h1-{debug,release}`.
- **The ignored suites** (runs `2026-11-13-t8-*`, at `f322876`): `tatic` and `church-bv` 656 passed, 0 failed
  (`hidden_state_is_classified` included); the `op_table_tests` exhaustive and all-edges `agree` runs over `mod`
  pass; `tatic-wasm` with ignored tests 53 of 54 and `tatic`'s `proof::` with ignored tests 123 of 124. The three
  failures are older than this branch, which touches neither cause: `a_large_check_does_not_churn_stack_segments`
  overflows `encoding::lit`'s `u128` shift at n = 256 in a debug build (its doc says to run it with `--release`, where
  it passes, 1 segment switch: `t8-wasm-stack-release`), and `measure_gate_costs` and `measure_stack_2mb` build
  `doubling(13)`, which is over `MAX_GATE_TREE` since v0.8 (`proof/tests/gate.rs#a_term_over_the_budget_is_not_covered`
  pins it as `NotCovered`).

What it leaves: `Div` has no row (its `MIN / -1` wrap), total-row guards are not folded, and Bit sites carry no guard;
each is a `PARKED.md` entry.
