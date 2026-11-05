## 79. Stuck spines stayed quadratic after §59: the spine walks (2026-10-16)

`nf_and_def_eq_are_linear_on_a_stuck_spine` gave 2,000-deep stuck spines a 500 ms budget. Under the parallel debug suite it took 1.09 to 1.18 s and failed; alone it passed. Timing several depths showed the cause was not load. Each doubling cost 3.5 to 4 times, in `whnf` alone as much as in `nf` and `def_eq`.

| depth | `whnf` before | after | `nf` before | after | `def_eq` before | after |
|---|---|---|---|---|---|---|
| 500 | 12 ms | 1.4 ms | 14 ms | 1.6 ms | 23 ms | 2.9 ms |
| 1,000 | 49 ms | 3.8 ms | 46 ms | 5.6 ms | 87 ms | 9.9 ms |
| 2,000 | 184 ms | 10.6 ms | 170 ms | 14.4 ms | 330 ms | 28 ms |
| 4,000 | 645 ms | 24 ms | 715 ms | 37 ms | 1.30 s | 69 ms |

Debug build, the test's spines: `x0 a1 ... an` with every argument a variable, `nf` on that spine, `def_eq` against the same spine with a redex for its head. Before: one or two runs. After: best of three. After, from 4,000 to 32,000 each doubling costs 2.0 to 2.3x (32,000 deep: 1.6 s for all four calls). Below that the spines stay in cache and the growth looks steeper.

**Cause.** `whnf_step` runs once per level of a stuck spine, since each level's fallback asks for its function part's whnf. At each level, `closed_prefix_spine` walked down looking for a prefix with no loose variable, which here meant walking to the bottom, and `beta_spine` walked down to the head. A throwaway probe that ran `closed_prefix_spine` at every level took about 60% of `whnf`'s time.

**The change.** A region memo, `Memos.spine`, maps an application to its spine's head and its longest proper closed prefix. `spine` answers a one-argument application directly. It memoises a longer one by recursing on the function part, so one walk fills every level. `whnf_step` asks only as needed: the closed prefix of `f a` is `f` when `f` is closed, else `f`'s own, and the head only after the closed-prefix shortcut fails. Both functions collect their arguments only once the prefix or head is a lambda.

**Cost** (`proof_cost_split`, cmp3d own, 300 laws, `cpu_ab.ps1` two-build mode against 1442f73, Defender real-time protection off). The `COST` lines (laws, nodes, occurrences) are identical.
- The first two versions asked `spine` of `e` itself on every application, so they walked even when `f` was closed. The first kept an explicit path `Vec`. Over 16 pairs at 18 to 53% load, old won 9 and new 6, with 1 tie: summed 22.76 against 21.85 s. The second recursed instead. Over 12 pairs at about 10% load, old won 8 and new 3, with 1 tie: summed 15.23 against 14.87 s, about 2% slower.
- Walking up to three levels directly before using the memo didn't help (old won 9 of 12) and was removed.
- The lazy version, run while other sessions loaded the machine 29 to 49%: new won 8 of 12, summed 19.87 against 20.81 s.
- The lazy version again, at 16 to 19% load, dropping a cold-start first pair: new won 5 of 11, old 4, with 2 ties. Summed 14.70 against 14.72 s, best 1.23 against 1.25 s. A tie.

**The test** times 16,000 deep against 1,000 deep, with fresh variables every run so no memo carries over. It asserts under 80x. In a debug build it measures 17-35x now, and 168-228x on the kernel without the memo (9 pairs over 3 runs, all failing). It first timed 8,000 against 1,000 with a bound of 30. A review found that too thin: without the memo it measured 41-65x, not the 64x theory, and passed one run in six under load, since one pair under the bound passes. The other chain guards (`def_eq` on chains at 1,000/16,000, `infer` on a spine at 500/8,000) moved to the same 16x gap and bound 80. With their fixes they measure 15-32x and 21-41x. The kernel's walk counters (`record-defeq`) are compiled out by default, so a plain `cargo test` can't count walks instead of timing.

**Every fixed-budget test in `src/kernel/tests.rs` now uses that check.** The helper is `assert_scales(what, small, large, max_ratio, run)`. It runs three small-then-large pairs on a thread of its own and passes when any pair's large run is under `max_ratio` times its small run plus 5 ms. The two runs of a pair share the machine's load. The first version took the best of three small runs and then of three large ones, and failed once in 13 full suites (`infer_types_an_application_spine_at_once`, bound 30x, usually 14 to 17x). Pairing passed 12 of 12. Each large run gets ten times its budget plus 2 s. So a regression to exponential time fails in about 2 s; before, it hung the suite (a memo-disabled spine ran past 15 minutes). The abandoned thread keeps running until the test process exits.

There are two kinds of guard. Tests that guard against walking a DAG as a tree use small sizes (10 against 20, say). Their runs take microseconds, so the 5 ms term dominates and the check reads "the large size stays cheap", where walking the tree would take seconds. Tests that guard against quadratic growth on spines and chains time 1,000 or 500 against eight times as many, in the linear range. `subst_top_shifts_a_used_argument_once` already calibrated itself and is unchanged. Two tests kept their old exponential guard but grew faster than linearly, and both were parked. `infer_memo_skips_unused_inner_binders` cost 2.8 to 7x per doubling of depth from 10 to 320 (153 µs to 246 ms, debug); §80 made it linear. `brief` costs 22 to 63x from 100 to 800 deep and is still parked.

