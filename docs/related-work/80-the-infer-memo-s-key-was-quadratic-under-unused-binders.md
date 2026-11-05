## 80. The infer memo's key was quadratic under unused binders (2026-10-16)

`infer_memo_skips_unused_inner_binders` (§79, parked) builds `b(i) = k ((λh:A. b(i+1)) a) ((λh:A→A. b(i+1)) f)`, `n` deep under `λx:A`, with `b(n) = x`. That is O(n) DAG nodes, but `infer` cost 2.8 to 7x per doubling of `n`. Two parts of `InferCache::memo_context` (§63's key, narrowed to a window that starts at the node's lowest loose variable `lo`) cost O(i) at level `i`.

**Cause 1: `hc::lowest_loose` was memoised by (node, depth).** `memo_context` asks for `b(i+1)`'s `lo` at depth 0. The walk goes under each `λh` and reaches `b(j)` at depth `j - i - 1`. Each level asks again from a new depth, so the memo held n²/2 entries: 51,359 at n = 320, where the term has 319 shared nodes. Called alone on every `b(i)`, it took 102 ms of `infer`'s 260 ms. *Fix:* a shared node's answer from depth 0, `l`, also answers every depth `d <= l` as `l - d`, so `lowest_loose` asks the node at depth 0 first and memoises per depth only past `l`. The memo is now one entry per shared node here (319 at n = 320). In general a shared node gets one entry for depth 0 and one per depth past `l` it is reached at.

**Cause 2: the skip walked `lo` parents.** `memo_context` stepped `lo` parents out from the context, `lo = i + 1` at level `i`: 1.64M steps at n = 1,280. *Fix:* each context id records `run`, how many binders with a type of the term it ends with, and a jump pointer (Myers' skew-binary scheme: the parent's jump's jump when the parent's two jumps span equal lengths, else the parent). `InferCache::skip` then climbs `lo` binders in O(log run) steps. `run` is 0 at the caller's context and at a `fresh` binder, so a skip past one falls back exactly as the walk did. Steps at n = 1,280 fell to 48k.

**Measured** (debug, best of 7, `infer` alone; other sessions loaded the machine 50 to 85%, Defender real-time protection off):

| n | before (from §79) | cause 1 fixed | both fixed | both fixed, 1 GB stack |
|---|---|---|---|---|
| 40 | 1.38 ms | 0.52 ms | | |
| 80 | 5.8 ms | 1.23 ms | | |
| 100 | | 1.64 ms | 1.73 ms | 1.56 ms |
| 160 | 40.6 ms | 4.21 ms | | |
| 320 | 246 ms | 10.2 ms | | |
| 400 | | 12.5 ms | 8.9 ms | 7.0 ms |
| 800 | | 34.5 ms | 18.8 ms | 13.8 ms |
| 1,600 | | 88.0 ms | 40.8 ms | 32.9 ms |

Both fixed, each doubling costs about 2x. In release, 100 to 400 deep doubles too (60 µs to 261 µs). The rest of the gap to the 1 GB-stack column is `grow`'s segment switches, which grow linearly: 122 at n = 1,600 in debug, 8 in release. `infer_in`, unlike `check_in`, doesn't start on one large segment (§76).

**Cost** (`proof_cost_split`, cmp3d own, 300 laws, `cpu_ab.ps1` two-build mode against cd9dbc1, 8 pairs, load 61 to 85%). The `COST` lines (laws, nodes, occurrences) are identical. New won 5 of 8: summed 19.49 s against 20.49 s, best 1.98 s against 2.30 s. The load was too high to call this a gain, but it shows no loss. A rerun of 12 pairs started at 19% load; the first 5 pairs stayed quiet. Over those, new won 3: summed 7.55 s against 7.69 s, best 1.36 s against 1.39 s, check phase 960 against 961 ms. Load then rose to 51% and the remaining pairs swung up to 4x (old won 5 of 7). A tie: the change neither costs nor saves on this workload, whose shared terms don't sit under deep stacks of unused binders.

**Tests.**
- `infer_memo_skips_unused_inner_binders` now times 800 deep against 100 deep and asserts under 30x, like §79's linear-range guards. Now it runs about 11x. With cause 1 restored it fails at about 180x (2.0 s against 11 ms). With only cause 2 restored it runs about 21x and passes: that quadratic's constant (one array read per step) is below this guard's resolution at these sizes.
- `infer_cache_skip_matches_a_parent_walk` checks `skip` against the walk it replaced. The test builds a random tree of 3,000 contexts with runs over 300 deep and some `fresh` binders, and checks boundary and random `lo` for every context. It fails when `skip` ignores the run (`saturating_sub` for `checked_sub`). It checks answers, not the step count.

