### Kernel memos, interning and substitution (2026-10-13)

**What else could be memoized (survey, 2026-10-13).** From the profile above and the code:
- *The side machines' step at each leaf, across a tree's lemmas.* `tree_proof` states m + 1 F lemmas per side (output and
  each next phi bit) over the same k + c bits, and each leaf of each recomputes `Machine::step` over `GoodOps` at its literal
  bits, then the phi tables of the next carries. One `(side, bits) -> (out, next)` memo per `tree_proof` would build each
  step once instead of m + 1 times. Building leaves was 32% of lemma time, `table_app` included; open what is left now.
  Done: "One builder memo, and each step once per leaf", below.
- *Normal forms of closed terms across `def_eq` calls (kernel).* `ReductionCache` lives for one top-level `def_eq`/`whnf`/
  `nf` call (`crates/tatic-kernel/src/lib.rs` near 1424), so every leaf renormalizes the same closed gate applications (`and` of two literal
  bits, say). A cache keyed by canonical pointer, per interning generation, for closed terms would collapse them. Reduction
  is context-free for closed terms, so it is sound, but it touches the trusted kernel. Gain unmeasured: first count distinct
  canonical closed `App` nodes normalized per lemma. Counted: at most about 1%, not worth it ("A closed-term normal-form
  cache would save about 1%", below).
- Smaller: `GoodOps::new` per `tree_proof` (rebuilds three `good2` proofs; not visible in the profile); the guarded leaves'
  `hty` and `inv_expr` (now hit the table memo).

**Interning in the kernel's reduction (survey, 2026-10-13; read-only, a subagent's report checked at the cited lines).** The
hash-cons table (`mod hc`, `crates/tatic-kernel/src/lib.rs` near 828) already uses a pointer hash (`PtrHasher`) and shallow keys (child
pointers); removing or narrowing it lost badly ("Hash-consing cost", above). Open options, most promising first:
1. `args_id` (near 1136) re-interns every argument of every `instantiate_n` (`intern((*a).clone(), None)`, a clone and a
   probe) although `beta_spine`/`whnf_step` hold canonical `Rc`s; taking `&Rc<Expr>` and skipping canonical ones removes
   that. `args_id` was 11-14% inclusive of lemma time; "Hash-consing cost" estimated at most about 7%. Done: "Canonical
   arguments are not interned again", below.
2. `inst_rec`'s per-child work makes up to four separate `TABLE.with` borrows (`uses`, `inst_get`, `intern`, `inst_put`);
   fusing them saves TLS and `RefCell` traffic. Inside `hc` only; gain unmeasured.
3. Pre-reserve `nodes`, `inst`, `uses` when the table switches on: `reserve_rehash` was 5-9%. One line per map.
4. The closed-term normal-form cache above (measured below: about 1%; dropped).
5. A separate, non-interning normalizer for closed Bool terms: largest change, adds to the trusted base; last.
Minor: `arg_sets` still used SipHash then (`Vec<usize>` keys); it is an `IdMap` now (`crates/tatic-kernel/src/spaces.rs`).

**One builder memo, and each step once per leaf (2026-10-13).** `constant` and `table_app` now share one helper, `gen_memo`
(`encoding.rs`): a thread's values by key for the current interning generation, emptied when the generation changes, with the
kernel's multiply-rotate hasher (`Fx`). Moving the two onto it changed nothing measurable: 8.02-8.34 s against 8.05-8.41 s
CPU over 4 alternating pairs of `proof_cost_split` (cmp3d own, against 4da7e02).
- Left off it on purpose: `CLOSED`/`shared_lemma` (rewrite.rs) and `TREE_LAWS`/`TREE_ENCS` (machine.rs) live for the whole
  thread. The generation changes mid-run (the table switches on after `WARM_UP` calls, and every outermost `InternScope`, one
  per scoring worker and per `prove` call in the miner, starts a new one), and
  `CLOSED` binds each key to a lemma parameter in `PARAMS`; emptying it per generation would rebind lemmas and could change
  outputs. `TREE_*` cache decisions and closed proofs that stay valid across generations.
- The step memo is local to `tree_proof`, not a `gen_memo`: its key would have to name the machine and the encoding tables,
  while within one `tree_proof` `(side, bits)` suffices. `guarded` now hands its case function the leaf's bits (`None` in the
  statement), and the F and P lemmas take a side's `(output, next carries, phi of the carries)` from the memo, so each leaf's
  step and its m phi values of the carries are built once instead of once per lemma (m + 1 F lemmas plus P). The `core`
  proof keeps the direct path (symbolic bits, built once per position).
- `proof_cost_split` (cmp3d own, 300 laws), CPU time over 16 alternating pairs with a temporary `NOSTEPMEMO` switch (removed;
  `scripts/cpu_ab.ps1`; CPU 17-35% from other sessions, RTP off): the memo won 13 of 16 (2 of 4, 5 of 6, 6 of 6 per round);
  summed 161.1 against 180.4 s, about 11%; rule-proof build 6.6-8.3 s against 8.5-10.1 s in the last round.
- Sequential pair against 4da7e02 (`scripts/step_seq.sh`, rows `sts_*`; covers the helper and the step memo; RTP off): rows,
  preferences and all 27 rule and unit files identical on both salts. Wall 29 against 28 s (salt 1), 27 against 28 s (salt 2).

**A closed-term normal-form cache would save about 1% (negative, 2026-10-13).** A temporary probe at 464e24f (reverted, no
patch kept) recorded, in the kernel's `whnf_rc` on a cache miss, every closed node (`loose_of == 0`) by pointer for the
interning generation. It counted the nodes reduced again, whether in the same public `check`/`infer` call or an earlier one,
and timed the outermost such repeats. `proof_cost_split` (cmp3d own, 300 laws, one run, 8.6 s CPU):
- Inside `check`/`infer`: 6.76 s over 1134 top-level calls, so the kernel is about 78% of the run (lemma checks fall in
  "build").
- Closed `whnf_rc` misses: 2.22 M, of which only 72.8 k reduced anything; the rest were already in weak head normal form.
- Repeats: 34.5 k within the same call (a later `def_eq` with a fresh `ReductionCache`) and 86.1 k from earlier calls, of which
  0.7 k and 23.5 k reduced anything. All repeats together took 70 ms.

So a cross-call cache of closed normal forms could save at most about 70 ms of 6.76 s (1%), and it would add to the trusted
kernel. Not built. A limit of the count: nodes are matched by pointer, so a closed redex rebuilt outside the hash-cons table
(e.g. `beta_spine`'s fresh head `Rc`) is never a repeat. Those heads are mostly gate lambdas, already in weak head normal
form. The kernel's time is in the reductions that do run and in interning (items 1-3 of the survey above), not in repeats.

**Canonical arguments are not interned again (2026-10-13).** `subst_top`, `instantiate` and `instantiate_n` now take their
arguments as `&Rc<Expr>` (every kernel caller already held them so; `beta_spine` passes its spine's `Rc`s through, and the
unit tests wrap theirs). `hc::args_id` uses a canonical argument's own address, which is its table node by definition, and
interns only the others; before, it cloned every argument and probed the node table for it on each substitution. Check:
`args_id_is_the_same_for_a_canonical_argument_and_its_twin` (the id of a canonical node and of a twin built outside the
table agree). The kernel's results are unchanged: the id is the same either way.
- `proof_cost_split` (cmp3d own, 300 laws), CPU time, `scripts/cpu_ab.ps1` in its two-build mode, HEAD 01018d6 against the
  change, RTP off. Other sessions' builds made the load swing (13-57%), and one round at 100% was dropped. Over the four
  other rounds (24 pairs) the change won 17, with 1 tie: summed 252.0 against 280.4 s, best 7.58 against 8.44 s, about 10%
  either way. In the quietest round it won 5 of 6, 8.03-11.11 s against 9.09-15.28 s.
- Sequential pair against 01018d6 (`scripts/aid_seq.sh`, rows `ais_*`): rows, preferences and all 27 rule and unit files
  identical on both salts. Wall 46/46 s against 39/30 s, with 57% load from other sessions' builds at the end; the
  sweeps' proof share is too small for a 10% gain on it to show, and the walls are not evidence either way.

**Where the time goes after the memos (samply, 2026-10-13).** Run on be98b3e, `proof_cost_split` (cmp3d own, 300 laws), built
with debug info, analysed by `scripts/prof_cases.py` with its directory pointed at the new profile (profile not kept; 9227
busy samples; CPU 21% at launch). Against the 0cb4e6c profile ("Where the case lemmas' time goes"):
- Case lemmas (`shared_lemma`): 41.6% of busy samples (was 52%). Inside them, the kernel check `ck` is now 81% (was 63%) and
  building (`lemma_n`) 17% (was 36%): the builder memos removed most of the build side.
- The kernel dominates the whole run: `infer` 74.5% inclusive, `def_eq` 59%, `beta_spine` 57%, `instantiate_n` 60%. Of the
  substitution, hash-consing is most: `hc::intern` 32% inclusive overall, `args_id` now 6.3% of lemma time (was 11-14%).
- Self time is table probes, not reduction logic. Under the case lemmas: the node table probe (`intern_as`'s `TABLE.with`)
  17.4%, the instantiation memo probe (`inst_get`) 11.7%, `reserve_rehash` 6.4%, `intern` 5.8%, the `uses` memo 3.9%,
  `RawTable::insert` 2.8%, `args_id`'s set lookup 2.6%, `inst_put` 2.3%. `beta_spine` itself is 3.1%.
- Dropping the table at the end of each outermost scope (`hc::Scope::drop`, mostly `drop_inner_table`) is 5.6% of all.

Open leads from this, cheapest first (none tried yet):
1. Growth and teardown: `reserve_rehash` (6.4% self, 9.2% inclusive overall) and the per-scope drop (5.6%) together
   are about 15%. The table could keep its allocations across scopes (`clear()` keeps the capacity) or reserve on switch-on.
   Either one is a few lines inside `hc`.
2. The probes themselves (`intern_as` 17.4%, `inst_get` 11.7% self) are hash lookups in large tables, likely bound by
   cache misses. Fusing the `TABLE.with` borrows (survey item 2) saves thread-local and `RefCell` traffic, not misses.
   Fewer or smaller entries would, but no candidate has been identified or measured.
3. `hc::uses` (6.8% inclusive in the lemmas) recomputes per (node, depth, count); smaller.

**Keeping the table across scopes would save under 1% of a sweep (negative, 2026-10-13).** Lead 1 above. Probe: a temporary
line in `hc::Scope::drop` (reverted, no patch kept) logged each outermost table drop's sizes and drop time. Result from one
`mines own pooled` sweep on be98b3e, salt 1, 58 s wall:
- The sweep makes 160 outermost drops across 54 processes. A miner, server or pooled process drops 1-4 times; only the
  three `mine_ref` processes drop often (19-31 times each, 76 in all).
- Tables reach 0.4-1.2 M nodes and up to 3.5 M instantiation entries.
- All 160 drops together take 1.35 s, against up to 58 s × 12 threads of CPU (CPU time not measured). Growth reinserts about one final table's
  worth of entries per scope, which is the same order.
- So the 15% in `proof_cost_split` is that benchmark's shape: one scope that grows a large table and tears it down at
  exit. Retaining capacity helps only on a second scope in the same thread, and sweeps have few. Pre-sizing would need a
  size hint, and sizes vary 3× between processes. Neither was built.

**The spine's head reduced as its own node; `args_id` without a Vec per call (2026-10-13).** Two items from an
allocation scan of the hot paths. Allocator work (malloc, Vec growth, drop glue) was about 5% of the samply profile above;
the table probes are the bulk.
- `beta_spine` used to reduce a fresh `Rc` copy of the spine's head. That was one allocation per spine, and its
  `ReductionCache` entry could never hit again, because the cache is keyed by pointer. When the head was stuck, every
  level of the spine reduced the head again. It now reduces the head node the spine holds, and collects the arguments
  only once the head is a lambda.
- `hc::args_id` built a `Vec<usize>` of ids on every call, including the one-argument case, which returns at once. It
  then moved the Vec into the set, which freed it on a hit. Now one argument returns its id directly. Up to 8 ids go in a
  stack buffer, the set is probed with `get`, and the Vec is allocated only for a new list. Check:
  `args_id_is_stable_for_short_and_long_lists`.
- `proof_cost_split` cmp3d own, against a1ad219, two rounds of 12 alternating pairs. CPU load was 16-24% at the round
  boundaries; Defender RTP was off.
  - Round 1: new won 10 pairs, summed CPU 123.2 against 128.7 s.
  - Round 2: new won 7 pairs, 106.6 against 112.5 s.
  - Together: won 17 of 24, about 5% less CPU. The best single runs don't confirm it: 9.61 against 9.41 s in round 1,
    and 7.03 against 8.17 s in round 2.
- Sequential pair (`scripts/bsp_seq.sh`, rows `bss_*`): rows, preferences, pooled rules and units, and the 26 rule and
  unit files are identical on both salts. Only `own.tsv`'s elapsed-seconds column differs. Wall 36/21 s against 32/24 s.

**The builder side is about 8% (samply, 2026-10-13).** Run on af20655, `proof_cost_split` as above (profile not kept; 7206
busy samples; CPU 11% at launch). It answers whether the case-tree builder has allocations worth removing.
- Building (`lemma_n`) is 8.5% of busy samples. Of that:
  - Interning the built nodes is 65% (`intern_as`'s table probe alone is 33% self).
  - The machine step at the leaves (`Machine::step`, the gates) is 31%.
  - `table_app` is 29%.
  - Vec collects are 14%, and the `gen_memo` lookups 5%.
- `table_app`'s row evaluation, which the allocation scan suspected, is small: `table_app`'s own self time plus
  `tree_proof::closure$3::closure$0`, which is probably the row closure, come to 3.4% of building, about 0.3% of the run. Keying its memo by the caller instead of the rows would save
  about that much. The rest of `table_app` is applying the memoised body to the leaf's variables, which is interning.
- Each builder slice is at most about 2.5% of the run, and most of that is node interning that a build has to do. No
  builder change was made. The kernel's table probes (`intern_as` 27% inclusive, `inst_get` 14%) and growth
  (`reserve_rehash` 9.4%) remain where the time is.

**Reducing a built term without copying it when stuck is neutral (negative, 2026-10-13).** Five `whnf_step` sites pass a
term built for the call to `whnf_impl`, which copies it when it is stuck. A `whnf_owned(e: Expr)` returning `e` itself
(reverted, no patch kept) changed nothing measurable. `proof_cost_split` cmp3d own against aba7d83, 16 alternating
pairs: it won 8, summed CPU 115.1 against 115.7 s, best 6.27 against 6.08 s.

**Hit rates of the hc tables (2026-10-13).** Probe: counters in `hc` (reverted, no patch kept), written at the outermost
scope's end. Run on aba7d83, `proof_cost_split` cmp3d own. The counts were identical on two runs.

| Table | Lookups | Hits | Entries at the end |
|---|---|---|---|
| `nodes` (`intern_as`) | 16.77 M | 81% | 3.17 M |
| `inst` (`inst_get`) | 11.05 M | 39% | 6.77 M |
| `uses` | 8.48 M | 93% | 0.60 M |
| `arg_sets` (two or more arguments) | 2.09 M | 70% | 0.63 M |
| `shifts` | 1.66 M | 61% | 0.64 M |

- The instantiation memo is the largest table and has the lowest hit rate. Each miss costs a probe and an insert.
  68% of its misses (4.61 M) rebuild a node the node table already holds.
- Nodes whose children are all leaves (`Var`, `Sort`, `Const`, `Free`) are 40% of `inst_get`s (4.47 M), and only 36%
  of those hit. `App` nodes are 65% of `inst_get`s (7.16 M), and 36% of those hit.
- Lead, not tried: skip the instantiation memo for nodes whose children are all leaves.
  - That saves 4.47 M gets and 2.85 M inserts, and makes the table 42% smaller, which cuts growth and teardown too.
  - It costs 1.62 M rebuilds. Each is a node-table probe, plus a `shift` of the argument when it lands under binders,
    which is memoised.
  - The outputs cannot change: the memo only shares results that are built the same way anyway.

**Small nodes skip the instantiation memo (2026-10-13).** This is the lead above, with the cutoff measured.
- `inst_rec` now neither looks up nor stores a node at most two levels above its leaves (`hc::low`); it rebuilds it.
  Check: `low_is_height_at_most_two`.
- The cutoff was chosen with a temporary knob over heights 1-4 in one build (removed). Each step is 12 alternating pairs
  of `proof_cost_split` cmp3d own:

  | Step | New won | Summed CPU, new against old | Best, new against old |
  |---|---|---|---|
  | height ≤ 1 against no skip | 10 | 74.9 against 82.0 s | 6.00 against 6.53 s |
  | ≤ 2 against ≤ 1 | 11 | 76.6 against 81.4 s | 5.84 against 6.09 s |
  | ≤ 3 against ≤ 2 | 2 | 81.9 against 80.5 s | 6.66 against 6.41 s |
  | ≤ 4 against ≤ 3 | 0 | 76.8 against 67.4 s | 6.00 against 5.80 s |

  Beyond height 2 a node's rebuild costs more than its probe and insert.
- The final build against 8cd8dfa, 12 alternating pairs: won 11, summed CPU 76.9 against 86.6 s (11% less), best 5.70
  against 6.28 s. CPU load was 5-27%; Defender RTP was off.
- Sequential pair (`scripts/low_seq.sh`, rows `lws_*`): every file is identical on both salts (rows, preferences,
  pooled rules and units, the rule and unit files), apart from the elapsed-seconds column of `pooled_prefs.tsv`.

**After the skip; the same cutoff for `uses` and `shifts` does not pay (negative, 2026-10-13).** Probe as before
(counters, reverted, no patch kept) on 0fb9cad:

| Table | Lookups | Hits | Entries | Small nodes (height ≤ 2): lookups, hits |
|---|---|---|---|---|
| `nodes` | 18.77 M (was 16.77 M) | 83% | 3.17 M | |
| `inst` | 5.91 M (was 11.05 M) | 44% | 3.28 M (was 6.77 M) | skipped |
| `uses` | 8.52 M | 93% | 0.60 M | 1.70 M, 99.99% |
| `shifts` | 1.67 M | 61% | 0.64 M | 0.48 M, 99.7% |

The skip halved the instantiation memo's lookups and entries, for 2.0 M more node-table probes. Unlike the
instantiation memo, `uses` and `shifts` almost always hit on small nodes. Skipping their memo there was tried with
temporary knobs (removed), 12 alternating pairs each on `proof_cost_split` cmp3d own:
- `uses`: won 5, 85.6 against 86.5 s. Neutral. The memo hit costs about as much as walking a small node.
- `shifts`: won 3, 133.2 against 131.5 s, with other sessions' load at 54% during the round. Rebuilding a shifted node
  interns it, which costs a probe per node instead of one hit.

**How many lookups are keyed by a leaf (probe, reverted, no patch kept, 2026-10-13).** This is the ceiling for one shared
node id: an immediate tagged value for a leaf (`Var`, `Sort`, `Const`, `Free`), the address otherwise, plus per-table
height cutoffs in place of `hc::low` and the scattered shape checks. Counters on 1b7dad9, one `proof_cost_split` cmp3d own:

| Structure | Lookups | Keyed by a leaf | Other |
|---|---|---|---|
| `nodes` (by the interned node's height) | 18.77 M | 2.27 M (12%), 99.98% hit | height 1: 0.06 M; taller: 16.44 M, 81% hit |
| `args_id` arguments | 9.43 M | 2.56 M (27%), none non-canonical | |
| `shifts` | 1.67 M | 0.48 M (29%), 99.7% hit | |
| `ShiftMemo` (local) | 1.37 M | 0.26 M (19%) | |
| `whnf_rc` cache | 2.75 M | 0.04 M (1.5%) | 60% hit |
| `InferCache.types` (memo path) | 3.61 M | 0.98 M (27%) | 53% hit |
| `InferCache::enter` binder types | 0.62 M | 0.37 M (59%) | |

- Height-1 nodes are 0.3% of node lookups, so inlining them in the id would save nothing.
- Leaves in `args_id` are already canonical, so immediate ids would only remove the address-reuse risk there, not work.
- Probes an immediate id could drop: about 4.0 M of the 28.8 M across the hash tables (14%; `nodes` 2.27, `infer` 0.98,
  `shifts` 0.48, `ShiftMemo` 0.26, `whnf` 0.04). Most are hits on hot entries, cheaper than the instantiation misses the
  height-2 skip removed (5.1 M lookups and 3.5 M inserts for 11%), so the expected gain is a few percent at most.

**Leaves skip the infer and shift memos (negative, 2026-10-13).** The cheapest test of that ceiling: a temporary knob
(`LEAFSKIP`, reverted, no patch kept) skipping the memo for leaf keys in `infer_rc`, `shift_child` and `shift_memo_child`,
12 alternating pairs each on `proof_cost_split` cmp3d own (`scripts/cpu_ab.ps1` with a value), Defender RTP off:

| Memo skipped for leaves | New won | Summed CPU, new against old | Best, new against old | CPU load |
|---|---|---|---|---|
| `InferCache.types` | 8 | 110.1 against 112.1 s | 8.95 against 9.02 s | 59% |
| `shifts` | 6 | 94.2 against 91.0 s | 5.63 against 5.45 s | 31% |
| `ShiftMemo` | 4 | 82.2 against 81.6 s | 5.52 against 5.83 s | 12% |

All three are within noise: a leaf's memo hit costs about what inferring or re-interning the leaf does. So the shared
node id with an immediate leaf value and per-table height cutoffs is not worth building for speed (parked).

**Where the node table's time goes (samply, 2026-10-13).** Profile of `proof_cost_split` cmp3d own at 1f4db8b (profile not
kept; `scripts/prof_callers.py`), 5870 busy samples:
- `hc::intern` is 34% of busy samples. Its callers: `inst_rec` 22%, the builders' `app`/`app2`/`app3` 7%, `shift_child`
  and `shift_memo_child` 3%, the rest under 2%.
- Inside it, the probe itself (the `intern_as` closure's own samples) is 18%, `RawTable::insert` 7% and growth
  (`reserve_rehash`) 3%; allocation is the rest. With 3.2 M entries of 56 bytes (a 48-byte `NodeKey` and the `Rc`), the
  table is at least 180 MB, so most probes miss the cache.
- Growth across all tables is 10%: the node table 3.2%, `inst` 2.2%, `InferCache.types` 1.2%, `args_id` 0.9%, `whnf` 0.6%.
  Freeing the tables at the outermost scope's end is another 6%.
- Lead: keep the node table as a set of node pointers with their stored hashes (hashbrown's `HashTable`, comparing
  against the candidate node itself), 16 bytes per entry instead of 56. A hit already touches the node to bump its count,
  so comparing there costs no extra miss, and the smaller table caches better and grows more cheaply.

**Most infer-memo entries are never read (probe, reverted, no patch kept, 2026-10-13).** Hits per `InferCache.types`
entry, counted when its cache drops, same run:

| Node | Entries | Read at least once | Hits |
|---|---|---|---|
| `App`, closed | 0.25 M | 42% | 0.27 M |
| `App`, open | 1.02 M | 15% | 0.26 M |
| `Lam`, closed / open | 0.02 / 0.11 M | 70% / 10% | 0.29 / 0.01 M |
| `Pi`, closed / open | 0.004 / 0.03 M | 57% / 3% | 0.22 / 0.007 M |
| leaf, closed / open | 0.003 / 0.15 M | 57% / 45% | 0.13 / 0.70 M |
| other, closed / open | 0.03 / 0.07 M | 4% / 8% | 0.003 / 0.02 M |
| all | 1.70 M | 21% | 1.91 M |

79% of entries are never read. Open non-leaf nodes are 1.24 M entries (73%) for 0.30 M hits (16%). Skipping the memo
for them (knob `INFERSKIP`, reverted, no patch kept) is far worse: 12 alternating pairs, won 0, summed CPU 203.1 against
66.4 s, the check stage about 10 s against 1 s. Each lost hit re-infers a whole subtree, so the unread entries are the
price of the few hits that matter (negative).

**The node table holds node pointers with their hashes (2026-10-13).** This is the lead from the profile above.
- `hc::Table::nodes` is a hashbrown `HashTable<(u64, Rc<Expr>)>`. A lookup hashes the new node's key as before, then
  compares the stored hash and, only when it matches, the candidate node's own key (`hc::key_of`). An entry is 16 bytes
  instead of 56, and growth rehashes from the stored hash without reading any node.
- Check: `intern_finds_equal_nodes_after_growth`.
- Against 6cd8948, two rounds of 12 alternating pairs of `proof_cost_split` cmp3d own: won 8 (80.0 against 82.0 s, load
  9-23%) and 12 (67.7 against 73.2 s, load 11-15%). Together won 20 of 24, summed CPU 147.7 against 155.2 s (5% less);
  best 4.81 against 5.11 s. Defender RTP was off.
- Sequential pair (`scripts/pset_seq.sh`, rows `pss_*`): every file is identical on both salts (rows, preferences,
  mines, the 26 rule and unit files), apart from the elapsed-seconds columns. The sweeps took 22 and 19 s wall on both
  builds, too short for the difference to show.

**The memos store only their results (2026-10-13).** `inst`, `shifts` and `uses` no longer hold a copy of each entry's
source node. A source the node table does not already keep (one that is not canonical) goes once per insert into one
list, `Table::keep`, which lives to the scope's end, so no node built later takes an address a memo key holds. Entries
shrink from 40 to 32 bytes (`inst`, `shifts`) and 32 to 24 (`uses`), and a hit or insert no longer touches the source's
count.
- Check: `memo_sources_outlive_their_callers`, which fails when `pin` keeps nothing (a node built after the caller drops
  its source takes the address and inherits the entry).
- Against 9fab09a, 24 alternating pairs of `proof_cost_split` cmp3d own: won 16, summed CPU 138.8 against 141.0 s (2%
  less), best 4.97 against 5.05 s; load 7-12%, Defender RTP off. Small, but the entries are smaller and the code no
  simpler or more complex, so it stays.
- Sequential pair (`scripts/slim_seq.sh`, rows `sls_*`): every file identical on both salts, apart from the
  elapsed-seconds columns.
- `ShiftMemo` (the builders' local shift memo) still keeps source and result pairs; it is outside the table and its
  scope.

**Profile after the two table changes (samply, 2026-10-13).** Same run as "Where the node table's time goes", at 849bf22
(profile not kept; `scripts/prof_callers.py`): 5221 busy samples against 5870, load 4%.

| | 1f4db8b | 849bf22 | 0fdd223 (after the `uses` slot) |
|---|---|---|---|
| `hc::intern` (from `inst_rec`) | 34.4% (22.3%) | 30.9% (18.8%) | 33.2% (20.4%) |
| its own lookup (`intern_as` closure, self) | 18.0% | 18.1% | 17.4% |
| growth, all tables (node table) | 9.6% (3.2%) | 7.1% (1.1%) | 5.7% (1.0%) |
| `inst_get` (self) | 8.6% | 9.8% | 10.2% (9.0%) |
| freeing the table at the scope's end | 5.9% | 6.3% | 6.7% |
| `hc::uses` | | | 2.1% |

The 0fdd223 column (`scripts/prof_callers.py` and `scripts/prof_self.py`) has 6372 busy samples at 28% machine load,
so compare its shares, not its counts. The `uses` walk is down to 2.1%, and the two table probes are now 26% of busy
samples on their own (node table 17.4%, `inst` 9.0%). The next largest self times are `drop_glue` 5.7%, `intern`'s
own body 5.3%, `height_at_most` 2.8% (the instantiation memo's small-node test), `args_id` 2.7% and `key_of` 2.3%.

The lookup's own time did not shrink: a hit still reads the candidate node, at a random address, to compare it and
bump its count, so the cost is that one miss per hit rather than the table's size. Growth fell by a quarter, most of it
the node table's. Freeing the table is now mostly dropping its nodes (`Rc::drop_slow` 4.3%), not its arrays.

**Rebuilt nodes equal to their source (negative, 2026-10-13).** Probe (reverted, no patch kept) of the node-table
interns `inst_rec` makes, same run at f73a52e:

| Nodes | Interns | Found in the table | Result is the source node itself |
|---|---|---|---|
| small (no memo, height ≤ 2) | 5.49 M | 90% | 1.15 M (21%) |
| memoized | 3.28 M | 52% | 204 |

`Table::keep` stayed empty: every memo source was canonical. The 1.15 M can be recognized without a probe: when the
rebuilt node has its source's key and the source is canonical, the table's node is the source. `hc::intern_from`
(reverted, no patch kept) did that. Against f73a52e, 24 alternating pairs: won 8, summed CPU 134.2 against 126.2 s,
median pair +0.07 s. The probe it saves lands on the source, which the walk has just read and is cached, so it was cheap;
the key comparison costs on every intern.

**A per-scope arena for the table's nodes (survey, not viable, 2026-10-13).** Freeing the table is 6% of the profile;
an arena freed in bulk would skip touching each node. Probe (reverted, no patch kept), same run: the one outermost scope
interned 3.17 M nodes, and 0.49 M of them (16%) were still alive after its table dropped, held by the proofs, types and
caches the scope returned. Those are ordinary `Rc`s pointing into the scope's memory, so the arena could not be freed
while any is alive, and they cannot be moved. Dropping the table took 270 ms of the 6 s run. Also ruled out: dropping
it on another thread (`Rc` is not `Send`) and keeping it across scopes (under 1%, above). Fewer nodes interned is the
only way left to shrink it.

**Who looks up what, and how much a one-entry slot per node would catch (probes, reverted, no patch kept,
2026-10-13).** Same run at 35efc0f.
- The builders (`app`, `pi`, `lam` and the rest) interned 7.67 M terms, all with the table on, and 7.09 M (92%) were
  already there (0.74 M of those leaves). They take `Expr` by value, so a term the caller already holds as a node is
  rebuilt and found again. That is 41% of all node-table lookups, though only 7% of busy samples, since a found node
  was usually built moments before and is cached.
- `inst_get`: 0.86 M of its 5.91 M lookups (15%) use an argument-list id with no entry yet and so cannot hit. Skipping
  them would save at most about 1.4% of busy samples (parked: too small for the per-id flag it needs).
- A one-entry memo slot per node (the key of that node's previous lookup in the same table):

  | Table | Lookups | Hits | Hits the slot would also give |
  |---|---|---|---|
  | `inst` | 5.91 M | 2.63 M | 0.61 M (23%) |
  | `shifts` | 1.67 M | 1.03 M | 0.67 M (66%) |
  | `uses` | 8.52 M | 7.93 M | 7.03 M (89%) |
  | `InferCache.types` | 3.61 M | 1.91 M | 1.47 M (77%) |

Two unifying mechanisms follow (the first is built in the next section; the second is sized and parked two sections down):
- **Pure per-node facts in the node.** `loose` and `free` already live in the node header; `uses(x, d, m)` is a finer
  fact of the same kind and never changes. A slot for it fits the header's 4 padding bytes (no larger nodes), needs
  no generation tag, no keep-alive and no pointer-keyed table, and would answer 7.0 M of the 8.5 M lookups from a node
  the walk is already reading. It does not fit facts that are nodes themselves: a `shifts` or `infer` slot holding a
  result `Rc` makes reference cycles possible (a shift by +1 and back), and the infer cache also lives per call.
- **Canonical handles end to end.** Builders and their callers keep terms as interned nodes rather than `Expr`
  values, so a term already built is passed on, not rebuilt. It would remove most of the builders' 7.1 M re-finds,
  `canonical_inputs`' interning on entry and `args_id`'s interning of non-canonical arguments, but it changes the
  builder interface across `crates/church-bv`.

**Per-node facts in the node header (2026-10-13).** Each node keeps its last `hc::uses(x, d, m)` answer in a `Cell<u32>`
that fills the header's former padding (`Node<Expr>` stays `Expr` + 16 bytes): the query (d and m below 2^15) and the
bit, packed by `Rc::uses_slot`. `uses` answers from the slot before walking and writes the slot after. Check:
`uses_slot_is_free_and_agrees_with_the_walk`. `proof_cost_split` cmp3d own CPU, alternating pairs, Defender off:
- Slot plus the per-scope `uses` table behind it, against 7fe880f: 24 pairs, won 16, summed 122.6 against 127.2 s, best
  4.38 against 4.53 s.
- Slot alone (the table switched off by a temporary `USESNOTABLE` knob) against slot plus table: 12 pairs, won 8,
  summed 54.2 against 55.2 s, best 4.27 against 4.44 s.

So the `uses` table, its `pin` and the knob are deleted; a slot miss walks. (Since 2026-10-14 a miss goes to a per-scope
table of bounds instead, keyed by (node, d) rather than (node, d, m): "The slot in front of bounds".) Sequential sweep pair (rows `uss_*`, script
`uslot_seq.sh`): identical outputs on both salts. The slot can't hold `shifts` or `infer` results, which are nodes
(above).

**How many builder inputs the caller already holds (probe, reverted, no patch kept, 2026-10-13).** Sizes "canonical
handles end to end". `#[track_caller]` on the builders and `hc::intern_new`, counting node-table interns and hits per
call site, and `apps` tagging its first application, later ones, and the argument side. Same run at ec49e4c:
`intern_new` interned 9.36 M terms with the table on, 8.63 M of them found.

| Where | Hits | What is found again |
|---|---|---|
| `apps`: its head and every argument | 2.34 M (of 2.36 M) | held: `Expr` values the caller keeps (`Gb::go`'s `x.g`, `x.e`, the lemma heads) |
| `apps`: each later prefix `f a1 .. ai` | 1.28 M (of 1.52 M) | rebuilt: the same spine built again |
| `and`/`or`/`xor` (`app2` of a constant) | 1.23 M | about 3/4 held (the constant and the two operands), 1/4 the rebuilt prefix |
| `shift_memo_child`'s result | 0.98 M | rebuilt: a shift that equals an existing node |
| `arrow` | 0.47 M | about half held (the domain), half the shifted codomain |
| `infer_rc`'s `Pi`, `Refl` and `J` types | 0.71 M | mostly held: `(**a).clone()` of the term's own children |
| other sites | about 1.6 M | not classified |

So about 4 M of the 8.6 M hits (45-50%) are inputs the caller already held as a term; about 2.8 M are rebuilt terms,
which handles would not remove. The builders were about 7% of busy samples for 7.1 M finds (above), and a held input's
find lands on a node just read, so canonical handles would save at most about 3.5%, less in practice. Most of the held
inputs come through a few places: `apps` (callers pass `Vec<Expr>`), the `and`/`or`/`xor` wrappers, `arrow`, and
`infer_rc`. Parked: at most about 3.5% for a builder-interface change across `crates/church-bv`.

**Two shift memos (probe, reverted, no patch kept, 2026-10-13).** Of the 2.8 M rebuilt terms, 0.98 M are
`shift_memo_child` results. `postulates`' `cong1`, `trans_proof` and `cong_n` shift through a `ShiftMemo` that lives
for one call. It never reads or writes hc's per-scope `shifts` table, which `shift_child` uses. Same run at 0fdd223:
`ShiftMemo` hit 0.34 M times and missed 1.03 M times, every miss inside an interning scope. hc's table already held
the answer for 0.40 M of the misses (39%), the same node each time, although `ShiftMemo`'s own results are never
added to it. One shift memo, hc's table with `ShiftMemo` deleted, would take all of these. The question was whether
anything shifts large shared terms through `cong_n` outside a scope, where hc's table is off. There a shift without
`ShiftMemo` would walk every path of the shared term. It does: `crates/tatic/src/proof` builds its `cong_n` and `trans_proof`
chains with no scope open, and that is where `ShiftMemo` made the proof DAG 5x smaller (7f78291).

**One shift memo (2026-10-13).** `cong1`, `trans_proof` and `cong_n` now each open an `InternScope` and shift through
hc's `shifts` table. Inside a scope this costs a depth count. Outside one it gives the call its own table, the same
per-call sharing `ShiftMemo` gave. `ShiftMemo`, `shift_memo`, `shift_memo_child`, `cong1_in`, `trans_proof_in` and
the test `shift_memo_matches_shift` are deleted. New check: `cong_n_shares_shifted_copies_outside_a_scope`, which
builds `cong_n` over a 2^20-leaf DAG outside a scope; with the scopes removed it fails after 12 s. `proof_cost_split`
cmp3d own CPU against ff3eb86, two runs of 24 alternating pairs, both under other load:
- Run 1: won 16, median pair -0.06 s; summed 125.7 against 120.1 s, from four pairs inflated by load, one at 10.1 s.
- Run 2: won 12, median -0.005 s, summed 141.8 against 153.9 s.

Neutral in speed; kept as one memo instead of two. Sequential sweep pair (rows `sms_*`, script `smemo_seq.sh`):
identical outputs on both salts.

**Why the table lookups stay at a quarter of the profile: `whnf` repeats across `def_eq` calls (survey and probe,
reverted, no patch kept, 2026-10-13).** The node-table and `inst` lookups (17.4% and 9.0% self at 0fdd223) cost one
cache miss per hit (above), so only fewer lookups would shrink them. `instantiate_n` is 55% of busy samples, and
46.8% of it is `beta_spine` under `whnf_step`. `whnf` is a pure function of the node: it unfolds no constants and
reads no context. Yet its memo, `ReductionCache.whnf`, lives for one `def_eq` (or `whnf`, `nf`) call. Probe of
`whnf_rc` in the same run at 0064aa7:

| | Count | Time |
|---|---|---|
| `whnf_rc` cache misses (work done) | 1.09 M | |
| misses on a node already reduced earlier in the same interning scope | 0.86 M (79%) | |
| outermost misses (all time under `whnf_rc`) | | 3.95 s |
| repeats not nested in another repeat | | 0.83 s (21%) |
| outermost misses that reduce, and the repeats among them | 189 K, 93 K | |

The probe's timers ran about 1 M times and add overhead; an earlier run without the nested-repeat count gave 2.08 s
outermost. Most repeats are cheap, stuck terms. The repeats that reduce carry the time: about a fifth of `whnf`'s
time, so at most about 10% of busy samples. A per-scope `whnf` memo would catch them, kept like `inst` and `shifts`:
keyed by node in hc's table, results kept alive by `pin`. The result is a node, so it can't go in the header (cycles,
above). Following "one shift memo", `ReductionCache.whnf` could then be deleted for the table, with `def_eq`, `whnf`
and `nf` opening a scope of their own. (Built in the next section.) The other sources of lookups were sized above: the
builders' held inputs (at most about 3.5%) and `inst_get`'s argument lists with no entries yet (at most about 1.4%).
The `apps` prefixes (1.28 M finds, "How many builder inputs the caller
already holds") have no memo to share: the same spine is rebuilt from held arguments, which only canonical handles or a memo keyed by the caller would avoid.

**Weak head normal forms kept for the scope (2026-10-13).** While the table is on, `whnf_rc` reads and writes hc's
new `whnf` map (node -> its weak head normal form, sources kept alive by `pin`) instead of `ReductionCache.whnf`,
which now serves only calls with the table off. Check: `whnf_memo_outlives_one_def_eq_in_a_scope`, which fails with
the table path disabled. `proof_cost_split` cmp3d own CPU against 3892f3d, 24 alternating pairs, load 15%: won 17,
median pair -0.20 s, best 4.39 against 4.66 s. Summed 122.5 against 136.7 s, but one pair alone accounts for 6.2 s
of that. Sequential sweep pair (rows `whs_*`, script `whnf_seq.sh`): identical outputs on both salts.

**`conv` repeats pairs across `def_eq` calls (probe, reverted, no patch kept, 2026-10-13).** `conv_rc(a, b)` is pure
too: its result is whether `nf(a) == nf(b)`. Same run at 3892f3d, interning on:

| | Count | Time |
|---|---|---|
| `def_eq` calls | 1.88 M | 3.58 s in all |
| `conv_rc` comparisons (pointer-unequal) | 215 K | |
| pairs already compared earlier in the scope | 112 K (52%) | 1.88 s, counted where not nested in another repeat |
| `eq_noting`'s `unequal` notes | 193 K | |
| notes on a pair already met in the scope | 60 K (31%) | |
| `nf_rc` misses | 0 | |

A per-scope memo from pair to result (with `unequal` folded in) would answer those repeats without reducing either
side: at most about half of `def_eq` time. It would also cover much of what the `whnf` memo saves, so measure it
against the `whnf` build. `nf` does not run in this workload; its cache stays per call.

**Built and measured against f77238e (both reverted, no patch kept, 2026-10-13): neutral.** `proof_cost_split` cmp3d
own CPU, 24 alternating pairs each, Defender RTP off, about 12-16% other CPU load at the start:

| Variant | Won | Median pair | Best new / old |
|---|---|---|---|
| unordered node pair -> result in hc's table, read and written by `conv_rc` while the table is on | 10 of 23 | +0.08 s | 4.61 / 4.66 s |
| no memo; `conv_rc` skips `==` and the `unequal` note when both sides are canonical (distinct canonical nodes are structurally unequal) | 10 of 24 | +0.01 s | 4.80 / 4.80 s |

The first variant passed a check that a `def_eq` answer stays in the table for the scope and is gone without the memo;
the probe's 1.88 s was timed with its own timers on (inflated, as in the `whnf` probe), and after the `whnf` memo a
repeated pair costs only its walk over memoized weak head normal forms. Folding `unequal` into the table is moot: while
the table is on, canonicity already answers `==` for the pairs it would hold, and skipping it saved nothing measurable.
Closed.

**Profile at 8334948 (= f77238e's code; samply of `proof_cost_split` cmp3d own, profile not kept, 2026-10-13).** 9656
busy samples; about 11% other CPU load, Defender RTP off. Little moved after the `whnf` memo:

| Share of busy samples | 0fdd223 | 8334948 |
|---|---|---|
| `instantiate_n` inclusive | 55% | 54.4% |
| ... under `beta_spine` (from `whnf_step`) | 46.8% | 44.3% |
| ... under `infer_node` | | 8.4% |
| `whnf_rc` inclusive, all from `conv_rc` | | 35.0% |
| node-table lookup (`intern_as`'s closure), self | 17.4% | 16.4% |
| `inst_get`, self | 9.0% | 7.1% |
| `hc::intern` callers: `inst_rec` / `app` / `app2` / `shift_child` | | 19.7 / 4.6 / 2.5 / 2.1% |

Where the lookup's self time goes, by sampled instruction (`prof_addr.py` plus `llvm-objdump`; samples land on
the instruction after the one that waited): 29% just after the indirect call that fetches the thread-local `TABLE`
(its lazy-initialization accessor) and the copy of the moved `Expr` out of the closure; 18% on the probed slot's stored
hash and 12% on the group of control bytes (cache misses on the table itself); 8% writing a new entry; 4% building a
new node. Comparing a candidate's key (reading the candidate node) is not among the hot spots: the stored hash filters
almost every mismatch. So about a third of the lookup is memory latency inherent in a table this size, and about a
third is call overhead around it. Leads: a `const`-initialized `TABLE` (no lazy accessor; hashbrown's tables and the
default hasher can be made in a `const`), and interning without moving the `Expr` through the closure. At most about 5%
of busy samples between them.

**Both built (2026-10-13): `TABLE` is `const`-initialized (`Table::new`; `arg_sets` moved to the pointer hasher, whose
ids come from insertion order, not the hash), and `intern_as` looks up under a shared borrow that captures only the key,
moving `e` once into `build` on a miss and inserting under a second borrow.** `proof_cost_split` cmp3d own CPU against
8334948, two runs of 24 alternating pairs, Defender RTP off, about 12% other CPU load at the start: won 14 (median pair
-0.06 s, best 4.61 against 4.61 s) and 16 (median -0.12 s, best 4.81 against 4.98 s). A small win, about 1-2.5%, less
than the 5% ceiling. Sequential sweep pair (rows `cts_*`, script `ctab_seq.sh`): identical outputs on both salts.

**Fewer substitutions: what was tried before (survey, no code, 2026-10-13).** `beta_spine` -> `instantiate_n` is 44% of
busy samples. Doing fewer substitutions rather than cheaper ones was explored on 2026-09-30 (the git-ignored
`docs/superpowers/specs/2026-09-30-bitvector-interface-design.md` §25-§35, and `src/kernel_lazy.rs`, deleted in 306a968): a closure-based
(call-by-need, Rocq-style) `def_eq` was 13-25x slower without sharing, 8-18x with a pointer-keyed memo, and level with
the kernel from n = 32 once it memoized closed nodes only; it took 467x the kernel's beta steps (each one cheap), so a
step-certificate kernel was dropped. That comparison predates hash-consing, the per-scope instantiation and `whnf`
memos and n-ary `beta_spine`, each of which made the substituting kernel faster, so the lazy evaluator likely trails it
now (not re-measured). What has not been measured is how much of what `instantiate_n` builds is ever read: `conv` reduces only where the
sides differ, so a built subterm that no later `whnf`, `conv` or `infer` visits is pure cost, and only that share is
what laziness (building on demand) could save.

**How much of what `instantiate_n` builds is read (probe, reverted, no patch kept, 2026-10-13).** At 7643319, one
`proof_cost_split` cmp3d own run with a flag byte in the node header: set when `inst_rec` interns a new node, when the
checker reads a node (`whnf_rc`, `conv_rc` on a pointer-unequal pair, `eq_noting` recursing into a non-canonical pair,
`nf_rc`, `infer_rc`, `beta_spine`'s spine walk), and when `inst_rec` or `shift_child` recurses into it. Tallied over
every node in the table at each outermost scope drop:

| | Count |
|---|---|
| nodes in the tables at their drops | 3.17 M |
| `inst_rec` interns | 8.56 M: 2.16 M new nodes, 6.40 M (75%) already in the table |
| new nodes later read by the checker | 0.95 M (44%) |
| ... read only by a later instantiation or shift | 0.27 M (12%) |
| ... never read | 0.94 M (44%) |
| instantiation memo (`inst_get`) lookups | 5.23 M, 1.95 M hits (37%) |
| children skipped by the `uses` shortcut (shifted instead) | 0.44 M |
| children below the memo's height cutoff (not memoized) | 5.28 M |

So more than half of the new nodes instantiation builds are never looked at by the checker, and three quarters of
what it rebuilds already existed. A delayed substitution (a node holding body, argument set and depth, forced when
`whnf`, `conv` or `infer` first reads it) could skip the unread half, but it is a new trusted constructor that every
reader must force, and new nodes are only a quarter of the interns; the saving is bounded by about half of
instantiation's 44% of busy samples, less the forcing overhead. Open: lead, not built.

**The instantiation memo still pays after the `whnf` memo (2026-10-13).** `go` with `memo` forced to false (reverted, no
patch kept) against 7643319, 24 alternating pairs, Defender RTP off: lost all 24, median pair +0.44 s, best 4.89 against
4.45 s (about 9% slower). Kept.

**The instantiation memo keyed by the arguments a child uses: neutral (reverted, no patch kept, 2026-10-13).** A child
whose loose variables reach only the last `j < m` arguments instantiates the same under any list ending in those `j`, so
`inst_rec` keyed it by that suffix's `args_id` (made once per `instantiate_n` call and suffix length, up to 8) instead
of the whole list's. It did what it was meant to: memo lookups fell from 5.23 M to 4.19 M (hits found higher in the
tree), hits rose from 37% to 41%, and 1.76 M lookups used a suffix key, hitting 52%. But `proof_cost_split` cmp3d own
CPU against 136bbe5, two runs of 24 alternating pairs: won 11 (median pair +0.005 s, best 4.70 against 4.69 s; about
28% other load at the start) and 10 (median +0.035 s, best 4.80 against 4.86 s; about 14%). The rebuilds it avoids
were cheap ones. Kept from it: `instantiate_n_matches_sequential_substitution_in_a_scope`, which checks
`instantiate_n` against one `subst_top` per argument inside one scope with arguments from a small pool, so the memo
answers across lists; it fails when the memo key ignores the argument list.

**Design note: delayed substitution (no code, 2026-10-13).** The question was whether `instantiate_n` could build a
child only when something reads it (the 44% of new nodes no one reads, above). Two shapes:

| | A: a new constructor `Subst(body, args, d)` | B: a node whose value is computed on first `Deref` |
|---|---|---|
| Readers | every `match` on `Expr` gains an arm that forces (238 `Expr::` uses in `kernel.rs`, 204 in its tests, 78 in `kernel_soundness_fuzz.rs`); exhaustive matches make the compiler list them, but any of the 10 `_ =>` arms in `kernel.rs` that match an `Expr` would take `Subst` silently | none change: the kernel's `Rc::deref` forces |
| Cost on every read | only where `Subst` is matched | a check on every `Deref` of every node, the kernel's hottest path |
| Missed force | through a `_ =>` arm: a wrong shape, so `same_shape` answers unequal and `infer` errors; incomplete rather than unsound only if each such arm is audited | impossible, but the suspension and its value have different addresses, so address-keyed memos see two nodes |
| Header (`loose`, `free`) | must be known unforced: an upper bound from the body and the arguments is safe (it only skips less) | the same |

Both lose to hash-consing, which is what the kernel's speed now rests on. A node is canonical only if everything under it
was interned; a suspension can't be interned (its children are unknown until forced), so every term holding one is
non-canonical. That turns off the pointer shortcuts for all its ancestors: `==` and `eq_noting` compare canonical
pairs by address and stop, `conv_rc` and the per-scope memos key by address, and the 75% of instantiation interns that
find an existing node are the sharing that lets later comparisons stop at an address. Forcing could intern the result
only by forcing all of its children too, which is eager substitution again. The closure-based evaluator was measured on
2026-09-30, level with a kernel that had none of today's tables (hash-consing came on 2026-10-01).

The saving is also smaller than the 44% suggests. Unread new nodes are 0.94 M of 8.56 M instantiation interns (11%), and
each suspension left at the frontier still costs an allocation and a memo lookup, likely close to what building the node
costs (not measured).
If unread table hits were as common as unread new nodes, the bound would be about 44% of instantiation's 44% of busy
samples (about 20%); counting new nodes only, about 5%. That is before the losses above. Parked. Gate to reopen: a
probe weighting each `inst_rec` result (new or found) by the work below it and counting how much of that work is never
read by the checker in the same scope; reopen only if it is over about 15% of busy samples, and then prototype B
behind a feature with `kernel_soundness_fuzz` and the scoped `instantiate_n` test as the checks.

**What `conv` reduces, and the type checker's own substitution (probe, reverted, no patch kept, 2026-10-13).** The
profile at 8334948, by caller: `whnf_rc`'s 35.0% of busy samples is all `check_rc` -> `def_eq` -> `conv_rc` (34.0%
through `def_eq` from `check_rc`, 1.5% through `same_shape`), and 34.1 of `beta_spine`'s 44.3 points are inside it, so
the two leads above are mostly one cost. The other `instantiate_n` caller is `infer_node`'s `App` rule (`subst_top(cod,
a)`, 8.4%). One `proof_cost_split` cmp3d own run at a73c6a1 with thread-local counters (`inst_rec` and `shift_via`
visits; each pair `conv` or `conv_rc` reduces, classed by which side `whnf` changed; the `App` rule's calls):

| Pairs reaching `whnf` | Pairs | `inst_rec` visits in their `whnf` |
|---|---|---|
| all (`conv` at the top: inferred against expected) | 113 k | 1.81 M |
| all (`conv_rc`, below the top) | 327 k | 8.16 M |
| only the first side reduces | 52 k | 0.16 M |
| only the second side reduces | 83 k | 0.95 M |
| both sides reduce | 148 k | 8.86 M (89%) |
| neither reduces | 157 k | 0 |
| same head (pointer or `==`) and arity | 20 k | 0.68 M (7%) |
| ... arguments pairwise convertible | 8 k | 0.20 M (2%) |

Comparing heads before reducing does not pay: same-head pairs carry 7% of the reduction work, the argument check
succeeds for under half of them, saving 0.20 M visits, and the argument checks themselves cost 1.17 M visits. Not built.
The work is in pairs where both sides are redexes with different heads.

The `App` rule: 1.27 M calls, all with the table on. In 1.05 M (83%) `cod` is closed and comes back as is; in 142 k it
has loose variables but not `Var(0)`, so it is only shifted (0.28 M shift visits); the rest use the argument. In all,
0.65 M `inst_rec` visits and 0.44 M shift visits, against about 10 M under `conv`'s reductions. 0.87 M of the calls
(69%) are on an `App` spine, but substituting a spine's arguments at once could only save the repeated walks of the
non-closed codomains, a small part of the 8.4%. Not built.

**The pairs where both sides reduce are equal redexes with different lambdas (probe, reverted, no patch kept,
2026-10-13).** The same run at 4bad241 without the argument checks (which had added pairs of their own above), counting
only pairs where `whnf` changed both sides, in `conv` and `conv_rc`:

| Both sides reduce | Pairs | `inst_rec` visits in their `whnf` |
|---|---|---|
| all (of 10.29 M in the run) | 124 k | 8.52 M |
| results `==` (never the same pointer) | 90 k | 7.13 M |
| results with the same constructor, not `==` | 33 k | 1.39 M |
| results with different constructors | 0 | 0 |
| `conv` answers equal | 124 k (all) | 8.52 M |
| both heads are a literal `Lam` | 124 k (all) | |
| heads `==` | 5 k | |

So the bulk of the reduction work goes into showing that two applications of different lambdas, `(\x. s) a` against
`(\y. t) b`, are equal, and in 73% of the pairs both reduce to the same term. The results are never pointer-equal
because `whnf_rc` wraps the reduct's top node in `Rc::new` rather than interning it (its children are interned). Where these redexes come
from is answered below (`lemma_n`'s case-tree leaves), and interning the reduct is measured below (neutral).

**Where those redexes come from: `lemma_n`'s case-tree leaves, each a different computation (probe, reverted, no patch
kept, 2026-10-13).** The same run at 3e7e019, with each pair where both sides reduce charged to the `App` rule whose argument
check it fell under (keyed by the spine heads of the function and the argument), and counted again by structure (a
hash over each side's tree) across the whole run:

| Function <- argument | Pairs | Visits | Structurally new pairs |
|---|---|---|---|
| `Var` with 1 argument <- `Refl` | 32.8 k | 4.13 M | 30.3 k (all the visits) |
| `Var` with 2 arguments <- `Refl` | 32.8 k | 3.28 M | 30.3 k (all the visits) |
| `Var` with 1 or 2 arguments <- `Var` with 3 (top-level pairs) | 34.9 k | 0.95 M | 33.1 k |
| `J` <- `J` | 20.7 k | 0.16 M | 6.1 k (all the visits) |

The first two rows are the leaves of case trees: at each split, `g motive on_true on_false` with `g : GoodBool b`
eliminating a bit, and `refl` at a leaf. Checking a leaf `refl(a)` against the motive at that leaf's bits reduces both
sides: the motive `(\b. body) bit` on the expected side, and on the inferred side `a`, a gate term written as
Church-encoded lambdas applied to bits. A first reading charged them to `bit_lemma`, which has the same shape, but a
count of builder calls in the same run (temporary prints, reverted) found `bit_lemma` called 0 times and `lemma_n` (`crates/church-bv/src/encoding.rs`) 392 times:

| Case bits `k` | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 9 |
|---|---|---|---|---|---|---|---|---|---|
| trees | 4 | 2 | 14 | 19 | 83 | 46 | 30 | 182 | 12 |
| leaves (`2^k` each) | 4 | 4 | 56 | 152 | 1328 | 1472 | 1920 | 23296 | 6144 |

34.4 k leaves in all, matching the 32.8 k leaf checks per row above. Most are `machine.rs`'s `guarded` trees over the
`k + c` operand and carry bits, one per side, tag (`F0..Fm`, `P`, `D`) and encoding, each memoized by `shared_lemma`
and checked once per process. Every pair is structurally new across the run, and repeats within a scope already cost
nothing (the memos answer them).

A memo spanning scopes would find nothing either. A count of every `whnf_rc` miss with the table on (a structural hash
of the term, kept for the whole run) found 227 k misses, 7.74 M `inst_rec` visits under the outermost ones, and none
structurally repeated, closed or not. The trees for `F0..Fm` of one side evaluate the same step at the same bits, but
`beta_spine` instantiates each leaf's body whole, so no reduction is shared at `whnf`'s granularity.

So 72% of the reduction work under `conv` is the kernel evaluating gate terms on concrete bits, once per leaf. It is
the proof by computation itself, not a redundancy, and a kernel memo cannot remove it. Only fewer or smaller leaves
(fewer case bits; decision diagrams lost to the case tree at `nv` = 9 and 11, "Decision diagrams deleted"), leaves
whose sides the builder states already evaluated, or a cheaper evaluation per visit can.

**Leaves stated evaluated, or one tree per side: neither pays (probes, reverted, no patch kept, 2026-10-13).** Two
builder changes were surveyed against the leaf work above, at cacb94b.

*A leaf whose sides are already evaluated.* A leaf proves `refl(a) : Id(a, a)` against the statement at its bits,
`Id(a', b')`. A counter in `check_rc` after each successful check of a `Refl` (about 50 k, sampled every 5000) found `a`
pointer-equal to `a'` in all of them, and `a` structurally equal to `b'` in 32%. So `conv` evaluates `a` and `b'`, and
nothing in that 32%. A leaf `refl(v)` with the value `v` written by the builder would need `a'` and `b'` evaluated against
`v`: the same two evaluations, and more work in the 32%. No gain.

*One tree per side for all its `F_j`.* Temporary prints in `guarded` (`machine.rs`) for the same run:

| Tag | Trees | Leaves |
|---|---|---|
| `F1..Fm` | 291 | 32 662 (96%) |
| `D` | 66 | 968 |
| `F0` | 25 | 550 |
| `P` (no invariant here) | 0 | 0 |

Mostly four `F_j` trees of 7 bits per side (47, 47, 47 and 40 of them). One tree proving the four equalities at once
would keep every leaf evaluation (each `F_j` is a different function of the step, and no `whnf` repeats structurally
across the run, above) and save only the splits: the pairs charged to `Var` <- `Var` with 3 arguments above, 0.95 M of
10.29 M visits, about three quarters of which would go. That is at most about 7% of the reduction work, for leaves that
are conjunctions (a `Sigma` of four `Id`s and its pairs, with their own checking cost). Parked: not worth the change to
the proof format unless the split cost grows.

*Which side the evaluation is on.* `conv_rc`'s two `whnf_rc` calls counted apart (probe, reverted, no patch kept): of
7.74 M `inst_rec` visits, 4.22 M (54%) under the first side's (the inferred one: a leaf's step term) and 3.52 M (46%)
under the second's (the statement: `G_j` as a table over the bits). Neither dominates, so a cheaper table encoding
could save at most the second side's share, and only the part of it that is the table rather than the shared shape.

**The table sized for the last scope: neutral (reverted, no patch kept, 2026-10-13).** Rehashing is 8.4% of busy
samples in the profile at 4bad241 counting callers (5.5% under `inst_rec` and `instantiate_n`, 1.1% under `infer_rc`'s
cache). The prototype merged the table's three switch-on sites into one that reserved the node, instantiation, shift
and `whnf` maps for the sizes the last scope with the table on ended with. `proof_cost_split` cmp3d own CPU against
3e7e019, Defender RTP off, three runs of 24 alternating pairs: won 16 (median pair -0.21 s, best 4.81 against 4.88 s),
6 (median +0.05 s, best 5.28 against 5.09 s; about 74% other load at the end) and 14 (median -0.015 s, best 4.97 against
5.05 s; about 37%). 36 of 72 in all. A likely reason (not measured): scopes differ too much in size for the last one to
predict the next, so a small scope pays to clear a large reservation, and a large one after a small one rehashes as
before.

**Interning the reduct's top node in `whnf_rc`: neutral (reverted, no patch kept, 2026-10-13).** With the table on,
`whnf_rc` interned the reduced term (`hc::intern(r, None)` in place of `Rc::new`), so equal reducts are one node.
`proof_cost_split` cmp3d own CPU against 3e7e019, Defender RTP off, two runs of 24 alternating pairs: won 9 (median
pair +0.015 s, best 4.80 against 4.80 s; three new runs took 10.7-11.3 s, both phases about 2.4x slower) and 10
(median +0.11 s, best 4.89 against 4.80 s; runs over 8 s in both builds, about 13% other load after). The slow runs
were load, not the change. The reducts are compared child by child at canonical pointers already, so making them one
node saves nothing.

**Profile at 4bad241 (samply, profile not kept, 2026-10-13).** `proof_cost_split` cmp3d own, CPU about 9% before the
run, Defender RTP off; 5031 busy samples (the run at 8334948 had 9656; shares compared, not counts). `instantiate_n`
55.4% (46.8% under `beta_spine`, 7.3% under `infer_node`); `conv_rc` 39.3%, all from `check_rc` -> `def_eq`, with
`whnf_rc` 38.9% and `beta_spine` 38.1% inside it; `hc::intern` 30.3% (19.3% from `inst_rec`). Leaves: `intern_as`'s
lookup 9.7%, `inst_get` 8.8%, rehashing 5.2%, `Rc::drop_slow` 4.4%. The const `TABLE` did not change the picture.

**Kernel speed-up thread: closed (2026-10-13).** Every lead that avoids work has been measured and closed above: the
head-first `conv` shortcut, interning `whnf`'s reduct, pre-sizing the table, any memo across scopes (no `whnf` miss
repeats), leaves stated evaluated, one tree per side (at most about 7%, parked), a cheaper table encoding (at most the
statement side's 46% of the leaf work, only in part), and delayed substitution (parked behind its gate). What remains is
the proof by computation itself: 72% of the reduction work under `conv` is gate terms evaluated on concrete bits, once
per case-tree leaf, and every such evaluation is distinct. Reopen only for a new proof shape (fewer leaves, for example
a symbolic per-gate lemma in place of `lemma_n`'s 2^k trees; "Decision diagrams deleted" and the parked closed
`cong_mux` lemma are the earlier attempts) or a cheaper evaluator (below).

