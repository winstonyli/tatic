### Kernel scaling and the id arena (2026-10-14)

**Closed function values are reduced once (kernel change, kept, 2026-10-14).** The n=48 wall above was unsharing
in `whnf`. A word's bit is a shared node such as `s = xor_ a b`, and each use applies it to its own continuations
(`s C X Y`). The whnf memos are keyed by node, and every application is a new node, so they never hit. `beta_spine`
also peeled past `s` to the gate constant at the bottom of the spine, so `s` was never a key either. Each bit was
evaluated again once per path that reached it. `sub` chains grew about 0.7n-fold per level (n=16: 1.5, 9.9, 69 and
407 ms at depth 1-4).

The mechanism is in `crates/tatic-kernel/src/subst.rs`, `hc.rs` and `reduce.rs`:
- `closed_prefix_spine` runs first for every `App` in `whnf_step`. It finds the longest proper prefix `P` of the
  spine with no loose variable, with `d` arguments left over.
- `hnf_rc(P, d)` is `P`'s head normal form to depth `d`: its whnf, then the body's whnf under each of up to `d`
  lambdas.
- The result is instantiated with the `d` arguments by `instantiate_n` and reduced on.
- `hnf_rc` is memoised by `(P, d)`, in the scope's `hc` table while it is on, else in the per-call
  `ReductionCache`. An application recurses on its function at depth `d + 1`, so `s` gets an entry at depth 3
  whichever prefix of `s C X Y` was asked for.
- Head reduction commutes with substitution, so this does no more reduction than the application would have done.
- Since 2026-10-15 the depth is gone: `hnf_rc(P)` reduces under every lambda and is memoised by `P` alone, so a Church
  boolean selects under its own `\C t f` and a table prefix drops the branches its arguments rule out ("Full head normal
  form", in "Where a sweep spends its time"). That can reduce more than the application would have.

Check: `closed_function_values_are_reduced_once` (`crates/tatic-kernel/src/tests/substitution.rs`). It builds
`b(i+1) = \C x y. b(i) C (b(i) C y x) (b(i) C x y)` to depth 30, both outside a scope and inside one. With
`closed_prefix_spine` disabled, depth 20 took 9.6 s for one `def_eq`, doubling per level. With it, the whole test
reports 0.00 s.

Results (machine at 15-46% CPU from other sessions, about 60% for the n=16 "before" row; Defender real-time
protection off):

| `sub^d(7) = 7-d` (`reduction_probe`, reverted) | before | after |
|---|---|---|
| n=16, d = 1, 2, 3, 4 | 1.5, 9.9, 69, 407 ms | 0.57, 0.27, 0.31, 0.38 ms |
| n=64, d = 1, 2, 3 | 17.5, 818 ms, over 4 GB | 1.7, 1.5, 1.6 ms (d = 4-6: 1.8-2.2 ms) |

| countdown from 3, fuel 4 (`control_flow_probe`, reverted) | n=16 | 32 | 48 | 64 |
|---|---|---|---|---|
| before (table above) | 0.24 s | 3.5 s | over 4 GB | over 4 GB |
| after | 2.7 ms | 8.0 ms | 9.2 ms | 14.8 ms |

Every concrete answer and every control in that probe came out as expected at n = 16, 32, 48 and 64. Rule transfer
on a regenerated 27-rule cmp3d ref library came out as before:
- 24 of 24 at n=4 in 0.84 s;
- 24 of 24 at n=64 in 30.6 s (27.7 s before, under other load; not an A/B);
- the NEG control 0 of 24 at n=4.

The NEG control at n=64 still went over 4 GB. Its words are symbolic: the bits are variables bound under the
probe's binders, so no prefix is closed.

`proof_cost_split` (cmp3d, 37-rule own library, 300 laws, `cpu_ab.ps1`, own CPU, 10 alternating pairs against
85daf95):
- new won all 10 pairs; best 4.19 against 5.16 s; median pair -1.15 s;
- summed rule-proof build time 27.9 against 40.6 s, and kernel check 6.5 against 6.0 s;
- an earlier build without the stuck-spine shortcut won 8 of 8 pairs;
- law counts, node counts and occurrences identical;
- peak working set about 654 against 607 MB.

`loop_stream` (ref, cmp3d) wrote identical rules, laws and `m.tsv`. The kernel lib tests (366) and church_bv's
tests (75) pass.

Tried and dropped: keying every prefix, open ones too, behind a throwaway switch. It was slower everywhere:
countdown at n=64 took 155-194 ms, and rule transfer at n=64 took 51.8 s. The n=64 NEG control still went over
4 GB. So that wall is not this unsharing (it is traced below, "The NEG control's wall was the error message").
`cpu_ab.ps1` reads `cmp3d_own_rules.txt` next to itself, and that file had never been committed. Salt 1's
`own_cmp3d_3_cmp3d/rules.txt` from the `cts_*` sweep was used for this run. That is 37 rules with no `winner  OVER
loser` preference lines, and every 2026-10-13 sweep (`sls`, `uss`, `sms`, `whs`, `cts`) wrote the same file. It is
now committed as `docs/runs/2026-10-12/scripts/cmp3d_own_rules.txt`. The older file that earlier rows used also
carried preference lines (the 2026-10-14 width probes above dropped them with `grep -v OVER`). `check_laws` reads
those preferences, so absolute times before this row may not match runs on the committed file. A/B pairs within
one run are unaffected.

Related, from memory and not re-checked: this is full laziness (sharing maximal free expressions, as in
Peyton Jones's "The Implementation of Functional Programming Languages", 1987) applied to the spine prefixes the
reducer meets, rather than by lambda lifting ahead of time. Rocq's `Zupdate` (section 77 of `docs/related-work/`)
shares an evaluated closure in a similar way.

**The NEG control's wall was the error message (kernel change, kept, 2026-10-14).** With the law replaced by
`refl`, `def_eq` rejects the two `lt` circuits quickly. What blew up was `check_rc`'s `type mismatch` message. It
printed `brief(&nf(inferred))` and `brief(&nf(expected))`, so it built two whole normal forms of 64-bit symbolic
circuits and then printed 400 characters of each.

How it was found:
- Rule 21 (`lt(add(x, y), sub(shl1(y, 0), z))`) was the slowest rule alone. It grew about n^3 in time and memory:
  0.05, 0.29, 1.03, 2.83 and 11.6 s, with peaks of 70, 133, 293, 639 and 2142 MB, at n = 8, 16, 24, 32 and 48.
  The positive check (the real law) took 0.9 s and 242 MB at n=48.
- A samply profile at n=32 put 81% of busy samples under `nf_rc`. Most stacks lost their callers past `grow`'s
  stack segments, and `conv` calls no `nf`. The only `nf` caller on this path is the message.
- Printing the raw terms instead brought rule 21 to 16 ms (n=32) and 19 ms (n=64), with peaks under 70 MB.

The fix is `brief_nf(e)`, a printer that normalizes as it prints:
- `Debug for Expr`'s single `match` became `write_expr`, generic over how children are printed.
- `brief_nf` whnfs each node through one `ReductionCache` when the printer reaches it.
- `brief`'s character limit stops the writer, so only the printed prefix is ever reduced.
- The text is the same as `brief(&nf(e))`. The wrec children-type message uses it too. The other `nf` callers
  are semantic (`infer_sup`'s occurs check, `typecheck`'s returned type, `normalize`) and stay as they were.

Check: `brief_nf_normalizes_only_what_it_prints` (`crates/tatic-kernel/src/tests/substitution.rs`). It compares the output with
`brief(&nf(..))` on three small terms, and prints the Church numeral `16 4`, whose normal form has 4^16 nested
applications. With `brief(&nf(e))` restored, the test went over 4 GB within 8 s.

After the fix, `control_flow_probe` on the 27-rule cmp3d ref library (machine at 14% CPU; Defender real-time
protection off):

| | n=4 | n=24 | n=64 |
|---|---|---|---|
| NEG control, 24 rules | 0/24, 0.32 s | 0/24, 0.42 s (24.6 s before) | 0/24, 0.58 s, peak 585 MB (over 4 GB before) |
| rule transfer, 24 rules | 24/24, 0.75 s | | 24/24, 26.5 s, peak 2.2 GB |

Rejecting is now about 45 times cheaper than accepting at n=64.

*The accepting side is the rule laws, not the transfer.* A probe (reverted, no patch kept) timed each rule's
phases. It used the committed 37-rule `cmp3d_own_rules.txt` (32 `lt` rules) rather than the ref library above,
with the machine at about 20% CPU and Defender real-time protection off. At n=64:

| | 32 rules, sum of checks |
|---|---|
| program proof with the rule law inlined (as above) | 46.9 s |
| the same proof with the law as a hypothesis of its type | 0.38 s |
| the laws checked alone | 43.8 s (32 of 32 hold) |

Proving the law (`prove_rule`) takes 0.03-1.6 s per rule, and building the program proof takes about 0.02 s. The
inlined law is 86-95% of each proof's unique nodes (rule 0 at n=64: 51,784 of 60,292). Unique nodes grow about
linearly in n (rule 0: 9,958 at n=8, 31,531 at n=32), but checking the inlined proof slows faster (rule 0: 33 ms at n=8,
0.24 s at n=32, 0.64 s at n=64). A samply profile of the inlined run at n=64 (profile not kept) puts it in type
inference: `check_rc` and `infer_rc` cover nearly all samples, `expect_pi` 13%, and `InferCache` rehashing 11%.
Freeing hash tables of per-call `ReductionCache`s (under `whnf` and `def_eq`) and `InferCache`s costs about 8%; which maps fill them was not checked.

So the transfer to compiled programs costs about as much as rejecting it: 0.86 s for 32 rules with the law as a
hypothesis (0.38 s of it checking), against the NEG control's 0.58 s for 24. The remaining cost is
checking each law, a cost per rule rather than per program. The mechanism for paying it once already exists and the
miner uses it: `shared_lemma` checks a law's proof once and returns a parameter whose type is the law's statement.
A proof that uses the law mentions the parameter, and the checker only looks up its type (`Plan::Law` with
`LawKind::Rule` goes through it). The probe called `prove_rule` directly and inlined the proof, so it paid for the
law in every check; its "law as a hypothesis" row is what `shared_lemma` gives. Every `Plan::Law` kind now goes
through it (see "Every law by name" below).

*Why checking a law slowed faster than it grew.* `infer_rc`'s memo missed about 20 times per node: rule 0 at n=64
had 1,036,365 misses for a 51,784-node proof, counted with a probe (reverted, no patch kept). There were two causes:
- The key (node, window of the innermost binders down to the node's highest loose variable) fell back to the whole
  context past `MAX_WINDOW` = 8 binders. A rule law nests about 6n per-bit binders (`k_var_law`), so 99.96% of
  misses were fallbacks. Removing the cap alone left 1,035,100 misses.
- `trans_proof`, `sym` and `cong1` (`postulates.rs`) build a J motive per use. Shared subterms of its endpoints then
  sit under that use's binders, which they never mention, so the window differs per use. The most-missed nodes were
  missed about 18n times each.

Fix: the window now starts at the node's lowest loose variable `lo`. The `lo` innermost binders are never looked up,
and the type mentions only positions at or above `lo`, so the answer is the same in any context that agrees above
`lo`. The key is (node, `lo`, window from the `lo`-th binder up), with no cap. Rule 0 at n=64 now has 59,195 misses
(about 1.1 per node), and every counter grows linearly in n. Check: `infer_memo_skips_unused_inner_binders`, where a shared
node sits under 30 nested binders, each with two types it never mentions. It passes in 0.29 s; before the fix it ran for
over a minute and then aborted on a 35 GB allocation. The laws checked alone (the probe above, three alternating pairs, machine
at about 11% CPU, Defender real-time protection off):

| | n=8 | n=16 | n=32 | n=64 |
|---|---|---|---|---|
| rule 0, before | 25 ms | 57 ms | 0.21 s | 0.71 s |
| rule 0, after | 23 ms | 54 ms | 0.11 s | 0.24 s |
| rule 33, before | 0.13 s | 0.37 s | 1.13 s | 3.9 s |
| rule 33, after | 0.10 s | 0.24 s | 0.54 s | 1.22 s |

Middle values of three. Time still grows 2.2-2.3 times per doubling of n, against linear unique nodes and misses,
so something outside the memo is still superlinear. On `proof_cost_split`, whose widths are
small, the change is neutral: 6 alternating `cpu_ab.ps1` pairs, median CPU 4.86 s before and 4.85 s after.

*What is still superlinear.* A samply profile of rule 33's law at n=64 (8 checks in one process, profile not kept;
machine at about 15% CPU, Defender real-time protection off) puts 18.8% of samples in `hc::lowest_loose`
(the memo key's `lo`) and 16% in `hc::uses` (called from `inst_rec`), with `hc::intern` at 10.5% and `infer_rc` at 8.1%. The first check
takes 1.25 s and each repeat about 0.49 s, since the node table's memos persist within the scope. Counted with a probe
(reverted, no patch kept), over n = 8, 16, 32, 64:
- `lowest_loose`'s (node, depth) memo entries per check grow linearly: 120k, 234k, 462k, 926k.
- `uses` walks (slot misses) grow 3.6-3.9 times per doubling from n=16: 1.16M, 1.13M, 4.06M, 15.3M on the first check, and
  0.16M, 0.59M, 2.28M, 8.95M on a repeat.

`uses(x, d, m)` is `lowest_loose(x, d) < m`, so the two can share one mechanism. A prototype (reverted, no patch kept) did that:
the node header's slot held (d, lowest loose variable) and replaced both the (d, m) slot and `InferCache`'s `lows` map.
It made repeats faster (0.43 to 0.25 s at n=64) but the first check slower (1.41 to 1.68 s, 64M walks). The single slot
thrashes between the memo key's depth-0 queries and `inst_rec`'s other depths, and repeat walks stayed at about 9M. Those
walks follow `inst_rec`'s own work, which is keyed by (node, depth): instantiating a shared node at each depth it occurs
under is the quadratic part, not the cache in front of it. A key that doesn't depend on depth (each node's set of loose
variables, computed once) would answer both queries without walking.

Two prototypes followed, both in a throwaway worktree; the second has since landed (below). Both were
timed with the probe above against 75e9ece, alternating runs, machine at 12-14% CPU, Defender real-time protection off.
- *Loose-variable bitsets, negative.* The node table mapped each node to a bitset of its loose variables, built once
  from its children. `uses` and `lowest_loose` became bit scans while the table is on. Repeat checks got faster (rule 33
  at n=64: 0.40 to 0.30 s) but first checks did not (1.17-1.27 to 1.30-1.34 s), and the process's CPU rose from 5.0 to
  5.3 s. The `uses` walks were not what made the first check slow.
- *Inferring an application spine at once, positive.* A samply profile of the first check alone (rule 33, n=64) has
  `hc::intern` at 17.4%, `inst_rec` at 17.2%, `uses` at 10.4%, the scope's drop at 10.3% and `shift_child` at 8.1%,
  with `infer_rc` at about 3%: instantiation, not inference. (Stacks are cut at `stacker::grow`, so callers above it
  can't be attributed.) `infer` typed `App(f, a)` as `subst_top(cod, a)`, so a spine `f a1 .. ak` copied the rest of
  `f`'s telescope once per argument. The prototype walks the spine, instantiates each domain with the arguments before
  it, and instantiates the codomain once with all of them (`instantiate_n`). If a codomain is not syntactically a Pi,
  it first instantiates the pending arguments and takes its weak head normal form. Results:
  - Rule 33 at n=64, first check: 1.39-1.41 to 0.78-0.87 s; rule 0 at n=64: 0.25-0.28 to 0.14-0.17 s.
  - The probe process's CPU: 5.7 to 4.1-4.3 s.
  - `proof_cost_split`: 6 of 6 alternating pairs won, check 500-570 to 339-385 ms, median CPU 4.16 to 3.95 s.
  - Kernel (368) and church_bv (75) tests pass.

  Rule 33's first check still grows about 2.3 times from n=32 to 64.

  Landed as the prototype was, in `infer_node`'s `App` case; the per-argument path is gone. Check:
  `infer_types_an_application_spine_at_once`, `f a .. a` with 1,000 arguments against a telescope whose codomain
  mentions every binder. It takes under 5 ms, against 0.64 s in release and 4.6 s in debug with the per-argument path.

*After the spine change.* The laws checked alone (one run, machine at about 5% CPU, real-time protection off), first check / repeat:

| | n=8 | n=16 | n=32 | n=64 |
|---|---|---|---|---|
| rule 0 | 20 / 11 ms | 24 / 15 ms | 60 / 35 ms | 187 / 101 ms |
| rule 33 | 76 / 33 ms | 169 / 77 ms | 408 / 191 ms | 875 / 400 ms |

Rule 33 still grows 2.1-2.4 times per doubling. A samply profile of its first check at n=64 (profile not kept) is still
mostly instantiation:

| self time | |
|---|---|
| `inst_rec` | 19.3% |
| `hc::intern` | 15.3% |
| the scope's drop | 12.7% |
| `lowest_loose` | 7.9% |
| `uses` | 4.9% |
| `shift_child` | 4.8% |
| `infer_rc` | 2.2% |
| `prove_rule` (building the law, inclusive) | 11.8% |

46% of samples are under `instantiate_n`, and the callers above it are attributable this time. Nearly all of it is reduction, not typing:
`hnf_rc` 21.5% (15.5% from itself), `closed_prefix_spine` 13.6% and `beta_spine` 6.6%, all under `whnf_step`, against
2.9% from `infer_node`. What is left is conversion evaluating the law's Church-encoded circuits (the closed-function
head normal forms of e7d4347), and freeing what that allocates.

*The work is linear; each operation slows.* A probe (reverted, no patch kept) counted, for one law check in a fresh scope, the node table's new entries and its lookups:

| rule 33 | n=8 | n=16 | n=32 | n=64 |
|---|---|---|---|---|
| check | 56 ms | 132 ms | 351 ms | 807 ms |
| new interned nodes | 41,761 | 90,191 | 178,111 | 353,951 |
| new instantiation / shift / whnf / hnf entries (thousands) | 40 / 38 / 5.8 / 0.13 | 78 / 76 / 12 / 0.15 | 155 / 151 / 24 / 0.15 | 308 / 300 / 47 / 0.15 |
| `intern` calls | 113,370 | 225,114 | 446,314 | 888,714 |
| `inst_rec` calls | 61,104 | 120,930 | 239,138 | 475,554 |
| `instantiate_n` memo lookups | 60,792 | 120,057 | 238,041 | 474,009 |

Rule 0 is the same: everything doubles per doubling of n. Head normal forms are a fixed 153 (rule 33) and 52 (rule 0).
So the distinct reduction results and the lookups grow linearly, and what grows faster is the time per operation:
about 0.5 µs per `intern` call at n=8 and 0.9 µs at n=64, for both rules. Part of that is the `uses` walks, which grow
3.6-3.9 times per doubling (measured before the spine change) and are 5% of samples at n=64 (13% with `lowest_loose`). The rest is presumably
memory: at n=64 the tables hold over a million entries, well past the 16 MB L3.

*The scope's drop.* Timed in the same probe: freeing the table after rule 33's check takes 14, 40 and 83 ms at n = 16,
32, 64 (about 10% of the check, linear, about 80 ns per entry). At n=8 it took 212 ms, because that scope also held
the 1.19M nodes `prove_rule` built first. Rule 0 takes 2-14 ms. It is a linear cost, so it does not explain the growth. Options, none tried:
- *Keep the table across checks.* No drop per check, and repeats hit its memos: a repeat check of rule 33 at n=64 takes 0.40 s against 0.88 s for the first. Memory grows with every check, so it needs a bound and an eviction rule.
- *Allocate a scope's nodes in an arena and free them in bulk.* This needs every node that outlives the scope to be copied out, a larger change to `Rc`.
- *Free on another thread.* Not possible as is: the kernel's `Rc` is not `Send`.

*Where the miner's drops fall* (read from `search.rs`, not timed). The table and its depth are thread-local
(`hc::TABLE`, `hc::DEPTH`), so a scope on the main thread does not cover a worker thread: each worker's first scope
is outermost there, and dropping it frees that worker's table.
- `proof_cost_split` is single-threaded inside one `scoped` call, so its checks already share one table and it drops once per run. It is the "keep the table" option already, without a bound.
- `rule_miner`'s main-thread scope covers only main-thread work. Its proofs and scores run on workers, each with its own table:
  - eager proving: one scope per worker per batch of candidates;
  - scoring: one per worker per round;
  - each round's winner (`prove_any`): one thread and one scope per rule, so one table and one drop per rule proof.

  The winner's proof runs beside the main thread's search, so its drop is off the main path but still uses a core.
- Separately, under the driver (`LEMMA_CACHE=<file>`, set by `driver::run_loop`), `shared_lemma` reads statements that an earlier process of the same build recorded, so a loop's later processes skip those checks (unless `LEMMA_RECHECK=1`).

So keeping a table across checks would change only `rule_miner`'s per-rule threads, and those would need a long-lived prover thread to hold it.

*Every law by name.* `Plan::Law` now checks every kind once through `shared_lemma`: `Bitwise`, `Chain` and `Tree`
as well as `Rule`, `Assoc` and `Comm`. All use one key, (prover, both sides, n, k). On `proof_cost_split` the non-rule
laws are 280 assoc, 272 comm and 163 tree uses, with 6 distinct tree statements and no `Bitwise` or `Chain`. The checked
proofs shrink: the rewriter's 296 laws go from 327,190 to 200,994 nodes (check 191 to 107 ms), and the machine proofs
from 23,146 to 4,152 nodes (46 to 3.3 ms). Each law's one check now runs during build, so total CPU is neutral: 6
alternating `cpu_ab.ps1` pairs, median 5.06 s before and 5.10 s after, machine at about 11% CPU, real-time protection off.

The "printer stall" seen earlier with full-normalizing printers has the same cause as the NEG wall, and it can't be fixed in the
printer. A probe (reverted, no patch kept) normalized `add`, `sub` and `lt` on two free words and counted unique
nodes against occurrences:

| n | 8 | 10 | 16 | 32 | 64 |
|---|---|---|---|---|---|
| `add` without interning: unique nodes, time | 518k, 0.31 s | 8.4M, 6.7 s | over 6.5 GB at n=12 | | |
| `add` in an `InternScope`: unique nodes, time | 527, 0.5 ms | 813, 0.7 ms | 2,055, 3.4 ms | 8,183, 11 ms | 32,727, 58 ms |
| occurrences (both) | 5.2e5 | 8.4e6 | 3.4e10 | 1.5e20 | 3.4e38 |

`sub` behaves like `add` (about 2 times slower in a scope); `lt` has 976 unique nodes at n=64. Without interning,
`nf` builds the tree: about 16 times larger for every 2 more bits. Interned, the normal form is a DAG of about
8n² nodes, so `nf` itself is cheap. Any printer that walks the term still visits every occurrence, so printing it in
full is infeasible either way. Printers have to stop early, as `brief_nf` does, or print the DAG with shared nodes
named.

*Table size alone.* Hardware cache-miss counters are not available to a session here: AMD uProf is not installed, and
xperf's PMC sources need an elevated kernel trace. Instead, a probe (reverted, no patch kept) checked a law at
n=8 twice: in a fresh scope, and in a scope that had just built and checked the n=64 law. For rule 33 the n=64 work left 507k
nodes, 306k instantiations and 327k shifts in the table. The n=8 check makes about 154k new entries in a fresh scope, counting
the input that `check_in` interns, and 147k after n=64, which shares a few nodes with it. The filled check does slightly less
work, so its extra time comes from the size of the table and heap. Three
rounds per rule, Defender real-time protection off, machine at 4-6% CPU, pinned to 12 cores at below-normal priority:

| µs per new table entry | n=8, fresh scope | n=8, after n=64 | n=64, fresh scope |
|---|---|---|---|
| rule 33 | 0.33-0.39 (51-61 ms) | 0.45-0.54 (66-79 ms) | 0.57-0.71 |
| rule 0 | 0.20-0.42 (8-17 ms) | 0.36-0.46 (14-17 ms) | 0.44-0.59 |

The large table alone makes each entry 1.3-1.5 times slower. That accounts for about 40% of rule 33's rise from
n=8 to n=64, and most of rule 0's. Rule 0's times are small and noisy, and its fill (127k nodes) is a quarter of rule 33's.
It is an upper bound: the filled n=8 check runs against the table at the size the n=64 check reaches only at its end.
This shows that size slows each entry. It does not show which mechanism does it: cache misses on the table and the nodes,
longer probe sequences, or a scattered heap all fit.

*What else grows per entry.* The node table's key is fixed in size (constructor, leaf, up to five child pointers), and so
are the instantiation, shift, whnf and hnf keys. Hashing and comparing a node therefore cost the same at every n; wider
terms do not make them dearer. A second probe (reverted, no patch kept) counted the per-entry work of one law check in a
fresh scope (same machine state: Defender real-time protection off, 4-5% CPU, pinned, below normal):

| per new table entry, rule 33 | n=8 | n=16 | n=32 | n=64 |
|---|---|---|---|---|
| µs | 0.38 | 0.55 | 0.65 | 0.61 |
| `intern` calls | 0.92 | 0.88 | 0.88 | 0.92 |
| `inst_rec` calls (mean depth) | 0.40 (2) | 0.47 (2) | 0.47 (2) | 0.40 (3) |
| argument-set lookups (mean length) | 0.038 (6.1) | 0.044 (6.2) | 0.044 (6.2) | 0.038 (6.2) |
| `lowest_loose` nodes walked | 0.78 | 0.91 | 0.91 | 0.78 |
| `uses` calls past the cheap exits | 1.95 | 3.85 | 6.81 | 10.75 |
| `uses` nodes walked (header-slot misses) | 1.14 | 2.50 | 4.71 | 7.73 |

Rule 0 is the same: everything is flat except `uses`, at 0.63 nodes walked per entry at n=8 and 4.14 at n=64. Stack-segment
switches are 1 per check at every n. So the only work per entry that grows with n is the `uses` walks: they grow about
linearly per entry, and so quadratically in total. Each node's header slot keeps one (d, m) answer, and a node gets asked
at more (d, m) pairs as n grows. Both earlier fixes for `uses` were negative: a one-slot (d, lowest loose) header cache
and per-node loose-variable bitsets (see "What is still superlinear").

*The rise, priced by a profile diff.* Two samply profiles on c19808a (profiles not kept) recorded the same law check
repeated in fresh scopes: 120 checks at n=8 and 10 at n=64, each after one warm-up check. Each run printed wall-clock
marks around its repeated checks; `scripts/prof_diff.py` keeps only the samples between the marks and divides each
function's self time by the new table entries (154,275 and 1,185,460 per check). Busy time per entry was 240 ns at n=8
and 491 ns at n=64. The rise of 251 ns:

| self ns per entry | n=8 | n=64 | rise |
|---|---|---|---|
| `TABLE.with` bodies (the inlined node-table and memo probes) | 57 | 123 | +66 |
| `hc::uses` and its closure | 15 | 75 | +61 |
| `hc::lowest_loose` | 29 | 72 | +43 |
| `reserve_rehash` (table growth) | 19 | 29 | +10 |
| `infer_rc` | 11 | 21 | +10 |
| everything else, each +5 or less | | | +61 |

The earlier guess priced `uses` at about 0.03 µs from a profile taken before the spine change; it is 0.06 µs now.
`lowest_loose` rises without doing more: a third probe (reverted, no patch kept) counted 1.32 memo lookups per entry
at n=8 and 1.37 at n=64, and the walks are flat (above). What grows is its memo (`InferCache::lows`, one per check):
66k entries on average at a lookup at n=8, 515k at n=64. That is the table-size effect again, in a map the fill
probe above did not fill (its memo is per check). So the rise splits about evenly:
- **Size:** larger maps, with the same lookups per entry, cost about 120 ns: the node table and memos, `lows`, and rehashing.
- **More work:** the `uses` walks cost about 60 ns.
- **Spread out:** about 60 ns is spread thinly across the rest.

*Why `lowest_loose` cannot move into the node header* (reasoned, not prototyped). A node's lowest loose variable is
not a function of its children's. Take `Lam(A, body)` where `body` mentions `Var 0` and `Var 5`. The body's lowest
loose variable is 0, the one the `Lam` binds, and the `Lam`'s own lowest loose variable, 4, comes from the body's
second-lowest. A node needs each child's answer at every depth: the (node, depth) key of `lows`. The smallest summary
that composes is the whole set of loose variables, which was the bitset prototype (negative, "What is still
superlinear"). So the `lows` memo can only get cheaper per lookup, not go away.

*The rise after the bounds memo (2026-10-14).* The same two profiles, repeated on ded1a96 plus the probe (reverted, no patch kept; profiles not kept). Load was 33–36% from other work throughout, and both runs ran back to back. Absolute times are inflated: 526 ns busy per entry at n=8 against 240 above, and 83 against about 45 ms per check unprofiled. So only the rise within this pair is compared, still divided by the entry counts above. Busy time per entry was 526 ns at n=8 and 689 ns at n=64, a rise of 163 ns (251 before). By first non-std frame:

| self ns per entry | n=8 | n=64 | rise |
|---|---|---|---|
| `hc::intern` (node-table probes) | 77 | 114 | +37 |
| `hc::lowest_loose` (`InferCache::lows`) | 94 | 126 | +31 |
| `shift_child` | 47 | 63 | +17 |
| `infer_rc` | 24 | 40 | +16 |
| `hc::canon` | 22 | 34 | +12 |
| `hc::uses` and its closures | 15 | 26 | +11 |
| `height_at_most` | 9 | 15 | +6 |
| everything else, each +4 or less | | | +33 |

- **`uses`' share of the rise fell from about 24% (+61 ns) to about 7% (+11 ns).**
- **What is left is mostly size:** probes into the node table (`intern`, `canon`) and the per-check `lows` map, with `shift_child` and `infer_rc` behind them. These are what Stage 2 of the id arena targets.
- **`lowest_loose` is now the largest single cost at n=8 as well (94 ns per entry).** The `lows` memo needs exact minima, so the bounds memo cannot answer it.

*What `lows` does per call (probe on 77fe8a9, reverted, no patch kept, 2026-10-14).* Counters for one fresh-scope check of rule 33's law, after a warm-up check:

| n | `memo_context` calls | `lowest_loose` calls | gets at d=0 (hit) | gets at d>0 (hit) | `lows` size at the end |
|---|---|---|---|---|---|
| 8 | 36,732 | 289,570 | 60,634 (62%) | 143,552 (32%) | 120,475 |
| 64 | 280,948 | 2,228,402 | 478,898 (64%) | 1,140,324 (34%) | 926,455 |

- **The work per call is flat in n:** 7.9 `lowest_loose` calls and 5.6-5.8 memo gets per `memo_context` call at every width, with 41-43% of gets hitting.
- **Every miss stays in the map**, so it ends near one entry per new table node (926k against 1.19M at n=64). That is over 20 MB, past the L3, so the rise is the per-probe cost of a growing map, as for the node table.
- **Skipping the memo for small nodes (`hc::low`, height at most 2, as the instantiation memo does) removes almost nothing:** gets fall 0.4-0.5% and the map 0.7%. The memoised nodes are large, so it was not timed.
- **Left:** no `lows` lookup can be skipped, so only cheaper probes help.
  - Under the id arena, the d=0 entries (30% of gets, 64% hit) could live in a dense side array indexed by node id, with no probe at all.
  - Sharing the `uses` bounds table was the "shared memo" variant above, which did not help.

**Allocation schemes against the size cost (survey, 2026-10-14).** The size cost is about 120 ns per table entry at
n=64 (profile diff above): node-table and memo probes (a hit reads the candidate node at a random address), the
`lows` memo, and rehashing. Today a node is one mimalloc block of 80 bytes: `std::rc::Rc`'s two counts (16), the
header (`loose`, `free`, `generation`, `uses`: 16) and `Expr` (48; `size_of` checks in `kernel/tests.rs`). mimalloc is
v3 (`libmimalloc-sys` 0.1.49), the global allocator of every binary. `docs/related-work/` §64 surveyed node
representations for linearity ("Allocation"), and "A per-scope arena for the table's nodes" above ruled out a
bulk-freed arena of `Rc` nodes, because 16% of a scope's nodes outlive it. The schemes:

1. *Large OS pages (measured, positive).* mimalloc maps its arenas in 2 MB pages when `MIMALLOC_ALLOW_LARGE_OS_PAGES=1`,
   which needs the account's "Lock pages in memory" privilege. This account holds it (disabled until a process enables
   it, which mimalloc does). With it set, mimalloc reserved 1 GiB of large pages at start (`MIMALLOC_VERBOSE=1`). Fewer TLB
   misses on the same random accesses, presumably (no counters measured it). A probe (reverted, no patch kept) timed rule 33's law in fresh scopes, three
   alternating pairs. At n=64 large pages won 3 of 3, median 483-489 → 433-436 ms (-10%, about 42 ns per entry). At
   n=8: no change (medians 32-36 ms). On `proof_cost_split` (`scripts/cpu_ab.ps1`, 6 pairs) they won 6 of 6: CPU 3.02-3.20
   → 2.69-2.75 s (-12%), build 1.80-1.92 → 1.56-1.62 s, check 256-283 → 227-240 ms. Defender RTP off, load 2-8%.
   **Adopted (2026-10-14).** `.cargo/config.toml` compiles mimalloc's defaults in: large pages and a 64 MiB
   `arena_reserve`. `mi_option_set` from `main` would be too late for large pages, because mimalloc enables the
   privilege when the process loads; `arena_reserve` is read at each reservation, so a set from `main` reaches every
   arena after the first ("Survey: the open-law filter, `Term::show` and mimalloc's purge", P2).
   `MIMALLOC_ALLOW_LARGE_OS_PAGES=0` turns them off for one run. The test
   `machine::mimalloc_defaults_to_large_pages` fails if the define stops reaching mimalloc (checked by building
   without the config). Every timing's machine-state line now ends `lockpriv=… pages=large|normal`. **Every timing in
   this file before this entry is on normal pages; later ones are on large pages unless they say otherwise.**
   - *The reservation's size* (`scripts/cpu_arms.ps1`, `proof_cost_split`, 6 rotating rounds, load 7-18%, RTP off).

     | Arm | CPU (s) | Peak private (MB) |
     |---|---|---|
     | normal pages | 3.66-4.80 | about 700 |
     | 1 GiB | 3.30-3.92 | 1090 |
     | 256 MiB | 3.22-3.72 | 1090 |
     | 64 MiB | 3.22-4.14 | 898 |

     The size makes no measurable difference to CPU, so the smallest was kept, since it locks the least.
   - *A full sweep* (`SALT=1`, `mines own cold pooled`, 178 processes, measured as one job object: the job's CPU and
     its largest process's peak commit). Five rotating rounds; the outputs are identical apart from the seconds columns.
     - At load 10-36% (rounds 3-5), large pages won 3 of 3: job CPU 53.1-56.2 s against 55.0-58.6 s, about 4%.
     - At load 20-69% (rounds 1-2), they lost 2 of 2: 61.0-61.7 s against 55.3-61.3 s.
     - The gain is smaller than `proof_cost_split`'s 12% because most of the sweep's processes are short.
     - Memory: the largest process peaks at 578 MB against 413-419 MB (+40%), and the whole job at 769-834 MB against 498-506 MB.
       Presumably because Windows commits large pages when they are reserved and cannot decommit them.
   - Risks: large pages are locked, never paged out. Each process locks what it reserves, so parallel sweeps each lock
     their own, out of the machine's 62 GB. Without the privilege mimalloc falls back to normal pages, so a machine
     without it times differently.
2. *A node in 64 bytes (unmeasured).* mimalloc's size classes step 64 → 80, so dropping only the unused weak count
   (an own `Rc`, as `triomphe`) leaves 72 bytes in the 80-byte class and saves nothing. Reaching 64 also needs 8 bytes
   off the header, e.g. 16-bit `loose`/`free` (saturating; rule laws nest about 6n binders, 384 at n=64). 20% less node
   memory, so fewer misses on node reads, at the cost of hand-written `unsafe` refcounting in the trusted kernel.
3. *A per-scope mimalloc heap for interned nodes (unmeasured).* `mi_heap_new` gives the scope's nodes their own pages,
   not interleaved with `Vec` buffers and memo arrays. The toolchain is nightly, so `Rc::new_in` with a zero-sized
   allocator that reads a thread-local heap is possible. Only locality is gained: `mi_heap_destroy` (free without
   walking) is unsound while 16% of nodes escape, so the heap would have to be released with `mi_heap_delete`, which
   keeps live blocks. mimalloc already places same-size blocks contiguously in a page, so the gain may be small.
4. *A two-space arena of 32-bit ids, hash-consed (nanoda_lib's design, §64).* The end-state design: `Expr` children are
   4-byte ids (a node about 40 bytes, no counts), equality is an id compare, ids are the memo keys (`lows` entries 12
   bytes instead of 24, node-table entries 8-12 instead of 16), allocation is sequential, and a scope frees in bulk.
   The 16% that escape a scope are copied into the persistent space when it ends, remapping their ids. Costs, from §64:
   every constructor and pattern goes through a context across the kernel and `proof.rs`; garbage stays until the
   scope ends; an id used with the wrong space names another term. It addresses the whole size cost (smaller maps,
   smaller nodes, and the scope's drop) and is the only scheme here that does.
5. *Rejected before, still rejected.* A bump arena with `&'a Expr<'a>` children (lifetimes through every proof record
   and the JIT, §64). A tracing GC (slower than `Rc` in Rust, no cycles to collect, §64). An `Rc` arena freed in bulk
   (escaping nodes, above). Freeing on another thread (`Rc` is not `Send`).
6. *Adjacent, not allocation.* Reserving the maps' capacity ahead (rehashing is about 10 ns per entry at n=64) needs a
   size estimate per check. Reordering nodes for locality does not apply: hash-consing shares a node among many parents,
   so there is no one order to put it near.

Ranking by end state: 4, then 1, which presumably stays useful under 4 (its maps and nodes would still exceed the TLB's reach at large
n), then 2 and 3. Only 1 is measured; it is additive and leaves no rework.

*Against the directions in this file (reasoned, not measured).* Scheme 4 gains under most of them:
- **Proofs about the target at n=64** (option B of "Formalizing the target machine") run where the size cost dominates.
- **Compiled transformations** can read ids, as indices into linear memory, where they cannot read `Rc` pointers.
- **The two spaces match the tiers:** the per-check region is working memory, the persistent space long-term memory, and ids are stable keys for proved statements (today `lemma_cache` keys by printed strings).
- **Parallel checking** could share a frozen persistent space read-only across threads, which `Rc` (not `Send`) cannot.

Its shortcomings there, with mitigations:
- **The persistent space only grows** (nanoda never reclaims it), and a cycle keeps what it learns: rules, lemmas, statements. Mitigation: a major collection at quiescent points, between rounds. The roots are explicit and few (the rule library, the lemma statements, whatever caches are kept), so copying the live set into a fresh space costs what is live, not what was built. Rebuildable memos are dropped, not copied. The cheapest form exists already: the driver runs each loop's work in separate processes, with long-term memory in files (`LEMMA_CACHE`, rule files), so a process boundary is a major collection.
- **An id used with the wrong space names another term.** Mitigation: two id types, a generation-checked handle (`Expr`) and a persistent id (`PExpr`), with a copy-out function (`persist`) the only way from one to the other. Two ids alone do not make returning a region id fail to compile, since neither carries a lifetime. What does: `scoped(|| ..)`, whose result must implement an `Escape` trait, and which copies the result out when it opened the region. A dead handle panics on every read, in release builds too; it never names another term. Branded lifetimes would also catch stores, but were rejected for spreading (§64). Specified in the id-arena spec (`docs/superpowers/specs/2026-10-14-id-arena-spec.md`, local).
- **Every constructor and pattern through a context** (§64's main cost). Mitigation: the current space is thread-local, as `hc::TABLE` is now, so constructors take no context parameter. A node of id children (24 bytes as an enum, plus 12 in side arrays) is `Copy`, so a pattern matches a copy (`match id.node()`) and needs no borrow from the arena.

*The id-arena spec (draft 3, 2026-10-14, 5 review rounds).* Its decisions:
- **Copy-out is eager**, with a twin map. A persisted node reads as its region twin until the region closes, so equality stays an id compare and a `PExpr`'s hash never changes.
- **One interning rule:** a node over persistent children looks in the persistent space first.
- **The checking entries are `scoped`**, so a check outside a region frees its transients.
- **Returns are checked by `scoped` with `Escape`** at compile time (D1, decided 2026-10-14); stores by the generation check on handle reads.
- **Stage 1, built first (decided 2026-10-14), is a trace replay** of rule 33's table and memo traffic in three layouts: today's; ids; and a hybrid of `Rc` nodes with dense u32 memo keys, which shrinks the maps without the port.
  - It is a one-sided filter: a loss stops the port.
  - Its gate is re-profiled on large pages first.

*Measured for it* (probe reverted, no patch kept):
- The miner builds no node outside a scope, and none in a scope before the table switches on (`proof_cost_split` and a full salt-1 sweep).
- 19-21% of the nodes built are not in the table when it drops.
- 17% (`proof_cost_split`) to 22% (largest sweep child, 0.42 M) of interned nodes are still alive after it. This is the live set, not the copy-out volume, which is unmeasured.
- **Small checks gain little.** Mitigation: share one region across a batch of checks, as `proof_cost_split` shares one scope, and reset a region by its pointer, keeping its pages mapped.
- **The compiled hot path should not allocate at all.** When it must produce terms (proof witnesses), it bump-allocates into the region through linear memory. Not a shortcoming of the arena; the arena fixes the format at the boundary.

Scheme 1's caveats, with mitigations:
- **Each process locks its reservation for its whole life.** Mitigation (done): `arena_reserve` is 64 MiB. Large pages were on in every process at first, because the sweep of short processes seemed to gain a little at low load. Rechecked, they lost, so `driver::sweep` now turns them off for its children ("How often the large-page stall hits a sweep").
- **A machine without the privilege falls back to normal pages.** Mitigation (done): the machine-state line logs `pages=`, as it logs Defender's state, so baselines compare.

*Stage 1 result (2026-10-14; tracer and replay throwaway, reverted, no patch kept): continue.*
- **The trace:** one law check of rule 33 after a warm-up, at n=8, 16, 32 and 64 (5.4 to 44 MB). Its new entries (intern misses plus memo puts) are 154,427, 301,740, 596,364 and 1,185,612, against the 154,275 and 1,185,460 above. Every arm reproduces every lookup's hit or miss and every `uses` and `lowest_loose` answer.
- **The arms:** (a) 80-byte `Rc` blocks, pointer-keyed maps, `keep`; (b) 24-byte nodes in a vector with side arrays, u32-keyed maps, a bulk clear at scope end; (c) (a)'s nodes in 96-byte blocks with a u32 id, memos keyed and valued by ids.
- **ns per new entry,** decoding subtracted, work plus the scope's drop, median of 5 alternating processes (load 25% at the start, Defender RTP off, large pages):

  | n | (a) today | (b) ids | (c) hybrid |
  |---|---|---|---|
  | 8 | 229 | 153 | 183 |
  | 16 | 286 | 186 | 255 |
  | 32 | 342 | 253 | 314 |
  | 64 | 406 | 326 | 378 |

  A second rotation (load 70% falling to 16%) gave, best of 5 at n=64: (a) 411, (b) 314, (c) 367.
- **Gate passes:** (a) rises 177 ns from n=8 to n=64, against the ~206 ns re-profiled on large pages for the maps, `uses` and `lowest_loose` (at 23-26% load): a ratio of 0.86.
- **Stop rule not met:** (b) is 20% below (a) at n=64 (24% in the second rotation). Without the drop phase it is 13.5% (17.6%), so the scope drop carries part of the gain.
- **The hybrid is not the cheaper end:** (c) is 7% (11%) below (a), about a third of (b)'s gain.
- **The rise is unchanged.** (b) rises 173 ns from n=8 to n=64, as (a) does. In the replay, ids take a near-constant ~75 ns off each entry; the growth with n does not come from node or entry size.
- **Not in the replay:** the `ReductionCache` (no traffic while the table is on), `context_of`, the reducer's own node reads (which understate (b)), and the port's own costs (which overstate it).
- **Next, per the spec:** the narrower real prototype (`shift`, `instantiate`, `uses` and `lowest_loose` on ids, on a branch, timed against `main`). **Dropped before it was built (2026-10-14):** callers use its results as `Rc` at once, so its boundary would build every new node twice. That cancels the intern and node-build gains, and the per-op costs below leave about zero net at n=64 (`lowest_loose` +20, memo get +15, memo put −26, `uses` −11 ns per entry). Stage 2 went first instead ("Id arena Stage 2" below).

*Where the rise comes from (the same replay, 2026-10-14; reverted, no patch kept).* Cycles were charged to each trace op, one run at n=8 and n=64 per arm, with 3 reps and the quietest kept (the profiler adds its own cost, about equally per op). Top-level op counts per entry hardly change with n: memo gets 0.97 against 1.00, `uses` calls 0.52 against 0.53. So the rise is in what each op costs. ns per entry, n=8 → n=64:

| op | (a) today | (b) ids |
|---|---|---|
| `uses` | 18 → 68 (+50) | 21 → 79 (+57) |
| `lowest_loose` | 55 → 94 (+39) | 42 → 74 (+32) |
| intern | 50 → 92 (+42) | 33 → 44 (+11) |
| memo get | 34 → 66 (+32) | 25 → 51 (+26) |
| memo put | 25 → 31 (+6) | 31 → 57 (+26) |
| node build | 26 → 37 (+12) | 14 → 27 (+13) |
| all ops | 277 → 478 (+201) | |

- **`uses` (a quarter of the rise) is algorithmic.** Nodes visited per call grow linearly with n: 5.5, 9.1, 16.3 and 30.5 at n=8, 16, 32 and 64. The cost per visit falls (6.3 to 4.2 ns), so this is more walking, not slower walking, and no layout changes it.
- **The rest is lookups in tables that grow:** `lowest_loose` (its visits per call stay at 7.9, but each one probes the `lows` memo), intern, memo gets and puts. Ids remove most of intern's rise (an 8-byte table entry) and little of the memos'.
- **Tried and rejected: a 64-bit set of loose `Var`s per node,** which would answer `uses` and `lowest_loose` without walking. It is exact only when no node beneath has loose above 64. Most nodes at n≥16 have more (515,113 of 523,216 at n=64; the context is deep), so it covers 81% of `uses` calls and 16% of `lowest_loose` calls at n=64. A fixed-width set does not scale with n. Checked against every traced answer where it applies.

*Why `uses` walks grow, and what table growth costs (the same replay, 2026-10-14; reverted, no patch kept).*
- **The walks revisit old nodes whose slot holds another query.** At n=64, 0.8% of visits are a node's first. Per call, slot misses with a different query are 14.5 and misses on an empty slot 0.24. Nodes are asked at many depths (d up to 384), so a slot keyed by d alone does no better (30.2 visits per call).
- **A memo fixes it at every n.** Visits per call:
  - an unbounded `(node, d, m)` memo: 1.59;
  - `lowest_loose` with its `(node, d)` memo, answering `uses(x, d, m)` as `lowest_loose(x, d) < m`: 1.57.
- **Timed in arm (a),** ns per new entry with decoding subtracted: median, then best of 7 in brackets. The reps alternate, at load 23% falling to 13%:

  | n | today (slot) | `(node, d, m)` table behind the slot | `uses` through `lowest_loose`'s per-scope memo, no slot |
  |---|---|---|---|
  | 8 | 266 (194) | 242 (217) | 256 (230) |
  | 64 | 483 (449) | 427 (367) | 388 (376) |

  - At n=64 the shared memo wins 6 of 7 paired reps, and the rise from n=8 to n=64 falls from 217 to 132 ns. An earlier rotation (load 40%) gave 445 → 360 best-of-5 at n=64 with the table.
  - At n=8 it is within noise: 4 of 7 paired reps.
  - This does not contradict "Per-node facts in the node header", where slot alone beat slot plus table 8 of 12 on `proof_cost_split`. That workload is small-n; at n=64 the walks are 5.5 times longer.
  - In the replay the shared memo is the one mechanism: it subsumes the slot and the `uses` walk. In the real kernel it loses on small work, with or without the slot in front (next paragraph).
- **Most memo entries are never read:** inst 85%, shift 78%, whnf 62% and types 77%, the same at n=8 and n=64. Hit rates are flat in n (inst 35%, shift 44%, whnf 58%, types 74%).
- **Pre-sizing the tables to their final size gains nothing** (2 rotations, within noise). The growth cost is probes into tables larger than the caches, not resizing.
- **Bounded memos keep most hits only for some tables.** A 2-way cache of 2^16 entries at n=64 keeps 97% of inst's hits, 98% of whnf's, 88% of types' and 75% of shift's (2^14: 93, 85, 70, 62). A lost hit means recomputation, which the replay cannot time, so this needs a real prototype.
- **A one-entry slot per node** would answer all of whnf's hits, 99.9% of hnf's, 86% of types', 66% of shift's and 38% of inst's.

*The shared memo in the real kernel: negative (2026-10-14; branch reverted, no patch kept).* On 012e4c5, the node's `uses` slot was deleted, and `uses(x, d, m)` became `lowest_loose(x, d) < m` through a `(node, d)` memo in the `hc` table (pinned like the other memos). `InferCache::memo_context` used that table while it was on, and its own map otherwise. The kernel unit tests passed. Alternating pairs, BelowNormal on 12 cores, load about 25%, real-time protection off:

| workload | today (slot) | shared memo | pairs won by the memo |
|---|---|---|---|
| rule 33's law, n=64, 5 checks per process: median of medians | 672 ms | 586 ms (−13%) | 6 of 6 |
| rule 33's law, n=8, 61 checks per process: best | 42.9–45.4 ms | 45.1–48.4 ms (+6%) | 0 of 6 (medians: 2 of 6) |
| `proof_cost_split`, CPU per process: median | 3.84 s | 4.36 s (+13%) | 0 of 8 |

- `proof_cost_split`'s check rose 350 → 418 ms and its build (which also runs the kernel) 2.35 → 2.70 s.
- So the replay's n=64 gain is real (−13% against its −20%), but small checks pay more for a hash probe into the table than the slot's one header read saves. This agrees with "Per-node facts in the node header", where the slot beat slot plus table on `proof_cost_split`.
- **The slot first, with the memo only behind its misses, also loses on small work.** Two variants of that hybrid, against today's, with load 8–30% for `proof_cost_split` and rising to 42% by the end of the rule 33 runs:
  - With `memo_context` also on the table's memo: `proof_cost_split` CPU median 3.83 → 4.11 s (+7%, the hybrid won 1 of 8), check 344 → 406 ms.
  - With `memo_context` on its own map as today: `proof_cost_split` 3.84 → 4.03 s (+5%, won 2 of 8), check 340 → 373 ms. Rule 33 at n=64, median of medians 635 → 576 ms (−9%, 4 of 6); at n=8 neutral (3 of 6, by best and by median).
  - So the slot's misses alone carry the loss. A likely cause, not measured: `lowest_loose` must visit every child to find the minimum and hashes each node it visits, while the `uses` walk stops at its first hit and hashes nothing. On small terms that walk is cheaper than the memo.
  - The memo pays only where walks are long (large n). Choosing between walk and memo by term size would be a size threshold, not a general mechanism; not tried.

**The slot in front of bounds (2026-10-14, adopted).** `uses(x, d, m)` keeps the node's slot and today's walk, which stops at its first hit. A slot miss looks up the `hc` table's `bounds[(x, d)] = (lo, hi)`, bounds on `lowest_loose(x, d)` that start at `(0, loose − 1 − d)`. A query with `m > hi` is true and one with `m <= lo` is false, without a walk. Otherwise the walk runs, and its answer narrows the entry to `(lo, m − 1)` if true or `(m, hi)` if false. So one (node, d) entry answers every `m` its bounds decide, as `lowest_loose`'s memo does, without visiting every child for an exact minimum. Check: `uses_bounds_agree_with_lowest_loose`, which asks every (d, m) in three orders. Against main's kernel (012e4c5, unchanged to 981540b), alternating pairs, BelowNormal on 12 cores, real-time protection off:

| workload | today (slot) | slot, then bounds | pairs won by bounds |
|---|---|---|---|
| `proof_cost_split`, CPU median, rotation 1 (load 12–20%) | 3.73 s | 3.69 s | 6 of 8 (1 tie) |
| `proof_cost_split`, CPU median, rotation 2 (load ~25%) | 3.63 s | 3.68 s | 6 of 10 |
| `proof_cost_split` check, median, rotations 1 and 2 | 348, 335 ms | 345, 348 ms | 5 of 8, 4 of 10 |
| rule 33's law, n=64, 5 checks per process: median of medians | 644 ms | 541 ms (−16%) | 5 of 6 |
| rule 33's law, n=8, 61 checks per process: median of bests, of medians | 41.0, 50.7 ms | 41.2, 50.6 ms | 2 of 6, 2 of 6 |

- Neutral on small work and −16% at n=64, so it is adopted.
- Bounds without the slot lose on small work: `proof_cost_split` check 343 → 369 ms (won 1 of 8), CPU median 3.78 → 3.77 s (won 2 of 8). The slot's one header read still beats a hash probe when it hits.
- This supports the cause guessed above: the `lowest_loose` hybrid lost on small work while this one, with the same slot in front, does not. The difference is the walk that stops at its first hit.
- `InferCache`'s `lows` stays as it is: it needs the exact minimum.
- Sequential sweep pair (rows `bnd_*`, script `bounds_seq.sh`; CPU 24% at launch, RTP off): identical outputs on both salts (181 files each, lemma caches included; logs differ only in timings and their own paths). Walls 18 against 20 s (salt 1) and 19 against 18 s (salt 2).

**Id arena Stage 2 (2026-10-14, adopted on branch `id-arena-stage2`).** The types the arena needs, on today's `Rc` nodes:
- **`PExpr`** is a term kept past its scope. Only `persist` makes one, and it lends no `&Expr` (`get` hands out a clone), because an id cannot lend one.
- **`kernel::scoped(f)` replaces `InternScope`** at its 79 sites. The call that opens the scope passes `f`'s result through `Escape`, which is `persist` on every term, before closing it. So returning a type that holds terms without an `Escape` impl fails to compile.
- **The checking entries open their scope the same way,** without switching the table on: `def_eq`, `infer_in` and `check_in` use `hc::scoped(false, ..)`.
- **Long-lived stores hold `PExpr`:** `Globals`, `Postulates`' parameters (`PARAMS` and `PRELUDE` keep a `Postulates`), `CLOSED`, `TREE_LAWS` and `PARAMS`' lemma proofs. `CONSTANTS` and `BODIES` stay `Expr`, since they are rebuilt per generation.
- **Behaviour unchanged:** every suite passes with the base's counts (lib 371 = 370 + the new `scoped` test, church_bv 76).
- **Sequential sweep pair** (rows `s2_*`, script `stage2_seq.sh`; CPU 24% at launch, RTP off): identical outputs on both salts. Logs differ only in timings and their own paths, and `mines.tsv`/`pooled_prefs.tsv` only in their seconds column. Walls are 22 against 21 s (salt 1) and 18 against 21 s (salt 2).
- **Timing:** `proof_cost_split`, 8 alternating pairs against 4769775 (load 23%, RTP off). CPU median 3.98 → 3.94 s (new won 5 of 8), check median 370 → 363 ms. Within noise.
- **What the copy-out would copy.** A feature `copy-volume` records each node's region (outermost scope) and gives every node `persist` reaches an id in a simulated persistent table, once per node. The counts:
  - `copied`: nodes from the open region;
  - `outside`: nodes built outside any region, persistent already in the arena;
  - `stale`: nodes from an earlier region that were never persisted, which would be dead handles;
  - `unique`: the table's size.

  | workload | `persist` calls | copied | outside | stale | unique | interned (spec probe) |
  |---|---|---|---|---|---|---|
  | `proof_cost_split` | 1,712 | 493,753 | 0 | 0 | 494,561 | 2.98 M (0.49 M alive after) |
  | salt-1 sweep, 125 children | 9,620 | 1,554,721 | 0 | 0 | 1,559,422 | 10.8 M (2.61 M alive after) |

  - The copy-out is 17% of `proof_cost_split`'s interned nodes, and matches the 0.49 M the spec's probe found alive after the table drops.
  - For the sweep it is 14%, below the 2.61 M alive after. So that live set also holds nodes no `persist` reaches, such as memo entries and terms dropped later.
  - `stale` = 0: no converted store and no return keeps a region node unpersisted.
  - Each of the 125 children printed one `COPYVOL` line, and the `copy-volume` build's sweep totals equal the default build's.
- **The port's risk "an outermost `scoped` copies out large results"** is small on this workload. Copying 0.49 M nodes at about an intern's cost (50-90 ns per entry in Stage 1's replay) would be about 25-45 ms of `proof_cost_split`'s 3.9 s, about 1%. That is an estimate, not timed.
- **Departures from the spec:**
  - The counter counts by region, not generation: 19-21% of a scope's nodes never enter the table, but every node built in a region is a region node.
  - `Postulates` holds `PExpr`, which the spec did not list.
  - `NO_SCOPE` and the other A/B toggles stay as `if c { scoped(body) } else { body() }`; the port deletes them.
  - An outermost `infer_in` (as in every `Postulates::push` outside a scope) persists the type it returns, since the arena copies it out too.
- **Two plan misses fixed on the way:**
  - `uses_slot_is_free_and_agrees_with_the_walk` asserts the 64-byte node as well, so it is off under `copy-volume`, like `a_node_is_64_bytes`.
  - `kernel_soundness_fuzz`'s `to_globals` now takes the `Globals` its callers pass.
- **Next:** the Stage 3 decision (the port). It rests on Stage 1's replay (ids 20% below today at n=64, 33% at n=8, the rise with n unchanged) and on this copy-out volume.

**Id arena Stage 3 (2026-10-14, adopted on branch `id-arena-stage3`).** Terms are ids into two hash-consed spaces. Plan `docs/superpowers/plans/2026-10-14-id-arena-stage3.md` (main checkout only), in two phases:
- **Phase A** (3be0e79): the API port on `Rc` storage. `Expr` is a handle over `Node<Expr>`, the old enum's variants with children `C`, read with `e.node()` and built with `mk`. Internals take `s: &Spaces` first. Twin functions merge (`whnf_impl`+`whnf_rc` into `whnf_in`, likewise `nf_in` and `conv`). `copy-volume`, `hc_probe`, `with_ranges` and `LEAF` are deleted. `shared` (two or more parents, counted at build) replaces `strong_count > 1`.
- **Phase B** (1166b0e `spaces.rs`, ff173a6 the switch): `Expr` is `Copy`, 8 bytes: a node `Ref` and the region epoch it was made in. `Spaces` (thread-local) holds a persistent space and one region, both hash-consed, so equal structure is one resolved `Ref` and `==` is an id compare. A handle from a closed region is dead: reading it panics ("dead handle"), and `Debug` prints `<dead handle>`. `scoped` opens the region and persists its result on close. The memos (instantiation, shifts, `whnf`, `hnf`, `nf`, argument lists, `uses` bounds) live in `Spaces.memos`, keyed by `u32` node ids, and clear on close. Every public entry (`whnf`, `def_eq`, `normalize`, `infer_in`, `check_in`, `typecheck`) runs in a region.
- **Deleted in B:** `Drop for Header`, `ReductionCache`, `PtrHasher`/`PtrMap`/`PtrSet`/`PtrKey`, `ShiftKey`, `eq_noting` with its `unequal` set, `whnf_fresh`, `canonical_inputs`, and `hc::Scope`/`activate`/`intern`/`generation`. Tests deleted with the mechanism each asserted: `memo_sources_outlive_their_callers`, `args_id_is_the_same_for_a_canonical_argument_and_its_twin`, `dropping_a_deep_term_does_not_overflow_the_stack`, and `infer_memo_changes_no_answer` (under hash-consing its "unshared copy" is the same node).
- **Behaviour unchanged.** Every suite passes with the base's counts except lib: 371 in the base, 370 in A (`a_node_is_64_bytes` deleted), 374 in B (+6 `spaces` unit tests, −4 deleted, +2 dead-handle tests). church_bv stays at 76, and no dead handle fired in the suite or the four sweeps. Sequential sweep pairs against the base 6833fb9 (Stage 2 plus the `law_time` harness; rows `s3a_*`, `s3b_*`, script `s3_seq.sh`, RTP off) give identical outputs on both salts for both phases. Logs differ only in timings, their own paths and the filtered-out count, and `LEMMA_CACHE` lines match. One log, `lib_sbo3/mine_ref.log`, moves its `LEMMA_CACHE starts empty` line by one: the base exe moves it between its own runs too (stdout and stderr interleave).
- **Tests whose expectation changed** (hash-consing now holds outside a region too):
  - `bin_round_trips_and_shares_nodes`: the encoding's size is equal in and out of a region;
  - `constants_are_built_once_per_generation`: the second region's rebuilt gate is the copy `scoped` persisted from the first;
  - `close_is_linear_in_the_dag_of_a_shared_body`: 64 nodes, not 93, because the postulate `f` is one node.
- **Timing, Phase A** (informational; load 30-41%, RTP off): `proof_cost_split` CPU median 3.79 → 3.90 s (A won 2 of 8). Rule 33's law at n=64: median 555-632 → 489-497 ms; n=8 within noise.
- **Timing, Phase B** (RTP off, load 9-24% at each block's checks; another session's `tier_eval_nn` was resident):

  | workload | base 6833fb9 | B | |
  |---|---|---|---|
  | `proof_cost_split`, 8 alternating pairs: CPU median | 3.73 s | 2.54 s | −32%, won 8 of 8 |
  | the same: build / check median | 2213 / 352 ms | 1737 / 221 ms | |
  | rule 33's law, n=8, median of each run (3 pairs) | 50-54 ms | 21-25 ms | won 3 of 3 |
  | n=16 | 89-246 ms | 43-136 ms | won 3 of 3 (noisy) |
  | n=32 | 215-507 ms | 110-273 ms | won 3 of 3 (noisy) |
  | n=64 | 478-491 ms | 252-315 ms | won 3 of 3 |
  | salt-1 sweep in a job object, 3 alternating rounds: job CPU median | 51.5 s | 51.1 s | won 3 of 3 |
  | the same: peak commit, largest process / job | 578 / 769-833 MB | 514 / 705 MB | |
  | gcd benches (criterion, 3 alternating runs, pinned): median of the 3 point estimates, 7 benches | 5.5 µs-551 µs | 3.3 µs-275 µs | 0.43-0.59 of base, gate 1.10 |

  The n=16 and n=32 rows swing about 2× between pairs for both arms (contention). Every pair at every n goes to B, at 0.42-0.64 of the base's median.
- **Decision rule** (plan): keep the port if rule 33 at n=64 is faster and `proof_cost_split` is not slower beyond its spread. Both hold by a wide margin, and the gcd gate passes (plan departure 11 expected small proofs to pay the full interning; they take about half the time instead).
- **Departures from the spec** are listed in the plan (1-13) and recorded in the spec. Made during execution:
  - every `crates/tatic/benches/proofs.rs` iteration runs in its own region, not only the gcd ones;
  - `Spaces::from_key` became `expr_of`, since it reads the epoch through `self` (clippy's `wrong_self_convention`).
- **`docs/learned-vs-fixed.md`:** no row changes; no learned or fixed part moved.
- **Parked:**
  - departure 2's raw-`Ref` walks (`inst_rec`, `uses`, `conv_whnf`), if a profile shows `resolve`;
  - departure 12's bitset for `hc::exceeds`, if its walk shows;
  - the spec's own parked list.
- **Next:** profile B on rule 33 at n=8 and n=64, to see what the rise with n is made of now (the per-entry costs in "The rise after the bounds memo" were measured on `Rc` nodes). Done below.

**What rule 33's rise with n is made of on B (2026-10-14; probe reverted, no patch kept).** The probe proves the law once outside a region, then checks it in fresh regions, counting the nodes each check adds to the region. It ran 300 checks at n=8 and 25 at n=64 under samply (RTP off, load 4%), and compared them with `prof_diff.py` per new node. The checks add 50,487 and 385,032 nodes. These units are not the old table's entries: the proof is persistent and hash-consed, so only the check's own nodes count, and the numbers compare only within this pair.
- **Busy time per new node:** 322 ns at n=8, 604 ns at n=64. Self time per new node, by first non-std frame:

  | | n=8 | n=64 | rise | calls per node, n=8 / n=64 | ns per call, n=8 / n=64 |
  |---|---|---|---|---|---|
  | `Spaces::mk` (with its hashbrown probe) | 62 | 130 | +68 | 2.15 / 2.19 | 29 / 60 |
  | `hc::lowest_loose` | 33 | 66 | +34 | 2.16 / 2.24 | 15 / 30 |
  | `infer_rc` | 18 | 43 | +25 | 0.95 / 0.91 | 19 / 47 |
  | `hc::shift_get` | 18 | 41 | +23 | 1.44 / 1.52 | 12 / 27 |
  | `hc::uses` | 23 | 43 | +20 | 2.16 / 2.23 | 11 / 19 |
  | `hc::inst_get` | 11 | 28 | +18 | 1.16 / 1.18 | 9 / 24 |
  | `spaces::hash` | 12 | 25 | +13 | one per `mk` | 6 / 11 |
  | `shift_child` | 8 | 19 | +12 | 1.86 / 1.92 | 4 / 10 |
  | `hc::whnf_get` | 7 | 17 | +10 | 1.11 / 1.06 | 6 / 16 |
  | `hc::height_at_most` | 19 | 28 | +9 | 3.90 / 3.95 | 5 / 7 |

- **The calls per new node stay flat** (a second probe counted the calls of these nine functions; each count moves by about 5% or less between n=8 and n=64). So the rise is the cost per call. It is broad: hash probes, memo lookups and walks each take about twice as long per call.
- **The rise looks like memory, not work.** `spaces::hash` is register arithmetic over a node's tag and child ids, yet its time per call doubles too. That is most likely samples landing on it while the loads around it stall.
  - ns per node climbs smoothly with region size: about 460-540 at n=2-4 and 990-1070 at n=128 (two sweeps), with no sharp knee. These runs were contended (another session's `tier_eval_nn` and one other job, about one core each); idle n=8 reads about 340.
  - The same contention, at a total load of only 17-18%, slowed n=8 by about 1.6×. That fits a shared L3 between jobs.
  - **Ballast test:** before each n=8 check, 335,000 unrelated leaves were interned into the region, bringing it to n=64's size. They grow the node table and the per-node vectors but not the memos. ns per node rose 5-27% over three alternating rounds; n=64's own figure stood 39-54% above n=8's in the same rounds. With 1,000,000 leaves the rise was 6-49% (noisy).
  - So the node table's size explains part of the rise. The rest is plausibly the memos' size and the check's nodes being spread over a larger region; this was not measured.
- **What it points at:** the region's footprint per node, not its algorithms. Each node has an entry in `nodes`, `loose`, `free`, `uses`, `parents` and the table, plus its memo entries. Candidates, unmeasured: a footprint count of bytes per node at n=64; smaller memo entries; and denser layouts for the walks (departure 2's raw-`Ref` walks, still parked).

**Footprint per node of rule 33's check on B (2026-10-14; probe reverted, no patch kept).** The probe measured a law check in a fresh region, the second of two. It read the region's vectors and table, the `Spaces` memos, and `check_in`'s `InferCache` (read before it drops). It counts bytes in use (entries × entry size) and bytes allocated (capacity, or hashbrown's `allocation_size`), per new node. The probe missed `CtxScope` and `check_open`'s `FreesMemo`.

| per new node | used B | allocated B | entries per node |
|---|---|---|---|
| `region.nodes` (`Node<Ref>`, 24 B) | 24.0 | 36.0-37.8 | 1 |
| `region.loose`, `free`, `uses` (4 B each) | 12.0 | 18.0-18.9 | 1 each |
| `region.parents` | 1.0 | 1.5-1.6 | 1 |
| `region.table` | 8.0 | 11.7-12.3 | 1 |
| `memo.inst` | 12.6-12.7 | 22.1-23.1 | 0.79-0.80 |
| `memo.shifts` | 13.2-13.6 | 22.1-23.1 | 0.83-0.85 |
| `ic.lows` (`lowest_loose`'s memo) | 9.0-9.4 | 16.9-17.7 | 0.75-0.79 |
| `memo.bounds` | 5.1-5.4 | 11.0-11.6 | 0.32-0.34 |
| the rest (`whnf`, `arg_sets` and its keys, the other `ic` maps, `hnf`) | 7.6-8.4 | 12.5-14.9 | |
| **total** | **92.5 / 94.4** | **151.7 / 160.9** | |

- **The footprint per node is flat in n**, at about 93 B in use and 150-160 B allocated. So the region and its memos grow linearly: 7.7 MB at n=8 (50,487 nodes) and 62 MB at n=64 (385,032).
- **That straddles this machine's caches:** 1 MB of L2 per core and 16 MB of L3. n=8's set fits in L3 and n=64's is about 4× it. At about 155 B per node, L3 fills near 100,000 nodes, which is n=16. In the contended sweep above, ns per node is 547-688 up to n=16, 691-749 at n=24-32, and higher beyond. The rise above therefore matches a working set that leaves L3, consistent with the flat call counts and the doubled cost per call.
- **The hash maps hold about half the bytes, and they are the random-access ones.** The memos plus `region.table` come to about 56 B used and about 100 B allocated per node. Their allocation is 1.5-2.2× their use (load factor and power-of-two growth), and a probe can land anywhere in it.
  - `memo.inst`, `memo.shifts` and `ic.lows` each have about 0.8 entries per node, at 16 B (shifts, inst) and 12 B (lows) per entry before overhead.
- **`Node<Ref>` is 24 B because of `J`'s five children** (`WRec` has four). Every other variant fits in 16 B: a tag and three `u32`s.
- **Candidates, unmeasured:**
  - make `Node<Ref>` 16 B, by moving the children of `J` and `WRec` out of line;
  - shrink the memo entries, or hold the common case (one entry per node) in side vectors, as `uses` does;
  - make the region's per-node vectors one struct-of-arrays row.
  - Each attacks bytes per node; the test is rule 33 at n=64 against n=8.

**16-byte stored nodes, rejected (2026-10-14; reverted, no patch kept).** The first candidate above, built and timed against 41f48c1.
- **Change:** `Space.nodes` held a 16 B `Slot` (a tag byte, then three `u32`s) in place of `Node<Ref>`. A leaf kept its value in the first word, and a node with up to three children kept them inline. `J` and `WRec` set a `WIDE` bit in the tag, kept their first two children inline and the rest in a per-space `wide: Vec<[Ref; 3]>`, indexed by the third word.
  - One generic `Node::from_parts(tag, leaf, kid)`, the inverse of `tag_leaf` with `for_kids`, decoded every variant. `push` encoded and `node_at`/`find`/`persist` decoded; nothing outside `spaces.rs` changed.
  - Every suite passed (lib 375, the base's 374 plus a round-trip test of all 16 constructors through build, dedup and persist; church_bv 76).
- **Timing** (RTP off; load 17-42%, another session's `tier_eval_nn` on about one core throughout):

  | workload | base | slot | |
  |---|---|---|---|
  | rule 33's law, n=8, 8 alternating pairs × 15 reps: median of the run medians | 27.2 ms | 27.4 ms | +0.7%, within spread |
  | the same at n=64 | 436 ms | 429 ms | −1.5%, within spread |
  | `proof_cost_split`, 8 alternating pairs: CPU median | 2.79 s | 2.94 s | +5%, slot lost 6 of 8 |
  | the same: build median | 1.91 s | 2.05 s | +7% |

- **Why it doesn't pay:** 8 B off about 155 B allocated per node is 5% of the footprint, too little to move n=64 measurably. Meanwhile, encoding on every push and decoding on every read and table compare (a `from_parts` match where a 24 B enum copy was) costs about 7% of proof building.
- **Conclusion:** node size is not the lever. A footprint change has to come from the hash-map half (about 100 B of the 155 B allocated per node).

**Memo census of rule 33's check (2026-10-14; probe reverted, no patch kept).** For each memo the probe counted lookups and hits during one law check, and at the end the entries per node and how many sit on `hc::low` nodes (height at most 2). Values are n=8 / n=64.

| memo | lookups | hit rate | entries | nodes with entries (of 50,487 / 385,032) | share of those nodes with one entry | entries on low nodes |
|---|---|---|---|---|---|---|
| `shifts` | 72,892 / 584,060 | 0.43 / 0.44 | 41,729 / 329,094 | 21,491 / 165,271 | 53% / 54% | 3.0% / 2.7% |
| `inst` | 58,591 / 454,455 | 0.32 / 0.33 | 39,792 / 306,408 | 5,979 / 34,046 | 60% / 61% | 0 (gated) |
| `ic.lows` | 68,446 / 567,070 | 0.51 / 0.53 | 33,398 / 267,870 | 21,621 / 171,869 | 66% / 66% | 0.5% / 0.6% |
| `bounds` | 26,946 / 198,637 | 0.09 / 0.11 | 22,049 / 171,849 | 18,531 / 143,355 | 83% / 83% | 0.2% / 0.03% |
| `whnf` | 56,184 / 408,872 | 0.80 / 0.79 | 11,539 / 86,747 | 11,539 / 86,747 | 100% | 0.2% / 0.02% |

- **A low-node cutoff for the other memos is falsified, not built.** It would remove 3% of `shifts` entries and under 1% of the others. Those entries are among the best: `shifts` lookups on low nodes hit 81% / 83%, against 43% overall. (The 2026-10-13 leaf-only skip was neutral for the same reason.)
- **Per-node side arrays don't pay either.** Holding each node's first entry in a per-node array costs a slot for every node, but only 43% of nodes have a `shifts` entry.
  - For `shifts`, the array would be 12 B × every node (606 KB at n=8). It would take 21,491 entries out of the map, at about 27 B allocated each (about 580 KB). That is break-even.
  - For `whnf` (one entry on 23% of nodes) it loses. For `ic.lows` it saves about 1.6 B per node.
- **What stands out instead:**
  - `inst` has 6.7 / 9.0 entries per memoized node (many argument lists and depths per node), rising with n, and a 32% hit rate.
  - `bounds` has 0.11 / 0.13 hits per entry: 16 B entries, about 11 B per node allocated, almost never read back. But a hit can save a deep `uses` walk, so its value isn't its hit rate.
  - Neither is a footprint fix by itself.

**Removing the `bounds` memo: negative (2026-10-14; reverted, no patch kept).** `uses` kept its per-node slot and its `loose`-based shortcut, and walked on every slot miss. Against 5bab407, rule 33's law over 8 alternating pairs × 15 reps (RTP off, load 25%, two other sessions' jobs on about one core each):

| | with `bounds` | without | |
|---|---|---|---|
| n=8, median of run medians | 27.9 ms | 28.7 ms | +3%, removal lost 7 of 8 |
| n=64 | 425 ms | 524 ms | +23%, removal lost 8 of 8 |

The decision was clear from the law alone, so `proof_cost_split` was not run. `bounds` stays: its rare hits save deep walks, as its adoption measured (−16% at n=64, "The slot in front of bounds").

**Why `inst` has many entries per node, and the unshared nodes (2026-10-14; probe reverted, no patch kept).** A census of rule 33's check (values n=8 / n=64; hits counted during the check only):
- **Argument lists, not depths, make the entries.** Every (node, argument list) pair has exactly one entry, and no node has more than 2 depths.
  - There are 1,911 / 14,287 distinct argument lists, and 88% / 91% of entries are for lists of several arguments.
  - 17% of entries repeat another entry's result on the same node. So a coarser key would merge little; the lists really differ.
- **87% of entries are never hit** (34,739 of 39,792; 267,251 of 306,408).
  - Hits concentrate on hub nodes instantiated with many lists: nodes with 16 or more entries (447 / 782) hold 70% / 79% of the entries and get 92% / 98% of the hits.
- **Entries on unshared nodes** (one parent, `Spaces::shared` false) **get almost no hits**, across every memo that serves one walk:

  | memo | entries on unshared nodes | hits on unshared nodes |
  |---|---|---|
  | `inst` | 77% / 77% | 14 / 14 (of 18,799 / 148,047) |
  | `ic.lows` | 70% / 69% | 0 / 0 |
  | `shifts` | 69% / 69% | 4.6% / 4.4% |
  | `bounds` | 77% / 77% | 27% / 29% |
  | `whnf` (one memo for the whole region, not one walk's) | 88% / 88% | 73% / 76% |

  - The reason is the one `infer_rc` and `abstract_frees_in` already rely on: an unshared node is reached only through its one parent, so a repeat of the walk stops at the parent's entry first.
  - `shifts` keeps some unshared hits through parents with no entry of their own (call roots, and `inst_rec`'s low nodes, which take the shift path). `bounds` keeps more because `uses` reaches a child again for each new `m`.
  - `whnf` serves calls on arbitrary terms, not one walk, so the rule doesn't apply to it.
- **Candidate, not built:** one rule, "a walk's memo stores only shared nodes", for `inst`, `ic.lows` and `shifts` (`bounds` to be measured separately).
  - At n=64 it would drop about 650,000 of the region's memo entries, 1.7 per node, about 45 B of the 160 B allocated per node (at each memo's allocated bytes per entry). It would also skip their inserts and missed lookups.
  - It loses only `shifts`' unshared hits, on nodes small enough to re-walk cheaply.

**Walk memos store only shared nodes (2026-10-14, adopted).** The candidate above, built.
- **Change:** `inst_rec` memoizes a child only if it is shared and not `hc::low`. `shift_child` shifts an unshared node without the memo. `lowest_loose` reads and writes `lows` only for shared nodes.
  - The rule is stated once, in `hc`'s module doc. It is the one `infer_rc` and `abstract_frees_in` already followed, so every walk's memo now follows it.
  - Since 2026-11-08 `shifts` keeps every node again: the gate's check re-shifted unshared nodes from call roots, 4x the work per doubling (doc 15, "Why the check grew 4x per doubling").
  - `whnf`, `hnf`, `nf` and `bounds` keep every node, as the module doc says why.
- **Check:** `walk_memos_store_only_shared_nodes`. A shared node gets an `inst` and a `lows` entry and an unshared one neither; the test fails with `inst_rec`'s old gate. Every suite passes with the base's counts plus this test (lib 375).
- **Timing** against b0404ef (RTP off; load 26-28%, other sessions' `tier_eval_nn` and `manifold` resident):

  | workload | base | shared only | |
  |---|---|---|---|
  | rule 33's law, n=8, 8 alternating pairs × 15 reps: median of the run medians | 26.6 ms | 20.1 ms | −25%, won 8 of 8 |
  | the same at n=64 | 426 ms | 317 ms | −26%, won 8 of 8 |
  | `proof_cost_split`, 8 alternating pairs: CPU median | 2.95 s | 2.74 s | −7%, won 7 of 8 |
  | the same: build / check median | 2067 / 266 ms | 1891 / 227 ms | |

- **Sweep pair** (`s3_seq.sh shm`, rows `shm_{old,new}_{1,2}`): every unit file is identical on both salts, and so are the `LEMMA_CACHE` lines with paths masked. Only `own.tsv`'s elapsed-seconds column differs (one row on salt 1, 1 s against 0 s). Wall 19/17 s against 17/18 s.

**`bounds` under the same rule: neutral, not adopted (2026-10-14; reverted, no patch kept).** `uses` read and wrote `bounds` only for shared nodes, keeping its per-node slot. Against 0d50e97 (RTP off, load 23-33%):

| workload | base | shared only | |
|---|---|---|---|
| rule 33's law, n=8, 16 alternating pairs × 15 reps: median of the run medians | 21.6 ms | 20.6 ms | −4%, won 8 of 16 |
| the same at n=64 | 321 ms | 301 ms | −6%, won 11 of 16 |
| `proof_cost_split`, 8 alternating pairs: CPU median | 2.68 s | 2.64 s | −1%, won 4 of 8 |

- No workload clears the noise: per-pair differences ran from −7.5 to +3.3 ms at n=8 and from −91 to +67 ms at n=64.
- This fits the census: unshared nodes hold 77% of `bounds`' entries, which the rule no longer stores, but they took 27-29% of its hits, which now walk.
- `hc`'s module doc keeps `bounds` as the exception. Adopting it only for one uniform rule would need its own sweep pair.

**Footprint per node after shared-only walk memos (2026-10-14; probe reverted, no patch kept).** The probe from "Footprint per node of rule 33's check on B", rebuilt unchanged and run on 4ba3f6c. The checks add the same 50,487 and 385,032 region nodes as before. Values are n=8 / n=64, in B per new node:

| | used before | used now | allocated before | allocated now | entries per node now |
|---|---|---|---|---|---|
| `memo.inst` | 12.6 / 12.7 | 2.8 / 2.9 | 22.1 / 23.1 | 5.5 / 5.8 | 0.18 (was 0.79-0.80) |
| `memo.shifts` | 13.2 / 13.6 | 4.0 / 4.2 | 22.1 / 23.1 | 5.5 / 5.8 | 0.25 / 0.26 (was 0.83-0.85) |
| `ic.lows` | 9.0 / 9.4 | 2.6 / 2.7 | 16.9 / 17.7 | 4.2 / 4.4 | 0.22 / 0.23 (was 0.75-0.79) |
| `memo.bounds` (unchanged) | 5.1 / 5.4 | 5.1 / 5.4 | 11.0 / 11.6 | 11.0 / 11.6 | 0.32 / 0.34 |
| region vectors and table (unchanged) | 45.0 | 45.0 | 67.2 / 70.6 | 67.2 / 70.6 | |
| the rest | 7.6-8.4 | 7.6 / 8.2 | 12.5-14.9 | 12.6 / 14.7 | |
| **total** | **92.5 / 94.4** | **67.1 / 68.4** | **151.7 / 160.9** | **106.0 / 112.9** | |

- **The rule saved 46-48 B allocated per node (−30%),** as the census predicted (about 45 B). A check's working set is now 5.4 MB at n=8 and 43 MB at n=64, against 7.7 and 62 MB.
- **The region's own arrays are now the largest part:** 67-71 B of the 106-113 allocated. These are `nodes` (36-38 B at 24 B used), `loose`/`free`/`uses` (18-19 B), and the table (12 B). `bounds` is now the largest memo, at 11-12 B.
- **The vectors' growth slack is not a cache cost** (read from `spaces.rs`, not timed). The vectors' allocation is 1.5-1.6× their use, but capacity past `len` is never touched. `Space::clear` (`reset_vec`) keeps capacity unless the region used under a quarter of it, so repeated checks of one size never reallocate after the first. The hash maps are different: a probe can land anywhere in them, so their slack is touched.
- **What the cache sees** is therefore the vectors' used bytes plus the maps' allocated bytes:
  - now: about 38 + 50-54 ≈ 88-92 B per node, so 4.4 MB at n=8 and 35 MB at n=64, about 2.1× the 16 MB L3, which fills near 185,000 nodes (about n=32);
  - before the rule: about 38 + 95-102 ≈ 133-140 B per node, so 54 MB at n=64, with L3 full near 120,000 nodes (about n=20).
  - The "about n=16" in the first footprint entry used allocated bytes, so it overstated the working set.
- **Rule 33's law still rises with n:** 20.1 ms at n=8 against 317 ms at n=64, 15.8× for 7.6× the nodes.
- **Candidates left:** a struct-of-arrays region row (fewer cache lines per node visit), and the hash maps' load factor and entry size (they now hold most of the touched bytes). The 16-byte node was rejected above.

**ns per node against n after shared-only walk memos (2026-10-14; probe reverted, no patch kept).** This is the Stage 3 B sweep (rule 33's law proved once, then checked in fresh regions; 1,500 reps at n=2 down to 6 at n=128). b0404ef and cb36ad2 alternated per n, over 4 rounds. Load was 43-63%: `manifold`, two `renno` processes and `tier_eval_nn` were resident, so the figures are best-of-4 and the gaps within an arm are noise-sized. RTP was off.

| n | 2 | 4 | 8 | 12 | 16 | 24 | 32 | 48 | 64 | 96 | 128 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| region nodes (both) | 14,579 | 26,588 | 50,487 | 74,384 | 98,280 | 146,072 | 193,864 | 289,448 | 385,032 | 576,200 | 767,368 |
| b0404ef, ns per node | 510 | 560 | 720 | 748 | 718 | 916 | 931 | 1099 | 1219 | 1039 | 1146 |
| shared only, ns per node | 459 | 491 | 509 | 589 | 611 | 621 | 683 | 863 | 805 | 901 | 808 |
| ratio | 0.90 | 0.88 | 0.71 | 0.79 | 0.85 | 0.68 | 0.73 | 0.79 | 0.66 | 0.87 | 0.70 |

- **Shared-only is 10-34% cheaper per node at every n,** and its rise is smaller: from about 460-510 at n=2-8 to 800-900 at n≥48 (about 1.7×), against old's 510-720 to 1,040-1,220 (about 2×).
- **The knee is not resolved.** The footprint above predicts L3 filling near n=20 before and n=32 now. Under this load, best-of-4 still has non-monotone steps (old at n=96 reads below n=64; new at n=128 reads below n=96), which are larger than any knee to be read. A quiet-machine rerun is parked until the other sessions' jobs are gone.

**The hash maps' load and entry size (2026-10-14; analysis, nothing built).** hashbrown allocates buckets × (entry size + 1) + 16 bytes, and that formula reproduces every allocation in the footprint probe above exactly. So each map's bucket count and load follow from it (n=64 on cb36ad2):

| map | entries | entry B | buckets | load | allocated B per node |
|---|---|---|---|---|---|
| `region.table` | 385,032 | 8 | 524,288 | 0.73 | 12.3 |
| `memo.bounds` | 129,123 | 16 | 262,144 | 0.49 | 11.6 |
| `memo.inst` | 68,673 | 16 | 131,072 | 0.52 | 5.8 |
| `memo.shifts` | 100,072 | 16 | 131,072 | 0.76 | 5.8 |
| `ic.lows` | 87,571 | 12 | 131,072 | 0.67 | 4.4 |
| `memo.whnf` | 86,747 | 8 | 131,072 | 0.66 | 3.1 |
| `ic.types` | 37,658 | 16 | 65,536 | 0.57 | 2.9 |
| `ic.window_of` | 31,945 | 16 | 65,536 | 0.49 | 2.9 |
| `memo.arg_sets` | 15,761 | 32 (plus heap keys) | 32,768 | 0.48 | 2.8 + 0.7 |
| `ic.context_of` | 20,411 | 20 | 32,768 | 0.62 | 1.8 |

- **No load-factor lever.** Tables are powers of two with a 7/8 maximum load, so load is 0.44-0.875 by where the count lands. `bounds` just doubled, and the size below (131,072 buckets) cannot hold 129,123 entries at 7/8. Pre-sizing cannot help either: tables already keep their capacity between regions.
- **Little entry-size lever.** Nearly every entry is 8-16 B of `u32`s.
  - Packing `bounds`' `(lo, hi)` into one `u32` saves about 2.7 B per node (about 3% of the ~90 B the cache sees), and needs a fallback past 65,535.
  - Packing `shifts`' cutoff and amount saves at most about 1.5 B.
  - Dropping the table's stored hash halves its 12.3 B, but makes every probe read `nodes`.
- **Merging the memos into one table** would pool their power-of-two slack, but they clear at different times (`ic` per check, `Memos` per region). It is a large restructure for at most about 15 B per node, unmeasured.
- **Verdict: parked.** The maps hold about 30 B used and 54 B allocated per node, and the cheap levers left are worth about 3%. Shrinking bytes per node has reached diminishing returns.

**Where `proof_cost_split` spends its time on B (2026-10-14; probe reverted, profiles not kept).** Two samply profiles of `proof_cost_split` (cmp3d own, 300 laws) on fc68b43 (kernel code as of 0d50e97) built with debug info. A throwaway wrapper test set `cpu_ab.ps1`'s environment in-process, because samply's task cannot pass one. Analysed with `prof_cases.py` (pointed at each profile), `prof_callers.py`, `prof_self.py` and `prof_addr.py` with `llvm-symbolizer`. RTP off.
- **The first profile caught a slow large-page state.** Load not recorded; 7,673 busy samples; the rule proofs' build took 5,673 ms against its usual 1.7-2.0 s.
  - `Space::push` was 43% of busy samples. 29% was `RawVec::grow_one`, reaching mimalloc's realloc and then the kernel's `NtAllocateVirtualMemory`, and 12% was the table's `reserve_rehash`.
  - An A/B of large pages on against `MIMALLOC_ALLOW_LARGE_OS_PAGES=0` followed (4 alternating pairs, load 19%, user and kernel CPU per process). The first run with large pages took 2.20 s of kernel time and a 3,897 ms build. Every other run, either arm, took 0.23-0.67 s of kernel time and 1,651-1,922 ms.
  - So committing large pages is sometimes very slow, presumably when the OS must find and zero contiguous memory. One event in 4 runs: how often a sweep's short processes pay it is unmeasured.
- **The second profile is the steady state** (load 17%, 2,856 busy samples, rule-proofs build 1,980 ms). Inclusive shares of busy samples:
  - kernel checking (`check_rc`) 66%: `whnf_in` 52%, `conv` 51%, `instantiate_n` 45%, `hnf_rc` 30%;
  - the 37 rules' own proofs (`prove_rule`) 50%, made of their case lemmas' kernel checks (`ck`, 38.5%) and their building (`lemma_n`, 11%);
  - the 296 laws (`check_laws`) 7.5%.
  - `Space::push` is 5.4% here, so growth is not a steady-state cost.
- **Interning is the largest single cost:** `Spaces::mk` is 37% inclusive and 19% self.
  - 384 of its 542 self samples (13.4% of all busy samples) sit on one instruction. It follows the load of the region table's first control group in `region.find` (`spaces.rs:317`, `Group::load` in hashbrown's `find_inner`), which is a cache miss on the probe.
  - hashbrown's find closure, which reads the bucket's stored hash and on a match the node, adds 10.6%.
  - `mk`'s callers: `inst_rec` 23.4% of busy samples, `app` 4.9%, `shift_unchecked` 2.3%. So instantiation's hash-consing in a large region is about a quarter of the run.
- **What it points at:** the cost per `mk` is about three random cache lines (control group, bucket, node), not instructions. The census entries above give the volumes on rule 33: 19-21% of built nodes are not in the table when it drops, and 87% of `inst` entries are never hit. So building fewer transient nodes is the lever on `mk`, not cheaper probes. Candidates, unmeasured:
  - a software prefetch of the control group, issued as soon as `hash(n)` is known;
  - instantiation that does not intern intermediate spines (`closed_prefix_spine` is 45% inclusive) where only the head normal form is kept;
  - for the large-page stalls: count how often they hit a sweep's processes before choosing between keeping large pages and a smaller reserve.

**Instantiating only the head would save little (2026-10-14; probe reverted, no patch kept).** `proof_cost_split` on fb5c176, with a probe at each of the four beta sites. Per site, it counted the `mk` calls in the instantiation, the region nodes the instantiation newly built, and how many of those the reduced result still reaches. The reduced result is the whnf, or for `hnf_rc` its head normal form.

| site | frames | `mk` calls | new nodes | reached by the result |
|---|---|---|---|---|
| `whnf_step`, one argument | 57,279 | 175,608 | 65,616 | 768 (1%) |
| `beta_spine` | 15,576 | 174,793 | 33,024 | 23,783 (72%) |
| `closed_prefix_spine` | 293,670 | 1,272,208 | 639,215 | 633,967 (99%) |
| `hnf_rc` | 261,280 | 2,403,958 | 1,728,809 | 1,382,575 (80%) |
| all four | 627,805 | 4,026,567 | 2,466,664 | 2,041,093 (83%) |

- **The run made 10.1 M `mk` calls; 4.27 M of them (42%) are inside `instantiate_n`,** and the four sites account for 4.03 M of those. Instantiation's calls are more often new nodes (61%), which fits their larger share of `mk`'s time in the profile above (23.4 of 36.6 points).
- **The bound:** only the 425,571 unreached nodes (17%) could be skipped by instantiating just what the head needs. That is 4.2% of all `mk` calls, so at most about 2% of the run, even before paying for the closures a lazy instantiation needs.
  - "Reached" means kept in the result, not read later. A fully lazy, environment-based machine could skip more. But hash-consed equality compares built nodes, so `conv` would build most of them anyway.
  - The one-argument beta in `whnf_step` throws away 99% of what it builds: a Church boolean picking a branch. But it is only 2.7% of these nodes.
- **Verdict: dropped.** `mk`'s cost is the price of each interning, not wasted work. What is left is the price per probe: a software prefetch of the region table's control group, issued as soon as the node's hash is known (unmeasured).
- The build took 3,561 ms under the probe (its reachability walks), against about 1,900 unprobed; the counts are deterministic.

**How often the large-page stall hits a sweep (2026-10-14).** Six full sweeps (`sweep_job.ps1`, salt 1, `mines own cold pooled`, 178 processes each) on fb5c176, alternating large, normal, normal, large, large, normal pages. RTP off, load 14-22%. `sweep_job.ps1` now also prints the job's kernel time.

| pair | large: job CPU / kernel / wall | normal: job CPU / kernel / wall |
|---|---|---|
| 1-2 | 57.3 / 23.02 / 40.5 s | 54.4 / 20.17 / 37.3 s |
| 3-4 | 53.1 / 22.55 / 38.3 s | 52.8 / 20.13 / 37.2 s |
| 5-6 | 52.9 / 19.69 / 37.1 s | 51.8 / 19.97 / 36.7 s |

- **Normal pages give a flat 20.0-20.2 s of kernel time.** Two of the three large-page sweeps took 2.4-2.9 s more; the third took none. That is about one `proof_cost_split`-sized stall per sweep, or the per-process commit below plus noise; these runs cannot tell the two apart.
- **Large pages lost all 3 pairs on job CPU** (by 0.3-2.9 s), against winning 3 of 3 by about 4% when adopted. One reading: the adopted gain was within the pairs' spread. The job's peak memory is 545-609 MB against 380-382 MB.
- `proof_cost_split`'s 12% gain from large pages is unaffected: it is one long process.
- **Large pages cost every process an up-front commit.** An empty launch of the test exe (a test name matching nothing, 20 per arm in a job object, `floor_job.ps1` in the scratchpad, not kept) took 3.9-23.4 ms of kernel time per process with large pages (median 7.8, 14 runs; all reserved 64 MiB, see below) against 2.3-5.5 ms without (median 3.9, 3 runs), at loads up to 94%. About 4 ms more for each of 178 processes is about 0.7 s a sweep.
  - A smaller reservation can't cut it: `MIMALLOC_ARENA_RESERVE=8MiB` still reserved 65,536 KiB (`MIMALLOC_VERBOSE=1`), so 64 MiB is the floor as built.
  - A bare number there is read as bytes ("8192" is 8 KiB, rounded up to the same floor).
- **Decided: `driver::sweep` turns large pages off for its children** (`MIMALLOC_ALLOW_LARGE_OS_PAGES=0` in the environment it passes them). Its machine-state line now runs with that environment, so `pages=` reports the children's pages. Single long runs (`proof_cost_split`, the law checks, loops) keep them.
  - A sweep on the change: `pages=normal`, 1.26 M faults and a 270 MB peak process (the normal arm's), and outputs identical to round 1 apart from the seconds column.
  - Its timing is void: load 78-99%.
- **Kernel time is 37-40% of the sweep's CPU in both arms,** about 112 ms per process, as Windows accounts it. That accounting turned out to be unreliable (last bullet).
  - Not the launch: an empty launch takes 2.3-5.5 ms.
  - Not page faults alone: normal pages took 1.33 M faults and large 0.56 M, at the same 22 s of kernel time.
  - samply doesn't see it. A profile of the sweep (a throwaway wrapper test setting its environment, reverted) has only 8.0% of busy samples with a kernel-mode leaf, about 4.4 s of 54 s. The single-process `proof_cost_split` profile shows the same gap: 2.1% kernel-mode leaves against 10-22% of its accounted CPU.
  - A pure user-mode loop is charged 3% kernel time (0.16 of 5.0 s), so the accounting isn't simply biased. Sampling the machine's privileged-time counter during a sweep was swamped by other sessions' 14.6% baseline.
  - **Resolved (2026-10-14): the accounted kernel/user split is unreliable on this machine; the sweep doesn't spend 40% in the kernel.**
    - **xperf trace of a salt-1 sweep on 10b68ad** (`sweep_xperf.ps1`, run elevated by the user: sampled profile with stacks, context switches, all page faults, virtual allocations; no lost events).
      - The job reported 50.8 s CPU, 20.6 s of it kernel, and 1.37 M faults.
      - The profile saw 48.3 s in the sweep's 166 processes, so the totals agree.
      - Only about 4.5 s of that was in kernel modules (`ntoskrnl.exe` 3.9 s, `Ntfs.sys`, `ahcache.sys`, `vgk.sys`, `FLTMGR.SYS` and the GPU driver the rest). The rest was in the test binary, which agrees with samply.
    - **Not page faults:** touching fresh committed memory costs about 0.5 µs per demand-zero fault, so 1.37 M faults are under 1 s.
    - **The split moves between identical runs:** eight `proof_cost_split` runs were charged 0.11-0.61 s of kernel time, while kernel plus user stayed at 2.70-2.91 s.
      - Turning mimalloc's purging off (`MIMALLOC_PURGE_DELAY=-1`) changed nothing (old 0.11-0.47 s, new 0.16-0.61 s), so decommits and the TLB flushes they cause aren't it.
      - Windows charges whole timer ticks of time to a thread's kernel or user mode, and the machine runs under the hypervisor (virtualization-based security is on, no services under it). What misattributes the ticks is not known.
    - **Consequence:** compare total CPU (kernel plus user), never kernel time alone, as `runs`' `jobcpu` does (and `cpu_ab.ps1` and `sweep_job.ps1` did). Where the time actually goes, use samply or xperf samples.

**Prefetching the region table's control group: neutral, not adopted (2026-10-14; reverted, no patch kept).** `Spaces::build` issued a `_mm_prefetch` (T0) of the region table's first control group as soon as the node's hash was known. That is before the persistent lookup and the region lookup, which "Where `proof_cost_split` spends its time on B" found to be a cache miss worth 13.4% of busy samples.
- **Reaching the control bytes:** hashbrown 0.16.1 has no prefetch hook. But an `OccupiedEntry` from `insert_unique` gives its entry's address and bucket index, and the entries lie downwards from the control bytes. So the control array starts at the entry's address plus (index + 1) × 8 B, refreshed on every insert since a resize moves it. The group is at that start plus (`spread(h)` & bucket mask).
  - This depends on hashbrown's undocumented layout. A debug check (the inserted bucket's control byte equals the hash's top 7 bits) held across all 126 kernel unit tests.
- **`proof_cost_split`, prefetch on against `NO_PREFETCH=1`, same binary** (`cpu_ab.ps1`, 8 alternating pairs, load 58% at the start and 24% at the end, RTP off):
  - CPU median 2.59 s on against 2.61 s off; prefetch won 3 of 8 pairs.
  - Build median 1,762 against 1,764 ms.
- **Why nothing:** the prefetch issues no earlier than the out-of-order core already issues the load. The lookup's address depends only on the hash, which is ready at the same point. When a node has persistent children, the region lookup sits behind a branch on the persistent lookup that is almost always predicted, so it already runs speculatively in parallel. The two misses after the control group (the entry, then the node to compare) depend on the first one and cannot be prefetched from the hash.
- **Having the hash earlier is not possible (checked 2026-10-14).** A node's hash is computed from its children's `Ref`s, and `inst_rec` calls `mk` as soon as the last child returns, so the hash exists no sooner. The last child's `Ref` comes out of its own lookup, so the misses form a dependent chain: child lookup, then the parent's hash, then the parent's lookup. A hash of content rather than `Ref`s doesn't help either, since computing one for a child not yet built means walking it.
- **Placing nodes by recency would not help (counting probe on 3e5c74b, reverted, no patch kept).** The idea was to put the bucket of a node near the buckets of nodes built just before it, so lookups touch a warm part of the table. A probe counted `proof_cost_split`'s 10.1 M region builds by how many builds ago the node's newest region child was made:

  | newest region child made | region hit | new node |
  |---|---|---|
  | no region child | 786,287 | 510 |
  | 1 build ago | 0 | 2,591,264 |
  | 2-16 | 200,877 | 121,482 |
  | 17-256 | 225,224 | 105,782 |
  | 257-4K | 641,273 | 201,982 |
  | 4K-64K | 1,629,312 | 273,976 |
  | over 64K | 3,167,735 | 153,845 |

  - The new nodes total 3,448,841, the region's size; no build hit the persistent space.
  - Hits are mostly over old children (3.2 M over 64K builds ago), so recency gives them no locality. Recent children are mostly new nodes, which the next point handles without the table. Dropped.
- **Skipping the lookup that must miss: adopted (2026-10-14).** A node whose region child has no parent yet cannot already exist. `parents` is raised only when a node is pushed, and persistent nodes have no region children. 2,591,264 builds (26% of all, 75% of the new nodes) fall in the "1 build ago" row, where that holds by construction; more may fall in other rows. So `Spaces::build` skips `region.find` for them, which is safe for Invariant I. A debug assertion that such a node really is absent holds in all kernel unit tests. The insert still touches the same control group, but nothing waits on it, since the new `Ref` is the array length.
  - `proof_cost_split`, skip on against off in the same binary (`cpu_ab.ps1`, two rounds of 8 alternating pairs, RTP off):

    | round | load | CPU median, off / on | build median | skip won |
    |---|---|---|---|---|
    | 1 | 33% at the start, 45% at the end | 2.84 / 2.64 s (−7%) | 1,954 / 1,797 ms (−8%) | 6 of 8 |
    | 2 | 28% at the start, 33% at the end | 2.84 / 2.65 s (−7%) | 1,935 / 1,830 ms (−5%) | 7 of 8 |
  - **Full salt-1 sweeps: no detectable effect (2026-10-15).** Twelve sweeps of the same binary in job objects, `SKIP` off and on alternating (two sets of 3 pairs, load 16-39%, RTP off). Job CPU median 51.5 s off against 52.2 s on (+1.5%); the skip won 2 of 6 pairs. Identical sweeps vary about ±10% (46.7-55.7 s off, 49.5-58.8 s on), so the sweep cannot resolve a few percent. It likely spends less of its CPU in large regions than `proof_cost_split`, though that is not measured. Kept: it is sound, and it wins on the kernel-bound benchmark.

**mimalloc against the system heap, after the id-arena port (2026-10-14; probe reverted, no patch kept).** The question was whether to drop mimalloc and do its useful parts directly, now that the kernel keeps its nodes in a few large arrays instead of one block each. Two test binaries were built from 193a1a5. One is as committed. The other has the test crate's `#[global_allocator]` removed, and `machine::large_pages_option` made to return false, since it calls into mimalloc. `MIMALLOC_VERBOSE=1` printed 50 lines from the first and none from the second. RTP off.

| run | mimalloc | system heap | system's cost |
|---|---|---|---|
| `proof_cost_split`, mimalloc on large pages (8 pairs, load 10%) | CPU median 2.26 s, build 1,552 ms | 2.81 s, 1,834 ms | +24% CPU; mimalloc won 8 of 8 |
| `proof_cost_split`, mimalloc on normal pages (8 pairs, load 11%) | 2.22 s | 2.47 s | +11%; mimalloc won 7 of 8 |
| full salt-1 sweep (3 pairs, load 3-25%) | job CPU 43.9 / 46.5 / 58.9 s, wall 32.7-41.4 s | 67.9 / 72.6 / 81.0 s, wall 43.7-50.2 s | +38% to +65%; mimalloc won 3 of 3 |
| sweep memory | peak process 285-295 MB, job 487-550 MB | 208-209 MB, 299-302 MB | mimalloc uses 40% / 70-80% more |

- **Most of mimalloc's value is outside the kernel.** The sweep, which also mines, scores and builds proofs, gains far more than `proof_cost_split`'s check. Those parts allocate many small, short-lived objects, which is what mimalloc is fast at. Replacing it means writing a general allocator, so dropping it is ruled out.
- The two `proof_cost_split` runs are not comparable with each other (they ran one after the other, not interleaved), so they say nothing new about large pages.
- The system heap faults more (1.79 M against 1.25 M per sweep) but peaks lower. mimalloc keeps freed memory for reuse instead of returning it.
- **Still open:** moving the id arena's own arrays and table onto reserved address space, committed as they grow, so they never move and can use large pages on their own (option 1 of the allocator question). mimalloc stays the global allocator either way. Its upper bound was then measured and found to be zero; see the next entry.

**Arrays that never grow: no measurable gain, so reserved storage for the id arena is parked (2026-10-14; probe reverted, no patch kept).** This spike bounds what storage that never moves could buy. A probe on ef75b36 reserved the region's five arrays and its table for `PRESIZE` nodes when `Spaces::open` runs, so nothing grew or was copied. `proof_cost_split` has one region, which ends at 3,448,841 nodes; it grows to capacity 4,194,304 and 4,194,304 table buckets. `PRESIZE=3500000` was compared against the same binary without it (`cpu_ab.ps1`, two rounds of 8 alternating pairs, RTP off).

| round | load | CPU median, growing / presized | build median | presized won |
|---|---|---|---|---|
| 1 | 20% at the start, 53% at the end | 2.57 / 2.47 s (−3.7%) | 1,799 / 1,641 ms | 6 of 8 |
| 2 | 10% at the start, 36% at the end | 2.36 / 2.55 s (+8%) | 1,602 / 1,732 ms | 2 of 8 |

- Over the 16 pairs presizing won 8, and the two rounds disagree in sign by more than either effect. The cost of growth (about 22 doublings, each copying the arrays and rehashing the table once) is below this benchmark's noise, about ±5% here.
- Reserved storage could also give the arena large pages of its own. That is not measured by this probe, but mimalloc already serves these arrays from large pages in `proof_cost_split`, so there is little left to gain.
- **Parked:** option 1 of the allocator question. Revisit only if a profile shows growth (`reserve_rehash`, `memcpy` from `Vec` growth) as a visible share of the build.

