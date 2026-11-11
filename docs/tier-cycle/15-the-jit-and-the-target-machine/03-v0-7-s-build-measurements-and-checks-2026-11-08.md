### v0.7's build: measurements and checks (2026-11-08)

The checks and measurements the v0.7 plan (`docs/superpowers/plans/2026-11-08-v07-straight-line-gate.md`) takes on
the way to the gate.

**The closure prover covers what `prove_pure_expr` accepted.** Before `prove_pure_expr` is deleted, terms outside the
fragment must still install through `prove_closure_expr`. A temporary probe in `kernel_verify` and in `ir_fuzz`'s
reference run printed, for every term `prove_pure_expr` accepted, whether `prove_closure_expr` accepted it too, over
the whole tatic suite (run `2026-11-08-v07-c1-closure-covers`): 932 lines, 170 distinct terms, all covered, no miss.
A temporary test also checked the three terms the plan relies on to install through the chain:
`\a b. 1 + (if a < b then a else b)`, `\a b. if (if a < b then a else b) < 1 then 1 else 0` and `\a b. a / b`, all
accepted. The probe was reverted.

**The operator table agrees with eval and wasmtime.** `crates/tatic/src/jit/op_table_tests.rs` checks each `Op` row
three ways: `\a b. a OP b` (or `if a OP b then 1 else 0` for a compare) through `eval::apply_term`, the same source
through the production lowering under wasmtime, and the row's kernel circuit by `def_eq`, all at n bits with the
arguments sign-extended to i64. `Op::LtU` has no source operator, so only its circuit is checked, against unsigned `<`.
Each check was shown to fail on its own: mapping `Lt` to `LtU` in `shape::op_of` broke eval against wasm at
`(MIN, 0)`, and giving `Op::LtS` the `lt_u` circuit broke `def_eq` there. The default test (n = 64) first used
`ir_fuzz.rs`'s 8 edges squared and took 4.0 s, 3.9 s of it in `mul`'s circuit; cut to `{MIN, -1, 0, 1, MAX}` it takes
1.6 s (`mul` 1.5 s), still over the plan's 1 s, and kept as the only always-on guard on the table (debug build, one test
thread of a parallel suite); the 8 edges run ignored since (`op_table_agrees_at_n64_on_all_edges`, 5.0-6.1 s after
the `karrow` fix, `mul` 4.9-6.0 s of it, so that fix did not touch `mul`'s circuit check). The ignored n = 8 test runs all 65,536 pairs per row and passed in 47 s, `mul` 26 s of it
(run `2026-11-08-v07-op-table-n8`).

**The gate's costs, and the rules they triggered.** `proof/gate.rs` proves the emitted body of a fragment term equal to
the source at n = 64 (`gate`); its tests accept the 5 Goal 1 terms and 4 more, and reject every Goal 2 mutation and a
`Raw` line. Spec section 8's measurements ran on the production statement builder and check (`measure_gate_costs`,
run `2026-11-08-v07-gate-measure_gate_costs`; tatic's test profile is optimized with debug info), build ms + check ms:

| term | build | check |
|---|---|---|
| `inc`, fuel 1 on the `loop` wrapper | 7.2 | 1.4 |
| `inc`, bare body, fuel 0 | 7.3 | 1.4 |
| `doubling(4)` (32 nodes) | 28 | 2.7 |
| `doubling(7)` (256 nodes) | 250 | 21 |
| `doubling(8)` (512 nodes) | 606 | 51 |
| `doubling(10)` (2048 nodes) | 2520 | 531 |
| `doubling(13)` (16,384 nodes, the JIT's tree cap) | 26,126 | 67,580 |
| `\a b. a * b` | 12.7 | 12.3 |
| `\a b. if a < b then a * b else a` | 16.3 | 17.3 |

- **Fuel 1:** the wrapper costs nothing measurable, so the gate proves `[Loop(body)]` as printed; no fallback and no
  trusted "a `loop` with no `br` is its body" fact.
- **Tree size:** the build doubles with the tree (linear) and the check grows faster (5.8x from d = 12 to 13), so the
  gate alone passes the JIT path's 0.4 s at 512 nodes, far below the 16,384-node cap. `in_fragment` takes trees of at
  most 256 nodes (`MAX_GATE_TREE`, `doubling(7)`; 1024 since the build fix below, 2048 since the shift memo below, 8192 since the build's constants below); a larger straight-line term
  installs through the existing chain.
- **`Mul`:** 25-34 ms with two parameters as operands, so `Mul` stays in the fragment unrestricted.
- **Stack:** building and proving `doubling(13)` on a 2 MB thread overflowed (run `2026-11-08-v07-gate-measure_stack_2mb`),
  so `Wasm::seq` and the gate's `cps` now run each step under `tatic_kernel::grow`; the same run then passed in 105 s
  (run `2026-11-08-v07-gate-measure_stack_2mb-grow`). It stays an ignored test: the bound keeps such trees from the
  gate, and 105 s is no default test.
- **After `grow`, and nested `Mul`:** the table above was measured before `grow` was added. Rerun with it (run
  `2026-11-08-v07-gate-costs-after-grow`, cpu 26%, one rep per tree): `doubling(7)` 305 + 19 ms, `doubling(8)` 591 +
  44 ms, `doubling(13)` 31,968 + 104,208 ms. The bound stands: 256 nodes is the largest power of two under the JIT path's
  0.4 s. Products of symbolic products cost no more to check than one: `(a*b)*(a*b)` 25 + 10 ms, `(a*b)*(b*a)` 29 + 10
  ms, and a chain `a * b * .. * b` of k products builds in 24 ms (k = 2) to 48 ms (k = 8) and checks in 10-13 ms
  throughout, so `Mul` needs no rule of its own.
- **The build was `karrow`:** a samply profile of the build at `doubling(7)` and `(8)` (run
  `2026-11-08-gate-build-profile`) put 61% of its samples under `Wasm::sty` -> `word` -> `bv_ty` -> `karrow`, all of
  it `arrow`'s codomain shift: `karrow(n)` nested n arrows, so each 64-bit word type cost about 2,000 node shifts, and
  `sty` makes one per stack slot per instruction. Rebuilding `Op::term(64)` per instruction (0.25 ms each) and building
  `prog` twice were the smaller part. `karrow` now writes its binders directly, as `bool0` does
  (`karrow_is_the_arrow_chain` pins it to the arrow chain). Rerun (run `2026-11-08-gate-costs-direct-karrow`, cpu 77%,
  one rep per tree): `doubling(7)` 17 + 26 ms, `doubling(8)` 34 + 53 ms, `doubling(9)` 66 + 184 ms, `doubling(10)`
  126 + 790 ms, `doubling(13)` 1,748 + 102,289 ms. The build is now linear and small; the check grows about 4x per
  doubling from d = 9 and is the whole cost above 512 nodes. By the same rule the bound is now 1024 nodes
  (`doubling(9)`, 0.25 s even at 77% load; `doubling(10)` takes 0.92 s); the table test accepts `doubling(9)` and
  `in_fragment_rejects_the_rest` refuses `doubling(10)`. The sweep barely gains: in a samply profile of a salt-1 sweep
  on the build before the fix (run `2026-11-08-karrow-sweep-profile`, 199,220 busy samples) `karrow` is 0.62%
  inclusive, since the sweep mines at small widths, where the n^2 / 2 shifts are few. That share caps the gain, so no
  sweep A/B was run.
- **Why the check grew 4x per doubling:** `shift_child` memoised only shared nodes, by the rule for a walk's memo (doc
  14, "Walk memos store only shared nodes"): a repeated walk stops at the parent's entry first. But shifts start from
  call roots with no entry, and the check reached the same unshared program suffixes from such roots at every step: at
  `doubling(9)`, 2.43M shift calls over 11,823 distinct (node, cutoff, amount), 97% of the left side's whnf work (run
  `2026-11-08-o5-check-growth`, a probe). `shifts` now keeps every node (`hc`'s module doc). The check's kernel work at
  `doubling(7)`, `(8)`, `(9)` fell from 216k, 715k, 2.60M to 59k, 106k, 201k, and `gate_check_work_is_linear_in_the_tree`
  fails above 2.6x per doubling (the old memo gave 3.3x and 3.6x; runs `2026-11-08-memo-check-work-a` and `-b`). Rerun (run `2026-11-08-memo-gate-costs`, cpu 44%, one
  rep per tree): `doubling(10)` 184 + 147 ms, `(11)` 402 + 309 ms, `(12)` 945 + 828 ms, `(13)` 2,265 + 2,495 ms, against
  102 s of check before; the build now grows 2.2-2.4x per doubling too (next bullet). By the same rule the bound is
  now 2048 nodes (`doubling(10)`, 0.33 s; `doubling(11)` takes 0.71 s). The church-bv gate is unchanged (run
  `2026-11-08-memo-gate3`, salts 1-3: M 447 and held-out M 5166 both arms, rules the same in 9 of 9 loops, peak process
  3,336 MB both). Its pin test (`streams::stream_sequences_are_pinned`, about 863 G instructions) passed on both arms
  and counts the same (run `2026-11-08-memo-count-rot2`, 2 runs per batch, batches a b b a b a a b on CPU 4, cpu 37%):
  the two flat batch pairs (max/best 1.0002 or less) differ by -0.001% and -0.010% in B's favour, and the first two pairs
  (max/best up to 1.004, the large-page wander of doc 14, "Why a retired-instruction count wanders") by +0.15% and
  +0.30% against it.
- **Why the build grew 2.2x per doubling:** the build rebuilt closed constants. Profiled at
  `doubling(7)` to `(13)` in release (`2026-11-08-build-growth-profile2`, samply), 80% of its samples sit in
  hash-consing: `seq_step` rebuilds `bv_ty(64)` for every slot of every instruction's stack type (49% inclusive), and
  `Op::term` the operator's circuit at every `Op` (15%). A stack slot's type costs `O(depth)` per instruction, the
  log factor. `statement` also builds the left side twice, once for the statement and once in `refl`. Memoising
  `bv_ty` and `Op::term` per interning generation (as `gates::constant` does for closed constants) and building `sty`
  with one shift of the base took the release build at `doubling(13)` from 837 ms to 64 ms, its kernel work from 738k
  to 148k, 1.98x per doubling. Test profile, one rep each (`2026-11-08-build-memo-gate-costs`, cpu 25%):
  `doubling(11)` 30 + 166 ms, `(12)` 42 + 317 ms, `(13)` 94 + 738 ms. The spike
  (`docs/superpowers/spikes/2026-11-08-build-memo.patch`) added two thread-locals, which church-bv's
  `hidden_state_is_classified` rejects; as landed, `gates::constant`'s one memo takes a key and `constant_n` builds a
  family of closed terms once per (builder, width), used by `bv_ty` and `Op::term` (`Source::op`'s local cache went), and
  `gate_build_work_is_linear_in_the_tree` fails above 2.05x per doubling (1.94x, 1.97x). Timed, before against after,
  A B A B, best of 3 per tree (runs `2026-11-08-gate-ab-a1-t18`, `-b1-t8`, `-a2-t8`, `-b2-t6`, cpu 12-24%, after 34
  refusals on a busy machine), build + check in ms: `doubling(12)` 491 + 285 and 477 + 290 before, 45 + 334 and
  41 + 306 after; `(13)` 1105 + 733 and 969 + 604 before, 96 + 788 and 85 + 656 after. The check is the same on both
  arms (its kernel work too, within 0.04%), so the faster check of the one-rep run was the 44% load of the run before it;
  after reads 5-15% higher at d = 12 and 13, inside the wall noise here. By the 0.4 s rule the bound is now 8192 nodes
  (`doubling(12)`, 0.35-0.38 s; `doubling(13)` takes 0.74-0.88 s), set by the check.
- **Where the check's time goes at the bound (profile):** `doubling(13)` in release took 80 ms to build and 641 ms to
  check (run `2026-11-09-check-profile`, samply, 759 busy samples, one run). The check is weak-head reduction of the
  machine: `whnf_in` 35% inclusive, of which `whnf_sigrec` / `beta_spine` 28% (stepping the stack records), and
  `instantiate_n` 31%, which is mostly the hash-consing it drives (`Spaces::node` 19%, `Spaces::build` 17%) and the
  `hc::uses` test that lets an instantiation skip a subterm (12%). No frame stands out on its own; the largest leaf is
  hashbrown's probe (`_mm_movemask_epi8` 5%, `probe_seq` 4%). Doubling the bound would need the check to be more than
  twice as fast, so it stays at 8192 until the machine's reduction changes. Half the gate's build was its proof's copy
  of the lhs (build work 37491 against 18792 without it at `doubling(11)`, a one-off probe). `encoding::law` now walks
  its telescope once, its body giving the proof and the statement together, so every law builds a subterm the two
  share once (the gate's lhs and frame, `wfold::proof`'s machine sides, the `refl` laws of `wasm/laws.rs`); the gate's
  build work at `doubling(11)` went from 37491 to 18774. The check is unchanged by it: the kernel interns both copies as
  one node and the checker memoises shared nodes.
- **Where the check's wall time goes past linear:** the check's wall time grew 2.1-2.3x per doubling, but its kernel
  work does not (run `2026-11-09-check-shapes`, two one-off probes at 02c10f1). Work per doubling of `doubling(d)` rises
  toward 2.0 from below, 1.68, 1.81, 1.89, 1.94, 1.97 for d = 7 to 11 (a fixed cost amortising), and a left-deep chain
  `t = add(t, x)` of the same tree size gives the same work within 1% at each d (776575 against 768735 at d = 11), so
  the stack depth of `doubling`'s machine program is not the cause either. What grows is the cost per unit of work:
  in release, best of 3, 112 ns at d = 6, 146-149 at d = 7-8, 185-205 at d = 9-11 and 235-239 at d = 12-13 (other
  sessions held about 49% of the CPU, so the levels are rough). The kernel's tables outgrowing the caches is the
  measured part of the cause; how much of the time it explains is open (next bullet). The check's footprint (region nodes, side arrays, table and memos, by capacity) doubles with d: 1.0 MB at d = 6,
  2.2 MB at 8, 16.5 MB at 11, 66 MB at 13 (525168 region nodes). Under cachegrind, with the last level simulated at
  the 7840U's L2 (1 MB) and L3 (16 MB), data references and L1 misses per doubling stay at 1.8-2.0, like the work, but
  last-level read misses do not (run `2026-11-09-cachegrind-doubling`, the check's misses taken as the difference
  of a build-only and a build-and-check run). At 1 MB they grow 2.2-2.7x per doubling, from 6449 at d = 6 to 3.93 M at
  d = 13. At 16 MB they are nearly zero through d = 9 (21-302), then 8060 at d = 10, 151127 at 11, 511902 at 12 and
  1.47 M at 13, so the jump starts where the footprint passes 16 MB. The two clear steps in time per unit of work
  (d = 6 to 7, d = 11 to 12) sit at those two crossings. cachegrind is close to deterministic here: the two runs of each
  d differed by a few ppm in data references and 0.06% in L1 misses. Raising the bound past 8192 therefore needs a
  smaller footprint per node, or a check that touches less of it, as well as less work. `docs/runs/2026-11-09/scripts/cg.sh`
  reruns the sweep on the ignored test `measure_cachegrind`; the footprint probe is in
  `docs/runs/2026-11-09/patches/y1-cache-probes.patch`.
  `gate_check_work_is_linear_in_the_tree` now holds the work ratio under 2.05, below the 2.1 a log factor gave.
- **What the check builds and where it misses (survey, 2026-11-09):** at `doubling(13)` the statement is 26520 region
  nodes and the check grows the region to 525168. Comparing the lhs with the rhs (`conv` under `def_eq_in`) builds
  498192 of the 498648 new nodes and does 40% of the work (1.21 M); typing the claim (`infer(expected)`) does 60%
  (1.83 M) and builds 455 (`docs/runs/2026-11-09/patches/a1-phase-probes.patch`). Memo hit rates in the check: whnf
  98% (157K entries, 7.62 M hits), shift 78%, spine 46%, inst 26% (164K entries); `bounds` holds 214K entries
  (`patches/z1-memo-probes.patch`). cachegrind by function (run `2026-11-09-cg-annotate-d13b`, debug-info build,
  `docs/runs/2026-11-09/scripts/cg_annotate.sh`): at a 16 MB last level, 34% of read misses are `memcpy` (`Vec`
  growth), about 14% table rehashes, 9% `whnf_step`, 5% `beta_spine`, 4% each `hc::uses`, `shift_get` and the node
  table's `find`; `whnf_get` is 0.3%, so the whnf memo stays in cache. At 1 MB the loose-variable and shift machinery
  leads: `hc::uses` 10%, `shift_unchecked` 7%, `Space::push` 6%, `shift_put` 5%, `shift_get` 4%. The misses explain
  only part of the time, an inference: the excess over d = 6's cost per unit of work is about 386 ms at d = 13 (about
  195 ms on a quieter machine: "Where the excess goes, profiled", below), and weighting the random misses by latency
  (about 0.7-1 M at 16 MB at ~80 ns, 3.9 M at 1 MB at ~10 ns) gives about 100-120 ms, while the `memcpy` misses stream
  and cost a few ms. cachegrind models no TLB and no prefetcher (the TLB was then tested, next bullet). Options, fewest
  concepts first: check the top
  telescope under fresh typed free parameters instead of `Var` binders, so the program is closed and the shifted
  copies of its suffix go (kernel, trusted base); one `u64` loose-variable mask per node in place of the `uses`
  slot, `bounds`, `lowest_loose` and `InferCache::lows`; `inst` as per-call scratch, deleting `arg_sets` and `Aid`;
  `whnf_in` returning non-redex tags without a probe and storing result -> result (a work cut, not a miss cut); one
  32-byte row per node in place of six arrays. Rejected: per-case encoding rewrites, lossy bounded memos, a custom
  table, narrower `loose`/`free`, a separate whnf slot array.
- **Testing the survey's options (2026-11-09):** four follow-ups, at 026f290 plus the change named.
  - *TLB.* mimalloc's large OS pages, on by default here, save only 4-7% of the check at d = 12-13 (best of 3, timed
    lease: d = 13 511 ms with them, 537 ms with `MIMALLOC_ALLOW_LARGE_OS_PAGES=0`; d = 12 246 against 265; runs
    `2026-11-09-lp1-*` and `2026-11-09-lp0-*`, `docs/runs/2026-11-09/scripts/lp.sh`), and the time still grows 2.03-2.07x
    from d = 12 to 13 either way. So large pages remove about 26 ms of the excess at d = 13, not the bulk of it; where
    the rest goes: "Where the excess goes, profiled", below.
  - *Closed parameters, the falsifier.* Opening the law's 7 binders onto postulated constants (public `whnf` of each
    `Pi` and `Lam` applied to a `Const`, then `Postulates::check`; `docs/runs/2026-11-09/patches/b2-opened-binder-spike.patch`,
    kernel untouched) cuts the memo tables at d = 13 by about two-thirds (shifts 162K to 50K entries, inst 164K to 34K,
    bounds 214K to 49K, arg_sets 90K to 25K) but the check builds more nodes, 680K against 499K, because the closed
    machine spine turns on `hnf` (49K entries, 77 before). Work falls 6.5% (3.04 M to 2.84 M; 6.3% at d = 11) and the
    untimed check 9%. The survey's estimate that nodes would fall to 40-70% was wrong: the option trades memo bytes for
    node bytes and is not worth a change to the trusted base on this evidence.
  - *A loose-variable mask.* A `u64` per node (56 bits of loose `Var`s and a byte for the lowest index lost to the cap)
    agreed with `hc::uses` on every query it answered exactly (141K of 160K random ones), the kernel and wasm suites and the gate at d = 6-13 (identical work),
    but answers only 24% of the gate's `uses` calls exactly: the rest ask nodes whose loose variables run past 56, under
    the 64-binder word telescopes, though only 1.6% of queries have d + m of 64 or more
    (`docs/runs/2026-11-09/patches/b3-mask-spike.patch`). One word cannot replace `bounds` and the slot; rejected.
  - *The whnf fast path,* adopted (`reduce.rs#whnf_in`): non-redex tags skip the memo and a reduced result is stored as
    its own whnf. The check's work falls 1.9% at d = 13 (3039350 to 2981514) and 2.7% at d = 6; the ratio per doubling
    is unchanged (1.992 from d = 12 to 13). Too small to time.
- **Where the excess goes, profiled (2026-11-09):** xperf traces (sampled stacks and faults, large pages on, untimed,
  other load 4-12%) of repeated checks at d = 6, 8, 11 and 13, all on one build with 4892e62's kernel (runs
  `2026-11-09-c1-xperf`, `2026-11-09-c1-xperf-small` and `2026-11-09-c1-xperf-few`;
  `docs/runs/2026-11-09/scripts/prof.sh`, `prof_report.sh`, `prof_agg.py`). Each d has two traces with different
  numbers of checks, and a check's cost is their difference over the difference in checks, so the process's one-off
  costs (start, build, its 256 MB stack, exit) cancel. `measure_cachegrind` now repeats the check `GATE_REPS` times and
  takes its settings as test filter arguments, since the elevated profiler drops the environment. A traced check runs
  about 7% slower than an untraced one (523 against about 488 ms at d = 13).
  - *Size.* A check costs 107 ns per unit of work at d = 6, 126 at 8, 150 at 11 and 171 at 13. The excess at d = 13
    over d = 6's rate is 195 ms of 523, not the 386 ms above, which came from timings taken while other sessions held
    about 49% of the CPU.
  - *Where.* Mostly in the functions that probe a table or memo: interning (`Spaces::mk`, `find`, `Space::push`,
    `hash`) 44 ms (23%), `inst_rec` with its memo and `args_id` 27 ms (14%), `hc::uses` and `lowest_loose` 26 ms
    (14%), the shift memo 20 ms (10%), `spine` 9 ms (4%); the checker's own closures 29 ms (15%); Windows' kernel
    18 ms (9%); mimalloc 7 ms (4%); 15 ms elsewhere. The kernel's part is noisy (8.0 ns per unit of work at d = 11,
    6.0 at 13) and its cause untested: soft page faults (`KiPageFault`) and working-set trimming (`MiTerminateWsle`,
    `MiActivePageClaimCandidate`) are both among its frames. From d = 11 to 13 the excess is 64 ms, led by interning
    (27%), the inst memo (24%) and the shift memo (19%); its top functions, `Space::push` (15%) and `shift_get` (14%),
    are also among the top 1 MB misses above.
  - *Against the misses.* cachegrind of a repeat check (`REPS=2` less `REPS=1`, run `2026-11-09-c1-cg-reps`,
    `scripts/cg.sh`) at d = 13: 3.37 M read misses at 1 MB and 0.81 M at 16 MB, against 3.89 M and 1.56 M for a first
    check, which also copies and rehashes as its arrays grow. At about 10 ns for an L2 miss that hits L3 and 100 ns
    for one that goes to memory, these come to about 107 ms, 55% of the 195 (inference: nominal latencies, no
    overlap); with the kernel's 18 ms, about 64%. The rest is not attributed; write misses (2.7 M at 16 MB per repeat
    check; attributed after the per-call memo, below: "After the per-call memo, the inst gate and the write misses"), TLB walks (large pages are worth about 26 ms, above) and the latency guesses are the candidates. The 100 ns
    weight may be high: by it, the first check's extra random (rehash) misses at 16 MB, about 0.22 M, would cost it
    about 20 ms more than a repeat, and the next sub-bullet measured 4.7 ± 5.0. Separating these needs per-function hardware miss counts,
    which the Samply task does not record.
  - *Growth costs nothing measurable.* A first check (arrays and tables growing, with the `memcpy` and rehash misses)
    and a repeat check (`scoped` keeps capacity) take about the same time: medians 490.8 and 487.2 ms at d = 13, 112.2
    and 114.2 at d = 11, from 10 processes of 3 checks (untimed, other load 17%); first minus the mean of the repeats,
    paired, +4.7 ± 5.0 ms (standard error) at d = 13 and -0.8 ± 2.0 at d = 11 (run `2026-11-09-c2-reps-b`,
    `scripts/reps.sh` with `N=10`). So presizing the region would gain at most about 3% at d = 13 (95% interval
    -6.6 to +16 ms), too little to justify it without a timed A/B: `PARKED.md`, item (i).
- **The survey's last two options, spiked (2026-11-09):** at 14fb70a, checked by cachegrind (the check's misses, c = 1
  less c = 0) and work, each spike reviewed and one cachegrind config reproduced by a second agent.
  - *One 32-byte row per node,* rejected. All six per-node fields are 38 bytes, so the row that fits holds the tag,
    `parents` and `height` in the node's padding, five child slots, `loose` and `free`, with `uses` kept apart (variant
    B swaps `uses` in and `free` out). Work is identical at d = 6-13, but read misses do not fall: +0.5% at 1 MB and
    0.0% at 16 MB at d = 13, +3.2% at 16 MB at d = 11; write misses fall 1.3-2.2% (runs `2026-11-09-d1-row-cg`,
    `2026-11-09-d1-row-b-cg`; `docs/runs/2026-11-09/patches/d1-row-spike.patch`, `d1-row-b-spike.patch`). So the
    misses that grow are not the per-node arrays read side by side but the tables and memos.
  - *`inst` as per-call scratch* (`patches/d1-inst-scratch-spike.patch`): the memo is keyed (node, depth) and emptied at
    each top-level `instantiate_n`, since the argument list is fixed within a call and nothing reachable from `inst_rec`
    calls `instantiate_n` again; `arg_sets`, `args_id`, `Aid` and `LIST_BIT` go (+24 / -66 lines). Work rises 2.4% at
    d = 11-13 (3055582 to 3129184 at 13): the old memo's cross-call hits were few, and the map now holds at most 64
    entries between calls. The check's read misses fall 11.7% at 1 MB and 14.5% at 16 MB at d = 13 (11.6% and 19.5% at
    d = 11), write misses 9.7-12.5% (run `2026-11-09-2026-11-09-d1-inst-cg`, reproduced by
    `2026-11-09-2026-11-09-d1-inst-verify`). Time, untimed and contended (other load 33%, a game; the timed lease
    refused at 38%, run `2026-11-09-d1-ab-timed`), 12 paired rounds in ABBA order (`docs/runs/2026-11-09/scripts/ab.sh`,
    run `2026-11-09-d1-ab-untimed`): the spike was faster in 10 of 12 rounds at each d, best of 12 573 against 641 ms at
    d = 13 (-11%) and 124 against 143 at d = 11 (-13%); paired means -77 ± 29 and -32 ± 10 ms. Timed on a quiet machine (total
    CPU 3-5%, `run.ps1 -Timed`), 10 paired rounds each, two runs: medians 485.6 to 442.4 and 460.9 to 421.6 ms at
    d = 13 (paired -42.0 ± 4.8 and -41.5 ± 6.1), 107.8 to 101.4 and 105.8 to 98.5 at d = 11 (-6.2 ± 1.4 and
    -5.8 ± 2.0) (runs `2026-11-09-d1-ab-timed2`, `2026-11-09-d1-ab-timed2-2`). Adopted in f0e6b09, with a debug
    assertion that `instantiate_n` never re-enters.
- **After the per-call memo, the inst gate and the write misses (2026-11-09):** at f0e6b09, by cachegrind's instruction
  count (`I refs`) and misses for the check, one debug-info build with a knob choosing the gate
  (`patches/f2-inst-gate-spike.patch`, `scripts/f2_cg.sh`; runs `2026-11-09-f2-gate-cg2`, `2026-11-09-f2-gate-s0`).
  - *Which nodes get an `inst` entry.* The shipped gate (shared and height > 2) against the same gate with height > 0,
    1 or 3: work equal to within 3 units of 3129184 at d = 13, instructions within 0.09% (5341.0 M; 5345.5 M at
    height > 0), misses equal to within 0.01%. With no height cutoff, `Var` leaves get entries too: work falls 1.6%
    (to 3079830) but instructions rise 1.1% (5398.8 M). Without the shared test (any node with height > 2)
    instructions rise 4.7% (5590.7 M) and D1 misses 2.5%, for 0.3% fewer last-level read misses at 16 MB. The same holds
    at d = 11. So under the per-call memo the shared test still pays, and the height cutoff only has to keep out
    `Var` leaves: shared nodes of height 1-3 almost never reach the memo with a used argument. The old cutoff was
    chosen on church-bv's `proof_cost_split`, and there it still pays: retired instructions (ICOUNT.md, large pages
    compiled off, 3 rotated batches of 4 on CPU 4; `scripts/g1_pcs.sh`, run `2026-11-09-g1-pcs-counts2`) with height
    > 0 against height > 2 were higher in every batch pair, by 0.72%, 0.62% and 0.23% of the median (about 39.85 G),
    and 0.18% best against best, while each arm's batches wandered up to 0.24% among themselves. So the height field
    stays: dropping it costs 0.2-0.7% of a proof workload's instructions, and 0.09% on the gate too.
  - *Where a repeat check's write misses go.* `REPS=2` less `REPS=1` at d = 13, 16 MB: 2.39 M last-level write misses,
    attributed per instruction (callgrind with the same caches, totals within 30 of cachegrind's; two reviewers
    reran the numbers). Machine stack frames of the deep recursions 1.22 M (51%: the shift walk 0.34 M, `Spaces::mk`
    0.17 M, the wasm lowering's `seq_step` 0.13 M, `lowest_loose` 0.12 M, `hc::uses` 0.11 M, `inst_rec` and `infer`
    0.13 M); the interning table's bucket writes 0.36 M (15%; 68% of its 525168 inserts miss); the per-node arrays
    appended by `Space::push` 0.31 M (13%, one miss per 64 bytes of their 38 per node, to within 7); the memos' bucket
    writes 0.31 M (13%: `bounds` 0.14 M, `shifts` 0.10 M, `spine` 0.05 M, `whnf`/`nf`/`hnf` 0.02 M, `inst` about 0.1 k);
    mimalloc 0.15 M (6%). So the interning table is not most of them. About 69% are address-sequential (stack,
    appends, fresh allocator pages), which a hardware prefetcher may hide and cachegrind does not model; the random 28%
    are all hash-table bucket writes. Stack lines are partly first touches of the check's fresh 64 MB stack segment
    (`stack.rs`), whose cost on hardware is page faults, not misses (*The check's stack segment*, below). `hc::uses`'
    per-node slot store does not miss (the slot was just read).
  - *Which memo entries are read* (counters per memo and per entry, `patches/h1-memo-counters-spike.patch`, run
    `2026-11-09-h1-memo-parents-skips`; rep 2 of `GATE_REPS=2` counted directly, equal line for line to rep 1 since
    the memos are cleared at each region close). At d = 13 (d = 11 about a quarter, same rates): `inst` 221 k gets,
    14.8% hits; `shifts` 777 k, 79%; `whnf` 98.8 k gets, 21 hits, for 197 k inserts; `hnf` 8.5 k, 99%; `nf` none;
    `spine` 107 k, 46%; `bounds` 233 k, 3.5%. `hc::uses`' per-node slot answers 88.6% of what reaches it, and the rest
    goes to `bounds`, which inserts 214 k entries of which 31 are ever read (one shared node takes 8191 of the 8233
    reads), and no answered hit came from an `m` other than the storing call's. Skipping `bounds` inserts for
    unshared nodes (run, not simulated) leaves 359 inserts for 127 more walks (+0.01% of `uses` calls) and unchanged
    work (3129184). `spine` is the other way round: its unshared entries are read about once each (74% of them, by
    the next level of a stuck spine), while 26 of its 24.7 k shared entries take half of all its hits; skipping
    either class costs 8.6-15% more spine calls. Write-miss savings are inferred from insert counts, not measured.
  - *The check's stack segment* (`patches/h2-stack-probe-spike.patch`; runs `2026-11-09-h2-cg`, `-h2-winrun`,
    `-h2-wintime`). stacker makes a new segment per `grow` call (`CreateFiber`/`DeleteFiber` on Windows, `mmap` on
    Linux), so each large check faults its stack in afresh. Depth at d = 13: 61.7 MB on Windows (5.4 MB under the
    64 MiB segment), 46.1 MB on Linux; at d = 11 15.4 MB and 11.5 MB. Native page faults per check: 15107 at d = 13 and
    3804 at d = 11, about the pages touched; 0 with one segment reused across checks (from the second check; the
    first faulted 22% fewer pages than the depth, unexplained). The reuse arm was faster by 42-52 ms of about 570 ms
    at d = 13 (8-9%; untimed, at 29% machine load, and it also moves `statement()` onto the segment). Under cachegrind
    the segment sits at the same simulated addresses every check, so first touches cannot be told from re-touches;
    the depth bounds them at 0.72 M lines, at most 59% of the 1.22 M stack write misses. Since the segment is 3-4 times
    the 16 MB last level, reuse would not keep its lines cached; only smaller frames cut those misses.
    Shipped (cbcc4c1) as no segment at all where the thread has the room: `check_in` runs a large check in place when
    `stack::has_check_room()` holds, and church-bv's entry thread has a 256 MB stack (`CHECK_STACK`); a thread with
    less room takes the segment as before. church-bv's worker task threads and lanes were on default stacks and still
    took it; since 2026-11-09 they have the check stack too (their tests assert the room). A salt-1 sweep's commit,
    ae6f369's `entry.rs` and `driver.rs` against 6f1cb06, two sweeps each (`scripts/stack_commit.sh`, run
    `2026-11-09-q1-stack-commit`, 48-57% other load): the job's peak falls from 4537 and 4538 MB to 4490 and 4502 MB
    (-36 to -47 MB, about 1%), and the largest process's peak is 3336 MB in all four, so the segments were not at its
    peak. The 150 MB of the 2026-10-23 worker is not reproduced: that sweep (`cold:cmp3d`, 446-490 MB) no longer
    exists, and today's processes are seven times larger. Job CPU 168-171 s against 175-177 s, under that load no
    verdict; faults not remeasured. Page faults per
    repeat check, f159775 against cbcc4c1 (`scripts/faults.ps1`, run `2026-11-09-m1-faults`; the process's count at
    `GATE_REPS=3` less `GATE_REPS=1`, halved; 3 runs each, equal to within 6 faults): 15104 to 0 at d = 13 and 3802 to
    -2 at d = 11; the first check also faults less (20398 to 17054 and 6589 to 5730 for the whole process). Timed
    (run `2026-11-09-q2-m1-timed-1`, `scripts/ab.sh` under the CPU lease, total load 14%, n = 12 pairs): the repeat
    check at d = 13 is 29.4 +- 5.7 ms faster (438 to 410 ms median, 6.7%); the first check at d = 13 (-1.7 +- 7.2 ms
    of 432) and both checks at d = 11 (repeat +0.3 +- 8.9 ms of 107, first -12.5 +- 24.2) show no difference. An
    earlier untimed pair at 70% load could not see it (run `2026-11-09-m1-ab-untimed`: d = 13 rep 3 B - A
    -26.8 +- 22.9 ms of about 760; n = 20).
  - *One-probe interning* (`patches/h3-one-probe-intern-spike.patch`; runs `2026-11-09-h3-base`,
    `-h3-onepass-destructure`). `Space::build`'s region path with one `HashTable::entry` instead of `find` and
    `insert_unique`: instructions -0.44% at d = 13 (5279.96 M to 5256.51 M) and -0.47% at d = 11, -1.4% for building
    the statement alone; last-level and D1 misses unchanged (the second probe re-reads a group the first just loaded,
    an inference). Holding the vacant slot across the appends needs the region's fields borrowed one by one, so the
    spike copies `push`'s body into the region path; swapping the table out instead (`mem::swap`) cost +2.9%.
    Shipped as `Space { cols: Cols, table }` (`spaces.rs`): one `Cols::push` for every column, `Space::push` adding the
    table entry, and the region path holding the vacant entry across `Cols::push`, with no copied body. Cachegrind
    (runs `2026-11-09-wf1-j1-cg-2`, `-wf1-j1-cg-irefs`): d = 13 5261.82 M instructions (-0.34%), d = 11 1327.56 M
    (-0.36%); last-level misses unchanged (d = 13 16 MB 4,724,413 against 4,724,334).
  - *One bounds entry in the node's row* (runs `2026-11-09-wf1-i1-cg`, `-wf1-i1-cg-reps2`, `-wf1-i1-pcs-counts`).
    `Memos.bounds` and the per-node `(d, m, answer)` slot became one per-node slot of bounds `(lo, hi)` on the lowest
    loose variable from the last depth asked (`Spaces::bounds_slot`, one `u64`: `d` 15 bits, `lo` and `hi` 24 bits each,
    loosened by the caps only), so the walk's answer is stored once per node and read by any `m` outside the narrowed
    bounds. Cachegrind with the one-probe change in both arms: d = 13 5225.58 M instructions (-0.69% from 5261.82 M),
    d = 11 1318.48 M (-0.68% from 1327.56 M), d = 13 without the check unchanged (460.97 M; the -2.3% from 471.86 M is
    the one-probe change's); last-level data misses, all this change's, at d = 13 4,524 k at 16 MB (-4.2%; writes
    3,189 k against 3,383 k) and 8,753 k at 1 MB (-5.4%); d = 11 16 MB 821 k (-3.3%); `work` unchanged (3129184 at
    d = 13). Repeat check (`REPS=2` less `REPS=1`, d = 13, 16 MB): 2.25 M write misses against 2.39-2.44 M.
    Retired instructions of church-bv's `proof-cost-split`, both changes together (large pages off, CPU 4, 3 rotated
    batches of 4; paired batch medians, 9f65018 against both): 40.025 G to 39.496 G, 39.896 G to 39.469 G, 39.892 G to
    39.475 G (-1.32%, -1.07%, -1.05%; within-batch (median - best) / best 0.0001-0.0013); not split between the two.
    A timed pair of the gate check (`scripts/ab.sh`, run `2026-11-09-n3-ab-timed2`, 9f65018 against f159775, 10 paired
    rounds) cannot see a saving this size: d = 11 B - A +1.9 +- 3.6 ms of 107, d = 13 -20.7 +- 26.8 ms of 517. The
    count verdict stands as "less work", with no time claim.
  - *Whether the whnf memo pays* (at 9f65018; `patches/l1-whnf-counters-spike.patch`, run
    `2026-11-09-l1-whnf-counters2`; `patches/l1-whnf-memo-arms-spike.patch`, runs `2026-11-09-l1-ir`, `-l1-cg`,
    `-l1-pcs-counts`, `-l1-pcs-a1`, `-l1-tests`, `-l1-tests2`). The gate's check reads it 21 times for 197 k inserts,
    but `proof-cost-split` hits on 51% of 1.63 M gets (44% return a reduced term), the kernel's tests on 23% (nearly
    all stuck terms) and tatic-wasm's on 45%. Arms: no memo; the get and the `e -> r` put only (the `r -> r` put and
    its test-only whnf assert dropped). Without the memo the gate check retires 1.46% fewer instructions (d = 11 and
    13; last-level misses -2.3% to -3.2%, `work` +109 of 3.1 M), but `proof-cost-split` retires 14.4% more (45.62 G
    against 39.90 G, whole process, 3 rotated batches of 4) and 3 kernel tests fail, among them
    `nf_and_def_eq_are_linear_on_a_stuck_spine` (still running at n = 16000 after 20 s), so it stays. Dropping only the
    `r -> r` put: -0.78% (d = 13) and -0.77% (d = 11) on the gate check, -0.47% on `proof-cost-split` (39.71 G), all
    tests green, outputs identical; untimed, and it would leave `whnf_in`'s doc and `whnf_of_a_whnf_does_no_work`'s
    stated purpose (a reduced result answers without a `whnf_step`) out of date. Counted at 89% load in batch 1.
    Shipped (4ff9a86): `whnf_in` stores `e -> r` only, with the doc and the test's purpose rewritten (the first ask of
    a reducible-tagged result is one `whnf_step` that stores its own entry). The dropped put was already redundant for
    a beta result, since beta ends in `whnf_in` of the contractum, which stores it; it mattered only for results of J,
    WRec and SigRec steps and for an application whose head reduced to something stuck. Not timed (0.8% is under the
    timed pair's noise, above).
- **Against the old proof:** `prove_pure_expr`'s `refl` over the model of `straight_line` took 3.37 µs [3.20, 3.77]
  (criterion `straight_line_refl_proof`, untimed on a contended machine because the timed lease refused it at 42% load;
  run `2026-11-08-v07-straight-line-refl-baseline-untimed`), against the gate's 12-34 ms for a term of that size. The
  bench row is deleted with the prover.

**Fragment terms install on the gate's verdict alone.** `jit.rs#prove_install` sends a term in the fragment to `gate`
and nothing else, and every other term to `kernel_verify`, which no longer tries `prove_pure_expr` (deleted, with its
`setup`, `finish` and `LitScope::Arith`). A body with its `If` arms swapped is refused although the closure prover would
accept the term (`jit/tests.rs#the_gates_verdict_is_final_for_fragment_terms`); all five Goal 1 terms install, and an
operand `If`, outside the fragment, still installs through the chain. The workspace suite passed with 795 tests listed,
782 before the plan plus 21 added and 8 removed (run `2026-11-08-v07-workspace`).

