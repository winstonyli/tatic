### Why a retired-instruction count wanders (2026-11-05)
The `church_bv` test exe's count moved about 0.5% run to run, against the 0.002-0.03% of a quiet single-threaded workload. Two
things drove it. Large OS pages in mimalloc add kernel time to some processes, most often the first run of a batch: xperf stacks show a
search for contiguous physical pages, and its link to the extra instruction count is by shape, not measured. That cost remains in the
default build. And stacker learned a proof thread's stack limit on a fiber, so
where the OS placed that fiber decided whether the thread paid 1903 extra stack segments: with large pages off the miner test wandered
1.6% unjoined against 0.07% joined, and reading the limit first left 8 unjoined runs within 0.11% of each other. That is fixed
(`learn_floor`, 94ad5f4): a build with large pages off now repeats to 0.07% on the whole exe, max / best 1.001, over 12 runs, with no change to `Rounds::play`.
Joining did not remove the 1903 segments: they were the top four of 96 joined `extras_by_first` runs. A few high runs stay unexplained.

Each arm is `548df0e` in a throwaway worktree, sweep profile, `icount.ps1` on CPU 4, `--test-threads=1`, the parent's row only
(children are separate rows). "Joined" means each proof thread is joined at once. Every arm but the first row carries a small dump
of per-site counts; the rotated unchanged arm shows the dump itself moves nothing. Fixed order, 3 rounds of 4
(`2026-11-05-e1-armt`), then rotated order, 12 batches of 4 runs, so no arm keeps a place (`2026-11-05-e1-rotate`). Unjoined with
large pages off was not in the rotated run, so its whole-exe 0.53% is confounded with run order; the miner test settles that below:

| Arm | Run | Best (G) | Median (G) | (median - best) / best | max / best |
|---|---|---|---|---|---|
| unchanged, no dump | fixed | 157.491 | 158.354 | 0.55% | 1.026 |
| large pages off | fixed | 159.491 | 160.334 | 0.53% | 1.009 |
| joined | fixed | 156.870 | 157.373 | 0.32% | 1.025 |
| joined, large pages off | fixed | 158.778 | 158.873 | 0.06% | 1.002 |
| unchanged | rotated | 157.905 | 158.329 | 0.27% | 1.032 |
| joined | rotated | 157.458 | 158.600 | 0.72% | 1.027 |
| joined, large pages off | rotated | 158.776 | 158.872 | 0.06% | 1.002 |
| joined, system heap | rotated | 199.961 | 200.211 | 0.13% | 1.012 |

Read both spread columns: the large-page cost lands on few runs, so it shows in max / best and can miss the median. Neither is a
tolerance: the joined arm read 0.32% and 0.72%, the unchanged arm 0.55% and 0.27%. The system heap row has 11 runs: the fourth run
of its first batch stops at 183.6 G with no child rows after it, so that is a cut trace, not a count.

The table and the bullets below describe the code before 94ad5f4 unless they say otherwise; "the limit read" is the experiment that became `learn_floor`.

- **Large pages: some processes pay, and which is not predictable.** In the rotated run the first run of 4 of the 6 batches with large
  pages on read 159.5-163.0 G against 157.5-158.8 G for the rest of the batch; no other position ran high, and the first run of the 3
  large-off `joined` batches stayed within 0.2% of its batch's best. So it is neither the batch position alone nor the dump. The arm
  before does not settle it: after the large-off arm one batch paid and one did not, after a large-on arm one paid and one did not;
  both batches after the system heap paid, but that is two. The fixed order agrees: the first run is above the rest of its batch in
  all six, by 2.5-3.9 G in four and 0.2-0.8 G in two; in `e1-arml` the first of three batches of four read 162.5-163.1 G against 157.9-158.6 G for the other three runs.
  Children are the clearest sign. A child process that costs 25-30 M reached 0.05-1.2 G unjoined and up to 1.5 G joined with large pages
  on, sometimes in most of a batch (`e1-armt`, `e1-arml`, `e1-rotate`), and never passed 30 M with them off (`e1-armt`, `e1-rotate`)
  or on the system heap (`e1-arml`, `e1-rotate`). xperf samples by image, one whole-exe run
  each in a fixed order, no symbols and no instruction count (`2026-11-05-e1-kernel2`; samples are time): large off, 1113 of 28892
  samples in `ntoskrnl.exe`; large on straight after that, 1852 of 27171, and two children 560 of 565 and 274 of 282; large on again
  at once, 340 of 23831, no child over 30 samples. The children tie kernel time to the extra count; a parent's extra 1.5-3 G is tied
  by nothing recorded, and the large-off parent's kernel share sits between the two large-on ones. Page totals did not separate
  the batches that paid. With large pages on, the limit read first
  and unjoined, 8 batches of 4 (`2026-11-06-e1-h3h2`, `2026-11-06-e1-h2b`), the first run beat the batch's next highest by 3.6-5.7 G in
  6, by 0.3 G in one and not at all in one; the second run also read 1.5-2.4 G over its batch's lowest in 3 of the 8. Free memory logged
  just before those 6 first runs was 1158-5292 MB, and before the other two 4275 and 3967 MB; one later run started on 92 MB and read
  level with its batch. Standby at each run's start was 22.3-27.1 GB. Eight batches cannot rule a free-memory effect out, and a total says nothing of
  contiguity; the next bullet looks at the search itself. The limit read does not touch this cost: children still reach
  1.7 G. With large pages off, unjoined, one of 3 first runs read high, 159.88 G against 158.92-159.01 G, starting on 568 MB free (`e1-h2b`).
  With large pages on the level also moves between batches (`joined`, rotated: 158.4-158.8 G, then 157.5-158.1 G).
- **The large-page work: searching for contiguous physical pages.** With kernel symbols, nine whole-exe xperf traces of the 94ad5f4 build, large pages off,
  on, on three times over (`2026-11-06-e1-j1-trace`, `recount.txt`): in the exe's own processes, parent and children together, `LONG_E~1.EXE` (a test's copy of the exe under its short name) among them,
  `MiActivePageClaimCandidate`, `MiPfnsWorthTrying` and `MiSafeLockPage` hold 0 ms in
  all three large-off traces and 1051-2108 ms in the six large-on ones; `KeCopyPageNt` holds 0-3 ms and 5-447 ms.
  Stacks from one more large-on trace (`2026-11-06-e1-j1c-stacks2`) give the path, as a call graph of the whole trace: `NtAllocateVirtualMemory`, `MiAllocateVirtualMemory`, `MiReserveUserMemory`,
  `MiMapUserLargePages`, `MiCreateLargePfnList`, `MiAllocateLargeZeroPages`, `MiFindLargePageMemory`, `MiFindContiguousPagesEx`, then either `MiPfnsWorthTrying`
  and `MiActivePageClaimCandidate`, or `MiTradePage` and `MiCopyPage` down to `KeCopyPageNt`. So mimalloc's reservation runs a search of physical memory, and
  it can copy pages; what each function does is read from its name. The two branches under `MiFindContiguousPagesEx` were not split by caller, so how the exe's share divides between them is not known,
  though the per-process times above show it pays both. The larger caller of `MiFindContiguousPagesEx` in that trace is
  `MiRebuildLargePage`, under `MiRebuildLargePages` on a system worker: about 23 s of samples weighted 1 ms each, against 3.8 s from `MiFindLargePageMemory`. It runs in the `System`
  process, in large-off traces too (`k1-wf`: 111 ms in `MiActivePageClaimCandidate`, 378 ms in `KeCopyPageNt`), so the exe's counts leave it out.
  By batch position, three traces of 4 back-to-back runs
  (`2026-11-06-e1-j1b-batch`, machine busy), the parent's three claim functions held 1643, 992, 1267, 584 ms; 909, 461, 423, 788 ms; 1310, 810, 423, 714 ms.
  The first run is highest in all three, and its kernel time too (6.37 s against 3.59-5.41; 3.91 against 2.82-3.89; 5.88 against 3.70-4.99).
  Against the batch's lowest-kernel run, the first run's extra claim plus copy time is 42%, 49% and 56% of its extra kernel time, so the rest of
  the excess is other kernel work. Children's claim time, up to 2178 ms a run (`children.txt`), is never highest in a first run. These are times from three traced batches, with no instruction count, so the link to the 3.6-5.7 G is by shape, not measured.
  That later runs search less because the run before freed its 2 MB pages is an inference.
- **Proof overlap: the miner test's page-fault modes.** `a_false_winner_rolls_the_rounds_back` falls in three modes a step of about
  1910 faults apart, and the count rises with them: 9.8k faults 14.71-14.74 G, 11.7k 14.73 G, 13.6k 14.76-14.80 G (`e1-arml`). Large
  pages off keeps the wander (0.50%). Joining each proof thread at once leaves one mode, 5030-5082 faults, and spread 0.10%; with
  large pages off too, 0.04% (`e1-armt`). Those two ran in different sessions, so large pages off, the same test ran unjoined and
  joined in ABBA batches of 4, 24 runs each (`2026-11-06-e1-g1`): unjoined best 14.937 G, median 15.176 G, 1.6%, max / best 1.020, in
  three count modes, each batch holding at least two (127.1-129.8k faults 14.94-14.98 G, 129.7-131k 15.13-15.16 G, 133.5k and over
  15.19-15.24 G); joined best 14.735 G, median 14.745 G, 0.07%, 124.8-125.9k faults, with 3 runs at 14.82-14.94 G whose faults
  are ordinary. So the gap is not machine state or run order, and no first-run effect shows here. The next bullet gives the cause; the
  overlap only moves it, and time slices do not enter into it.
- **The cause: stacker's limit, learned on a fiber.** Per-thread counts (`2026-11-06-e1-h1`, 24 runs per arm) put the whole gap on two
  proof threads, candidates 41 and 42: main and workers are flat across arms, and each big proof reads 300 M, about 500 M or about 532 M
  while its kernel work is identical (`e1-h1b`). A high proof makes exactly 1903 extra 1 MB stack segments, each a fiber, and a low one
  none (`e1-h1d`, `e1-h1e`). `stacker`'s `STACK_LIMIT` is a lazily initialised thread-local. These proofs' first stack use is a large
  `check_in`, so its first read is in `fiber_proc`, on the 64 MB fiber: the fiber's limit is computed, saved as the "old" one and
  restored as the thread's, so it stays for the thread's life. `remaining_stack` on the thread then measures against a limit on another stack. With the thread's stack
  below the fiber it saturates to 0: `floor_here` puts `FLOOR` above the stack pointer, and every top-level `grow` on the thread
  takes a fresh segment. With the stack above the fiber it reads about 512 MB left on a 256 MB stack, so no crossings, but also no
  protection at the true end of the stack. Placement decides the mode, 24 of 24 proofs without the fix in `e1-h1f`: stack below, 1903 crossings;
  above, none. Joined, all 8 sat above in that run (why the join favours that placement is an inference: only one proof thread and
  its fibers are alive at a time), and a joined run that lands below is high, which is the 544 M proof in `e1-h1d`. Counted per run on
  `extras_by_first`, joined with large pages off, 4 of 96 runs made 1903 segments and they are the four highest, 14.460-14.491 G against
  a median of 14.238 G (`e1-h2b`).
  Reading `remaining_stack` at the top of `on_segment`, before the first fiber, leaves 0 crossings in 16 of 16 proofs under either
  placement, with 256 MB reported correctly, in the same ABBA run: 14.750-14.766 G over 8 runs, 0.11% end to end, unjoined; joined
  14.750-14.771 G; unchanged 14.953-15.267 G. The 200 M and 232 M levels differ by the 1910-fault step, about one fault per segment;
  what picks the level was not found, and both go with the crossings. The fix landed as `learn_floor` on entry to `on_segment` (94ad5f4), whose
  `floor_here` makes the same first `remaining_stack` read; `a_first_segment_leaves_the_thread_its_own_stack_limit` failed before it, with 0 bytes left.
- **The belief test's high runs are unexplained.** `the_sample_holds_no_self_claim` commits 1.4 GB, with faults constant at about 1730.
  Its first two runs after a miner batch read 27.50 and 27.59 G against 27.22-27.25 G, and 12 runs with large pages off stayed within
  0.22% (`e1-arml`), which fits the large-page cost; but one large-on batch of 12 was as calm (`e1-armpm2`, 0.12%), and high runs also
  came mid-batch (`e1-armhm` 4 of 8, `e1-armpm` 2 of 12, `e1-armx-count` 2 of 8). In `e1-armhm` one read 34.7 G, 27.6% over best.
- **The system heap is no cure.** It has no large pages and no child over 30 M, but costs 27% more instructions. Unjoined it is at
  200.7-202.3 G, 0.30% (`e1-arml`), as expected with the overlap present. Joined it is at 199.96-202.39 G, 0.13%, with high runs in
  two of three batches, one of them first: up to 2.4 G over best where the joined large-off arm's highest is 0.34 G. Whether that is
  a third source or sampling of 11 runs was not tested, and joining was shown to quiet the count only under mimalloc.
- **Hashing: not shown to matter.** On `extras_by_first`, all four arms joined with large pages off, 24 rotated runs each (`e1-h3h2`): base 14.254 G
  median, 0.22%; limit read first 14.254 G, 0.27%; address-free `op_hash` 14.305 G, 0.20%; fixed foldhash seeds 14.245 G, 0.23%. The address-free
  hash moves the level and neither hashing arm moves the spread. Their high runs (14.576 G; 14.487 and 14.759 G) are the size of one and two proofs'
  segments and the arms lack the limit read, so they are probably crossings (inference: those arms had no counter). Before that, unjoined, an address-free `op_hash` left the miner tests at 1.3-1.4% (`e1-armx-count`) and fixed foldhash seeds
  at 0.8-1.8% (`e1-armhm`, `e1-armpm`; the second's `bvp` is a stale copy of the same arm), with low runs (14.26-14.27 G; 14.50-14.52 G;
  and 9348 faults at 14.554 G in `e1-armpm2`). The unchanged baseline does not settle it, because it differs by series: no dump, 6 runs,
  1.4% with runs at 14.19-14.35 G (`e1-pertest`); with the dump, 12 runs, 0.30% and no low runs (`e1-arml`). Why the two differ was
  not looked into. The instrumented `walk` and
  `op` counts of `a_false_winner` are identical every run and `match` moves about 0.02% (`e1-armw`); they cover only the instrumented
  functions, not the proof, the allocator or hashing.
- **Not explained.** Joined with large pages off, `extras_by_first_mines_what_the_unpooled_file_mines` had runs 1.75% over best at 0.13%
  (`e1-armt`); that is the size of the crossing runs above (1.7-2.0% over), so it is probably one (inference). Two of the 92 runs without
  crossings in `e1-h2b` still read 14.353 and 14.368 G, 1.0-1.1% over best, and no others passed 0.6%. `a_false_winner` read 0.31% over at
  0.04% (`e1-armt`), and joined with large pages on one run is 1.6% over. In `e1-armhm` one miner run read 15.53 G, 5.7% over; neither it nor the 34.7 G above recurred, and neither was looked into.
- **Reading a count.** For a whole-exe A/B with large pages on, expect up to 4.7% over the arm's best on the first run of a batch (164.336 G against 156.887 G, `e1-h3h2`) and about 1-2% between batch
  levels, and judge by the median over rotated batches: best-of-N picks the lowest batch level, and dropping first runs leaves the level
  and the children. With large pages off the count is quiet, unjoined with `learn_floor`: 158.727 G best, 158.832 G median, 0.07%,
  max / best 1.001, 12 runs in 3 batches, no first run high (`2026-11-06-e1-i1-count`, whose `-dirty` tree holds the same `stack.rs` code as 94ad5f4, and one batch that opens `e1-j1-trace`,
  same exe; a fourth batch was lost to ETW buffers with `2026-11-06-i1-suite` running beside it). Before the fix, whole-exe max / best was 1.002 joined and 1.006 with the limit read (158.918 G best, 158.976 G median, 0.04%, 12 runs in 3
  batches, not in the table, `e1-h2b`). A large-off count needs a build with the define
  changed because mimalloc reads the option at load and the Samply task has its own environment, and `--skip machine::mimalloc_defaults_to_large_pages`,
  since that test fails on such a build and `icount.ps1` stops on a failing exe; `driver::sweep` children already run with them off. `2026-10-30-p1b`'s 161.96 G then 159.85 G, put down to
  load in `docs/runs/2026-10-30/rows/2026-10-30-p1land.txt`, has the first-run shape (inference; not rerun).
- **Joining makes the low mode likely; it saves no work of its own.** `a_false_winner` falls 3% joined (14.32 G against 14.75 G; 14.74 G against
  15.21 G with large pages off, compared across runs and builds), and the unchanged build also read 14.32 and 14.35 G in 2 of 6 runs
  (`e1-pertest`). That gap is the crossings above: with the limit read first, unjoined matches joined to within the spread (`e1-h1f`).
  The comment at `Rounds::play` describes the overlap and gives no reason; that it is there to hide proof time
  behind scoring is an inference, not measured here.
- **Large pages on against off, counts only (2026-11-07; time not measured).** Same commit (fcad41c), large pages compiled on or off, batches of 4 on CPU 4 with the arms rotated, other sessions at 44-61% load (`2026-11-07-m2-counts2`).
  `proof-cost-split` (about 12 s): on reads 33.27-33.29 G at its quietest and off 33.93-34.01 G, so on does about 2% less work at its best; but on's first runs read 41.21 and 35.29 G (24% and 6% over its best), and its first batch stayed at 33.66-34.30 G after that, where off stays within 0.2%.
  The whole `church_bv` lib test exe (about 427 G, not the 158 G exe above): on reads 425.2-432.8 G in the 2 batches that survived, off 427.0-428.3 G in 3 (a third on batch was lost to an xperf dump failure), so no clear saving and a wider spread.
  These are counts, so they do not say which arm is faster; the timed A/B was refused on a busy machine (`2026-11-07-m2-times`). Mining runs are unaffected: `driver::sweep` turns large pages off for its children.
