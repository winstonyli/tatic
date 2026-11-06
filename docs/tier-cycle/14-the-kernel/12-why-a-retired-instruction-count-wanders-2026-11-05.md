### Why a retired-instruction count wanders (2026-11-05)
The `church_bv` test exe's count moved about 0.5% run to run, against the 0.002-0.03% of a quiet single-threaded workload. Two
things drive it. Large OS pages in mimalloc add counted instructions to some processes, probably kernel work. And stacker learns
a proof thread's stack limit on a fiber, so where the OS places that fiber decides whether the thread pays 1903 extra stack segments:
with large pages off the miner test wanders 1.6% unjoined against 0.07% joined, and reading the limit first gives 0.11% unjoined.
With large pages off and the proofs joined the whole exe repeats to 0.06% in two runs of 12; single tests in that arm still have rare high runs.

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

- **Large pages: some processes pay, and which is not predictable.** In the rotated run the first run of 4 of the 6 batches with large
  pages on read 159.5-163.0 G against 157.5-158.8 G for the rest of the batch; no other position ran high, and the first run of the 3
  large-off `joined` batches stayed within 0.2% of its batch's best. So it is neither the batch position alone nor the dump. The arm
  before does not settle it: after the large-off arm one batch paid and one did not, after a large-on arm one paid and one did not;
  both batches after the system heap paid, but that is two. The fixed order agrees: the first run is above the rest of its batch in
  all six, by 2.5-3.9 G in four and 0.2-0.8 G in two; in `e1-arml` the first of three batches of four read 162.5-163.1 G against 157.9-158.6 G for the other three runs.
  Children are the clearest sign. A child process that costs 25-30 M reached 0.05-1.2 G unjoined and up to 1.5 G joined with large pages
  on, sometimes in most of a batch (`e1-armt`, `e1-arml`, `e1-rotate`), and never passed 30 M with them off (`e1-armt`, `e1-rotate`)
  or on the system heap (`e1-arml`, `e1-rotate`). That it is kernel work is an inference. xperf samples by image, one whole-exe run
  each in a fixed order, no symbols and no instruction count (`2026-11-05-e1-kernel2`; samples are time): large off, 1113 of 28892
  samples in `ntoskrnl.exe`; large on straight after that, 1852 of 27171, and two children 560 of 565 and 274 of 282; large on again
  at once, 340 of 23831, no child over 30 samples. The children tie kernel time to the extra count; a parent's extra 1.5-3 G is tied
  by nothing recorded, and the large-off parent's kernel share sits between the two large-on ones. That the work is assembling
  contiguous physical pages, so that it depends on what the whole machine did to memory (each batch starts after xperf has parsed
  a trace of a gigabyte or more), is a further inference: kernel symbols, or free and standby page counts logged before each run,
  would confirm it. With large pages on the level also moves between batches (`joined`, rotated: 158.4-158.8 G, then 157.5-158.1 G).
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
  restored as the thread's. `remaining_stack` on the thread then measures against a limit on another stack. With the thread's stack
  below the fiber it saturates to 0: `floor_here` puts `FLOOR` above the stack pointer, and every top-level `grow` on the thread
  takes a fresh segment. With the stack above the fiber it reads about 512 MB left on a 256 MB stack, so no crossings, but also no
  protection at the true end of the stack. Placement decides the mode, 24 of 24 proofs without the fix in `e1-h1f`: stack below, 1903 crossings;
  above, none. Joined, all 8 sat above in that run (why the join favours that placement is an inference: only one proof thread and
  its fibers are alive at a time), and a joined run that lands below is high, which is the 544 M proof in `e1-h1d`.
  Reading `remaining_stack` at the top of `on_segment`, before the first fiber, leaves 0 crossings in 16 of 16 proofs under either
  placement, with 256 MB reported correctly, in the same ABBA run: 14.750-14.766 G over 8 runs, 0.11% end to end, unjoined; joined
  14.750-14.771 G; unchanged 14.953-15.267 G. The 200 M and 232 M levels differ by the 1910-fault step, about one fault per segment;
  what picks the level was not found, and both go with the crossings.
- **The belief test's high runs are unexplained.** `the_sample_holds_no_self_claim` commits 1.4 GB, with faults constant at about 1730.
  Its first two runs after a miner batch read 27.50 and 27.59 G against 27.22-27.25 G, and 12 runs with large pages off stayed within
  0.22% (`e1-arml`), which fits the large-page cost; but one large-on batch of 12 was as calm (`e1-armpm2`, 0.12%), and high runs also
  came mid-batch (`e1-armhm` 4 of 8, `e1-armpm` 2 of 12, `e1-armx-count` 2 of 8). In `e1-armhm` one read 34.7 G, 27.6% over best.
- **The system heap is no cure.** It has no large pages and no child over 30 M, but costs 27% more instructions. Unjoined it is at
  200.7-202.3 G, 0.30% (`e1-arml`), as expected with the overlap present. Joined it is at 199.96-202.39 G, 0.13%, with high runs in
  two of three batches, one of them first: up to 2.4 G over best where the joined large-off arm's highest is 0.34 G. Whether that is
  a third source or sampling of 11 runs was not tested, and joining was shown to quiet the count only under mimalloc.
- **Hashing: not shown to matter.** An address-free `op_hash` left the miner tests at 1.3-1.4% (`e1-armx-count`) and fixed foldhash seeds
  at 0.8-1.8% (`e1-armhm`, `e1-armpm`; the second's `bvp` is a stale copy of the same arm), with low runs (14.26-14.27 G; 14.50-14.52 G;
  and 9348 faults at 14.554 G in `e1-armpm2`). The unchanged baseline does not settle it, because it differs by series: no dump, 6 runs,
  1.4% with runs at 14.19-14.35 G (`e1-pertest`); with the dump, 12 runs, 0.30% and no low runs (`e1-arml`). Why the two differ was
  not looked into, and neither hashing arm was tried with the two sources removed. The instrumented `walk` and
  `op` counts of `a_false_winner` are identical every run and `match` moves about 0.02% (`e1-armw`); they cover only the instrumented
  functions, not the proof, the allocator or hashing.
- **Not explained.** With both sources removed, `extras_by_first_mines_what_the_unpooled_file_mines` still has runs up to 1.75% over
  best at 0.13%, and `a_false_winner` 0.31% over at 0.04% (`e1-armt`); joined with large pages on, one `a_false_winner` run is 1.6%
  over. In `e1-armhm` one miner run read 15.53 G, 5.7% over; neither it nor the 34.7 G above recurred, and neither was looked into.
- **Reading a count.** For a whole-exe A/B with large pages on, expect up to 3.3% on the first run of a batch and about 1% between batch
  levels, and judge by the median over rotated batches: best-of-N picks the lowest batch level, and dropping first runs leaves the level
  and the children. Large pages off is quiet only with the proofs joined, which is a code change, and it needs a build with the define
  changed because mimalloc reads the option at load and the Samply task has its own environment; `driver::sweep` children already run
  with them off. A single test in the quiet arm still showed a 1.75% high run. `2026-10-30-p1b`'s 161.96 G then 159.85 G, put down to
  load in `docs/runs/2026-10-30/rows/2026-10-30-p1land.txt`, has the first-run shape (inference; not rerun).
- **Joining pins the low mode; it saves no work of its own.** `a_false_winner` falls 3% joined (14.32 G against 14.75 G; 14.74 G against
  15.21 G with large pages off, compared across runs and builds), and the unchanged build also read 14.32 and 14.35 G in 2 of 6 runs
  (`e1-pertest`). That gap is the crossings above: with the limit read first, unjoined matches joined to within the spread (`e1-h1f`).
  The comment at `Rounds::play` describes the overlap and gives no reason; that it is there to hide proof time
  behind scoring is an inference, not measured here.
