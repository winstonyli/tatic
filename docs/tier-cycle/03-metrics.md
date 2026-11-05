## Metrics

How the results are measured (code: `crates/church-bv/src/driver.rs` and its module doc; the gate's lines: `scripts/streams_ab.sh`).
- **Serving and mining.** A loop's law stream is cut into batches. Each batch is served (every law checked) under the
  rules in force *before* it is mined, so its M is what the stream costs as rules arrive.
- **M** (per batch, lower is better): the laws the rules did not settle by rewriting alone, i.e. those that needed a
  whole-term machine proof plus those not proved (proved − free + not proved, the `serve` closure).
- **total M:** a loop's M summed over its batches. **mined-batch M:** M of the batches served after a mine (in a sweep's
  K=3 loops, batches 1 and 2 counted from 0); batch 0 is served before any mining, so it says nothing about mining.
- **exhausted:** laws that used up the rule budget. **joined:** laws the
  bounded join closed with no machine proof. **reached:** terms the join's searches reached, its cost, which M does not
  show. **rules:** rules in force at the end.
- **Held-out M:** a loop's rules checked on laws no loop serves, in four bands by law size
  (`crates/church-bv/data/held_{11,13,15,17}.txt`, 1000 laws each; "The frontier on the gate"). The gate's `held` sums it over the
  bands and loops.
- **Free share** of a band: the share of its laws proved with no whole-term machine proof. Under the table alone (no mined
  rules) it is the table's share; mining's gain, in points, is the difference, and it is the frontier's measure.
- **Work counts** (`crates/church-bv/src/work.rs`): `interp` and `match_pat` nodes, `join_walk` calls and `Term::op` builds, summed
  per arm. They repeat within a few ppm, so they price a change where job CPU varies by 5-11% ("Work counts as the gate's
  cost").
- **Loop seconds** (`secs`): each loop's own time, summed in the tables; sweeps run in two lanes, so the sum exceeds wall.
- **Regimes.** A cold loop starts with no rules. A warm loop starts from a library: own (its family's ref library), cross
  (another family's), pooled (three families' merged), mixed (u3's, mined on a mixed stream). A ref mine mines once on all
  its batches, then serves them, and makes a family's library (`lib_<family>`); its own M is nearly always 0, so it is
  judged by the loops it seeds. Sweep loops serve K=3 batches of B=100 on phases 1-3; ref mines K=4 (`MINES`, `LOOPS`).
- **Salt:** reshuffles the stream's order (and the generator's sample); salts 1-10 are ten independent samples.
- **Paired counts** (better / equal / worse): per salt, the first arm's total M against the second's; 9/0/1 means lower
  on 9 salts of 10. A sign test p is given for weak splits.
- **The extras.** Laws a mine also mines on beside its loop's batch. First drawn from the law generator, then (class-table
  phase 2) from phase 0 of the stream sequence: L is the list for a scope after the filter and n = ⌊0.16 L⌋ each loop's share,
  in slices shared by its mines. Since 2026-10-28 (66a9810) each mine takes its own n = `EXTRAS_N` (319) laws of the
  4-growth sequence ("Count and slicing"). The filter drops a twin (an extra whose normalized key is a served law's: a
  served law in disguise; since 2026-10-28 also a held-out law's), a trivial law (sides equal once normalized below
  their roots) and a law with a served law's skeleton (variables written `v`).
- **Arms** (`gen_warm.sh`): `<ref>_<loop>`, whether the ref mines and the loops took extras (on/off, `ABLATE=gen`);
  `mon`/`moff` are the ref-mine sweeps.
- **Cost** (`tools/runs`, a run's `result.txt`): wall, jobcpu (CPU seconds of the sweep's process tree), peakjob (its peak
  commit), peakws (the largest peak working set of any of its processes, from 2026-10-23); the run record adds CPU load and Defender's real-time protection at launch. Compare wall only at similar load.
- Regimes other than cold, ref mines, the generator's L and n, and the `gen_warm.sh` arms belong to the family results
  (before 2026-10-23).

