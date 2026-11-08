## The streams and the gate

### Phase 2, the gate on the streams, ablations and work counts (2026-10-23/24)

*Phase 2 in the rewriter (2026-10-23; plan docs/superpowers/plans/2026-10-23-class-table-phase-2.md; runs
`2026-10-23-p2-restore-3`, `2026-10-23-p2-gate-8`).* Built as the spike had it: `rewrite_uncached` asks
`Classes::lookup` after a node's children; a known node is final, as its own representative or through the proved step,
and rules run only on unknown nodes. `ABLATE=classes` switches it off, `eq_classes` switches off phase 1.
- **Restore check** (untimed: it compares rules and M only): the build before phase 2 against this build with
  `ABLATE=classes`, salt 1: rules the same in 3 of 3 loops, M 19, 14, 16 and mine rounds equal in both. So the switch
  gives phase 1 exactly.
- **The gate** (`salts_ab.sh`, salts 1-5, `-Timed`, quiet at start; others' load rose to 60-96% from salt 3 on, so
  later walls are contended): A the build before phase 2 (phase 1 on), B with phase 2. M 233 to 0, 0 in every one of
  the 15 loops (A 19 14 16, 20 7 19, 19 15 7, 14 23 17, 18 13 12); rules differ in all 15 (B mines almost nothing);
  mine rounds 1931 to 194, lookaheads 18 to 0; job CPU 746 to 42 s, wall 170 to 31 s; no arm failed. The lookup memo's
  peak 1690 terms in a worker process (`CLASS_MEMO`, after each task), no `CLASS_UNUSABLE` in B (5 in A, from phase 1); largest peakproc A 663 MB, B 621 MB. Against the spike
  (A there had no table: M 377 to 0, job CPU 451 to 26 s, memo under 50000, peakproc 609 MB) the built phase 2 matches:
  on the old gate's laws, nearly all inside the table's domain, the table leaves the miner nothing to learn
  ("Phase 2 leaves the miner nothing to learn on the gate"), which is why the gate moves to the streams (spec §9).

*The gate on the streams and its A/A baseline (2026-10-23; plan docs/superpowers/plans/2026-10-23-class-table-phase-2.md;
runs `2026-10-23-held-regen`, `-cold-streams`, `-stream-sequence-mem`, `-streams-gate-check`, `-streams-aa-1-2-3`,
`-streams-aa-3-4`, `-streams-aa-5-6`, `-streams-aa-7-8`, `-streams-aa-9-10-2`).* The gate is now `scripts/streams_ab.sh`:
per salt and arm, one `cold:streams` sweep (three loops from no rules on phases 1-3 of the stream sequence, extras from
phase 0), then held-out M: each loop's rules run on `held_11.txt` and `held_13.txt` (1000 open laws each, from a salt no
sweep reaches; 64 of band 11's 19769 and 47 of band 13's 37996 laws were served by salt 1's loops and dropped; exact matches against salt 1 only, so other
salts may still overlap, equally for both arms: spec, "Risks").
- **The sequence**: 57928-58628 laws per salt from the 56 streams. Each sweep process builds it once, in 81-119 s, about
  half of an arm's wall. Built alone it peaks at 1537 MB commit (`-stream-sequence-mem`, 89.5 s), so every arm's
  peakproc (1538 MB) is the generation's, not the lookup memo's. Salt 1's extras: L 1429, n 228.
- **Held-out M** costs about 1.3 s per band per loop (band 11 on a `-cold-streams` loop: 973 proved, 941 free, 27 not
  proved).
- **A/A** (the phase 2 build against a copy of itself, salts 1-10, `-Timed`, quiet at each start, others' load 18-45%
  during): M per salt 176, 181, 167, 166, 171, 179, 168, 166, 169, 175 (total 1718); held-out M 809, 890, 884, 865, 880,
  908, 874, 898, 847, 866 (total 8721); both identical in the two arms on every salt. Job CPU A/B 389/393, 606/623,
  461/467, 819/823, 538/514, 294/293, 418/420, 693/656, 584/615, 1059/1033 s. Spreads (|B-A|/mean, maximum over the
  salts): M 0%, held-out M 0%, job CPU 5.4% (salt 8). Rules the same in 30 of 30 loops; no arm failed. Past the table's domain
  `step` finds no proof for 4757-5272 distinct replacements per sweep (`CLASS_UNUSABLE`, the same in both arms), every
  one with a shift in it; those nodes fall back to the rules. On the held-out files (`held_out_replacements_prove`) 1588 of
  1743 replacements have a verdict (408 bitwise, 1180 tree) and their proofs check, and the key's refuter refutes none
  of the other 155: they are true laws `verdict` cannot prove (it treats a shift subterm as a free atom, so
  `add(sub(y, z), shr1(-1, 0)) = add(y, xor(z, shr1(-1, 0)))` fails though `shr1(-1, 0)` is a constant), not false
  matches of `lookup`. The lookup memo peaks at 8857-9712 terms (1690 on the old gate); largest peakproc 1538 MB against
  663 MB on the old gate (Task 3), all of it the generation. So on these salts any move in M or held-out M is real; job
  CPU needs more than about 5% to count.
- **The families deleted (2026-10-23, run `2026-10-23-streams-deletion-1-2-2`):** the hand-written family pools, their
  sweep stages (mines, own, cross, pooled, mixed), the preference phase and drop units, `RULESET` and its rule files, and
  the yield proposers went (spec §10; commits 093ffc1, b63d5ed). Before (2571ee7's exe) against after (b63d5ed's), salts
  1-2: M 176 and 181 and held-out M 809 and 890 in both arms, the A/A's numbers; rules the same in 6 of 6 loops; no arm
  failed. Job CPU on salt 1 325.7 s against 335.3 s (−2.9%, inside the A/A's 5.4%); salt 2's arms ran under 50-83% other
  load and are not compared.
- **Preferences deleted (2026-10-23).** With the preference phase gone nothing learned `winner  OVER  loser` lines and no
  live rules file had one, so `parse_prefs`, `Rules::with_prefs` and `rule_step`'s hop to a winner went; a rules file's
  rules now fire most specific first (`Rules::new`) alone. `RULE_CONFLICTS=1` still counted conflicts, printed `CONFLICT <terms> <fired>  WITH
  <later>`, until it was removed (cleanup CU4e, 2026-10-27; "Conflicts that happen"). The record of what they gained stays above ("Learned preferences", "Preferences and rival orientations in the miner").

*Ablations of the class table (2026-10-23/24; plan docs/superpowers/plans/2026-10-23-class-table-ablations.md; runs
`2026-10-23-ablate-switch-check`, `-ablations-1`, `-ablations-3`, `-ablations-check-promoted-2`, `2026-10-24-promoted-untimed`).* The fixed parts the
table may make redundant, one at a time on the streams gate (B = A's exe with `ABLATE=<switch>` in its `.env`).
- **Which switches take effect** (held-out M with no mined rules, the plan's table): 8 of 9 change it. `tree`,
  `collapse` and `eq_classes` do so only with the class step off; `chain` changes nothing in any setting tried. This
  check is valid: its script shortened only the folder, so each exe kept its long name.
- **The driver's verdicts were void: no B arm was ablated.** The driver passes exes as 8.3 short paths (`cygpath -d`,
  for the space in the profile path). `exe_env` looked for `<current_exe>.env`, and `current_exe` then names the short
  file (`B_PROM~1.EXE`), so `B_promoted.exe.env` was never read. `ablations-3` therefore compared one build with itself:
  M 1718 in both arms, held-out M 8721 in both, rules the same in 30 of 30 loops. Its "free" verdict for the promoted
  rules was wrong, and their deletion (ebae480) was reverted on 2026-10-24.
- **The promoted rules pay.** The deletion check `ablations-check-promoted-2` was given the undeleted build as its A
  by mistake, and its B was named `B.exe` (its own short name), so the switch did apply. Salts 1-2: M 176 against 180
  and 181 against 192 (lower is better), held-out M 809 against 859 and 890 against 880, rules differ in 6 of 6 loops.
  A rise on any salt decides pays (plan D1). The fixed build gives the same numbers on both salts (`promoted-untimed`,
  untimed; `ablations-4`, the driver's timed re-run, was stopped after load refusals).
- **The fix:** `exe_env` canonicalizes the exe's path first (`job.rs`; test `exe_env_is_found_from_a_short_path`).
- **`assoc` pays** (the driver's next switch, run as Step 3 of "Work counts as the gate's cost" below): with
  `ABLATE=assoc`, M rises on all 10 salts (176 to 189 on salt 1; summed 1718 to 1836), held-out M on all 10, rules
  differ in 30 of 30 loops (`2026-10-24-work-assoc-1-2` ... `-9-10`, timed).
- **`tree` is free** with the class table on (`2026-10-24-ablations-6`, untimed, on a4eda36): over salts 1-10 M 1718 and
  held-out M 8721 in both arms, every counter within 0.01%. The timed pair on salts 1-2 (`-tree-timed-1-2`, quiet)
  agrees: job CPU -0.3% and -0.1%, rules the same in 6 of 6 loops. Deleted (2026-10-24): `tree_step`, its candidate
  index (`TREE_CANDS`, `CandIndex`, `tree_candidates`) and its test; a `sub` node the rules leave is now final. The class
  table's `tree` laws (`tree_encoding`, `add_tree_law`, `LawKind::Tree`) stay. The check (`-check-tree`, d5d8c0a against
  a4eda36 with `ABLATE=tree`, salts 1-2): M, held-out M and rules equal, counts within 11 ppm.
- **`chain` is free** too (`2026-10-24-ablations-8`, on d5d8c0a): over salts 1-10 M 1718 and held-out M 8721 in both
  arms, every counter within 0.01%. The timed pair (`-chain-timed-1-2-2`) has rules the same in 6 of 6 loops and job CPU
  785 s in both arms; per salt -9.2% and +7.3%, wider than `tree`'s pair, so other load came and went. Deleted
  (2026-10-24): `chain_step`, `LawKind::Chain` and its arms; `x + 0` and `x + ~x` are the class table's now.
  `carry_chain_law` and `find_constant_carry` stay (`conjecture_miner` and their test). The check (`-check-chain`,
  328e3c1 against d5d8c0a with `ABLATE=chain`, salts 1-2): M, held-out M and rules equal, counts within 11 ppm.
- **`comm` pays** (`2026-10-24-ablations-9`, on 328e3c1): without it M rises on 9 of 10 salts (not salt 2), 1718 to
  1784, and held-out M 8721 to 9000. The same run's `collapse` verdict is void: the arm cache keyed each exe by the 8.3
  short name the driver passes, under which `B_collapse.exe.env` does not exist, so every B arm was A's (fixed in
  `streams_ab.sh`; names that fit 8.3, such as `B_comm.exe` and `B_chain.exe`, were keyed right, and no other gate copied
  an arm across exes).
- **`collapse`, `eq_truth` and `eq_pos` pay** (`2026-10-24-ablations-10`, on 328e3c1, the fixed cache key; the driver
  now stops a gate at the first salt whose B rises). `collapse`: M 861 to 862 over salts 1-5, the rise on salt 5,
  held-out M equal. `eq_truth`: on salt 1 M 176 to 229, held-out M 809 to 1025, job CPU +64%. `eq_pos`: on salt 3 M 167
  to 192, held-out M 884 to 1055.
- **`eq_classes` is free** (same run): over salts 1-10 M 1718 and held-out M 8721 in both arms, every counter within
  0.01%, job CPU +2.3% (untimed). The timed pair (`-eq_classes-timed-1-2`, quiet) has M, held-out M and rules equal
  and job CPU 807 s to 739 s (-10.5% and -7.0% per salt; the A/A's spread is up to 10.9%, so this leans to cheaper
  without it, not proved). Every arm the cache reused was A's from A, B's from B. With the class step in the
  rewriter, both sides of a law reach `prove_eq` already in the table's normal form, so its second normalization there
  closes nothing new. Deleted (2026-10-24, 25db9c3): the table step in `prove_eq` (phase 1); its tests now go through
  `rewrite_plan`. The check (`-check-eq_classes`, against 328e3c1 with `ABLATE=eq_classes`, salts 1-2): M, held-out M
  and rules equal, counts within 3 ppm.
- **Each arm now proves its switches took effect** (2026-10-24, the final review's I3): `Setup::ablated` prints
  `ABLATED <name>` the first time a name switches something off in a setup, and `streams_ab.sh` fails an arm whose
  `.exe.env` names a switch with no such line anywhere in the arm (task logs, the sweep's own output, the held-out
  check's lines in `held_lines.txt`). The 8.3-name bug above would have failed every B arm instead of passing them
  as A. Overhead (`2026-10-24-ablated-overhead`, salt 1, `ABLATE=comm`, the build before against the build with it,
  untimed): M 183 in both, interp and walk equal, match +2.8 ppm and op +5 ppm, inside the A/A's few ppm; 15
  `ABLATED comm` lines, none from the old build.
- **The driver's stop could miss** (found by `scripts/test_gate.sh`, 2026-10-24): `taskkill /T` stops children first,
  and in about 1 stop in 4 the gate's script went on to its next command after its child was stopped and before its
  own stop. `scripts/ablations.sh` now lists the tree first and stops parents first: 24 of 24 stops held. No real
  verdict was affected: a gate that ran on only added salts after the deciding rise.

*Work counts as the gate's cost (2026-10-24; plan docs/superpowers/plans/2026-10-23-work-counts.md, Task 4; runs
`2026-10-24-work-aa-s1-2`, `-work-overhead-1-2`, `-work-overhead-2-1-2`, `-work-aa-{1-2,...,9-10}`,
`-work-assoc-{1-2,...,9-10}`; scripts and outputs in `docs/runs/2026-10-24/`).* Counts at four sites (`interp` and
`match_pat` nodes, `join_walk` calls, `Term::op` builds; `crates/church-bv/src/work.rs`), summed per arm by `streams_ab.sh`.
- **Determinism: within a few ppm, not exact.** A/A over salts 1-10, max spread per salt: interp 14.9 ppm, walk 0,
  match 11.8 ppm, op 0.08 ppm; job CPU 10.9% on the same quiet runs (twice the 5.4% of the earlier baseline). Only the
  mining tasks differ: the miner's scoring queue and its proofs run alongside the rounds, so how much speculative work is
  done depends on timing, though the result does not. Tolerance per counter: max(spread, 1%) = 1%. These runs gave a
  sweep's loop to the next free lane, and a lane's worker carries its lemma file and memos into its next loop, so loop 3
  could see 283 or 447 lemmas (`work-assoc-1-2`, salt 1). Since a4eda36 loop i runs on lane i mod lanes: in the A/A
  `work-aa-lanes-1-2` every loop loaded the same lemmas in both arms, and the counts differ by at most 6 ppm (match).
- **Under load too.** An A/A with 4 arms at once (`streams_ab.sh` `JOBS=4`, salts 1-4, run `work-aa-jobs4-1-4`): M,
  held-out M and rules equal, the same lemmas per loop, counts within 14 ppm (match). Each arm took about 1.8x its wall
  time alone and about 50% more job CPU, so 4 at once gave about 1.85x throughput (8 arms in 12.5 min against about
  23 min one at a time). The ablations driver runs `JOBS=4` and keeps finished arms in `streams_ab.sh`'s `ARM_CACHE`,
  so A runs once per build (plan `docs/superpowers/plans/2026-10-23-class-table-ablations.md`, D3).
- **`peakproc` moves in steps between runs of one exe** (2026-11-07). It took three levels, 3334-3336, 3591-3593 and
  4104-4106 MB, in an A/A over salts 2-3 (`w1-aa-salt23`: 3592 against 4105 MB at salt 2) and a B/B over salts 1-2
  (`w1-bb-salt12`: 4104 against 3593 MB at salt 1). The steps are about 256 and 512 MB, which looks like a buffer doubling
  (inference, not traced). A gap of one step between arms is noise, not a change. The same runs bound the counts: match
  spreads 0.3-2.3 ppm and op 0.02-1.05 ppm per salt, walk exact. The w1 extraction's A/B (`w1-stepproof-gate`, salts
  1-3) differed by at most 0.78 ppm (match), with M, held-out M and rules equal.
- **A cached arm is reused only where its inputs are unchanged** (2026-10-24). The key also hashes `runs.exe` and the
  held-out laws, and the exe reports each name it reads from the environment (`ENV <name>=<value>` or `ENV <name>
  unset`, once per setup, `Setup::var`); a hit needs each to read the same now, except the names the gate sets itself.
  Before, a variable such as `JOIN_VISIT` set in the shell would have reused arms run without it. The record costs
  nothing measurable: over 12 held checks each, instructions -0.07% against the build without it, inside its own 0.06%
  spread (runs `env-record-icount2-A`/`-B`; it is counted, not timed, as the read sits on per-join paths). On the real
  gate (salt 6, A/A, JOBS=1, runs `cache-check-1`..`-3`): the second arm reuses the first's (2.5 min against ~4 for two
  sweeps), a rerun reuses both (21 s), and `SWEEP_LANES=2` (its default, but unset when cached) reruns one arm, whose
  entry then replaces the stale one for the other; M 179 and held-out 908 in all three, work counts within 15 ppm.
- **Overhead: none measurable** once `interp` and `match_pat` sum their nodes in a local and add them once per call
  (`count_n`, 4d1a74f): job CPU against the uncounted f0390df build -1.5% and -6.0% on salts 1-2. A thread-local add per
  node had cost +6.8% and +8.2%.
- **Co-movement holds.** `ABLATE=assoc` against A, summed over salts 1-10: interp +7.8%, walk +5.7%, match +8.3%,
  op +9.1%, their sum +7.8%, job CPU +8.6%.
- **Proxy quality fails.** Job CPU per count varies over the 40 arm-salts by 24% (interp), 38% (walk), 46% (match) and
  45% (op), against the plan's 11%. Fitted by least squares as a weighted sum (`work_fit.py`), job CPU / fit still
  varies 18.4%, and the weights are unstable (op -24 ns per count over the 40 arm-salts, match -3.8 over the A/A's 20):
  the counters move together. Some of it is CPU's own noise (10.9% A/A); the rest is cost the counters do not see
  (hash-consing's cache misses, kernel proofs). The counts show that the work did not change, and which way it moved;
  they do not give its amount.

