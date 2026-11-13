### The proved loop form: measurements (2026-11-12)

What the build of the loop form measured (spec `docs/superpowers/specs/2026-11-12-proved-loop-form-design.md`, plan
`docs/superpowers/plans/2026-11-12-proved-loop-form.md`, tasks 1 to 5; the spikes it came from are in "v0.8's build:
measurements and checks"). A tail self call now lowers to `local.set`s of the parameter slots (last argument first)
and `Br`, printed `br $top` inside `loop $top (result i64)`. The gate proves `Br` as a restart of the function's own
entry on the current frame, so the loop is proved, not assumed. Run ids are in `docs/runs.md`; raw output is under
`%LOCALAPPDATA%\claude-runs\tatic\`.

**The bench (A B A, T5).** The `execution` bench's `jit` rows for the closure loop and gcd, main (`7ad2f0a`) against
the branch, each arm a copy of its exe (`docs/runs/2026-11-12/scripts/pfl-bench.sh`, criterion's 1 s warm-up and 3 s
measurement). A1 and B1 ran timed on CPU 8 (`pfl-bench-a1`, `-b1`). A2 was refused twice by the quiet check (CPU 8 at
12.5% and 28.1%; `pfl-bench-a2`, `-a2b`), so it ran untimed on `CFF` (`pfl-bench-a2-untimed`), then timed on a later
try (`pfl-bench-a2-timed1`).

| row | A1 main (timed) | B1 loop form (timed) | A2 main (timed) | A2 main (untimed) |
|---|---|---|---|---|
| closure loop, warm | 25.89 us | 4.416 us | 25.57 us | 27.19 us |
| closure loop, cold | 4.763 ms | 4.717 ms | 4.380 ms | 5.856 ms |
| gcd, warm | 126.4 ns | 127.2 ns | 125.8 ns | 146.3 ns |
| gcd, cold | 598.7 us | 557.9 us | 550.2 us | 657.7 us |

- The closure loop's warm call is back at the v0.7 loop's 4.4 us (4.357 us before v0.8), 5.9 times faster than
  `return_call`. Every A run reads 25.6 to 27.2 us, so the gap is the form, not the machine. This meets the ROADMAP v0.9
  check.
- Cold compile and verify is unchanged (4.72 against 4.76 and 4.38 ms; the plan's bound was 1.5 times main's). The cold rows
  are about 4.7 ms, not the 604 us of v0.8's S2b table, on both arms, while gcd's still match it. A probe that rebuilt
  the bench at six commits (`cold-probe`, untimed on `CFF`, `docs/runs/2026-11-12/scripts/cold-probe.sh`) puts the
  step at `c46cfe6`: 632 and 607 us at `0f97e17` and `59810fd`, then 4.70, 5.07, 5.02 and 4.86 ms at `c46cfe6`,
  `d4e54b3`, `64d1689` and `7ad2f0a`. That commit brought self calls into the gate, so the cold path now includes the
  closure loop's kernel proof, and most of it is the kernel check, not the build. A probe timed `build` and `holds`
  apart, 20 runs each, untimed on `CFF` (`cold-gap-release`, patch `docs/runs/2026-11-12/patches/cold-gap-probe.patch`,
  reverted). In release, build took 0.67 to 0.70 ms (kernel work 6804) and check 3.49 to 3.82 ms (work 23552). These
  hold on a `CHECK_STACK` thread and on a 1 MiB one like criterion's main thread, with one store reused or a fresh
  store and compile per run, as the bench does. So the O3 spike's 0.70 ms build stands in a release test exe. That
  exe is not the bench: its whole cold `jit.apply` read 5.84 and 6.12 ms (the two threads), against the bench's
  timed 4.4 to 4.8 ms, and the probe was untimed at 16 to 19% CPU load. At the test profile's opt-level 1 with debug
  assertions (`cold-gap-debug`), build is 0.85 to 1.05 ms and check 4.4 to 5.7 ms. The spike's 0.70 and 3.70 ms were
  taken at that profile too, on its own tree and machine state. On the 1 MiB thread the check, and not the build,
  moves onto one `CHECK_SEGMENT` stacker segment. In release that costs 0.24 to 0.29 ms more; at opt-level 1 it costs
  0.57 and 1.29 ms more.
- A samply profile of the cold row (`cold-prof`, table `docs/runs/2026-11-12/cold-prof/named.txt`) seemed to say the
  reverse: of the samples under `compile_verify_and_apply`, `gate::build` was 56% and the check 24%. That split
  disagrees with the direct timings above, and the profile's stacks show why. On the bench's main thread
  (`docs/runs/2026-11-12/scripts/profile-roots.py`), 3364 busy stacks walk back to the thread's start, and 1503 of
  those hold `gate::build`. Another 3423 end at an ntdll root that is not the thread's start; 3416 of them hold
  `on_segment` and a kernel frame, so they ran on a stacker fiber. A further 3079 reach samply's 256 frames, and all of
  them are in the kernel; their roots cannot be seen. None of the last two groups reaches a gate frame. Inference: these
  are mostly the check's samples. The probe shows that only the check takes a segment, and the counts fit:
  1503 build samples at about 0.7 ms put about 7500 at the check's 3.5 ms, against the roughly 6500 here. That the
  truncated stacks are not the build's is not shown, since `holds` is inlined and their roots are cut off. A build with
  `holds` kept out of line, or a deeper samply stack limit, would confirm it. In this profile, then, the share of a
  caller of kernel work reads low, because its samples on a segment or deeper than 256 frames never reach the
  caller's frame. The leaf shares are not affected.
- Where the check's 23552 units of work go (a survey with counters added to the kernel, test profile; patch
  `docs/runs/2026-11-12/patches/check-breakdown-probe.patch`, never merged). Shift is 10918 and instantiate 8838, so 84% is
  re-indexing and substituting terms with loose variables under the statement's 11 leading binders and the proof's
  lambdas. Infer is 3205, whnf 364 and full conversion 227; 16154 of the conversion attempts are pointer-equal. By
  phase: definitional equality 12618, instantiating application types 4829, the statement's own inference 1695. A
  check memo would save little: 16130 check calls cover 6377 distinct keys, but repeated calls hold only 46 units.
  Checking the instance closed, with the 11 binders opened onto postulated constants, took 13081 units plus 537 to
  infer the binder types, against 23552 open. That figure leaves out building the opened instance, and it ran
  after the open check in the same region, with warm memos; the spike in the next bullet removes both. The same
  opening on v0.7's encoding gate at doubling d = 13 saved only 6.5% and built more nodes (`docs/tier-cycle/`, "v0.7's build: measurements
  and checks", its "Closed parameters, the falsifier"), on a different proof shape. Persisting memos across gate calls
  saved nothing (26926 units), because each call is a fresh region. Only 42 of the 3205 inferred nodes are closed.
- Checking the instance closed does not pay (`closed-spike-2`, test profile; patch
  `docs/runs/2026-11-12/patches/closed-instance-spike.patch`, reverted). For each program, each arm ran in a fresh
  region on its own `CHECK_STACK` thread. Arm O checks with `holds`, as the gate does now. Arm C opens the statement's
  leading binders onto `Postulates` constants (10 or 11 of them) and instantiates the proof the same way, counting
  that work, then checks with `Postulates::check`. The build is identical in both arms.

  | program | build | open check | closed: opening + check | closed / open |
  |---|---|---|---|---|
  | closure loop | 6804 | 23552 | 1007 + 21799 | 0.968 |
  | straight_line | 3955 | 33989 | 1007 + 32685 | 0.991 |
  | doubling 1 | 2707 | 5509 | 884 + 5146 | 1.095 |
  | doubling 2 | 3129 | 5992 | 884 + 5617 | 1.085 |
  | doubling 3 | 3732 | 6935 | 884 + 6544 | 1.071 |
  | doubling 4 | 4889 | 8798 | 884 + 8383 | 1.053 |
  | doubling 5 | 7154 | 12501 | 884 + 12046 | 1.034 |
  | doubling 6 | 11635 | 19884 | 884 + 19357 | 1.018 |
  | inc | 2677 | 5513 | 884 + 5150 | 1.095 |
  | a_pap_capturing | 2854 | 6053 | 884 + 5604 | 1.072 |

  Closing saves 2 to 8% of the check, and the opening costs about as much, so the net runs from 3% less to 10% more.
  It also ends with more nodes in the region on every program but the closure loop and straight_line. With cold
  memos, the survey's 13081 does not reproduce: the closure loop's closed check is 21799. So most of the shift and
  instantiate work is not caused by the 11 leading binders. The next bullet
  finds where it does come from. This agrees with
  v0.7's -6.5%. gcd is not in the table: the gate does not cover it (`NotCovered`: "position 0 is outside what the
  source reading takes"), because `%` has no row in the gate's table yet (`PARKED.md`, "The partial row and gcd (after
  v0.8)"; pinned by `proof/tests/gate.rs#what_cps_cannot_take_is_not_covered` and `baseline.rs`'s `VERDICTS`). It
  installs through the older chain, so its cold row carries no gate check, which is why it still matches v0.8's
  S2b table.
- Where the shift and instantiate work comes from, by kernel call site (`check-origin2`, rerun byte-identical as
  `check-origin-rerun`; test profile; patch `docs/runs/2026-11-12/patches/check-origin-probe.patch`, which adds site
  tags to the survey's counters, never merged). Each tick is charged to the outermost tagged call that made it, and
  the site sums equal the totals (10918 and 8838 for the closure loop, as in the survey). Two caveats, from a static
  audit of the probe. Shift ticks at a substitution site are shifts done inside that substitution (lifting
  arguments, lowering unused subterms), not separate calls. And memo hits make no ticks, so an entry's cost goes to
  whichever site computed it first. The shares say where the work happens, not what would vanish if one site went.
  For the closure loop:

  | site | shift | instantiate |
  |---|---|---|
  | beta in whnf (spine, closed-prefix spine, single; 211 calls) | 7637 (70%) | 5542 (63%) |
  | instantiating application types (3 sites in `infer`'s App arm) | 1554 (14%) | 3275 (37%) |
  | lifting a context entry's type on `Var` lookup | 1306 (12%) | 0 |
  | `J`'s motive, `SigRec`, `Pair` | 421 | 21 |

  The phase counters put most of the beta inside definitional equality: that phase holds 6818 of the shift and 5298
  of the instantiate units (`check-breakdown-rerun`). A further counter (`check-origin-closedness`, patch
  `docs/runs/2026-11-12/patches/check-origin-closedness-addon.patch`) split the beta by whether the lambda has loose
  variables: 6202 of the 7637 beta shift units (81%) are on open lambdas, and 5170 on open lambdas with open
  arguments. Beta of closed lambdas, the closed-prefix site, is 1435 shift and 2157 instantiate. So the bulk is
  conversion reducing open terms of the proof, not instantiating the statement's binders. The largest share sits at
  context depth 4 (the next bullet shows it is not one top redex). Which binders the loose variables belong to was not measured: the probe's depth split is the
  checker's context size at the call, not the term's own binders. The other programs differ. In straight_line
  (shift 4812, instantiate 4162) the work is spread across beta, application types and `Var` lifts. doubling 6 is
  instantiate-heavy (10708 of 19884 work), and 8928 of that is instantiating application domains while inferring
  the statement, the opposite of the closure loop.
- What triggers that beta, and whether sharing a redex would remove it (`beta-trigger-3`, test profile; patch
  `docs/runs/2026-11-12/patches/beta-trigger-probe.patch`, with a reviewer's rerun and extra counters in
  `beta-trigger-probe-verified.patch` and `beta-trigger-levels-addon.patch`; never merged). Each beta is charged to
  the caller of the outermost `whnf` that missed the memo, so trigger shares are first-toucher shares too. For the
  closure loop, the `def_eq(inferred, expected)` nested inside `check` holds 80% of the beta's shift and 94% of its
  instantiate units. Two clusters make it up. At context depth 4, after the proof's four leading lambdas, conversion
  under 11 to 21 binders it opened itself does 43 betas: 61.5% of the beta units (3195 shift, 4910 instantiate). They
  are mostly distinct 64-argument applications of 64-lambda telescopes, and 4-argument closed-prefix ones, and nearly
  all of them are on the inferred side (2754 shift and 4726 instantiate against 441 and 206 on the expected side). At
  depth 26 the conversion inside `J`'s rule does 33 betas, 2946 shift and 278 instantiate. So it is not one
  4-binder top redex. Sharing would not help: no redex repeats exactly, because `whnf`'s memo
  already shares exact repeats, and keyed with its free variables anchored to the context only 30 of the 211 calls
  repeat, for 78 shift and 86 instantiate units (about 1.2% of the beta units, 0.8% of the shift and instantiate
  work). A lambda reused with new arguments still pays for its substitution. So a gain would have to come from making
  the substitutions cheaper or from not reducing the inferred side before comparing it. Where the depth-4 telescopes
  come from is the next bullet. The earlier 81% of beta shift on open lambdas reads 75.6% with this probe's cut
  (lambda has a free variable); the difference was not traced.
- Where the depth-4 telescopes come from, and whether the inferred side must be reduced (`n4-origin-closure4`,
  `n4-pre-modes`, `n4-gate-pre1`, a reviewer's `n4-ref-*` reruns; patch
  `docs/runs/2026-11-12/patches/telescope-origin-probe.patch`, which includes the beta-trigger probe, with the
  reviewer's `n4-referee-addon.patch`; never merged). The depth-4 betas are one call, the `def_eq(inferred, expected)`
  after the proof's four leading lambdas: 8303 units and 43 betas. Its inferred side still holds the redex that
  instantiating the simulation's program variable leaves (`machine/sim.rs`, `choose_fn`), where the statement side
  has the choice already inlined (`machine/statement.rs`, `SEnv::choose`). Conversion reduces both sides to weak head normal
  form before comparing heads, so it runs the program's 64-bit gates symbolically on the inferred side: the 64-lambda
  telescopes are Church bit-vector literals and gate continuations (`encoding/gates.rs`). The match is by signature
  against registered constructors and resolved most, not all, of the 43 (the `good_*` and `lift_*` constructors were
  left out to keep the probe under its memory cap). Before that reduction the two sides differ only at the head. A
  probe-only flag tried a congruence step before `whnf`; all verdicts stay `Accepted`:

  | program | off | congruence (heads equal, arguments convertible) | one head beta, then pointer equality |
  |---|---|---|---|
  | `capturing_closure_loop` | 23552 | 18644 (-20.8%) | 15400 (-34.6%) |
  | `straight_line` | 33989 | 31865 (-6.2%) | 31141 (-8.4%) |
  | `doubling(6)` | 19884 | 19163 (-3.6%) | 19462 (-2.1%) |

  With one head beta the depth-4 call falls from 8303 units and 43 betas to 181 and none: after one syntactic step
  the inferred side is pointer-equal to the expected one. These are totals over `holds()`, so the work is removed,
  not moved. Neither form is a keeper as written. A failed attempt is not memoised (the conversion memo records only
  successes), and with the congruence form on, 9 rejection tests in `proof::tests` did not finish in 43 minutes
  (107 passed; the whole module takes 1.19 s without the flag), and `modules::swapped_call_indices_are_rejected`
  alone ran past 60 s against about 1 s. The head-beta form was not run against the rejection tests.
- How the gate's work grows with program size (`dg-build-d1-12`, `dg-d14-16`, `dg-lean-d14-17`, `dg-lean-d18-19`,
  test profile; patch `docs/runs/2026-11-12/patches/doubling-growth-probe.patch`, which applies to a clean main and
  includes the reviewer's `doubling-growth-referee-addon.patch`; it also lifts the gate's 8192 and the JIT's 16384
  size caps behind an environment variable, so d past 12 could be measured; never merged). For doubling d, d = 1 to
  19, build and check work are linear in the compiled module's size, which has 2^(d+1) - 1 instructions; the source
  DAG's d + 2 nodes do not matter. Fitted over d = 8 to 15: check = 5256 + 115.0 per instruction, build = 2967 + 69.3
  per instruction, within 0.3%. Successive ratios reach 1.999 to 2.000 from d = 13 and hold to d = 19 (120.6 M check
  units), so there is no superlinear break like v0.7's hnf at d = 13. At d = 6 a fixed cost of about 5000 units is
  still 27% of the check. Inferring the statement is 96.5% of the check at d = 15; the proof stage adds only 4 units
  per instruction. One site dominates: instantiating an application's Pi domain while inferring the statement is
  exactly 240 + 68.0 units per instruction, 59% of the check from d = 12 on (45% at d = 6). Each Add in the statement
  applies a 64-bit word's eliminator, whose continuation's type is a telescope of 64 Pi binders ending in the result
  variable. Instantiating it with the one pending argument costs 66 units, at two context depths (27 and 91) per Add.
  Each Add is a separate single-use node, and `infer` skips its cache for those by design (2,327,037 of 2,327,552
  statement nodes at d = 15), while `instantiate_n`'s memo lasts one call. Across all of those calls there are only 3
  distinct (domain, argument) pairs, so nearly all of the 59% recomputes the same three instantiations. That
  redundancy is what a memo across calls, or a statement that shares those types, would remove (measured in the next
  bullet). Untimed wall time, on a shared machine: check 1.0 s at d = 14 and 29.5 s at d = 19.
- A memo of instantiation across calls (`inst-memo-programs-*`, `inst-memo-doubling-*`, `inst-memo-d16-lean-*`,
  `inst-memo-suite-*`, two reviewers' `ref*-` and `inst-sound*` reruns; patch
  `docs/runs/2026-11-12/patches/inst-memo-spike.patch`, which applies to a clean main and includes the doubling probe
  and the reviewer's region test). Arm B's design is merged (next bullet); arm A was not. Arm A keeps whole `instantiate_n` calls for the region, keyed by
  (term, the argument list interned to an id, depth), cleared with the `whnf` memo when the region closes; a hit
  ticks nothing, as the other memos' hits do. Arm B also keeps the inner entries across calls, with the argument
  list's id in their key. Check work, all verdicts unchanged:

  | program | off | A | B |
  |---|---|---|---|
  | `capturing_closure_loop` | 23552 | 21589 (-8.3%) | 20668 (-12.2%) |
  | `straight_line` | 33989 | 32493 (-4.4%) | 32467 (-4.5%) |
  | `held_out_b` | 46284 | 43908 (-5.1%) | 42983 (-7.1%) |
  | `doubling(6)` | 19884 | 10798 (-45.7%) | 10798 |
  | `doubling(12)` | 947382 | 369820 (-61.0%) | 369820 |
  | `doubling(14)` | 3773668 | 1463510 (-61.2%) | 1463510 |
  | `doubling(16)` | 15078674 | 5838096 (-61.3%) | 5838096 |

  Build work does not move (B: 2 units less on the loops). On doubling the Pi-domain site falls from 557296 to 374
  units at d = 12, and the check's slope from 115.0 to 44.5 units per instruction, still linear. The saving is the
  instantiate drop (611548 to 42176) plus a shift drop (35289 to 27099); inference and conversion ticks do not
  change. 77% of top-level calls hit at d = 12 (25 to 27% on the loop programs); the memo ends with 37125 entries at
  d = 12 and 590093 at d = 16. B saves nothing more on doubling and adds inner entries, 1.3 times A's count
  (196645 against 147721 at d = 14). The kernel tests, `proof::` (rejection and mutant tests included) and
  `jit::` pass in every arm at about the same untimed wall time (B fails one kernel test that reads the per-call
  memo's field directly). A reviewer's test over 40 regions, with persisted arguments and their region twins,
  matches a reference substitution and fails when the memo is not cleared at close. Not measured: time (each
  top-level call builds and hashes a key of up to 64 argument keys, unticked), and church-bv's tests.
- The merged memo (2026-11-12, by decision; `subst.rs#instantiate_n`, `hc.rs#inst_args_id`): one memo for the
  region, keyed (node, depth, argument-list id), which stores each call's root and, as before, the shared nodes
  above `hc::low`; the per-call clear (`inst_begin`) and its re-entry guard are gone. Its check work equals arm B's on
  all five programs measured (`p1-work`: 20668, 32467, 42983, 10798, 369820), no other test's work count moved,
  and the workspace suite passes (`p1-suite`: 822, the 819 before plus three memo tests). The timed A/B
  (`time_doubling_12`, six alternating runs per arm) was refused four times on a busy machine (`p1-ab-doubling12`,
  `-r2` to `-r4`; a game held CPUs 8 and 9), so the claim is "does less work", not "faster", until it runs.
- The head-beta shortcut on top of the merged memo (`hb-*`, a reviewer's `hb2-*`; patch
  `docs/runs/2026-11-12/patches/head-beta-on-memo-probe.patch`; never merged). The shortcut is the one in "Where
  the depth-4 telescopes come from": before `whnf`, one syntactic head beta on a side, then pointer equality with
  the other. Check work, memo alone against memo plus head beta: `capturing_closure_loop` 20668 to 19075 (-7.7%),
  `held_out_b` 42983 to 41380 (-3.7%), `straight_line` 32467 to 32092 (-1.2%), `doubling(6)` 10798 to 10779,
  `doubling(12)` 369820 to 369801; all `Accepted`. The memo had already taken most of what it saved on main. A
  failed attempt costs at most one contraction per side and a pointer compare, with no recursion into conversion,
  and the rejection tests do not blow up: `swapped_call_indices_are_rejected` passes in 0.3 s, `proof::` passes
  116 in 1.9 s against 1.7 s off, `gate_mutants` and `jit::` pass. One kernel test fails with it on,
  `whnf_memo_outlives_one_def_eq_in_a_scope`, because conversion settles that pair without calling `whnf`, so no
  `whnf` entry is written.
- The bench's cold row keeps the cost of the stacker segment, by decision (2026-11-12): it is what a caller on a
  1 MiB thread pays, as criterion's main thread is.
- gcd's warm call does not move (126 against 127 ns). Inference: its few iterations make the 1.25 ns per iteration
  that `return_call` costs invisible beside the call into the module; confirming it would take a gcd input with many
  steps.

**Correctness checks.**
- Goldens: 11 WAT files change, each a tail self `return_call` turned into `local.set`s and `br $top` inside the loop
  wrapper (`capturing_closure_loop` and its specialised form, `closure_typed_loop_carried_parameter_loop`, `gcd`,
  `gcd_with_two_base_cases`, `inconsistent_arity_loop_carried_parameter_loop`, `iterate`, `partial_application_loop`
  and its specialised form, and the two `tail_recursive_loop_with_*_self_call_arg` modules). `baseline.rs`'s verdicts
  do not change.
- The six loop-form targets are `Accepted` and the O3 spike's 54 mutants are rejected, each at its recorded layer
  (`proof/tests/loop_form.rs`). The shipped `capturing_closure_loop` and `held_out_b`, compiled as the lowering emits
  them, gate `Accepted` with `br $top` and no self `return_call`.
- `compile_fuzz` (1000 seeds, 12 trials each): all 1000 programs agree with eval through `jit.apply`. A temporary
  count (`t4-fuzz-loop-count-2`, reverted) found `br $top` in the compiled text of 482 of the 983 that compile. The
  test does not tell an installed loop from an interpreter fallback.
- A function with env words loops correctly through both env forms (`Params(1)` and `Pointer`), matching eval. It
  still pushes its env words before the `Set`s, and the `Br` drops them (`PARKED.md`, "Dead env pushes before a
  loop-form `br`").
- The workspace suite after T4 (`cargo test --workspace`, run `t4-suite`): 819 passed, 0 failed.
