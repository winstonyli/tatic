### A domain on every row: a cost spike (2026-11-13)

The question: the user picked a domain condition on every Word and Bit row, constant true on the total ones, over an
8th constructor for partial rows (t1, "if a cost spike passes"; `docs/decisions/2026-11-10-v08-shape-and-any-backend.md`,
"Decided: where the domain lives (2026-11-13)"). What does carrying the guard `choose(r, dom x y, K, z)` cost the
gate's programs? Throwaway, three rounds; patches against `a4ff039` in `docs/superpowers/spikes/`:
`2026-11-13-domain-on-every-row-M2-spike.patch` (machine guard only), `-MS2-` (machine and source guards) and `-MS3-`
(MS2 with `choose` taking its branches as arguments). Each includes the `p1_probe` work probe, which counts build
work (statement and proof) beside check work.

**Round 1, discarded.** The guard was `choose(r, dom, K, K)` and went through the opaque `ch` on the proof path, so
it never reduced on the literal 1 and the walk took both arms: check work rose 2.5 to 86 times and doubling(12) hit
the 12 GB cap. Neither choice is the design's.

**Round 2** (real `choose`, the statement's own `z` as the else branch, threaded through `MeaningEnv` and `SEnv`;
runs `2026-11-12-t2-*`). The guard on the machine alone (M2) is cheap: check work +8.2% (`capturing_closure_loop`),
+3.5% (`straight_line`), +4.1% (`held_out_b`), +4.0% (`doubling(6)`), +1.2% (`doubling(12)`, 374312 against
369820); build work +21 to +44%; both linear-scaling tests and every `proof::` and `tatic-wasm` test pass. The
source side needs no guard for total rows, since the machine's `choose` over the literal 1 reduces to its first
branch. With the guard on the source side too (MS2), build work grows 3.84 and 3.92 times per doubling
(`gate_build_work_is_linear_in_the_tree` fails) and doubling(12) hits the memory cap.

**Round 3: why the source guard is quadratic** (runs `2026-11-13-t3-*`). `choose(r, w, x, y)` put `x` and `y` under
its three binders, so it shifted them by 3. On the source side `x` is the continuation, the whole rest of the
program, and the next guard nests inside it; each suffix node is then shifted at a new cutoff per nesting level, and
the shift memo, keyed by cutoff, misses each time. Counted with temporary kernel counters: all of the statement's
build work is shifts, about half the square of the distinct cutoffs, which double with the tree (1537, 3073, 6145
at doubling_9..11); the walk's one `whnf` of the source term pays the same again. Folding a guard whose condition
is the literal 1 at build time restores M2's numbers within 1% (cutoffs stay at 21), and guarding only `If` compares
leaves `doubling` (which has none) at M2's. The machine side never showed it because its continuation is a bound
variable (`rest`), not an inlined term. It is the shape of "Why the check grew 4x per doubling", reached through the
cutoff.

**The fix, MS3:** `choose` becomes `(\X:R. \Y:R. w (Lift R) (\c T g. g (c R X Y)) R id) x y`, beta-equal to the old
form, so the branches stay at the outer depth and shift at one cutoff. With every Prim guarded on both sides and
nothing folded, build scales linearly again ([146395, 288604, 572893] at doubling_9..11) and check
too ([20551, 34990, 63765] at 7..9); `tatic-wasm` 46 passed, `proof::` 116 passed. Work against main: check +17.7%,
+6.8%, +9.5%, +23%, +26% (doubling(12) 465482); build +33%, +39%, +35%, +86%, +100% (1141342). Rerun by hand on
the spike's worktree (`t3-ms3-verify`, `t3-ms3-verify-lin`): the same numbers to the unit. Not measured: MS3 with
the constant-true fold (expected near M2, not run), If-heavy programs with a guard that does not fold, and `mod`
itself (no row in the spike).
