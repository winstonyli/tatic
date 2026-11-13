### Word-row guards through the probe: a spike (2026-11-13)

The question: the spec `docs/superpowers/specs/2026-11-13-partial-row-and-gcd-design.md` picks option 1 (v1 w1): a
domain on every Word row, every guard `choose(d x y, rest, z)` through the walk's opaque probe on both sides, nothing
folded, and a last-resort `refl` rule in `machine/sim.rs#Sim::sim_step`. Does gcd pass, and what does the walk cost?
Throwaway; the patch against `b2b86ab` (probe included) is
`docs/superpowers/spikes/2026-11-13-word-row-guard-through-the-probe-spike.patch`. It builds on MS3 of "A domain on
every row: a cost spike (2026-11-13)", minus the Bit and `If` guards, plus the `mod` row (`rem_s`, domain
`nonzero_second`) and `y` marked in `cps`. Runs `2026-11-13-x1-*`.

**Correctness: yes.** `gcd` and `gcd_with_two_base_cases` are Accepted (check work 71534 and 79895), and so are
`\a b. a % b`, `\a b. if a % b == 0 then a else b` and `\a b c. a % (b % c)`; `VERDICTS` changes only in the two gcd
rows. The controls are Rejected at the walk: a twin row `mod_total` (same circuit, total domain) named by gcd's
lowered list ("body/else: the branch conditions differ"; with no edit the twin table is Accepted), the machine's
Word guard dropped ("the machine calls a function but the source branches"), and the operator swaps `mul -> mod` and
`mod -> add`. `tatic-wasm` 48 passed; `proof::` 118 passed, 1 failed (below); `jit::` 113 passed.

**Cost: no.** Work against main (`b2b86ab` plus the probe; doubling(12) reproduces 369820):

| program | check main | check spike | ratio | build main | build spike | ratio |
|---|---|---|---|---|---|---|
| capturing_closure_loop | 20668 | 58614 | 2.84 | 6802 | 7838 | 1.15 |
| straight_line | 32467 | 109050 | 3.36 | 3953 | 4720 | 1.19 |
| held_out_b | 42983 | 82799 | 1.93 | 6963 | 8187 | 1.18 |
| doubling(6) | 10798 | 151123 | 14.0 | 11635 | 18773 | 1.61 |
| doubling(12) | 369820 | 192457261 | 520 | 570361 | 1001039 | 1.76 |

Build stays linear ([128098, 252849, 502272] at doubling_9..11). Check does not:
`gate_check_work_is_linear_in_the_tree` fails, "check work grew 2.94x from doubling_7 to doubling_8: [394717, 1159657,
3785911]", and doubling(12) needs about 15 GB of commit (it fails the 12 GB cap; 84 s at a 28 GB cap). A nested `mod`
chain grows 1.56x and 2.04x per doubling of depth (check 97098, 151570, 308898 at depths 16, 32, 64).

**Where it comes from.** `doubling` is only `add`, a total row, so its whole rise is guards whose condition is the
literal 1: through the opaque probe the walk cannot reduce them, and closes each by congruence on `CH` with the rest
of the program as both branches. The cause inside that congruence (the nested continuation carried on both sides of
every `cong` proof) is an inference, not counted. The fix the spec names as option 2 removes exactly this cost: fold
a guard whose condition is constant true at build time, on both sides, so total rows build what main builds, and
only partial rows (today `mod`) pay a guard. Round 3 of the previous spike measured that fold within 1% of M2.
