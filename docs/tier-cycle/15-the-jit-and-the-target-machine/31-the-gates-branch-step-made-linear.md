### The gate's branch step made linear (2026-11-13)

The question: a nested `if a == k then .. else ..` chain on main grew the gate's check work 2.3x to 3.6x and its build
work up to 3.5x per doubling of depth ("Word-row guards through the probe: a spike (2026-11-13)", last part). Where
does it go? Counted with temporary kernel counters (shift calls and shifted nodes per calling operation and per
builder; removed afterwards), runs `2026-11-13-a1-*`. Three causes, all in the gate's term builders, none in the
kernel:

- **The walk's congruence** (`machine/sim.rs#cong`) built both J proofs inline, under three binders, with the else
  branch and its proof shifted into them. In a chain each level's proof contains the next level's, so every level
  shifted a new copy of everything below it: 74% of the build's shifting at depth 128 (7637, 25973, 94901, 361781
  shifted nodes at depths 16 to 128), and a share of the check's.
- **`machine.rs#choose`** shifted its branches, which hold the rest of the program, under its own three binders (the
  statement-side shape of "A domain on every row: a cost spike (2026-11-13)", round 3, still on main): about 25% of
  the build's shifting, also growing 3.5x.
- **The final comparison.** The proof's type has the real choice put in for the probe `CH`, while the statement held
  `choose` unfolded; the two are only beta-equal, so `def_eq` reduced both at every branch and shifted the rest of the
  program each time. With the first two causes gone it was 99% of the check's shifting (99.6k, 318k, 1114k shifted
  nodes at depths 32 to 128), mostly fresh copies (252k distinct nodes at depth 128), not memo misses by cutoff.

**The fix** (`5b062ee`): `cong` applies a closed lemma `sim.rs#cong_lemma` to its nine arguments at the walk's depth,
and `choose` is the closed `machine.rs#choose_fn` applied to its four arguments, never unfolded, so the proof's type
and the statement are the same term and compare without reducing. The MS3 form (branches as arguments) was a
stepping stone: build linear, check still 3.15x per doubling. Ablations at depth 128, check/build: main 4.64M/512k,
the lemma alone 1.41M/157k, `choose` alone 3.41M/411k, both 113k/56.6k.

| depth | check before | check after | build before | build after |
|---|---|---|---|---|
| 16 | 136279 | 18481 | 18180 | 9630 |
| 32 | 389345 | 31953 | 47220 | 16334 |
| 64 | 1274460 | 58897 | 146772 | 29742 |
| 128 | 4639314 | 112785 | 511764 | 56558 |

Both grow 1.9x per doubling at the last step. `gate_check_work_is_linear_in_an_if_chain` checks check and build at
depths 16, 32, 64 under 2.2x per doubling; it failed on the old main (`a1-iftest-main`) and passes now. The doubling
series move little (check [16523, 27944, 50757] to [15174, 25551, 46296] at doubling_7..9; build down 18 units).
Verdicts unchanged; `tatic-wasm`, `proof::`, `jit::` and church-bv's default tests pass (`a1-verify`,
`a1-verify-churchbv`).

**Option 1 of the partial-row spec on top of the fix** (patch
`docs/superpowers/spikes/2026-11-13-word-row-guard-on-the-linear-step-spike.patch`, against `5b062ee`; runs
`2026-11-13-a1s3-*`): every Word site guarded through the walk's probe, never folded, as in "Word-row guards through
the probe: a spike (2026-11-13)". Every verdict and control there holds again (gcd, `gcd_with_two_base_cases` and the
three `%` programs Accepted; the twin row, the dropped guard and the operator swaps Rejected), and every series is now
linear: the tree's check [47174, 89138, 173022] at doubling_7..9 and build [137106, 271058, 538898] at
doubling_9..11, the if chain 1.72x and 1.84x, the nested `%` chain 1.02x to 1.47x per doubling of depth (check 64944
to 162264 at depths 16 to 256, against 97098 to 2607683 before the fix). Work, check/build, against main plus the
probe at `5b062ee`:

| program | main | option 1 |
|---|---|---|
| capturing_closure_loop | 8485/6409 | 9288/7275 |
| straight_line | 28603/3866 | 29241/4530 |
| held_out_b | 30481/6562 | 31449/7568 |
| doubling(6) | 9981/11617 | 26170/19762 |
| doubling(12) | 336627/570343 | 1346914/1074514 |
| gcd | NotCovered | 61609/7037 |
| gcd_with_two_base_cases | NotCovered | 62100/7613 |

The loop programs pay 2-10% check and 13-17% build; `doubling`, all `add`, pays a constant factor (check 2.6x and
4.0x, build 1.7x and 1.9x), since every site is a guard the walk steps over. `tatic-wasm`, `proof::` and `jit::` pass;
church-bv's `job::hidden_state_is_classified` fails on the spike's test-only thread-local `DROP_GUARD` (`machine.rs`),
which a real build would not have.
