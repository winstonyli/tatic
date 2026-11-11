### A store at a run-time address across a call, the cost of `call`, and eta: three follow-ups (2026-11-10)

Three questions left by the section above, each a throwaway spike. The patch
`docs/superpowers/spikes/2026-11-10-frame-eta-spike.patch` applies on top of the call spike's patch; both reverted.

**Conversion has no eta, tested directly.** A kernel test (`conversion_has_no_eta`, first in the patch, kept since in
`crates/tatic-kernel/src/tests/conversion.rs`) checks
`\A B f. refl f` against `Pi A B (f : A -> B). Id(A -> B, f, f)`, which passes, and against
`Id(A -> B, f, \x. f x)`, which is rejected with a type mismatch; `def_eq` also says `f` and `\x. f x` differ (run
`2026-11-10-c3-eta`). It agrees with the code: `reduce.rs#conv_whnf` compares weak head normal forms constructor by
constructor and has no eta case. A generated proof must therefore pass continuations in exactly the form the machine
builds them, as the nest proof had to.

**What the call patch costs existing programs.** `wasm_scaling` (the existing machine checks at n = 4, 16, 32, 64,
controls at 64) was counted on the test exe built with and without the call patch, by retired instructions (run
`2026-11-10-c2-icount-aba`: `icount`, 6 runs per arm, arms in the order base, patched, base, on CPU 4). The patched
exe does about 1.1% more work: medians 654.8 M against 647.5 M and 647.0 M, best 651.9 M against 644.3 M and
644.2 M, with each arm's median within 0.5% of its best. An unrecorded first count gave the same gap (652.0 M against
644.3 M and 645.3 M). The patch adds the ninth constructor and also threads the environment through the interpreter
(`meaning_env`), and the count covers the whole process, start-up included, so neither part's share nor the extra
work per check is separated. One wall-time run per arm (`2026-11-10-c2-scaling-base`, `-patched`) moved in both
directions on single checks, up to 2.6 times on one of 0.2-0.5 ms and by a quarter on ones of 3-7 ms, which is noise
for checks this short. The other three ignored tatic-wasm tests (`a_large_check_does_not_churn_stack_segments`,
`bv_lemma_scaling_h3_d2_good_add`, `or_disjoint_scaling`) pass on the patched tree (run
`2026-11-10-d4-ignored-patched-2`; the first try, `-patched`, built main instead and does not count). They exercise
only the bit-vector encoding, not the machine, so they show the patch leaves the encoding alone and say nothing more.

**A store at an address computed at run time, across a call.** The caller stores at its argument's address and reads
it back after a call whose callee writes the next cell:

- caller `x`: `mem[x] := 5; g x; x + mem[x]`;
- callee `g y`: `mem[y + 1] := 7; y`.

Both are machine programs built through `prog` with the call spike's `call`; the callee has no calls. For every `R`,
`z`, `x` with `GoodBv x`, `h` and `k`, the caller's meaning equals `k (x + 5) (upd (x + 1) 7 (upd x 5 h))`. The load
after the call meets two equality tests on symbolic addresses, which conversion cannot decide. Two lemmas over
`GoodBv x` settle them:

- `eq x x = true`: one bit split per bit, chained by `cong1` and `trans_proof`, as in `add_identity_proof`;
- `eq (x + 1) x = false`: one split on bit 0 only. Adding 1 always flips bit 0, so once bit 0 is a literal the
  conjunction inside `eq` reduces to `false` whatever the other bits are.

The law is two J rewrites, one with each lemma, and needs no induction. `GoodBv`'s motive must land in Sort2 and
`Id(Bool0, ..)` lands in Sort1, and the kernel has no cumulativity, so the first run was rejected (run
`2026-11-10-c1-frame-spike`); the lemmas state their motive as `Pi Q:(Bool0 -> Sort1). Q b -> Q (lhs y)` and recover
the `Id` at the end. The second run (`-2`) rejected the frame law with a lambda domain mismatch; the cause, found by
reading the code rather than the log, was a callee that left two values on the stack instead of one. Run `2026-11-10-c1-frame-spike-3`
(untimed, one run, 7% load):

| check | n = 4 | n = 24 | n = 64 |
|---|---|---|---|
| `eq x x = true` (proved) | 0.22 ms | 0.73 ms | 1.83 ms |
| `eq (x + 1) x = false` (proved) | 0.14 ms | 0.48 ms | 1.56 ms |
| frame law (proved; it contains both lemmas) | 0.71 ms | 1.14 ms | 2.33 ms |
| the callee writes `y`, not `y + 1` (rejected) | 0.39 ms | 0.84 ms | 2.94 ms |
| the caller reads `x + 1` after the call (rejected) | 0.38 ms | 0.91 ms | 2.37 ms |
| the right program, proof `refl` (rejected) | 0.16 ms | 0.25 ms | 0.57 ms |

The last control shows that conversion alone does not decide the frame. The two program controls reuse the intended
proof and statement; all three fail with a type mismatch, and the reasons were not inspected further.

What it settles, and what stays open:

- **Frame steps at symbolic addresses are proofs, not conversion** (shown for one offset, `+1`, and a callee with no
  calls). Each read after a write at a run-time address costs one J with an address lemma. The lemmas have no
  rejected control of their own; only the three program-level controls above. A lemma for a literal offset is cheap when the offset flips a bit no carry can
  reach. For `+1` that is bit 0, so one split.
- **A literal offset `k` with low zero bits** needs the carry into its lowest set bit shown to be zero. That costs a
  chain over those bits, like `add_identity_proof`'s (inference; the next section runs `k = 2`: two splits).
- **Open: a region.** A recursive caller whose callees allocate at `p + 1`, `p + 2`, ... up to a depth that is only
  known at run time needs `eq (p + j) p = false` for symbolic `j` with `0 < j < 2^n`. This was framed as a carry-chain
  lemma over `lt_u` or no-overflow; the next section shows neither is needed and proves it.

