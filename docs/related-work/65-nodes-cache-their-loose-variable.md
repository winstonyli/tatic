## 65. Nodes cache their loose-variable range

This builds stage 1 of §64: cached loose ranges, without constants.

**What changed** (`src/kernel.rs`).
- Every child of an `Expr` is a kernel `Rc`: `std::rc::Rc<Node<T>>`,
  where `Node { loose: u32, val: T }`. `Rc::new`, `ptr_eq`,
  `strong_count`, `as_ptr` and every pattern keep compiling, so only
  `proof.rs`'s two test uses of `Rc` on kernel nodes changed.
- `loose` is `loose_of(e)`: one more than the largest loose `Var` index,
  0 when closed, computed from the children's cached ranges when the node
  is built. It saturates, so it's exact only below `u32::MAX`, which no
  real term reaches.
- `shift`, `instantiate` and `is_var_free` return early when
  `loose_of(e)` is at or below the cutoff or depth. `shift` and
  `instantiate` also keep each such child by pointer (`shift_child`, and
  `instantiate`'s `go`), rather than rebuilding it.
- A heap node grows from 64 to 72 bytes: the `u32` plus padding.
- `shift_sigma_family` stayed. The spec said it goes once `shift`'s arms
  are one line each. But its reason, at `infer_sigma`, is only that
  smaller hot frames cost nothing, and that still holds.

**Measured.** `scripts/gate/bench_ab.sh 43b5e15 --bench proofs`, 3 rounds,
CPU 4 to 9% around every run. Each round runs base, candidate, then base
again; *noise* is that rerun against base. Round 1's noise was -7 to -63%,
so it's unreliable. Round 2's noise was within ±8% except `relational_x1`
(+13%). Round 3's was wider, up to +36%. Times are best of 3, in µs.

| bench | base | stage 1 | change | noise, rounds 2 / 3 |
|---|---|---|---|---|
| `gcd_2_leaves` | 1,730 | 1,350 | -22% | -7% / -5% |
| `gcd_3_leaves` | 3,210 | 2,530 | -21% | +1% / -5% |
| `universal_x1` | 1,640 | 1,370 | -16% | +8% / -4% |
| `closure_typed_loop_carried_parameter_universal_proof` | 2,430 | 2,480 | +2% | -2% / +16% |
| `if_between_closures_self_call_arg` | 8,020 | 8,190 | +2% | -3% / +10% |
| `pap_producing_root_self_call_arg` | 5,980 | 5,720 | -4% | -6% / +6% |
| `relational_x10` | 111 | 116 | +4% | +7% / +22% |
| `relational_x5` | 60.1 | 57.5 | -4% | +6% / +1% |
| `non_tail_embedded_call` | 18.1 | 18.0 | -1% | -4% / +27% |
| `branching` | 18.0 | 18.4 | +2% | -8% / +15% |
| `partial_application_capturing` | 15.3 | 15.5 | +1% | -4% / +18% |
| `partial_application_non_capturing` | 13.1 | 13.7 | +5% | +1% / +36% |
| `gcd_relational_proof_single_call` | 11.9 | 10.9 | -8% | +1% / -4% |
| `non_capturing` | 10.9 | 10.3 | -6% | +1% / +1% |
| `relational_x1` | 9.9 | 9.1 | -8% | +13% / +1% |
| `capturing` | 9.7 | 9.9 | +2% | -2% / +8% |
| `straight_line_refl_proof` | 9.6 | 8.0 | -17% | +2% / -14% |

The three universal proofs are 16 to 22% faster, well past the noise.
Every other bench but one moved 8% or less, and none got measurably
slower. The exception, `straight_line_refl_proof`'s -17%, is noise: its
per-round change was +10%, +10% and -20%.

**`fib(16)`.** `fib16_instance_proof_cost`, 3 interleaved rounds against
the base worktree, best of 3:

| | base | stage 1 | change |
|---|---|---|---|
| build | 510 ms | 454 ms | -11% |
| check | 448 ms | 401 ms | -11% |
| DAG nodes | 265,366 | 227,157 | -14.4% |

The spec expected `check` to be about 20% faster; it's 11%. The plan
expected the DAG unchanged, but it shrank, the same in every round, to
exactly the spike's loose-ranges figure (§64). The builder in `proof.rs`
shifts through the kernel: `Anchored::at`, `kernel::arrow`, and direct
`kernel::shift` calls. Those used to rebuild every node. Now closed
subterms come back as the same allocation, and the probe's `dag_size`
counts allocations, so the built proof shares more.

**Where the spec's 20% went.** It never existed on an idle machine. The
spec took it from §64's payoff table (1.90 s to 1.49 s), measured while
another session held 7 to 8.5 cores (a lower bound: until the 25H2
upgrade on 2026-09-25, Windows undercounted per-process CPU time, so
every "held N cores" figure in this file is at least that). Rerun idle from the spike patch
(`docs/superpowers/spikes/2026-09-25-constants-and-loose-ranges.patch`,
applied to e9f10e6; `SPIKE=... cargo test --release --lib spike_fib -- --ignored`; best of 5, in-process), `fib(16)` goes from 785 ms to
690 ms prove plus re-check, 12%. Stage 1's probe in the same idle window,
best of 3, goes from 800 ms to 686 ms, 14% (build 417 to 365 ms, check
383 to 321 ms). So stage 1 matches the spike, and the load inflated the
spike's gain. The spike's node-visit counter shows why the gain is small:
`shift` still visits 1.84 million nodes, against 2.22 million, 17% fewer.
Nearly every term mentions a postulate as a `Var`, so almost nothing is
closed. Constants (stage 2) are what make terms closed; with both, §64
measured the DAG at 10,501 nodes.

**Tests.** Each was checked against a mutation, then reverted.
- `loose_matches_a_walk`: 20,000 random terms; the cached range equals a
  walk. It caught `loose_of` without the `-1` under `Pi`/`Lam`/`W`/`Sigma`,
  and with `l` for `u` on `Pair`'s `fam` and on `WRec`'s `children_ty`.
- `shift_and_instantiate_match_a_reference`: 20,000 random terms. `shift`
  (by 1, 2 and -1), `instantiate` and `is_var_free` agree with the pre-§64
  versions, kept in the test module. It caught `<= cutoff + 1` in
  `shift_child` and in `shift`'s early return, `<= d + 1` in
  `instantiate`, `<= idx + 1` in `is_var_free`, and `shift_sigma_family`'s
  `Pair` arm shifting `fam` at `cutoff`. The -1 cases, added after review,
  also catch, on their own, a `shift` that returns early for any negative
  amount (the shift-up-and-back round trip already caught it).
- `shift_keeps_closed_children_by_pointer`: caught `shift_child` always
  rebuilding.
- `dropping_a_deep_term_does_not_overflow_the_stack`: drops a 100,000-deep
  `refl` chain on a 1 MB thread. It aborts when the wrapper's
  `strong_count` is one too high, since `Drop for Expr` then never frees a
  child on a fresh segment. `check_survives_a_term_far_deeper_than_the_native_stack_allows`
  passed under that mutation: its 1,000-deep terms drop fine by plain
  recursion.
- `infer_memo_changes_no_answer` built its unshared copy by shifting up
  and back, which now keeps closed subterms. It copies with the reference
  `shift` instead, asserts that the copy shares nothing, and still catches
  §63's length-keyed mutation.

**What's left.** Stages 2 to 4 of §64: `Const` and `Free` in the kernel,
the builder using them, then removing what no longer pays.

