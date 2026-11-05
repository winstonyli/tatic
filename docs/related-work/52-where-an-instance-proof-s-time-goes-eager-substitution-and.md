## 52. Where an instance proof's time goes: eager substitution, and a shift cache that no longer pays

`over_application_instance_proof` is the slowest proof bench after §51
(90 to 135 ms at `n = 4`). Timers around each stage of
`prove_tail_recursive_instance`, and counters inside the kernel, both
throwaway and reverted, give this for `n = 4` on the `If`-between-closures
term. The machine was shared with another session's build, so the
figures are rough, but the proportions held across runs.

| stage | time |
|---|---|
| `build_universal` (includes its own `check`) | 3 to 6 ms |
| `build_ev_witness` | 1 to 4 ms |
| `infer` on the applied instance proof | 65 to 80 ms |
| `whnf` of the inferred type | 44 to 51 ms |
| leaving `with_shift_cache` (dropping the cache) | 53 ms |

**The term isn't shared.** The applied proof has 9172 nodes as a tree and
8900 as a DAG, so §50's memo B wouldn't help. The kernel spends about
4 µs per node.

**`subst_top` on a dependent body is the cost.** With the shift cache
off, `subst_top` took 5.9 ms of `infer`'s 9 ms at `n = 1`, and did 80k of
its 87k `shift` node visits. The `whnf` of the type was three
`subst_top` calls with 43k shift visits between them. §51's guard
doesn't apply, since these bodies do use `Var(0)`. The eager path shifts
`s` once, again at every binder `subst` crosses, and then shifts the
whole result back by -1. `ctx_lookup` was small: 1205 lookups and 4.6k
shift visits.

**The shift cache is engaged here by mistake.** `instance_visit_count`
decides whether to use it. It returns "expensive" when it can't evaluate
a self-call argument concretely, and a closure application like these
self-call arguments can't be. So the cache is on even at `n = 1`, where
it doubles the time (44 ms against 20).

**Spike: A2, a fused `instantiate`.** A single pass over `body`:
`Var(d)` becomes `shift(s, 0, d)`, higher indices drop by one, and `s`
is shifted only where it's used. It passes
`subst_top_is_substituting_then_shifting`. `prove_tail_recursive_instance`
end to end:

| term, `n` | today (eager, cache on) | A2, cache off | A2, cache on |
|---|---|---|---|
| `If` between closures, 1 | 49 ms | 7.3 ms | 14 to 16 ms |
| `If` between closures, 4 | 191 to 195 ms | 15 to 20 ms | 29 to 33 ms |
| `If` between closures, 8 | 274 to 283 ms | 33 to 36 ms | 52 to 59 ms |
| PAP root, 4 | 109 to 122 ms | 16 to 17 ms | 20 to 22 ms |
| `fib`, 8 | 1.8 s | 90 to 98 ms | 214 ms |

The eager `fib(8)` with the cache off took 3.5 s, which is the 2x win
`with_shift_cache` was added for. It was recovering reshifts that the
eager substitution caused. With A2 those reshifts don't happen, and the
cache costs more to fill and drop than it saves on every term measured.

**Proposal (not landed, since it changes the trusted kernel).**
1. A2: replace `subst_top`'s eager path with `instantiate`, about 30
   lines mirroring `shift`. Checked by the existing differential test,
   `kernel_fuzz` and `kernel_soundness_fuzz`.
2. Then delete `with_shift_cache`, its thread-locals, `shift_rc`'s cache
   path, and `proof.rs`'s `instance_visit_count` and `VISIT_THRESHOLD`.
   That removes hidden state from the kernel. It needs the same
   measurements redone on the benches and `fib(30)`'s cold compile
   before it lands.

`subst` has no caller besides `subst_top` and the differential test's
reference formula, so it would move into the test module.

The first proposal landed in §53, the second in §54.

