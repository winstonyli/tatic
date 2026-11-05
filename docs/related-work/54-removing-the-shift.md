## 54. Removing the shift cache

This lands §52's second proposal. `kernel.rs` loses `with_shift_cache`,
its two thread-locals and `shift_rc`, so `shift` recurses directly.
`proof.rs` loses `instance_visit_count`, `VISIT_THRESHOLD` and the
closure `instance_from_scaffold` wrapped in the cache, and the tests
that exercised them. That is 325 lines deleted and 61 added, and the
kernel no longer has hidden state.

§10's cache was worth 2x on `fib(8)` because eager substitution
reshifted the same arguments. After §53, §52's spike measured the cache
as a net loss on every term tried (`fib(8)`: 214 ms with it, 90 to 98 ms
without), and it had been engaged by mistake on closure self-call
arguments.

**Measured against §53** (the full bench A/B, while another session's
job held most cores). The base run was the most contended of the three,
so each change is read against the noise column, the base's own re-run:

| bench | candidate | noise re-run |
|---|---|---|
| `over_application_instance_proof/if_between_closures_self_call_arg` | -46% | -31% |
| `over_application_instance_proof/pap_producing_root_self_call_arg` | -54% | -22% |
| `fib_30_non_tail_recursion/jit_cold_compile_and_verify` | -9% | -5% |
| `gcd_tail_recursion_to_loop/jit_cold_compile_and_verify` | -57% | +13% |

Nothing regressed beyond the noise. `closures_fragment_proof/
partial_application_non_capturing` read +295% once. Re-run alone, it
read -2%, while the base's own re-run jumped +213%. That bench never
engaged the cache. `fib(30)`'s cold compile in `cargo run --release` read
104 ms in this run and 40.6 ms in §53's, both single runs under load.
The bench's 79 ms against a base of 88 ms is the better number.

