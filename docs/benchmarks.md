# Benchmarks

`crates/tatic/benches/` has two [criterion](https://docs.rs/criterion) suites (`cargo
bench`, or `cargo bench --bench execution` / `--bench proofs` for one):

- `execution.rs` — interpreter vs. JIT, cold (compile + verify) vs. warm
  (cache hit), for a non-tail-recursive term (naive `fib`), a
  tail-recursive one (`gcd`, compiled to a loop), and straight-line
  `factorial`. Shows both the steady-state speedup and how much of it the
  one-time compile+verify cost eats into — `fib`'s cold-compile cost
  includes building its (two-self-call) universal proof. That number,
  29 ms, idle, on 2026-09-25, also included 3 concrete instances of the
  theorem, which the JIT no longer builds (`docs/related-work/` §73; it is 12.8 ms at fbc988b, §74, and 6.1 ms once `verify`
  stopped interpreting `fib(20)`, §71; it was about 140 ms
  before `subst_top` substituted in one pass, `docs/related-work/` §53; ~15ms with
  no kernel proof involved at all); the warm (cached) case is unaffected
  either way, since none of this runs again for a hash already in the cache.
  Also `capturing_closure_loop` — a tail-recursive term that creates and
  immediately calls a fresh capturing closure every iteration, isolating
  the closure-conversion path's own cost (the bump allocator, not
  `call_indirect`'s unpacking). Building this benchmark surfaced a real
  bug, not just a number: warmed up, it ballooned to several GB and never
  finished within criterion's default sample window, because the bump
  allocator's pointer was never being reset between the many separate
  calls this cache makes to one compiled instance (`README.md`, the `jit.rs` row
  of "Architecture") — fixed, and now warm calls (20,000 iterations each) run at
  ~87µs total with memory staying bounded regardless of call count
  (about 7µs since closure specialisation, `docs/related-work/` §37). Also
  `partial_application_loop`
  — the same idea for the compile-time partial-application desugaring
  (`register_partial_app`/`Lowering::pap_env`): each iteration partially
  applies a literal lambda and completes it through a wrapper, so the
  synthesized wrapper combinator compiles once but its environment (the
  partially-applied function's own, empty, environment plus the
  newly-supplied argument) gets allocated fresh every time. Ran clean —
  no repeat of the capturing-closure bug, memory stays bounded across
  250k+ warm iterations — but noticeably slower than a plain capturing
  closure's warm call (~194µs vs. ~87µs, both 20,000 iterations, before
  §37's specialisation removed most of both: 8µs vs. 7µs now), the expected cost of the
  extra indirection: creating the underlying function's own environment,
  then the wrapper's own, then a call through the wrapper on top of the
  real one. Also `closure_typed_loop_carried_parameter_loop` — the
  opposite shape from `capturing_closure_loop`: a closure-typed
  *parameter* (`inc`, non-capturing) threaded through every iteration and
  called via `call_indirect` each time, rather than a fresh closure
  created per iteration, isolating `call_indirect`'s own unpacking cost
  from closure-conversion's allocation cost. On this machine, warm calls
  (same 20,000 iterations) run at ~56µs, cheaper than either loop above (no
  environment to build at all, every iteration). The self-recursive function itself
  (`prove_tail_recursive_universal` covers a closure-typed loop-carried
  parameter, see `proven.md`) gets the universal theorem,
  checked directly against it — but since a `Clo`-typed parameter can't be
  supplied through `jit.apply`'s plain-`i64` args from the outside, the
  benchmark itself bakes an initial closure in and calls through a
  wrapper, and `is_kernel_verified` on *that* wrapped term actually
  reflects `prove_closure_expr`'s own, separate "self-recursive combinator
  called directly" postulate (opaque either way) rather than the
  universal theorem — an honest distinction, not a weaker guarantee:
  either way it is a theorem over every input, which is what the
  installation gate requires.
- `proofs.rs` — the cost of building each kind of kernel proof from
  `proof.rs`: one `refl` for a straight-line term, one relational
  (per-execution) proof per call, and the one-time universal
  proof. Includes a direct N-relational-calls-vs.-one-universal-proof
  comparison, since that crossover is the actual argument for building the
  universal proof at all — on this machine it lands around 150-200 sample
  points (a universal proof ≈ 5ms once vs. ≈ 25µs per relational call), so
  which is cheaper depends entirely on how many sample points
  `jit.rs` would otherwise verify against. Also `closures_fragment_proof`
  — `prove_closure_expr`'s own cost across the closures fragment's shapes,
  none of which touch `prove_tail_recursive_universal`'s induction machinery at all (the
  top-level term must be non-recursive for this fragment): on this
  machine, `twice_inc_5` (non-capturing, the same term `bin/demo.rs`'s own
  demo uses) is the cheapest at ~10.3µs; a directly-called capturing
  closure costs ~14.4µs (the extra `Env` value); a non-capturing partial
  application ~11.8µs; a capturing one ~21.8µs (paying for both the PAP
  wrapper postulate and its own `Env`, on top of everything the
  non-capturing PAP case already does). Also
  `closure_typed_recursion_universal_proof` — `prove_tail_recursive_universal`'s
  own cost for a closure-typed loop-carried parameter (`iterate`'s
  shape, see `proven.md`), which unlike
  `closures_fragment_proof`'s own group *does* go through
  `prove_tail_recursive_universal`'s full induction pipeline (`denote_closure`'s self-call
  readings, not just its whole-body one): at ~13.7ms, noticeably more than the same 2-leaf
  shape's plain-arithmetic counterpart (`gcd_2_leaves`, ~9.0ms above) —
  the closure-typed pipeline's extra bookkeeping costs something even on
  a term, like this one, that never actually creates a closure inside the
  loop.

