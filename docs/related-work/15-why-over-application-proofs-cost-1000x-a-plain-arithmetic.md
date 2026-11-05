## 15. Why over-application proofs cost ~1000x a plain arithmetic call — investigated to root cause

`benches/proofs.rs`'s own `over_application_instance_proof` doc comment
had flagged, since the benchmark was first written, that each
over-application instance (`eval_and_prove_call_over`'s own
`clo_eq_ref_if_between`/`clo_eq_ref_pap` shapes) costs roughly
20-30ms — three orders of magnitude past
`gcd_relational_proof_single_call`'s own ~24us per plain-arithmetic
call — "left as a discovered fact this benchmark documents, not
something fixed here." Investigated properly this session, with two
genuinely separate findings, one real and fixed, one real and inherent.

**Fixed, on the first attempt: real, but aimed at the wrong three of
five files.** `term::Hash` is a BLAKE3 digest — 32 bytes, already
uniformly random — and profiling `over_application_instance_proof`
under `callgrind` found `<DefaultHasher as Hasher>::write`/
`BuildHasher::hash_one` accounting for over 40% of all instructions
retired, re-hashing that already-good digest through Rust's default,
cryptographically-oriented SipHash for no benefit. The first fix applied
a small, self-contained rotate-xor-multiply hasher (`term::FxHasher`/
`FxBuildHasher`, the same reasoning `rustc-hash`/`FxHash` is built on)
across all 17 `HashMap<Hash, _>` sites in `term.rs`, `compile.rs`,
`jit.rs`, and `proof.rs`. It was correct (full test suite, fuzzers,
clippy, release demo all green) but helped only modestly (0% to -8.5%
wall-clock) — a sign something was off, since eliminating a 40%
instruction-count contributor should have moved the needle much more.

**Root cause, found via re-profiling and a direct question about
`hashbrown`'s own defaults: three of the five touched files were
already on a fast hasher, and the fix needed to go somewhere else
entirely.** Re-profiling after the first fix showed instruction count
barely moved (1.040B → 1.028B, ~1%) — the real win wasn't where the
first fix looked. `hashbrown` (already a direct dependency, and already
imported directly as `HashMap` in `term.rs`, `compile.rs`, and
`jit.rs`) ships its own `default-hasher = ["dep:foldhash"]` feature,
enabled by default: a bare `hashbrown::HashMap<K, V>` (no explicit
third type parameter) already uses `foldhash`, a modern, fast,
well-vetted non-cryptographic hasher — meaning those three files were
never the problem, and the custom `FxHasher` applied to them was a
lateral move, not a fix. The two files that *did* import
`std::collections::HashMap` (always SipHash, `hashbrown` or not) —
`proof.rs`'s `ClosurePostulates` memoization tables and `kernel.rs`'s
`ReductionCache`/`ShiftCacheMap` — were the real bottleneck, and hadn't
been switched to `hashbrown` at all (the first fix had only bolted a
custom `BuildHasher` onto their existing `std::collections::HashMap`,
which works but is strictly worse than the library's own vetted
default). Corrected by fully reverting the custom `FxHasher` everywhere
(deleted from `term.rs`; all 17 sites back to plain, unparameterized
`HashMap`) and instead changing exactly two import lines —
`proof.rs`'s and `kernel.rs`'s own `use std::collections::HashMap;` to
`use hashbrown::HashMap;` — no struct or constructor changes needed
anywhere, since every call site already used the simple `HashMap::new()`
API both types share.

**Confirmed properly this time: re-profiled, not just re-measured.**
Re-profiling `over_application_instance_proof` under `callgrind` after
the real fix found `DefaultHasher`/SipHash gone from the profile
entirely — not reduced, gone — with total instructions retired down
~44% (1.04B → 584M). Wall-clock (criterion) confirmed it independently:
-24% to -26% on both benchmark shapes, `p < 0.05`. This is also,
incidentally, the fix for this project's own previously-open lead on
`kernel.rs`'s `ReductionCache`/`ShiftCacheMap` sitting on the same
default SipHash — the same one-line-per-file import change covers both.

**Ruled out: `with_shift_cache` doesn't help here, confirmed by
measurement, not assumed.** Given ~938,812 `shift_rc` calls for 4
iterations, the natural next guess was that the existing
`with_shift_cache` mechanism (a proven ~2x win on large branching-leaf
instances, per its own docs) was simply not engaged for this shape.
Tried directly (wrapping the benchmark's own `prove_tail_recursive_instance`
call in `kernel::with_shift_cache`): it made both shapes measurably
*slower* (223ms vs 202ms; 139ms vs 127ms), not faster. This matches the
cache's own documented limitation: it wins when the *same* subterm gets
reshifted by the *same* amount across several callers, and loses
(HashMap overhead paid for nothing) when it doesn't. This workload's own
938K shift calls aren't that pattern — see below for what they are.

**The real, inherent answer: the cost is super-linear in iteration
count by construction, not a hidden bug.** A direct scaling check (the
same term, `prove_tail_recursive_instance` at 1, 2, 4, 8, 16, 32
iterations) measured 69.6ms / 102ms / 204ms / 441ms / 985ms / 2672ms
(measured before the hashbrown/foldhash fix above — the fix changes the
constant factor throughout, not this shape). Each doubling of the
iteration count costs progressively *more*, not a
constant multiple (1.47x, 2.00x, 2.16x, 2.24x, 2.71x) — consistent with,
and explained by, `trans_proof`'s own cumulative composition: each new
iteration's own step proof is built by transitivity against the *entire*
proof chain accumulated so far (`kernel::trans_proof`, chained once per
iteration), so total work across `n` iterations is a sum of growing
terms — the same reason repeatedly appending to a growing structure by
copy is inherently superlinear, not specific to closures or
`eval_and_prove_call_over` at all. `with_shift_cache`'s own inability to
help is the same fact from a different angle: there's no *repeated*
work to cache here, just a genuinely *growing* one.

**This also means the original comparison was apples to oranges.**
`gcd_relational_proof_single_call`'s ~24us proves one *relational* step
of a tail-recursive call (`prove_tail_recursive_call`) — it never
unrolls or accumulates a chain across iterations at all, by design (see
this project's own module docs on the relational-vs-universal-vs-instance
proof strategies). `over_application_instance_proof` measures a fully
*unrolled instance* proof's own amortized per-iteration cost instead — a
structurally different, inherently more expensive strategy, run here at
just 4 iterations specifically because that's what real usage
(`build_ev_witness`'s own per-self-call-argument handling) needs, not
because the underlying operation is 1000x more expensive at matched
strategies. The three-orders-of-magnitude framing measured a real
number correctly, but implied a comparison ("over-application closures
are inherently ~1000x slower than arithmetic") that doesn't hold once
the two benchmarks' own proof strategies are accounted for.

