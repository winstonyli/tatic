## 36. Lambda lifting of directly called combinators

Step 4 of the IR design (`docs/superpowers/specs/2026-09-23-jit-ir-design.md`).

**What was wrong.** §34 kept flat closures and noted lambda lifting as later
work, and a first reading of the builder suggested it had nothing left to
do: a lambda literal in function position already becomes a statically
known `CallKnown`. But the lowering still allocated that callee's
environment in linear memory on every call (`push_closure_env`), even
though nothing else could ever see it. `capturing_closure_loop` paid one
bump allocation per iteration for a closure that never escapes.

**The spike first.** Before designing, hand-written equivalents of the
three closure benches were timed against today's code (20,000 iterations,
warm JIT, best of 15 interleaved, machine shared): lifting the capturing
closure 3.1-3.4x; specialising `caller (add acc) n` to `add acc n`
7.0-7.6x; substituting the loop-invariant closure parameter `g` 1.2-1.6x.
Only the first leaves the term unchanged, so only it fits the hash-exact
gate of §35; the other two need a validator beyond hash equality and are
recorded as future work in the spec.

**What changed.** A capturing combinator that nothing reaches through the
table -- never packed by `MakeClosure`, never a partial application's root
(`lower_wat::direct_only`) -- takes its captures as leading `i64`
parameters. Its `Env(k)` reads are locals, a call pushes the captured
values, and a non-tail self-call forwards them. Everything reachable
through the table keeps the uniform `$env` convention, so no indirect call
pays anything. It is a lowering choice derived from the module (field
parity class 3): the IR, `ir::check`, the decompiler and the gate are
untouched. The rejected alternatives -- a dual entry for every capturing
combinator (each indirect call pays an extra Wasm call through a stub), or
a hybrid for combinators both called directly and escaping -- are in the
spec; the hybrid stays open.

**How it was checked.** Golden WAT changed for exactly the two direct-only
capturing terms (`capturing_closure_loop`, `a_capturing_closure_call`):
the allocator, `hp` and memory exports disappear. New differential cases in
`ir_fuzz.rs` cover two captures in order, tail and non-tail recursion that
forwards a capture, a direct call made from inside a direct-only one, and
an escaping closure built from one's capture, under both dispatch modes.
Verify-teeth, each caught: reading `$e0` for every slot, forwarding zeros
on a non-tail self-call, and pushing a call's captures in reverse. The
memory-bound test that relied on the capturing loop allocating now uses an
escaping closure.

**Cost.** Criterion `capturing_closure_loop/jit_warm_cache_hit`, `main` vs
this change, three interleaved rounds on a shared machine: best-of-three
medians 301.6 µs -> 94.6 µs (3.2x). The unchanged controls moved 7-14% in
the same runs (`partial_application_loop` 628.7 -> 541.7 µs,
`closure_typed_loop_carried_parameter_loop` 161.3 -> 149.4 µs), so the
3.2x is well above noise and matches the spike. `capturing_closure_loop`'s
bench now also goes through the JIT and measures §37's specialisation on
top of this step's lambda lifting; lambda lifting itself stays covered
separately by its own `try_compile`-level golden-WAT test, not by the
bench number alone.

