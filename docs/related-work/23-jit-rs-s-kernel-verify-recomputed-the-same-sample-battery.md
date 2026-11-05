## 23. jit.rs's kernel_verify recomputed the same sample battery three times, and invoke() paid a heap allocation on every call -- found and fixed

Two small, independent inefficiencies in `jit.rs`'s hot verification/
invocation paths:

`kernel_verify` called `sample_arg_vectors(arity)` three separate times
(once truncated to the first 3 samples for
`prove_tail_recursive_universal_with_instances`, once in full for
`prove_tail_recursive_call`, once more in full -- identical output to
the second call -- for `prove_closure_expr_instance`), recomputing and
reallocating the same `Vec<Vec<i64>>` each time even though only the
first call's result is ever truncated. Fixed by computing the sample
battery once and reusing it for all three: the truncated slice
(`samples.iter().take(3).cloned()`) for the first strategy, and the full
`samples` (already alive, only ever borrowed by the second strategy's
own `.iter().all(...)`, never consumed) for the second and third.

`invoke` -- the function every real compiled-function call (and every
`verify()` sample call) goes through -- built a fresh `Vec<Val>` from
`args` on every single call, an unconditional heap allocation on what's
meant to be the JIT's fast path. Fixed with a small stack-allocated
buffer (`Val` is `Copy`, confirmed from wasmtime's own source) for the
common case: `STACK_ARGS = 8` covers every combinator arity this
project's own demo/bench/test corpus reaches, with a `Vec` fallback kept
for the rare case above that bound, so correctness at any arity is
unaffected.

Verified directly, not just by inspection: added
`invoke_agrees_with_the_interpreter_past_the_stack_buffer_threshold`
(a 10-ary summing term, deliberately past `STACK_ARGS`), asserting both
that the compiled result agrees with the interpreter *and* that the term
actually went through the compiled path (`jit.stats.compiled == 1`) --
the second assertion turned out to be load-bearing: a deliberately
truncated heap-fallback buffer (dropping the last two arguments) didn't
produce a wrong *value* here, since `verify()` itself calls `invoke` on
its own sample battery first and a corrupted fallback just makes that
verification disagree, safely blacklisting the term to the interpreter
(exactly the project's own "sound, not complete" architecture doing its
job) -- confirmed by watching `jit.stats.compiled` read back `0` instead
of the expected `1` under the deliberately broken version, then
restoring the fix and confirming `1` again.

