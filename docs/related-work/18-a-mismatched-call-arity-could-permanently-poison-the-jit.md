## 18. A mismatched call arity could permanently poison the JIT cache -- found and fixed

`JitEngine::compile_verify_and_apply` cached `CacheEntry::NotCompilable`
whenever a call's `args.len()` didn't match `h`'s own structural arity
(`frag.arity`, from `compile::try_compile`) -- conflating "is `h`
compilable at all" (a real property of `h` alone) with "did *this one
call* happen to pass the right number of arguments" (a property of the
call, not the term). Since `eval::apply_term` is fully generic over arg
count (applies one at a time, so under- or over-applying a term is a
legitimate, well-defined shape, not an error condition in itself), a
single mismatched call permanently defeated compilation for that term:
every later call, even one with the correct arity, hit the cached
`NotCompilable` entry and was routed to the interpreter forever, with
compilation never retried.

A second, related gap in the same area: `apply`'s own dispatch for an
*already-compiled* cache entry never checked the incoming call's arity
against the arity it was actually compiled for before calling
`call_compiled` -- which carries a `debug_assert_eq!(arity, args.len())`
of its own. A mismatched call against an already-compiled term would
therefore panic in a debug build, or in release, hand the compiled
function's fixed Wasm signature the wrong number of `Val`s, surfacing as
a spurious `Trap` rather than the correct, ordinary interpreter fallback
every other "can't serve this shape from the cache" path already gets.

Fixed by (1) no longer caching `NotCompilable` on an arity mismatch --
just interpreting that one call and leaving the cache untouched so a
later, correctly-sized call gets a fresh attempt, and (2) checking a
`Compiled` entry's own stored `arity` against the call's `args.len()`
in `apply` itself before ever reaching `call_compiled`, falling back to
`eval::apply_term` on a mismatch exactly like every other "not servable
from the cache" case already does.
`jit::tests::a_mismatched_arg_count_does_not_poison_the_cache_and_is_served_by_the_interpreter`
covers both: a mismatched call followed by a correctly-sized one (which
must still compile), and a mismatched call against an already-compiled
entry (which must fall back cleanly, not panic or trap) -- reverting
either half of the fix makes it fail immediately.

