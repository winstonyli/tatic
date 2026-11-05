## 17. A structural verification-coverage gap in `sample_arg_vectors` for arity >= 3 -- found and fixed

`jit.rs`'s `sample_arg_vectors` (the sample battery both `verify()` and
every per-sample `kernel_verify` fallback use to gate trust in a
compiled term) had a higher-arity (`_`, arity >= 3) branch whose own
comment promised two diagonals -- "the all-equal and all-small-distinct
diagonals" -- but only ever generated the first: `vec![a; arity]` for
each of a few sampled `a`s, every position the *same* value. No code
path produced a sample where different positions held different values.

The consequence is structural, not incidental: a compiled-code bug that
swaps or misindexes two argument positions (a codegen slot mixup between
parameters 1 and 2, say) is *invisible* to an all-equal sample -- swapping
two equal values changes nothing observable. Every arity->=3 term's
`verify()` call, and every per-sample kernel proof attempt built on the
same battery, was checking a battery that could never have caught that
bug class, for as long as this project has had a JIT. Confirmed nothing
in the fuzz suite exercised arity->=3 at all either (`compile_fuzz.rs`'s
generators all cap arity at 1 or 2), so this wasn't compensated for
elsewhere.

Fixed by actually generating the promised second diagonal: several
rotations of `SAMPLE_ARGS`, each assigning a different sampled value to
each argument position (`(0..arity).map(|i| SAMPLE_ARGS[(i + offset) %
SAMPLE_ARGS.len()])` for a handful of `offset`s). No bug was found by
adding this -- the compiler itself checked out clean -- but the coverage
gap itself was real, and closing it is what makes that a confirmed
absence of bugs rather than an unchecked one.
`jit::tests::sample_arg_vectors_for_higher_arity_includes_a_genuinely_distinct_sample`
is the permanent regression guard; reverting the fix makes it fail
immediately, confirming every sample it generates really was constant
across positions before.

