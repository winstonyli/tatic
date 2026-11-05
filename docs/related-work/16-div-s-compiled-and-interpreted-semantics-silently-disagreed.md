## 16. `Div`'s compiled and interpreted semantics silently disagreed at one input — found and fixed

`eval.rs`'s reference interpreter implements `PrimOp::Div` with
`wrapping_div`, the same non-trapping, silently-wraps-on-overflow
convention `Add`/`Sub`/`Mul` already use uniformly (`Mod` needs no such
treatment -- `wrapping_rem` and Wasm's `i64.rem_s` already agree at the
one input that matters here). `compile.rs`'s codegen, until now, emitted
a bare `i64.div_s` for `Div` -- and per the WebAssembly spec, `i64.div_s`
*traps* at exactly one input, `i64::MIN / -1` (the one case where the
mathematical quotient itself overflows `i64`), rather than wrapping.
Interpreted: `Ok(i64::MIN)`. Compiled: a trap, i.e. `Err`. A genuine,
if narrow, disagreement between the reference semantics and the
compiled fragment -- exactly the class of bug `jit.rs`'s own sample
verification exists to catch, and it does, whenever a term's structure
happens to divide by a sampled `-1` while the dividend is `i64::MIN`.
`SAMPLE_ARGS` (`jit.rs`) never includes `i64::MIN`, though, so a term
that instead *computes* `i64::MIN` at runtime (from small sampled
inputs, e.g. via repeated doubling or a shift) and then divides that by
`-1` would never trigger the mismatch during verification, and its
wrong compiled behavior on that one input would go undetected.

Fixed by special-casing that one combination in codegen
(`compile::emit_wrapping_div`) rather than changing `eval.rs`: two new
scratch locals (`$diva`/`$divb`, declared unconditionally in
`compile_function` alongside `$envtmp`/`$papenv`, the same "harmless if
unused" convention) hold the two operands, an `i32.and` of two `i64.eq`
checks decides whether this is the overflow case, and an `if (result
i64)` either yields `i64::MIN` directly or falls through to the ordinary
`i64.div_s`. `jit::tests::division_agrees_with_the_interpreter_at_i64_min_over_negative_one`
is the permanent regression guard -- reverting the fix makes it fail
immediately with a `Trap`, confirming it actually exercises the new
codegen path rather than passing vacuously.

