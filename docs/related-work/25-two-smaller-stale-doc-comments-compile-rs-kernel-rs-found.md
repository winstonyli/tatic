## 25. Two smaller stale doc comments (compile.rs, kernel.rs) -- found and fixed

Two more small doc-staleness items, each caught by grepping for a claim
the code no longer supports:

`compile.rs`'s `emit_curried_stages` still said "Not yet reachable from
`try_compile`'s own codegen" -- true when originally written (Phase 1 of
the curried-dispatch rewrite, built and tested in isolation before being
wired in), stale since Phase 2 actually wired it into `try_compile`'s own
stage-generation loop. Fixed to describe the real, current gating: called
once per combinator that's both in a fragment needing generic dispatch
(`Combinators::needs_generic_dispatch`) *and* actually reached as a bare
value (`Combinators::used_as_bare_value`, section 21 above).

`kernel.rs`'s `infer_sigma` doc still said "nothing in this crate
constructs a `Sigma`/`Pair`/`SigRec` term yet (this primitive was just
added)" -- true when `Sigma` was first added as a postulate-free kernel
primitive, stale since the crate's own test module now builds and checks
several (`sigma`/`pair`/`sigrec` calls throughout `kernel.rs`'s tests).
Fixed to state the actual, permanent reason for the `#[inline(never)]`
extraction (keeping these arms' own locals off `infer`'s hot frame on
every *other* expression shape) without the now-false "nothing
constructs one yet" framing.

Comment-only changes; verified the same way as section 24: full build/
clippy/doc/test/fuzz/demo suite green, `cargo doc` showing no new
warnings.

