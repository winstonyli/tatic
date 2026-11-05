## 21. `try_compile` generated a curried stage chain for every registered combinator, whether or not anything ever dispatched through it -- found and pruned

Once a fragment needed generic dispatch at all (`Combinators::needs_generic_dispatch`
-- some closure-typed variable is called with genuinely different arities
at different call sites), `try_compile` generated `emit_curried_stages`'s
full curried stage chain (one Wasm function per remaining argument, plus
a densely-allocated funcref table slot for each) for *every* registered
combinator in the fragment, unconditionally. But a `stage_0` index is
only ever packed into an `i64` value at two specific sites in
`compile_node` -- a literal lambda used as a plain value, and an
under-applied root's own PAP-wrapper creation -- so a combinator only
ever reached through a direct, exactly-saturated call site (`call
$c{idx}` straight from another combinator's own body, never packed as a
value at all) had a stage chain generated for it that nothing could ever
call through: dead Wasm functions and dead table slots, purely from
generic dispatch being on anywhere in the fragment rather than from this
specific combinator ever needing it.

Fixed by tracking, during the discovery pass, exactly which combinator
(or PAP wrapper) indices are ever reached as a bare value --
`Combinators::used_as_bare_value`, a `HashSet<usize>` populated
unconditionally (not gated on `emitting`/`needs_generic_dispatch`) at the
same two sites that read `stage0_index`. Since discovery already walks
every reachable combinator's own body once (the existing fixpoint over
`combinators.pending`), and neither of those two sites' own control flow
differs between the discovery and emit passes (both branches of every
`emitting`-gated choice compile the identical set of sub-terms, just with
different Wasm sequencing -- confirmed by reading through the surrounding
`Term::Var(i)`-callee and over-application dispatch code, neither of
which itself registers or creates a bare value), the set is already
complete by the time discovery finishes, and the emit pass can only ever
re-confirm membership, never discover a new entry. `try_compile`'s stage-
generation loop, the funcref-table-length computation, and the `elem`
section's own listing all now skip any index the set doesn't contain,
freeing up `stage_needs_alloc` to narrow the same way (a fragment that
needs generic dispatch for *calling* through a variable, but never itself
creates a bare value locally, now needs no allocator-driven stage
machinery at all).
`compile::tests::a_combinator_never_reached_as_a_bare_value_gets_no_stage_chain_even_when_the_fragment_needs_generic_dispatch`
covers it directly: a fragment with one inconsistent-arity parameter (so
`needs_generic_dispatch` is true) alongside a second, unrelated literal
combinator that's only ever called directly and saturated -- asserts the
first still gets a stage chain (dispatch isn't broken) while the second's
`$c{idx}` fast-entry function has no matching `$s{idx}_*` anywhere in the
output. Reverting the pruning filter back to unconditional makes this
assertion fail, confirming it's exercising the real mechanism.

