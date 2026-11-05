## 29. The installation gate now requires a universal theorem -- option 1 from §28, taken

`compile_verify_and_apply` installed a compiled form on `verify()` alone.
`ProofStrength` (§28) made the weakness reportable; this makes it
actionable. Installation now requires **both** halves:

```rust
if proof != ProofStrength::Universal {
    self.cache.insert(h, CacheEntry::NoUniversalProof(proof));
    self.stats.declined_no_universal_proof += 1;
    self.stats.interpreted += 1;
    return eval::apply_term(terms, h, args);
}
```

The new `CacheEntry::NoUniversalProof(ProofStrength)` carries the
strength purely so `proof_strength` can still report what evidence did
exist; nothing reads it to make a decision. A declined term is served by
the interpreter from then on, exactly like `NotCompilable`, and shows up
in the new `Stats::declined_no_universal_proof`.

**Why both halves, and why neither is redundant.** The sample battery is
the only check in the system that touches the WAT wasmtime actually
runs. The kernel theorem is the only one that says anything about inputs
outside the battery -- but it is stated over `proof.rs`'s `denote`,
which models `compile_node` rather than reading its output (`proof.rs`
contains zero references to `wat`, `wasm` or `CompiledFragment`). So the
pair is strictly stronger than either alone, and still short of
end-to-end soundness. *(Later: the pair also said nothing about types, so
ill-typed code that goes wrong only off the samples got installed. §38
adds a third check.)* Anyone tempted to drop `verify()` now that a proof
is required should re-read that sentence: the proof does not cover
emitted code, and CompCert's own bug history (§28's prior-art notes) says
the printer is where wrong-code bugs actually live.

**The price.** This withdraws the JIT from the inconsistent-arity
curried-dispatch family -- the capability `compile.rs` went to real
trouble to support. Against this repo's corpus that costs nothing today:
the release demo still compiles all nine terms with
`declined_no_universal_proof: 0`, and exactly two tests changed behavior
(the arity-1 members of the `Samples` family measured in §28; the
arity-0 members classify `Universal` and still install). It is
nonetheless a capability regression, and the way to undo it is option 2
-- widen the universal fragment -- not relaxing the gate.

*(An earlier draft of this paragraph also claimed "every benchmark is
unaffected". That was asserted rather than measured. Running them
afterwards confirmed the gate changes no benchmark's behavior -- every
`jit_warm_cache_hit` bar still beats its `interpreter` bar by the same
orders of magnitude -- but also turned up a pre-existing crash in
`benches/execution.rs` that has nothing to do with the gate. See §30.)*

**A consequence worth flagging rather than fixing.** With the gate in
place, `kernel_verify`'s steps 4 and 5 can no longer change any
installation decision; they run purely to populate `proof_strength`.
`prove_closure_expr_instance` is expensive (it walks a full concrete
execution trace, exponential in trace size for the branching case,
bounded only by `DynBudget`), so a declined term now pays a real cost for
a diagnostic string. Left as-is deliberately -- it is once per term, and
the reporting is what makes the decline legible -- but skipping steps
4-5 unless someone asks for the diagnostic is an obvious cheap win if
that cost ever shows up in a profile.

Two tests renamed to match what they now assert
(`..._is_kernel_verified` -> `..._is_declined_for_want_of_a_universal_
proof`) and extended to pin `declined_no_universal_proof == 1`,
`compiled == 0`, `interpreted == 2`. Verify-teeth: relaxed the gate to
`if proof == ProofStrength::None` (letting `Samples` install again) and
confirmed exactly those two tests fail, then restored it. Full
validation green: `cargo build --all-targets`, `cargo test --lib --bins`
(191/191), all four fuzzers at release, and the release demo.

Note on `cargo clippy --all-targets`: on a 1.100-era nightly it now
reports four warnings from `cranelift-entity`'s `entity_impl!` macro
expanding the deprecated `std::u32::MAX` path at `term.rs:18`. Not
tatic's code, and deliberately not suppressed with an `#[allow]` that
would mask a future real deprecation in that file -- but "clippy clean"
is no longer a valid pass criterion on that toolchain. (Later fixed at
the root: `TermStore` was the crate's only user, and it needed no more
than a `Vec` and a hash-to-index map, so the dependency is gone and
clippy is clean again. Newer `cranelift-entity` releases, up to 0.135,
still expand the deprecated path.)

