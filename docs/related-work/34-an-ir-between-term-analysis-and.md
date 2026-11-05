## 34. An IR between term analysis and WAT

§33 made the *classification* shared; this separates the *meaning* from the
*representation*, the precondition for checking meaning per compilation.
`compile.rs` now builds a closure-converted, representation-neutral IR
(`ir.rs`): which function, which local, which environment slot, which kind of
call. `lower_wat.rs` turns it into WAT, one template per node. Closure packing,
the bump allocator, scratch locals, the wrapping-division sequence and the
curried stage chains all live in the templates. Design, alternatives and
research: `docs/superpowers/specs/2026-09-23-jit-ir-design.md`.

**Why this level.** The mid-level IR of every system surveyed (GHC STG,
CakeML BVL, CertiCoq-Wasm's λANF input, Lean IR, Flambda 2, Hoot's CPS after
closure conversion, MLton SSA) sits at this level or above it, and each makes
the layout concrete in exactly one pass downstream. The lowest levels (GHC
Cmm, Gibbon L4) are the least checked. An IR with explicit memory operations
would have made the step-2 decompiler a symbolic evaluator of memory traffic.
An annotated term would have left closure conversion, where past bugs were,
entirely trusted. Flat closures were kept rather than Lean-style lambda
lifting. Hash-exact decompilation needs to know which leading arguments are
captures either way, so lifting would not have made the decompiler simpler;
and keeping the representation let step 1 require byte-identical WAT.

**How it was checked.** For the whole transition, `try_compile` ran both
the old direct emitter and build → check → lower, and asserted identical
WAT, `needs_hp_reset` and `arity` on every call. That covered every unit
test, all four fuzzers in release, the demo and both bench suites. Golden
snapshots (`tests/golden/`) were then recorded, and the old path deleted.
Verify-teeth: swapping `If` branches in the builder, or skipping
`local_index`, made the gate panic across the suite (15 and 16 failing
`compile::tests`). After the deletion, a one-byte template change
(`i64.const 32` → `33` in `MakeClosure`'s packing) failed the golden test
for all 7 of the 20 terms that build a closure value, and 3 closure tests.
Five `rejects_*` terms in the same corpus pin rejections, recorded as
`REJECTED`.

**Field parity.** So that the step-2 decompile check cannot be vacuous,
every IR field is in one of three classes:
1. read by both the lowering and the decompiler (`Lit`, `Read`, ops, every
   `args`/`env`/`root_env`, `f`, `wrapper`, `Pap.root`, `callee`, `arity`);
2. read only by the decompiler and unable to change runtime meaning
   (`is_rec`; `SelfCall.tail`, whose two lowerings are both correct);
3. read only by the lowering, a representation choice that `ir::check`
   validates (`dispatch`, `env_len`, `Pap.supplied`).

`ir::check` is a complete precondition for lowering: besides ranges, arities
and environment lengths, it requires every lambda and every recursive
function to have `arity >= 1` and every `CallUnknown` to have arguments, so
nothing it admits makes `lower` panic, loop or disagree with the decompiler.
A check failure is a builder bug; release builds reject the term and count
it in `compile::builder_bugs(BuilderBug::IllFormed)`, which `compile_fuzz` asserts is 0.

**What changed besides the split.** The discovery pass is gone. The dispatch
mode is a field of the module, known before any WAT is written. Renames:
`compile_node` → `build_node` (term shape) plus `lower_wat` templates (emitted
code); `compile_var_read` → `build_read`; `emit_dynamic_apply` →
`Lowering::dynamic_apply`; `push_pap_env` → `Lowering::pap_env`. Cold-compile
timings (`jit_cold_compile_and_verify` medians, the step's base `deb8ec7 (unpublished)` →
after, median of three interleaved runs of each build) are fib_30 227 → 227
ms, gcd 78.9 → 73.5 ms, capturing_closure_loop 67.8 → 65.6 ms,
partial_application_loop 67.2 → 64.6 ms,
closure_typed_loop_carried_parameter_loop 18.4 → 20.1 ms and
inconsistent_arity_loop_carried_parameter_loop 4.9 → 5.6 ms, all within
this machine's run-to-run spread of up to about 15% (three longer
interleaved reruns of the last two gave 16.7 → 15.9 ms and 4.0 → 4.1 ms),
so the change is not measurable either way.

**Not yet, at the time.** Nothing checked the IR against the source yet.
That was step 2 (a decompiler that rebuilds the term and compares content
hashes), then step 3 (a differential test for each template) -- both now
done; see §35.

