---
status: done
---

# JIT IR: design

Status: steps 1-4 implemented (RELATED_WORK.md §34-§36).

## Goal

Put an intermediate representation between `compile_node` and WAT, so that:

1. the backend can change later (Wasm GC, Cranelift, `return_call`) without
   touching term analysis, and
2. a per-compilation **translation validator** can decompile the IR back to a
   term and require the *same content hash* as the source. That check reaches
   the "meaning drift" `compile::classify` cannot (`RELATED_WORK.md` §28
   correction, §33).

The IR->WAT lowering stays trusted, but as small context-free templates that
can be tested one at a time.

## Staging

| Step | Deliverable | Gate |
|---|---|---|
| 1 | IR types, well-formedness checker, IR builder (term->IR), WAT lowering (IR->WAT); old path deleted | WAT **byte-identical** to today's for every test, bench and fuzz term, including identical rejections |
| 2 | Decompiler + gate in `jit.rs` | `ir_validation_failures == 0` across the suite; mutation tests all rejected; verify-teeth on the builder |
| 3 | Differential test for each lowering template, at edge values | Every template agrees with `eval.rs` |
| 4 | Lambda lifting of directly called combinators, as a lowering choice | Differential tests agree; golden WAT changes only for direct-only capturing combinators |

This spec covers all four steps; the step-1 plan implements only step 1.

## Decisions

### IR level: closure-converted, representation-neutral

We compared three levels:
- **(A)** closure-converted, with abstract slot, local and table indices;
- **(B)** explicit memory operations and packing;
- **(C)** an annotated term with no closure conversion.

We chose **A**. Every surveyed system validates or checks at this level or
above it, and makes the layout concrete in exactly one place downstream:
- GHC STG, CakeML BVL, CertiCoq-Wasm's λANF input, Lean IR, Flambda 2, Hoot's
  first-order CPS and MLton SSA all sit at A.
- The lowest levels (GHC Cmm, Gibbon L4, GRIN's final passes) are the least
  checked.

B would make the decompiler a symbolic evaluator of memory traffic, and would
tie the IR to packed-i64 linear memory. C would leave closure conversion, where
past bugs were found, entirely trusted.

### Closure model: flat closures (not lambda lifting)

- **Why flat closures now.** They keep today's representation, so step 1 can
  require byte-identical WAT, and performance is unchanged by construction.
- **Why lambda lifting isn't cheaper to validate.** Lean-style lifting
  (a closure is a partial application of a lifted function) looks simpler to
  decompile. But `λx. y+x` capturing `y` and `(λy x. y+x) y` have different
  hashes. So a lifted IR must still record how many of the leading arguments
  are captures, which is the same information in a different place.
- **Later.** Lambda lifting remains a possible **IR->IR pass**, validated by
  the same decompiler. Its performance trade-off would be measured then:
  captures could be passed as arguments to known calls, but every indirect
  call would first have to unpack a partial-application object. Step 4 took
  the cheap half as a lowering choice instead (see there).

### Call kinds are explicit in the IR

Every surveyed system separates a known saturated call, an unknown call, and
building a partial application (Lean `fap`/`ap`/`pap`, Flambda 2 `call_kind`,
OCaml `Udirect_apply`/`Ugeneric_apply`, Hoot `$callk`/`$call`). Every one of
them rewrites over-application into a saturated call followed by an unknown
call. The curried stage chain is our version of a generic-apply helper
(`stg_ap_*`, `caml_curryN`), so it belongs to the lowering, not the IR.

## The IR (`src/ir.rs`)

```rust
pub(crate) struct Module {
    pub entry: Func,                    // $f -- env_len 0
    pub combinators: Vec<Combinator>,   // position = table index = $c{idx}
    pub dispatch: Dispatch,             // Fast | Curried, one choice for the whole module
}
pub(crate) enum Dispatch { Fast, Curried }
pub(crate) enum Combinator {
    Lifted(Func),                          // a lambda literal, closure-converted
    Pap { root: usize, supplied: usize },  // partial-application wrapper; its body is a lowering template
}
pub(crate) struct Func {
    pub arity: usize,
    pub is_rec: bool,
    pub env_len: usize,
    pub body: Node,
}
pub(crate) enum Read { Param(u32), Env(u32) }   // Wasm local $p{li} / environment slot
pub(crate) enum Node {
    Lit(i64),
    Read(Read),
    Arith(PrimOp, Box<Node>, Box<Node>),
    If { cmp: PrimOp, a: Box<Node>, b: Box<Node>, then: Box<Node>, els: Box<Node> },
    SelfCall { args: Vec<Node>, tail: bool },
    CallKnown { f: usize, env: Vec<Read>, args: Vec<Node> },   // saturated only
    CallUnknown { callee: Box<Node>, args: Vec<Node> },
    MakeClosure { f: usize, env: Vec<Read> },
    MakePap { wrapper: usize, root_env: Vec<Read>, args: Vec<Node> },
}
```

- **A tree, not A-normal form.** Wasm is a stack machine and the tree already
  fixes evaluation order. A-normal form would introduce locals and break the
  byte-identical gate.
- **Over-application is not a node.** It is
  `CallUnknown { callee: CallKnown{..}, args: extra }`.
- **No capture list in the IR.** A body's `Env(k)` is resolved by the
  decompiler from entry k of the `env` at the site that builds the closure.
  The layout therefore exists only where it is used: the site that builds the
  environment and the load that reads it.

### Field parity

The main risk of translation validation is a vacuous check: the IR carries a
fact the templates ignore, so the right answer can sit there while the WAT is
wrong. Every field therefore belongs to one of three classes:

1. **Read by both the lowering and the decompiler.** `Lit`, `Read`, both op
   fields, every `args`/`env`/`root_env`, `f`, `wrapper`, `Pap.root`,
   `callee`, and `Func.arity` (the lowering's parameter list, the
   decompiler's `Abs`^arity).
2. **Read only by the decompiler, never able to change runtime meaning.**
   - `is_rec`. A wrong value can only cause a false rejection; a `SelfCall`
     without `is_rec` is rejected by well-formedness.
   - `SelfCall.tail`. It is read by the lowering (loop or `call`), but both
     choices are semantically correct. Well-formedness forbids `tail: true`
     outside tail position.
3. **Read only by the lowering; a representation choice checked for
   well-formedness.**
   - `dispatch`. `Fast` with inconsistent arities traps; it never gives a
     wrong value.
   - `env_len` and `Pap.supplied`. Each must equal the corresponding list
     length at every site that builds that function's closure or partial
     application.

### Well-formedness (checked before lowering; failure rejects the term)

- `Param(li)`: `li < arity`. `Env(k)`: `k < env_len` of the enclosing function.
- `CallKnown.f` and `MakeClosure.f` are `Lifted`. For `CallKnown`, its arity
  equals `args.len()`. Its `env_len` equals `env.len()`.
- `MakePap.wrapper` is a `Pap` whose `root` is `Lifted`.
  `0 < supplied < root.arity`, `supplied == args.len()`, and
  `root.env_len == root_env.len()`.
- `If.cmp` is a comparison and `Arith`'s op is not (`compile::is_comparison`).
- `SelfCall` appears only in a function with `is_rec`, with
  `args.len() == arity`. `tail: true` appears only in tail position.
- `entry.env_len == 0`.
- Every `Lifted` function has `arity >= 1` (the curried dispatch has no
  stage 0 for a nullary combinator), and `is_rec` implies `arity >= 1` (a
  nullary tail self-call would lower to a bare `br $L`, an infinite loop).
- `CallUnknown.args` is non-empty (with none, the lowering still emits a call
  while the decompiler would read the bare callee).
- `dispatch == Fast` implies every `CallUnknown` whose callee is the same
  `Read` inside one function has the same `args.len()`.
- The combinator reference graph is acyclic: no `Lifted` combinator's body
  reaches its own index through `CallKnown.f` / `MakeClosure.f` /
  `MakePap.wrapper -> Pap.root`. Recursion is expressed only by `SelfCall`
  (a bound variable, not a fresh closure), so a lambda literal's own term
  can never contain itself and the builder can never produce a cycle here.
  Needed because `decompile`'s `closure` only memoises a combinator's hash
  after rebuilding its body, so a cyclic reference would make it recurse
  forever.

## Step 1: building the IR (`compile.rs`)

- **`compile_node` becomes `build_node(ctx, reg, h, tail) -> Option<Node>`.**
  It keeps the same `match classify(..)` and the same rejections (`OtherCall`,
  an unknown variable, `register` failing, a non-comparison condition).
- **`compile_var_read` becomes `build_read`,** which returns
  `Param(local_index(v))` or `Env(slot)`. `free_vars` and the capture list stay
  inside the builder's registry.
- **The `Combinators` registry keeps** index, arities, kind, captures and
  pending. It drops `emitting`, `stage0_index`, `call_indirect_arities` and
  `used_as_bare_value`. `needs_generic_dispatch` becomes `Module.dispatch`.
- **One walk replaces the discovery pass.** It builds `$f`'s body, then pops
  pending combinators in today's LIFO order, so registration order and every
  table index are unchanged.
- **`try_compile(store, h) -> Option<CompiledFragment>` keeps its signature:**
  build, then check well-formedness, then lower. A check failure (a builder
  bug) panics in debug builds; in release it rejects the term and bumps
  `compile::ir_check_failures()`, which the release-mode `compile_fuzz`
  asserts is 0.

## Step 1: lowering (`src/lower_wat.rs`)

- **One template per node,** moved verbatim from today's `compile_node` arms.
  Indentation comes from tree depth, adding 2 inside `If` branches.
- **`CallUnknown` in `Fast` mode:** lower `callee`, `i64.const 32`,
  `i64.shr_u`, `i32.wrap_i64`, the args, lower `callee` again, `i32.wrap_i64`,
  `call_indirect (type $ty{n})`. This reproduces both today's variable-call
  arm and today's over-application fast path, which computes its saturated
  call twice.
- **`CallUnknown` in `Curried` mode:** lower `callee`, then
  `emit_dynamic_apply(args)`.
- **Moved unchanged:** `emit_allocator`, `emit_wrapping_div`,
  `emit_pap_wrapper`, `emit_curried_stages`, `arith_instr`, `cmp_instr`, and
  `push_closure_env`/`push_pap_env` (which now take `&[Read]`).
- **Derived from the IR, not recorded by the builder:**
  - `call_indirect` arities: `args.len()` in `Fast` mode, `1` in `Curried`.
  - Which combinators are used as bare values: every `MakeClosure.f` and
    `MakePap.wrapper`.
  - `needs_alloc`: any `env_len > 0`, any `Pap`, or stages that allocate.
  - `stage0_index`.
- **Module assembly** (types, allocator, exports, table, elem, combinators,
  stages, `$f`) moves from the tail of `try_compile` unchanged.

### Byte-identical gate and retiring the old path

1. Add the new path alongside the old one.
2. A test asserts identical `Option<wat>` from both paths across every term
   built in `compile::tests` and `jit::tests`, every `benches/common.rs`
   builder, and a fixed-seed batch of the compile fuzzer's generated terms.
   Terms both paths reject count too.
3. Delete the old path in a separate commit, once full validation is green.
4. The comparison test becomes WAT golden snapshots under `tests/`, so any
   later change to the lowering shows up as a deliberate diff.

## Step 2: the decompiler (implemented in `src/decompile.rs`)

`decompile::decompile(&Module, &mut TermStore) -> Option<Hash>`; the gate
passes a scratch `TermStore`.
Content hashes (blake3) don't depend on the store, so the gate compares hashes
without the decompiler ever reading the source term.

| IR | Term |
|---|---|
| A function (`arity`, `is_rec`, `body`) built with environment `E` | `Abs`^arity(body), wrapped in `Rec` if `is_rec` |
| `Param(li)` | `Var(arity-1-li)`, written independently of `local_index` |
| `Env(k)` | `Var(E[k] + arity + is_rec)`, where `E[k]` is the outer `Var` that `env[k]` at the building site decompiles to |
| `Lit` / `Arith(op,a,b)` / `If{cmp,a,b,t,e}` | `Lit` / `Prim(op,a,b)` / `If(Prim(cmp,a,b), t, e)` |
| `SelfCall{args}` | `Var(arity)` applied to `args` |
| `CallKnown{f,env,args}` | closure(f, env) applied to `args` |
| `CallUnknown{callee,args}` | `callee` applied to `args` |
| `MakeClosure{f,env}` | closure(f, env) |
| `MakePap{w,root_env,args}` | closure(`w`'s root, root_env) applied to `args` |

- **Entry and memoisation.** The entry function is decompiled with an empty
  environment. Each closure is memoised on (f, env).
- **Independence.** The decompiler shares only `Term`/`TermStore` with the
  compiler: no `classify`, `peel`, `local_index` or `free_vars`.
- **Gate (`jit.rs`).** Build, check well-formedness, decompile and compare with
  `h`, then lower. A mismatch interprets the term instead and increments a new
  `Stats::ir_validation_failures`. Tests assert that stat is 0. A firing on a
  correct program is a false alarm, and a bug to fix.
- **Mutation tests.** Take a correct built IR and change one thing: swap two
  arguments, shift a `Param` by one, swap env entries, swap `If` branches,
  change `f`/`wrapper`, or change an `Arith` op. Each change must be rejected.
- **Verify-teeth.** Inject the same kinds of bugs into the builder itself.
- **Out of reach:** template bugs (packing, allocation, scratch-local reuse,
  stage chains, the div sequence) and wasmtime. Step 3 and the existing sample
  battery cover those.

**Deviations.** The decompiler lives in its own file (`src/decompile.rs`),
not inline in `ir.rs` as the table header above suggests, and it takes the
target `TermStore` as a parameter (rather than always allocating its own)
so step 3 can evaluate the term it builds. The failure count is a
process-wide counter (`compile::ir_validation_failures`), the same shape as
the pre-existing `ir_check_failures`, rather than a `jit::Stats` field --
every caller of `try_compile`, not only the JIT, is covered that way.

## Step 3: per-template differential tests

For each template, run a one-node IR module through the lowering and wasmtime.
Compare against `eval.rs` on edge values: `i64::MIN`, `-1`, `0`, overflow,
`MIN / -1`, and division by zero. Stage chains are tested at arities 1 to 4,
with captures and without. The trusted gap is then the templates' behaviour on
inputs they weren't sampled at.

## Step 4: lambda lifting of directly called combinators (implemented)

A `CallKnown` used to allocate its callee's environment in linear memory on
every call (`push_closure_env`), even when nothing else could ever see that
environment. A capturing combinator that nothing reaches through the table
-- never packed by `MakeClosure`, never a `Pap`'s root -- now takes its
captures as leading `i64` parameters `$e0 ..` (`lower_wat::direct_only`).
`Read::Env(k)` in its body is `local.get $e{k}`, a call to it pushes the
captured values, and a non-tail self-call forwards them.

- **Why a lowering choice, not an IR pass.** It is derived from the module,
  like the `call_indirect` arities (field-parity class 3). The IR, `check`,
  the decompiler and the hash gate are unchanged, so validation is too; the
  step-3 differential tests cover the new convention.
- **Why only direct-only combinators.** Every combinator reachable through the
  table keeps the uniform `$env` convention, so no indirect call pays for
  this. The alternatives were a dual entry for every capturing combinator
  (a direct function plus a table stub, costing each indirect call one
  extra Wasm call) and a hybrid giving the dual entry only to combinators
  both called directly and escaping. The hybrid stays open (below).
- **Measured before choosing.** A spike timed hand-lifted and hand-specialised
  equivalents of the closure benches (20,000 iterations, warm JIT, best of
  15 on a shared machine): lifting the capturing loop 3.1-3.4x;
  specialising `caller (add acc) n` to `add acc n` 7.0-7.6x; substituting
  the loop-invariant closure parameter 1.2-1.6x. The last two change the
  term, so the hash gate cannot validate them (future work).

## Files and docs

- New `src/ir.rs` (types, well-formedness, later the decompiler) and
  `src/lower_wat.rs` (templates, module assembly). `compile.rs` shrinks to
  `classify`, the registry, `free_vars`, closure-arity inference and the
  builder.
- The closure-representation sections of `compile.rs`'s module docs move to
  `lower_wat.rs`.
- Two new rows in the README file table.
- `RELATED_WORK.md` §34: the level decision, the research summary with sources
  (below), and the field-parity classes.

## Future work (not in scope)

- Lambda lifting as an IR->IR pass, validated by the same decompiler.
- The hybrid step-4 convention: a dual entry (direct function plus table
  stub) for a capturing combinator that is both called directly and escapes.
- Closure specialisation (inlining a known closure argument into a
  non-recursive callee; substituting a loop-invariant closure parameter).
  These change the term, so they need a validator beyond hash equality.
  V3, inlining a known closure argument (βv, certificate-checked by an
  independent replay), is implemented -- see
  `docs/superpowers/specs/2026-09-24-closure-specialisation-design.md` and
  `RELATED_WORK.md` §37. V1, substituting a loop-invariant closure
  parameter, is still open.
- An inlined bump-allocation fast path. A throwaway probe (2026-09-24)
  hand-edited `tests/golden/partial_application_loop.wat` and timed it at
  20k iterations, warm, best of 15, on a shared machine, across four runs.
  - Removing the allocation entirely (the env at a fixed slot, an upper
    bound) gave 1.42-1.53x.
  - Inlining the bump with no bounds check gave 1.26-1.41x.
  - Inlining the bump but keeping the `memory.size` check, with `call
    $alloc` only on overflow, gave 1.21-1.27x. This is the version that
    could ship.
  - Cranelift's `compiler_inlining` gave nothing (0.93-1.03x).
  - `memory.grow` is not the warm cost: memory stays grown across calls on
    one instance.

  So allocation is about a third of this loop's time. The pap-specialised
  spike's 7x comes mostly from removing the `call_indirect` and wrapper
  chain, so closure specialisation is the larger win. The inlined fast path
  is a cheap, independent lowering change that the hash gate already covers
  (class 3).
- A Wasm GC backend: flat closures map to a struct with a funcref and fields,
  as in Hoot and wasm_of_ocaml.
- `return_call` in place of the tail-call loop, which would make `tail` a pure
  lowering choice.

## Sources

- GHC: Marlow & Peyton Jones, *Making a fast curry* (eval/apply): https://simonmar.github.io/bib/papers/eval-apply.pdf; STG syntax: https://github.com/ghc/ghc/blob/master/compiler/GHC/Stg/Syntax.hs
- GRIN: Podlovics et al. 2020: https://cyber.bibl.u-szeged.hu/index.php/actcybern/article/download/4101/4018
- Gibbon pipeline: https://github.com/iu-parfunc/gibbon/blob/main/gibbon-compiler/src/Gibbon/Compiler.hs
- CompCert validation: Rideau & Leroy, https://xavierleroy.org/publi/validation-regalloc.pdf; Tristan & Leroy LCM, https://jtristan.github.io/papers/pldi09.pdf
- CakeML backend: https://kar.kent.ac.uk/71304/1/paper.pdf
- CertiCoq-Wasm (CPP'25): https://womeier.de/files/certicoqwasm-cpp25-paper.pdf
- Œuf (denote the AST back, check with `reflexivity`): https://homes.cs.washington.edu/~djg/papers/oeuf2018.pdf
- Necula, translation validation: https://people.eecs.berkeley.edu/~necula/Papers/tv_pldi00.pdf
- Myreen, decompilation into logic: https://www.cl.cam.ac.uk/~mom22/extensible-compilation.pdf
- Lean 4 IR (`fap`/`pap`/`ap`): https://arxiv.org/abs/1908.05647
- Flambda 2 call kinds: https://github.com/oxcaml/oxcaml/blob/main/middle_end/flambda2/terms/call_kind.mli
- wasm_of_ocaml closures: https://github.com/ocsigen/js_of_ocaml/blob/master/compiler/lib-wasm/gc_target.ml
- Guile CPS / Hoot: https://www.gnu.org/software/guile/manual/html_node/CPS-in-Guile.html, https://wingolog.org/archives/2024/05/27/cps-in-hoot
- Crocus / VeriISLE (verified lowering rules; not re-checked): https://dl.acm.org/doi/10.1145/3617232.3624862
