## 46. G2 in depth: where the type notions have to agree, and how other systems get one source

§44's G2 said the notions of type "must agree". This section says
exactly where, who checks each agreement today, and what other compilers
and checkers do instead.

**The agreements, one by one.**

| Pair | Must agree on | Checked by |
|---|---|---|
| `typing.rs` ↔ compiled code | `Int` vs closure at every value | `typing.rs`, which is independent (§38). Arity isn't covered. |
| `ArityUse` ↔ the closures that reach a variable | arity, under `Dispatch::Fast` | Nothing statically. `ir::check` checks that each variable is called at one arity, and its doc (`ir.rs`) says nothing proves the *values* reaching it have that arity. The proof gate covers it (§40). |
| `ArityUse` ↔ `proof.rs`'s parameter types | arity of each closure parameter | Shared code (`proof.rs` reads `ArityUse`), plus `return_type_of`, kept in step by hand. Not checked. |
| `proof.rs`'s `Denoted` ↔ the kernel | the type of each denoted `Expr` | The kernel. But `Clo_k` is curried (§11), so it can't tell `\x. \y. e` from `\x. (\y. e)` (§40, corrected). |
| The provers' parameter types ↔ the JIT's entry point | every parameter is an `Int` | `calls_a_parameter` (§42), a syntactic stand-in. |

`docs/types.md` already wrote the third and fourth rows down as one judgment,
and its §6.2 records a version of the fourth row's gap. It was closed by
opaque per-arity `Clo_k` postulates, then partly reopened when §11
replaced them with the curried arrow to save primitives.

**How others do it.**

- **A typed IR, re-checked between passes.** GHC's Core is typed, and
  Core Lint re-checks it after each pass when asked. Arity is a second
  notion there too: an `Id`'s arity lives in its `IdInfo`, apart from
  its type, and a lint invariant (GHC #10181) requires the arity not to
  exceed the type's. So GHC has tatic's "two notions that must agree",
  and handles it by checking one against the other. Lint is a debugging
  aid, not part of the trusted base.
- **An IR checker that knows calling conventions.** Lean 4's IR separates
  `fap`, `pap` and `ap` (§43), and `Lean.Compiler.IR.Checker` rejects a
  `fap` with the wrong number of arguments and a `pap` that supplies too
  many. That is `ir::check`'s `CallKnown` rule. Lean's `ap` then goes
  through `lean_apply_n`, which checks at runtime (§43, 1a).
- **A second checker on a lower IR.** rustc validates MIR at least once,
  and after every pass under `-Zvalidate-mir`. Borrow checking re-types
  MIR independently of the type checker that ran on HIR.
- **Type-preserving compilation.** TIL (Tarditi et al., PLDI 1996) and
  FLINT (Shao, ICFP 1998) keep types through every IR down to code
  generation, and TIL introduced the certifying compiler that TAL and
  proof-carrying code grew from. The types are the single source, and
  each pass must produce well-typed output.
- **One source by proof.** CakeML's type inferencer is proved sound and
  complete against a declarative type system (Tan, Owens and Kumar,
  IFL 2015), and type soundness is proved for that system. There is then
  nothing to keep in agreement: every consumer relies on the one
  declarative system.
- **The de Bruijn criterion.** A proof assistant is trusted if its proof
  objects can be checked by a small independent program (Barendregt's
  name for de Bruijn's design). The elaborator can be as large as it
  likes. Lean4Lean is such an external checker for Lean 4. §44's B2 is
  this criterion applied to types.
- **A typed target.** WebAssembly's typed function references add
  `call_ref`, which is statically typed, so the validator rejects a call
  at the wrong function type. `call_indirect`, which tatic uses, checks
  the type at runtime and traps on a mismatch (§40). wasmtime implements
  the proposal (`Config::wasm_function_references`; GC and exceptions are
  on by default from wasmtime 47, and tatic is on 42).

**Options for tatic.** §44 listed B1–B4. The survey adds two.

- **B5: a typed IR and a stronger `ir::check`.** Give each `Func`'s
  parameters and environment slots a type (`Int` or `Clo_k`, nested), and
  have `ir::check` check every node against them: `Arith` operands are
  `Int`, a `CallUnknown` under `Fast` calls a `Clo_k` with `k` arguments,
  a `MakeClosure` has the arity its type claims, and the entry point's
  parameters are `Int`. This is B2 at the IR, and it is Lean's checker
  extended from known calls to closures.
  - Pros: the IR is where every consumer meets. The builder emits it,
    `lower_wat.rs` reads it, and `decompile.rs` proves it means the
    term. Translation validation plus a type-checked IR means the
    compiled code is the term and can't go wrong, whatever
    `ArityUse` says, and §40's hole becomes a check failure independent
    of the proof gate. The checker is local and linear, with no
    unification. It would replace `calls_a_parameter` (the entry
    point's parameters are `Int` by type) and the Int-vs-closure part of
    the typing gate for compiled code.
  - Cons: the builder has to produce the types, which needs arity-aware
    inference (A1). `ArityUse` only knows about called variables, not
    which environment slots hold `Int`s. So a second, untrusted inference
    joins the code, the thing G2 counts against, though now it is checked
    rather than trusted. `ir::check` is in the same crate as the builder,
    so its independence would need the same `independence` test
    `typing.rs` has. The provers don't read the IR, so rows 3 and 4 of
    the table stay as they are.
- **B6: a typed Wasm target.** Lower to `call_ref` on typed function
  references, with `Int`s as `i64` and closures as typed references, so
  wasmtime's validator checks what B5's checker does.
  - Pros: the checker is external and already trusted, and was written
    by others to a public spec. That is as independent as a checker gets.
  - Cons: it replaces the uniform `i64` representation, the table and
    `call_indirect`, the linear-memory environments and the bump
    allocator (§9's design). It needs the same annotations as B5 to emit
    the types. It needs the GC proposal or a typed table, and wasmtime's
    GC is newer than the rest of the engine. It is the largest change
    here.

**How the options compare.**

| Option | Rows it closes | Trusted code | Size |
|---|---|---|---|
| B1: agreement tests | none (tests them) | unchanged | small |
| B2: annotated term + checker | 1, 2, 5, and 3 if the provers read the annotations | a small checker | large |
| B3: share `typing.rs` | 1, 2 | loses independence | small |
| B4: arity-exact kernel types | 4 | kernel postulates return | medium |
| B5: typed IR check | 1, 2, 5 for compiled code | the IR checker | medium |
| B6: typed Wasm | 1, 2, 5 for compiled code | wasmtime's validator | large |

**Recommendation.** Nothing in the corpus needs any of these yet. The
proof gate and `calls_a_parameter` keep out every term that would go
wrong (§41's fuzz). If the proof gate is ever relaxed:

1. **B5.** It closes the rows that matter for installed code, at the one
   place all of the compiler's consumers share, with a checker in the
   same style as `ir::check` and `spec_check`.
2. **B4**, if the provers are to stand on their own. Opaque per-arity
   `Clo_k` postulates come back, undoing §11's derivation, so the kernel
   sees the currying distinction the compiled code has. The cost is
   §11's saving in primitives.
3. **B6** as the end state, if typed references become the default in
   the wasmtime tatic uses.

