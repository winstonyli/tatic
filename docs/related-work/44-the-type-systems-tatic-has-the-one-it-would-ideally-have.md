## 44. The type systems tatic has, the one it would ideally have, and ways between

§38 to §43 each patched one place where a type was assumed and not
checked. This section steps back and looks at all of them together.

**What exists.** Five separate notions of type decide whether a term runs
compiled:

1. **`typing.rs`**: `Int | Fun | Var`, simple types with unification. It
   is monomorphic and can't see arity. It has two non-standard rules:
   `Rec` must wrap an `Abs`, and a closed condition types only the branch
   it picks. It is trusted, and the `independent_of_the_compiler` test
   checks that it shares no code with the compiler.
2. **`compile.rs`'s `infer_closure_arities`**: for each variable, an
   `ArityUse`, `Consistent(k)` or `Inconsistent`. It decides module-wide
   between `Dispatch::Fast` and `Curried`, and it knows nothing about
   `Int` versus closure.
3. **`proof.rs`'s `Denoted::Int | Clo(Expr)`**: `Clo` records no arity.
   Parameter types come from `ArityUse`, and `return_type_of` has to be
   kept in step with it by hand. Arity is checked at six `arg_denotation`
   sites and in `eval_dyn`.
4. **The kernel's `Clo_k`** (`curried_int_ty(k)`, `Int -> ... -> Int`):
   it is curried, so `Int -> (Int -> Int)` and `Clo_2` are the same type.
   Arity is exact only because the prover picks `Clo_k` from the number
   of arguments at a call site (§40, corrected below).
5. **`jit.rs`'s `calls_a_parameter`** (§42): a syntactic check that stands
   in for "the theorem's parameters are all `Int`".

**What would be ideal.** One type system, over the term language, that:

- (a) is arity-aware, so that `\x. \y. e` and `\x. (\y. e)` differ exactly
  as they do in compiled code, and a `Fast` call is well-typed only when
  the callee has that arity (Bolingbroke and Peyton Jones's "Types are
  calling conventions"; Downen et al.'s "Kinds are calling conventions");
- (b) is the one source for all four consumers: the typing gate, the
  choice of dispatch, prover parameter types and kernel types;
- (c) has a proved type-safety theorem: on `Int` arguments, a well-typed
  term never reaches `TypeError`, `NotAFunction` or `UnboundVariable`;
- (d) is linear in the hash-consed DAG, not in the tree it unfolds to;
- (e) is at least as permissive as the corpus needs, in which case
  let-polymorphism is optional.

**Gaps, by consequence.**

- **G1: arity blindness** (1 vs 2, 4). The §40 hole is closed only by the
  proof gate, and the protection comes from how the prover models calls,
  not from kernel types.
- **G2: four places to keep in agreement.** Every hole §38 to §42 found
  was one notion assuming another had checked something. §42's
  `calls_a_parameter` exists because the kernel's parameter types come
  from use (3), while the JIT's come from the entry point (all `Int`).
- **G3: exponential on DAGs.** `infer` walks the tree and has no memo. A
  term that nests `t + t`, `d` deep, takes 22 ms to type at `d = 18`,
  395 ms at 22, and 3.4 s at 25. `try_compile` is worse: 417 ms, 8 s and
  73 s. This breaks the ideal (d), and it is also a denial-of-service
  risk for anything that feeds terms in. (Typing is fixed in §45.
  `try_compile`'s cost turns out to be the size of its output, not the
  walk.)
- **G4: soundness is argued, not proved.** "By the usual type-safety
  argument" (`typing.rs`'s doc) covers the textbook rules. The two
  non-standard rules are covered only by argument plus §41's fuzz.
- **G5: the pruning rule exists for tests.** It keeps dead, ill-typed
  branches compilable, "used in tests and benches to exercise curried
  dispatch". It makes the checker depend on `eval`.
- **G6: monomorphism.** A closure used at two types is declined, e.g.
  `(\id. id (\x. x) (id 1))`. The corpus has no such term. Since every
  value is a uniform `i64`, polymorphism costs nothing at runtime.

**Options.**

*G1, arity in the types.*

- **A1: multi-arity arrows in `typing.rs`.** Replace `Fun(a, b)` with
  `Fun([a1..ak], b)`. The arity of an `Abs` chain comes from how it is
  peeled, the arity of a call from its spine, and unification requires
  equal arity. This is §40's proposal.
  - Pros: it makes the §40 hole a type error independent of the proof
    gate. It is small: one constructor and one unify case.
  - Cons: it is more restrictive than `eval`. A term that partially
    applies a two-argument lambda, or over-applies a lambda that returns
    one, is declined unless there are coercion rules. Those rules
    (subsumption from `Fun([a], Fun([b], c))` to `Fun([a, b], c)`) are
    exactly what Downen et al. need extensional types for. It also
    doesn't touch G2, so it becomes a sixth notion that must agree.
- **A2: infer arity by use, with eta coercions.** Generalise A1 by
  letting a closure used at arity `k` but defined at `j` get an eta
  adapter (§43's 1b), recorded as a coercion in the typing derivation.
  - Pros: it declines nothing that `eval` accepts, and the adapters can
    be certified as `spec_check` does.
  - Cons: it is an elaboration, not a check, which puts rewriting inside
    the trusted base. Of the options here it has the most code, for no
    term the corpus has.

*G2, one source or many.* This is the central tension: the typing gate is
trusted *because* it is independent (§38). Four ways out:

- **B1: N-version.** Keep the independent checkers and add a test that
  they agree (typing's arity per variable equals `infer_closure_arities`'
  on every fuzzed term).
  - Pros: no trusted code changes, and disagreement is caught in testing.
  - Cons: agreement is tested, not enforced, and each new notion adds a
    pair to check.
- **B2: an untrusted elaborator and a small trusted checker.** One
  inference, anywhere and as clever as needed, emits a typed term (each
  binder and call annotated with its type and arity). A small trusted
  checker re-checks the annotations. Compile, the provers and the gate
  all read the same annotations. This is how GHC treats Core (Core Lint
  re-checks the typed IR between passes), and how typed assembly and
  proof-carrying code (Morrisett et al.; Necula) and translation
  validation (§35) work.
  - Pros: one source for (b). The trusted part is smaller than
    `typing.rs` today (checking is simpler than inferring: no
    unification, one linear pass, and G3 disappears for the checker), and
    independence still holds, since the checker needn't share code with
    the elaborator.
  - Cons: the largest change here. Every consumer switches from its own
    walk to the annotations. The annotated form has to survive the
    specialiser (§37) and lifting (§36), or be re-inferred after them.
- **B3: share `typing.rs` with compile and the provers.**
  - Pros: least code.
  - Cons: it gives up §38's independence. A bug in the shared inference
    then misleads the gate and the compiler the same way, which is the
    failure independence exists to catch.
- **B4: kernel types as the source.** Put the arity-exact type into the
  theorem (§42's third option: record parameter types on each proof),
  and have the gate read them.
  - Pros: the gate then reads the theorem's own statement, which is the
    most direct form of "what was proved covers what runs".
  - Cons: it needs arity-exact kernel types first. Today `Clo_k` is
    curried (4), so the kernel itself can't tell the two lambdas apart.
    It also doesn't help the typing gate.

*G3, the DAG blowup.* Monotyping a DAG is not the same as monotyping the
tree it unfolds to. If shared occurrences share one type node, a lambda
used at two types in two places is declined where the tree typing
accepted it. Three repairs, from most to least exact:

- **C1: memo ground results.** Memoise on (subterm hash, the resolved
  types of its free variables) only when inference fixes every type
  inside the subterm. Reuse is then exactly what re-typing would do.
  - Pros: it changes nothing that is accepted. It covers the measured
    case, which is first-order arithmetic.
  - Cons: a shared subterm with lambdas of unresolved type is still
    re-walked, so the worst case is still exponential.
- **C2: generalise closed subterms.** Type each closed shared subterm
  once, generalise, and instantiate fresh at each use. That is
  let-polymorphism for closed subterms (Milner), and it is sound here
  because there are no effects, so no value restriction is needed.
  - Pros: linear for closed sharing, and it removes part of G6 as a side
    effect.
  - Cons: the gate would then pass terms the provers can't type (F1's
    con, below). The blowup term is open, so this doesn't help it.
- **C3: share type nodes per (hash, environment).**
  - Pros: linear always.
  - Cons: incomplete relative to tree typing, as above.

  Whichever is chosen, `try_compile` still costs as much as the tree:
  its IR has no `let`, so what it emits is as big as the tree (§45). ML
  typing is DEXPTIME-complete because of `let` sharing
  (Mairson), so full sharing-aware polymorphic inference can't be linear
  in general. A monomorphic system that gives up the lambda-at-two-types
  case (C3) can be.

*G4, soundness.*

- **D1: prove progress and preservation in the kernel.** Wright and
  Felleisen style, for the checker's rules including the two
  non-standard ones.
  - Pros: the only way to meet (c).
  - Cons: large. The kernel reasons about compiled code, not about the
    term language's typing, so this needs a deep embedding of `Term` and
    `eval`'s rules.
- **D2: a type-safety fuzz.** For random well-typed terms and random
  `Int` arguments, `eval` never returns `TypeError`, `NotAFunction` or
  `UnboundVariable`.
  - Pros: cheap, and it states the property directly. §41's fuzz tests
    the gates, not this.
  - Cons: evidence, not proof.

*G5, the pruning rule.*

- **E1: a dead-branch pass before typing and compile.**
  - Pros: typing gets simpler.
  - Cons: the pass's trust moves into the pipeline.
- **E2: make the tests' dead branches well-typed.**
  - Pros: typing loses the rule and its `eval` dependency.
  - Cons: those tests exercise curried dispatch *because* the branch is
    ill-typed at `Fast` arity. This should be checked per test before
    committing to it.

*G6, polymorphism.*

- **F1: Hindley-Milner at `(\x. b) e` redexes** (`let` in all but name).
  - Pros: no runtime cost.
  - Cons: no gain unless the provers and `infer_closure_arities`
    follow. They type a closure by one arity and one `Clo_k`, so a
    polymorphic term would pass the gate and then get no proof.

**Recommendation.**

1. **C1, then the same memo for `try_compile`.** G3 is the one gap with a
   concrete cost today, and C1 changes nothing that is accepted. (Done in
   §45. The second half was a wrong premise: see there.)
2. **D2.** Done in §45. Cheap. It turns G4's "by the usual argument" into something
   tested.
3. **B2**, if the proof gate is ever relaxed (§29's "widen the universal
   fragment"). Only with a single annotated source do A1 and B4 become
   one change rather than two more notions to keep in step.

A1 alone fails G2, and F1 alone gains nothing. E is housekeeping.

