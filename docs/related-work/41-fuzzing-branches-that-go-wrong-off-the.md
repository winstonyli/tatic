## 41. Fuzzing branches that go wrong off the samples

§38 and §40 each pinned their hole with one hand-built term. The random
fuzz couldn't: its ill-typed compiled terms went wrong on the samples, so
`verify()` caught them first, and the gates were never the last line.
`compile_fuzz`'s `a_branch_that_goes_wrong_off_the_samples_is_never_installed`
generates

```
if x == 777 then <goes wrong> else <gen_expr>
```

where 777 is outside `jit.rs`'s sample battery. `<goes wrong>` is one of
a closure used as an `Int`, an `Int` (always a parameter) called, an
over-applied lambda (all ill-typed), or §40's well-typed closure of the
wrong arity. The branch sits in one of four hosts:

- the body of a plain function;
- the per-iteration payload of a tail loop or a non-tail recursion, with
  `x` the counter, so the branch runs when the counter reaches 777;
- `\x1. \x2. if x2 == 777 then x1 a else e`, where `x1` is only ever
  called (below).

Each term is run at every combination of `[0, 1, -1, 7, 777]`, and the JIT
must agree with `eval`. The test tallies each host and kind by outcome,
and requires each ill-typed kind to reach the typing gate, and the wrong
arity the proof gate, in every host.

Latest run, 600 seeds: every term compiled and passed the samples, and
every one was declined, 467 as ill-typed and 133 for want of a proof.
Early versions lost about half of the "Int called" terms before any gate:
`compile.rs` compiles only a variable or a lambda as a call head
(`Shape::OtherCall`), so calling a literal or an arithmetic expression
was declined earlier and tested nothing.

**Teeth.** Disabling the proof gate fails it (seed 3, a tail loop: `eval`
gives `Ok(682316)`, the JIT `Trap`). Disabling the typing gate fails it
(seed 7: `eval` gives `NotAFunction`, the JIT `Ok(10)`), but only because
of the fourth host, and since §42 only together with the check that
section adds. In the first three, the proof gate declined every
ill-typed term too. The first version's typing-gate failure (its seed 190)
was a noisier instance of the fourth host: `v1` called, and otherwise
only passed to lambdas.

**What the fourth host found.** `\v0. \v1. if v0 == 777 then v1 5 else v0`
gets a universal proof from `prove_closure_expr`. `v1` is only called, so
the prover types it `Clo_1` and proves the theorem for every closure
argument. The JIT's entry point is only ever passed `Int`s, so the theorem
covers none of the calls the fragment is installed for. This is the case
§38 anticipated ("the kernel theorem is over postulated symbols with no
types"), now pinned down: the typing gate is currently the only thing
standing between such a term and installation. Fixed in §42.

