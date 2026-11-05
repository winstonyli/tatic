## 38. The JIT installed ill-typed code that goes wrong only off the samples -- found and fixed

**The bug.** `\n. (\g. if n == 777 then g 1 + g else n) (\x. x + n)`
adds a closure to an `Int` when `n == 777`. `eval` gives `TypeError` there;
the JIT installed the compiled form and returned `Ok(779)`. The specialiser
isn't involved (`g` is used twice and captures `n`).

**Root cause.** Compiled code is untyped: an `Int` and a closure are both a
raw `i64` (`lower_wat.rs`'s packed table-index/env-pointer), with no tag to
test. So compiled code is correct only if nothing uses a closure as an
`Int` or calls an `Int`, and nothing established that. Neither half of the
installation gate (§28, §29) sees it: `verify()` compares only on
`sample_arg_vectors`, which never reach `n == 777`, and the universal
theorem is stated over postulated symbols (`call_ref` always returns an
`Int`), so it has no notion of type. Several docs claimed `verify()`
catches ill-typed code (`lower_wat.rs`'s over-application notes,
`compile_fuzz.rs`, §37, the README). It does only when a sample reaches the
ill-typed code.

**Options considered.** More samples only hide the symptom. Runtime guards
are impossible without tags, and tagging values (63-bit ints, as V8,
LuaJIT and Chez do, or boxing) costs every operation and changes integer
semantics. A flow analysis of which sites can receive a closure is more
precise than typing and harder to trust, with no corpus term needing the
precision. Making the kernel theorem model types is very large. Taken:
the other standard answer, the one ML-family compilers rely on when they
erase tags (typed closure conversion, Morrisett et al.). Only a term with
a simple type `Int -> ... -> Int` is installed, so by the usual type-safety
argument (Wright and Felleisen) it can't reach `TypeError`, `NotAFunction`
or `UnboundVariable` on `Int` arguments.

**The fix.** `src/typing.rs`, `well_typed(store, h, arity)`: monomorphic
unification over `Int | a -> b | variable`, with an occurs check (Milner's
algorithm without generalisation). Two rules go beyond the textbook:
- `Rec` must wrap an `Abs`, which is also all `compile.rs` compiles. `eval`
  treats a `Rec` value as a function, so `Rec(Lit 5) + 1` would otherwise
  type as `Int` and fail at runtime.
- An `If` whose condition is closed arithmetic over literals only types the
  branch `eval` would take. Without this, the dead `if 1 < 0 then g(x, 999)`
  in `inconsistent_arity_loop_carried_parameter_loop`, and five `jit.rs`
  tests built the same way, would be declined.

`jit.rs` runs it on `h` after compilation and before instantiation. A
declined term is cached as `CacheEntry::IllTyped`, counted in
`Stats::declined_ill_typed` and served by the interpreter. The check is on
`h` rather than on a specialised `h'`: βv preserves types, and `h` is what
the caller wrote. `typing.rs` is trusted, so the independence scan pins it
to `eval` and `term`. `try_compile` is unchanged: the `compile.rs` tests
that exercise curried dispatch through ill-typed dead branches still
compile.

**Cost, measured before choosing** with a throwaway probe of the same
inference:
- Corpus: 21 of 23 terms are typed. The other two, `iterate` and
  `fixture_twice`, take closure parameters, which the JIT can't pass (its
  arguments are `i64`), so the JIT never installed them anyway.
- `gen_program`: 1000 of 1000.
- `gen_redex_rich`: 366 of the 408 that compile.
- `gen_over_applied`, `gen_inconsistent_arity`: 0 of 1000, as designed.
  They are ill-typed by construction and passed before only because the
  samples caught them.
- `cargo run --release`: compiled 9, specialised 3, `declined_ill_typed` 0,
  so the demo is unchanged.

The monomorphism is a real limit: a closure used at two different types
is declined, where let-polymorphism would accept it. No corpus term needs
it.

**Tests.**
- `jit.rs`'s `an_ill_typed_branch_off_the_samples_is_not_miscompiled` is
  the regression test for the bug, and pins `declined_ill_typed == 1`.
- `typing.rs` has seven unit tests: acceptance and arity, closure as
  `Int`, constant and non-constant conditions (and a constant one that
  fails), `Rec`, the occurs check, open terms and closure parameters, and
  the independence scan.
- `specialisation_is_checked_and_preserves_meaning_on_random_terms` now
  checks type safety directly: if `well_typed` accepts a term, `eval` must
  never give `TypeError`, `NotAFunction` or `UnboundVariable` on it. It
  also compares the JIT with `eval` on every term, and compares compiled
  fragments exactly on every typed term, where before it skipped only
  `TypeError` results. Latest run: 4376 compiled runs compared, 17 terms
  compiled but ill-typed.
- The over-applied and inconsistent-arity fuzz tests now pin
  `declined_ill_typed == 1`.

**Teeth**, each broken, seen to fail, then restored:
- Not forcing a `Prim`'s left operand to `Int` fails the type-safety fuzz
  (seed 25).
- Disabling the JIT gate fails the regression test.
- Dropping the `Rec` rule fails `rec_must_wrap_an_abs`.
- Dropping the pruning fails the five inconsistent-arity `jit.rs` tests.

Disabling the gate does *not* fail the random fuzz: its 17 ill-typed
compiled terms happen to be caught by the samples. §41 adds a fuzz of
off-sample ill-typed terms, which does fail.

