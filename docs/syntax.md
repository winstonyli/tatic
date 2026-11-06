# Surface syntax

```rust
use tatic::lang::{syntax, term::TermStore};

let mut store = TermStore::new();
let fact = syntax::parse(&mut store, "rec f n = if n <= 1 then 1 else n * f (n - 1)")?;
```

`let`/`\`/`rec`/`if` all extend as far right as possible, so — as in most
ML-family languages — they need parentheses as a function argument or an
operand: `f (\x. x) (if c then 1 else 2)`, not `f \x. x if c then 1 else 2`.
`let x = e1 in e2` is pure sugar for `(\x. e2) e1` (the term language has no
separate `let` primitive); a named recursive function reads naturally as
one `let` binding a `rec` value:

```
let fact = rec f n = if n <= 1 then 1 else n * f (n - 1) in fact 10
```

One honest, non-obvious finding from building this: nesting two `let`s
where the inner one's body references the outer one's binding can
desugar into a term that's genuinely *capturing* by the time `compile.rs`
peels its inner lambda standalone — even though nothing about the source
looks like a capturing closure (see `syntax.rs`'s own tests,
`higher_order_let_chain_evaluates_like_the_inlined_sample`). Real
closure conversion (see `compile.rs`'s module docs) compiles this
correctly now rather than falling back to the interpreter, and the
arity-0 per-instance certificate proves it, though `denote_closure`'s
universal proof declines it (`proven.md`).

`syntax::print` is the reverse direction — a precedence-aware
pretty-printer back to source text `parse` accepts, assigning each binder
a fresh name by nesting depth (`v0`, `v1`, ...) since `Var`/`Abs` don't
carry names. It round-trips (`parse(print(t))` hashes identically to `t`,
a strictly stronger check than "looks plausible") for every well-scoped term.
Unary minus on an integer literal parses as a negative literal (`-5` is
`Lit(-5)`, as in OCaml), so negative literals round-trip exactly too;
`print` parenthesises one where unary minus would otherwise bind
differently (`f (-2)`, since `f -2` is the subtraction `f - 2`).

`crates/tatic/src/bin/repl.rs` is a small interactive REPL built on `syntax::parse`/
`print`: each line is parsed, run through the JIT (falling back to the
interpreter automatically, same as ever), and reported with whether it
got a kernel-checked proof. `let NAME = EXPR` (no `in`) defines `NAME` for
later lines — since `syntax.rs`'s parser has no scope that persists
across separate calls, this works by re-parsing each new line with every
prior definition's `let .. in ` prefixed, not by threading parser state.
Building it is what surfaced two real `compile.rs` bugs (a crash on a
named recursive function used as a value, and a non-tail self-call that
hardcoded `call $f` instead of calling back into whichever function it
was actually compiled as) — see `compile.rs`'s own tests.
