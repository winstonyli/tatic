# tatic

An efficient implementation of an expressive higher-order language where,
once a high-level transformation is *found to be equivalent* to a low-level
sequence of operations on a formalized target machine, that low-level form
is used as a JIT-compiled implementation for future invocations of the same
transformation.

Concretely: terms are content-addressed (hash-consed), so structurally
identical transformations anywhere share one cache key. The first call for
a given term tries to compile it to WebAssembly and JIT it via `wasmtime`
(Cranelift); every later call for that same content hash skips straight to
the compiled, native-speed path. The compile step is
`compile::compile_specialised`: it first βv-reduces known closures
(`specialise.rs`, untrusted) and has an independent checker replay every
step (`spec_check.rs`), and when the checker accepts and the reduced `h'`
compiles, the fragment is built from `h'`, so for it `h' ≡ h` is
certificate-checked rather than kernel-checked (§37 of `RELATED_WORK.md`).
"Found to be equivalent" is not just
asserted — it's checked, with two complementary layers of assurance: sample
verification against a reference interpreter (always), and, where the term
falls in a covered fragment, an actual **kernel-checked proof** that the
compiled and interpreted readings agree.

## Scope

tatic is a research prototype, not a production compiler. The compilable
fragment is small (simply typed `Int -> ... -> Int` terms with closures);
anything else is served by the interpreter. Kernel-checked equivalence proofs
cover only the terms in the proof fragment; elsewhere the compiled code is
checked against the interpreter on sample inputs only. Alongside the JIT, the
repository holds a Church-encoded bit-vector library and a rewrite-rule miner
(`tests/church_bv/`, `tools/rulelm/`), which are research experiments and are
not needed to use the JIT.

## Requirements

- A recent stable Rust toolchain: the crate uses edition 2024, and its
  dependencies declare a minimum of Rust 1.91 (the crate itself declares no
  `rust-version`). `tools/rulelm` is a separate crate whose `burn` dependency
  needs Rust 1.95 and a Vulkan-capable discrete GPU (it selects
  `Device::vulkan(DeviceKind::DiscreteGpu(0))`); it is optional.
- Development and measurements were done on Windows 11. The Rust code is not
  Windows-specific, but several helper scripts under `scripts/` use bash and
  PowerShell (for example `scripts/quiet_ab/pin.ps1`), and the recorded
  timings come from one laptop.

## License and development notes

Licensed under the Apache License, Version 2.0 (see `LICENSE`; copyright 2026
Winston Li).

This project was developed with substantial AI assistance: over 90% of the
commits (500 of 536 when this note was written) carry a `Co-Authored-By:
Claude` trailer, and the design notes in `RELATED_WORK.md` were written the
same way. Treat the measurements and proofs as claims to re-run, not as
audited results. The internal planning notes and experiment scripts that some
commits and `RELATED_WORK.md` refer to (`docs/superpowers/`,
`scripts/experiments/`) are not part of this repository.

## The end-to-end loop experiment

An experiment on whether rule mining can run alongside execution: laws are
served in batches, rules are mined from each served batch, and the next batch
is served under the rules mined so far. The metric M is the number of laws that
still need a whole-term machine proof. The measured results are not in this
repository (they live in local notes), so treat the code below as the
reproducible part.

- `scripts/loop_stream.sh none|ref|loop OUTDIR` is the driver (`EXE` names the
  `church_bv` test executable). `none` serves with no rules, `ref` mines once on
  the whole stream, `loop` mines after each batch. It writes `OUTDIR/m.tsv`
  (round, M, laws, rules in force, seconds). The header documents all options:
  `B`, `K`, `OFFSET`, `STRIDE`, `FAMILY=add3|mix3|sbo3|cmp3`, `WINDOW=cum`, `POOL`,
  `MODEL` (needs `scripts/loop_candidates.sh` and a `rulelm` checkpoint),
  `WARM=<skip>:<laws>[:<phase>]` and `WARM_RULES=<file>` (start with rules in
  force; `scripts/rules/reassoc.txt` holds six general reassociation rules
  that cut machine proofs on add3, mix3 and sbo3 streams), and `SPLIT=0|1` (one
  structure-based half of the laws).
- The miner (`search::rule_miner` in `tests/church_bv/search.rs`) takes its
  settings from `RULEMINER_*` environment variables. Options added for this
  experiment, off by default unless noted: `NOIDENT` (drop identity candidates),
  `GENERAL` (generality penalty), `PHASE` (residue class of a strided law
  sequence), `SHAPE` and `SHAPE_SALT` (structure-based split of the laws),
  `NODUPLHS` (no candidate whose left side already has a rule in force; on by
  default, `0` turns it off), and `GUARD=<k>` (also score k laws that are
  already machine-free, so a rule that fixes stragglers but breaks those is not
  chosen; default 120, `0` turns it off).
- Unit tests for the split and the guard sampling: `shape_halves_partition`,
  `shape_salt_changes_the_split`, `guard_plan_samples_and_weights` in
  `tests/church_bv/search.rs`.

Headline result (machine proofs M; `none` = no rules, `ref` = rules mined once
on the whole stream; single runs, no noise estimate). A loop started from the
six rules in `scripts/rules/reassoc.txt` recovered 83-92% of `ref`'s gain: add3
194 / 62 / 51 for none / seeded loop / ref, sbo3 181 / 56 / 31, mix3 (offset
600) 136 / 22 / 6. A loop started cold recovered 37-48% on add3 and sbo3 (add3
125, sbo3 126). The first four rules were mined on add3; the fifth and sixth
(`sub(sub(x,y),z) -> sub(sub(x,z),y)` and `sub(xor(x,-1),y) -> sub(-1,add(x,y))`)
were picked from add3 and sbo3 runs, so sbo3 (built from similar operators) is
a related family, not an independent test. Served statically, the sixth rule
lowers M on five of six streams and never raises it, including two streams
disjoint from the ones it was picked on (add3 77 to 63, sbo3 68 to 65). A
seventh rule from the same mining runs changed M by at most 1 on five streams,
so the library appears to stop helping at six.
Over six disjoint samples of each stream the six rules gave M = 32-35 on add3
(four rules 44-53, none 86-109) and 48-59 on sbo3 (four rules 54-65, none
122-141), so differences of one or two proofs on a single stream are within
the sample-to-sample spread. On the shl, shr and lt families the rules change
nothing.
Loops on four disjoint samples: seeded 31-34 on add3 and 46-55 on sbo3, cold
60-73 and 93-112, so seeded beats cold on every sample; mining on top of the
seeded start adds 1 proof on add3 and 3-6 on sbo3 over the static six rules.
The library is specific to add/sub structure: on `cmp3` (comparisons `lt` of
small arithmetic terms; 308 laws) the six rules change nothing (21 proofs with
or without them) while three comparison-specific rules, found by `ref` or by a
loop after its first batch, take it to 3 (`ref`) or 19 (loops, which pay the
first batch in full).
On a family mixing both structures (`cmp3d`, 6194 laws; the comparison rules, in
`scripts/rules/cmp.txt`, were mined on a subset of it, so not independent) the six rules plus the three
comparison rules gave 69 against 130 with no rules, a loop seeded with them 54,
a cold loop 78 and `ref` 39; the comparison rules alone gave 124. Neither set
changed the two-variable `lt` family.
Over six disjoint `cmp3d` streams (stride 15, four batches of 100, approximate
`RULEMINER_FAST` mining) the seeded loop beat the cold loop every time, by 17-31
proofs (cold 74-93, seeded 43-73). Almost all of that is the first batch, served
before a cold loop has mined anything (gap 13-29); from the second batch on the two
are within a few proofs, so the library is a head start, not a lasting advantage.
The comparison rules never fire on add3, sbo3 or mix3 and never raise M there.

The planning notes and the per-experiment scripts and logs are not part of the
repository (see the previous section).

## Quick start

```sh
cargo run --release             # runs the demo in src/main.rs
cargo run --release --bin repl  # an interactive REPL (src/bin/repl.rs)
cargo test                      # unit tests across all modules
cargo bench                     # criterion benchmarks (benches/) -- see below
```

The demo starts by parsing a real source string (`syntax.rs`) into a term,
then builds a few more example terms by hand (factorial, gcd, a naive
Fibonacci, a non-capturing higher-order term, a genuinely capturing
closure, a straight-line arithmetic function), runs them all through the
JIT, and prints timing plus which ones got a kernel-checked equivalence
proof. (Two capturing-closure terms appear side by side, compiled via
*different* dispatch paths: one reached by over-applying a literal
lambda's saturated-call result, the other by calling a closure-typed
*parameter* — see `lower_wat.rs`'s module docs and `main.rs`'s comments on
each.)

## Validation

The full routine, run after every change:

```sh
cargo build --all-targets
cargo test --lib --bins
cargo clippy --all-targets
cargo test --release --test compile_fuzz --test kernel_fuzz \
           --test kernel_soundness_fuzz --test syntax_fuzz
cargo test --release --lib ir_fuzz -- --ignored
cargo test --release --test church_bv a_large_check -- --ignored
cargo bench
cargo run --release
```

`cargo bench` is in that list deliberately. It used to be left out on the
reasoning that `--all-targets` already builds the benchmarks — which it
does, and which is exactly why a stack overflow sat unnoticed in
`benches/execution.rs` until someone ran them (`RELATED_WORK.md` §30).
Building a target proves nothing about running it.

A full `cargo bench` takes a while — `fib_30`'s interpreter bar alone is
over a second per iteration. When the point is "does it still run", not
"how fast", cut the sweep down per suite:

```sh
cargo bench --bench execution -- --warm-up-time 0.3 --measurement-time 0.5 --sample-size 10
cargo bench --bench proofs    -- --warm-up-time 0.3 --measurement-time 0.5 --sample-size 10
```

Those flags need `--bench <name>`; passing them to a bare `cargo bench`
fails, because that also runs the lib unittest target, which doesn't
understand criterion's arguments.

A note on what "clean" means here: `cargo bench` prints criterion's
`change:` percentages against whatever it last stored, which on a fresh
checkout is nothing. Treat a regression line as a prompt to look, not as
a failure.

To compare two versions, `scripts/bench_ab.sh [REV] [cargo bench args]
[-- criterion args]` (default `HEAD`) benchmarks `REV` in a worktree
under `target/bench-ab`, then the working tree, then `REV` again, and
prints each bench's change next to the change the re-run of `REV` shows.
Re-running unchanged code on this laptop moves benches by up to
±100%, so only a change well beyond that noise column means anything.
For example, `scripts/bench_ab.sh HEAD --bench proofs`.

When other sessions keep the machine busy, `scripts/quiet_ab/ab.sh`
runs two commands in alternating rounds, samples total CPU throughout,
and `scripts/quiet_ab/clean.py` keeps only the rounds no other process
loaded. Its header has the usage; `scripts/quiet_ab/test_clean.sh`
checks the cleaning rules (RELATED_WORK §66).

## Architecture

```
 term.rs -----> eval.rs (reference semantics)
    |               ^
    |               | compared against
    v               |
 compile.rs ---> jit.rs ---> wasmtime (Cranelift JIT)
    |               ^
    |               | additional evidence
    v               |
 proof.rs <----> kernel.rs (Pi/Sort/Id/W/Sigma type theory)
```

| Module | Role |
|---|---|
| `term.rs` | Content-addressed term store. Hash-conses a small higher-order language (`Var`/`Lit`/`Prim`/`If`/`Abs`/`App`/`Rec`) by BLAKE3 content hash, so structurally identical terms — however independently constructed — always share one hash and one cache entry. |
| `syntax.rs` | A real, parseable surface syntax for that language, so a term doesn't have to be hand-built through `term.rs`'s De Bruijn-index builders. A small recursive-descent parser (no separate AST — each grammar production interns directly via `TermStore`) with ordinary named-variable scoping (`\x y. x + y`, `let`, `rec f x = ...`), translating names to De Bruijn indices as it parses; `print` is the reverse direction, a precedence-aware pretty-printer back to source text. |
| `eval.rs` | The reference interpreter (call-by-value). Defines correctness: everything else is judged against this. Supports the *full* language, including arbitrary higher-order closures. Trampolined for its own tail positions (an `If`'s chosen branch, and applying a value that resolves the current call), mirroring `lower_wat.rs`'s own `loop`/`br` lowering at the interpreter level: a tail-recursive term runs at any depth without growing the native stack, while a genuinely non-tail-recursive one (naive `fib`, say) still grows it, exactly as it would grow a Wasm `call` chain in the compiled reading. |
| `compile.rs` | Term analysis and the IR builder. Decides which terms fall in the compilable "first-order arithmetic with self-recursion and closures" fragment (`classify`, shared with `proof.rs`; `free_vars`; closure-arity inference; the combinator registry, including compile-time partial-application wrappers) and builds `ir.rs`'s IR for them (`build`). `try_compile` is a tree-size gate (§47), then build, then `ir::check`, then `lower_wat::lower`. Anything outside the fragment is rejected -- the compiler only needs to be sound, not complete. `compile_specialised` is the pipeline driver: it runs `specialise.rs`, checks the result with `spec_check.rs`, then calls `try_compile` on the specialised `h'` whenever the checker accepted its trace and `h'` compiles, and on `h` otherwise (no trace, a rejected trace, or an `h'` outside the fragment). For a specialised fragment the claim is: compiles `h'`, which decompiles to itself (§35) and is certificate-checked ≡ `h`, not kernel-checked -- see §37 of `RELATED_WORK.md`. |
| `specialise.rs` (untrusted) | βv-reduces known closures before compilation (`caller (add acc) n` -> `acc+n`), emitting the result plus a trace of steps. Nothing here is trusted: a bug here produces a trace `spec_check.rs` rejects, or a slower program. Soundness rests on `spec_check.rs` alone -- see §37 of `RELATED_WORK.md`. |
| `spec_check.rs` (trusted, independent) | Replays `specialise.rs`'s trace from the original term with its own `shift`/`subst`, step by step, and accepts only if it lands on exactly the claimed result. Its own independence allowlist (checked by a test, reusing `decompile.rs`'s import-scanner) permits importing only `crate::term` and `std` -- see §37 of `RELATED_WORK.md`. |
| `ir.rs` | The JIT's IR: closure-converted, representation-neutral; well-formedness checker. |
| `lower_wat.rs` | Lowers the IR to WAT; one template per node, plus closure representation, allocator and curried stages. Its module docs describe the closure representation (a packed `i64` of table index and environment pointer), partial application, over-application and the curried fallback for inconsistent arities. |
| `jit.rs` | The cache. On first use of a term, tries to compile it, then verifies the compiled code against the interpreter on a battery of sample inputs before trusting it; only then is the compiled form installed for future calls under that hash. A verification failure permanently blacklists that hash to the interpreter rather than risking a silently wrong optimization. For a fragment with capturing closures, `invoke` also resets the bump allocator's pointer before *every* call (not just the first) — caught by benchmarking the closure-conversion path, not by any unit test: since this cache reuses *one* compiled instance across many separate calls, every capturing closure any call created was leaking its environment forever, growing that instance's linear memory unboundedly over its whole cached lifetime. The reset can't happen inside the compiled function itself (at `$f`'s own entry, say) — a non-tail self-recursive call is an ordinary `call $f`, re-entering the whole function from the top, which would reset mid-computation and corrupt a closure created earlier in the same call that's still needed after the recursive call returns. From the host, once per top-level call, there's no such hazard: nothing outside one call ever reads a closure value `$f` itself returned. |
| `typing.rs` (trusted, independent) | Simple (monomorphic) type inference over `Term`, with a closed-constant-condition rule for dead branches. `jit.rs` installs a compiled term only if it has type `Int -> ... -> Int`: compiled code stores `Int`s and closures as the same untagged `i64`, so ill-typed code returns garbage where `eval` fails, and the sample battery only notices when a sample reaches that code -- see §38 of `RELATED_WORK.md`. Linear in shared subterms whose type is ground, and its type-safety claim is fuzzed (§45). |
| `kernel.rs` | A free-standing, minimal predicative dependent type theory: `Pi` + a stratified universe hierarchy (`Type₀:Type₁:...`) + `Id`/`Refl`/`J` (equality) + `W`/`Sup`/`WRec` (general inductive types) + `Sigma`/`Pair`/`SigRec` (dependent sums) — five primitives. The first four are provably the minimum needed for *definitional* computation of user-defined recursive functions in a predicative system (see doc comments for why weaker combinations don't work); `Sigma` is a separate addition for a different reason — `W`'s own children function maps back into `W` itself, so it can't stand in for an arbitrary, independently-chosen payload type the way a general dependent sum needs, and (as with `W` over Church-encoding) the usual `Pi`-alone encoding was rejected because it doesn't reduce by `refl`. Has a real bidirectional typechecker and normalizer. Every recursive traversal (and `Expr`'s `Drop`) runs through a `stacker`-backed `grow`, so term depth is bounded by heap, not native stack -- see §31 of `RELATED_WORK.md`. |
| `proof.rs` | Connects `kernel.rs` to the JIT. For terms in scope, builds an actual `Id`-typed proof — checked by `kernel.rs`'s typechecker, not just asserted — that the compiled and interpreted readings of a term agree, and records it as additional evidence in `jit.rs`'s cache. Every walker here dispatches on `compile::classify`, the same case analysis `build_node` uses, so the proofs and the compiler cannot disagree about which case a term falls into -- see §33 of `RELATED_WORK.md`. |
| `decompile.rs` | Translation validation: rebuilds the term an IR module implements, from the IR alone; `try_compile` requires the rebuilt term's content hash to match the source's before accepting the module -- see §35 of `RELATED_WORK.md`. |
| `ir_fuzz.rs` (test-only) | Differential tests of the lowering templates against `decompile.rs` + `eval.rs`: each template, and random well-typed IR, run through both `lower_wat`+wasmtime and `decompile`+`eval`, and must agree -- see §35 of `RELATED_WORK.md`. |

The closures fragment's own `Int`/`Clo` type system — implicit, spread
across `compile.rs` and `proof.rs`, never written down as one thing until
now — is formalized in [`TYPES.md`](TYPES.md): its grammar, its typing
judgment (with each rule tied to where it's actually implemented), and a
real finding the writeup surfaced — `Clo` used to be a single,
arity-blind kernel type, so the kernel-checked proof verified
*structural* agreement but not closure arity, which was tracked entirely
by Rust-level bookkeeping the kernel itself never inspected. `Clo` is now
`Clo_k`, a family of kernel types indexed by arity (one postulate per
distinct `k` actually used, mirroring how captures were already
postulated per signature), so an arity mismatch — e.g. an `If` choosing
between two closures of genuinely different arity — is now a
kernel-checked type error instead of two `Clo`s silently unifying; see
`TYPES.md` section 7.

## Surface syntax

```rust
use tatic::{syntax, term::TermStore};

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
`higher_order_let_chain_evaluates_like_the_hand_built_demo_term`). Real
closure conversion (see `compile.rs`'s module docs) compiles this
correctly now rather than falling back to the interpreter; it still
doesn't get a *kernel-checked* proof, though, since `proof.rs`'s own
fragment doesn't cover higher-order terms at all yet (see below) —
independent of what `compile.rs` itself can compile.

`syntax::print` is the reverse direction — a precedence-aware
pretty-printer back to source text `parse` accepts, assigning each binder
a fresh name by nesting depth (`v0`, `v1`, ...) since `Var`/`Abs` don't
carry names. It round-trips (`parse(print(t))` hashes identically to `t`,
a strictly stronger check than "looks plausible") for every well-scoped term.
Unary minus on an integer literal parses as a negative literal (`-5` is
`Lit(-5)`, as in OCaml), so negative literals round-trip exactly too;
`print` parenthesises one where unary minus would otherwise bind
differently (`f (-2)`, since `f -2` is the subtraction `f - 2`).

`src/bin/repl.rs` is a small interactive REPL built on `syntax::parse`/
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

## What's actually proven, and what isn't

This is stated precisely because it would be easy to overclaim here.

- **Straight-line (non-recursive) terms**: `proof.rs` builds one kernel
  proof covering *every* input. `lower_wat.rs`'s instruction emission and
  `eval.rs`'s evaluation recurse over this fragment in exactly the same
  shape, so the proof is `refl` — an honest witness that a stack-based and
  a tree-walking evaluation of side-effect-free code compute the same
  value by construction, not a shortcut.
- **Recursive terms, tail or not** (`gcd`'s `loop`, factorial's or naive
  Fibonacci's plain `call`): proven two ways. `prove_tail_recursive_call`
  validates one *execution* — for one specific call, the proof follows
  the interpreter's actual execution trace, symbolically composing each
  step's new parameters (recursing into non-tail self-calls too, wherever
  they sit), until it reaches a base case; a genuine per-call certificate,
  checked by the kernel, but not a universal theorem. Deliberately *not*
  called translation validation: that term means validating one
  *compilation*, whose success covers every input — see `proof.rs`'s
  module docs for why the distinction is the whole point here.
  `prove_tail_recursive_universal` goes further: it postulates an
  inductive "evaluates-to" trace family `Ev(params, v)` (the same
  "postulated inductive family" pattern `Int` itself uses) with one
  constructor per leaf of `body`'s decision tree — `body` can be an
  arbitrary tree of nested `If`s, and each leaf can itself contain any
  number of self-calls combined arithmetically (zero for a base case, one
  in tail position, or several — e.g. Fibonacci's `f(n-1) + f(n-2)`), even
  when some of those self-calls sit inside a further `If` nested in the
  leaf itself, not just as the whole body of some branch — either purely
  arithmetic (e.g. `n + (if c then f(n-1) else f(n-2))`), or choosing
  between two `Clo`-typed values (e.g. a self-call argument
  `f(n-1, if c then g else h)`, via `ite_clo`, same as `prove_closure_expr`
  below) —
  together with a recursor obeying the same universal-motive shape as
  `kernel::WRec`, and uses real induction on that recursor to prove
  `loop_val(params, v, e) = v` once, for every `params` and `v`, not per
  call. Each leaf's constructor is gated by the *conjunction* of
  hypotheses that `cond` denotes to whichever value selects that branch at
  every ancestor `If` on the way to it — without that, a leaf's
  constructor would make `Ev(params, v)` trivially inhabited for *any*
  `params` regardless of `cond`, which isn't what "the trace starting at
  `params`" is supposed to mean. Recombining a leaf's induction hypotheses
  (for leaves with more than one self-call) uses `kernel::cong_n`, an
  `n`-ary congruence lemma built from `cong1`/`trans_proof`; a leaf with
  zero or one (tail-position) self-calls is the special case where that
  reduces to the identity/no-op it always was. This is a *reusable lemma*,
  not itself a per-input guarantee: instantiating it at a concrete
  `params` needs an actual `Ev`-witness built by following `cond`'s real
  value at each step (`prove_tail_recursive_instance`, via
  `build_ev_witness`/`eval_and_prove`), grounded in one postulated axiom
  per distinct concrete primitive application the trace performs
  (`ArithPostulates::assume_prim_fact` — a postulated operator has no
  built-in computation rule, so a witness for one call has to assume each
  concrete fact it needs, the same pattern `Int` itself is postulated
  under). Covers any number of self-calls per leaf, including genuinely
  branching ones (Fibonacci's two self-calls) — `build_ev_witness` always
  derives *internally* in terms of the canonical literal params for a call
  (trivially self-consistent, `refl`-provable, and identical regardless of
  which call site reaches a given concrete argument tuple), memoized by
  concrete args (`memo`, a real DP table: without it a branching leaf
  re-derives every shared subproblem from scratch, exactly mirroring the
  interpreter's own unmemoized exponential call count — `f(5)` rebuilt once
  via `f(7)`→`f(6)`→`f(5)` and again via `f(7)`→`f(5)`, and so on
  recursively). The one place the canonical form doesn't already match what's
  needed is where a recursive call's result becomes an argument to *its*
  caller's own `Ev` constructor (which expects the *actual denoted call
  argument expression*, e.g. `n-1`, not just its value — postulated
  operators have no built-in reduction, so `Id`/`def_eq` can't equate
  `sub_ref(8,1)` with `lit_ref(7)` on their own): the caller recasts the
  canonical witness via `kernel::sym` + `kernel::cong_n` + `kernel::transport`
  (congruence for `Ev` over the params, then transport along the resulting
  type equality) — two new, general-purpose kernel primitives, not a
  special-cased hack, following the same pattern as `cong1`/`trans_proof`.
  Building this surfaced a real, previously-latent bug in `cong1`/`cong_n`
  themselves: they silently assumed the function being reasoned about had a
  codomain equal to its domain type (every existing caller happened to
  satisfy that), which broke the moment this needed `Int^arity -> Sort(0)`
  (`cong1` now takes an explicit `b_ty`). Per-call instantiation for a
  branching leaf is now also fast. Profiling `fib(8)`'s instance proof
  found `shift` dominating by three orders of magnitude, with the same
  subterm reshifted by the same amount repeatedly. A scoped shift cache
  (`with_shift_cache`, engaged from a dry run of the instance) won ~2x for
  a while. The reshifts turned out to come from `subst_top` substituting
  eagerly, shifting its argument at every binder crossed. It now
  substitutes in one pass (`RELATED_WORK.md` §53), which made `fib(8)`'s
  instance about 18 times faster, and the cache, now a net loss, is gone
  (§54).
- **Closures combined with self-recursion, in `prove_tail_recursive_universal`**:
  covers a self-recursive function whose own parameters may be
  `Clo`-typed — threaded through the recursion unchanged, or called via
  `apply_k` within a leaf or a self-call argument — e.g. "iterate a closure
  `n` times": `rec f n g x = if n<=0 then x else f(n-1, g, g(x))`, a shape
  `compile.rs` already compiled (its own `infer_closure_arities`/
  `build_node` machinery is generic over self-recursion vs. not) but that
  had no proof strategy at all before this. This part needs only `Clo`/
  `apply_k`, reused directly via `ClosurePostulates: Deref<Target =
  ArithPostulates>`, which lets the whole induction pipeline (`Ev`,
  `loop_val`, the congruence/transitivity chaining) keep calling every
  plain-arithmetic postulate method unchanged. `prove_tail_recursive_instance`/
  `_with_instances`'s own per-call specialization still declines whenever
  any parameter is `Clo`-typed (there's no way to represent a closure value
  as the concrete `i64` its model needs), but that's the weaker,
  sample-oriented proof — the *theorem* itself (what `jit.rs`'s
  `kernel_verified` actually depends on) covers every input regardless.
  Caught a real bug while building this: `ClosurePostulates::apply_ref`'s
  lazy-postulate memoization was designed for `prove_closure_expr`'s own
  usage, where the postulate context only ever grows; here, the induction
  machinery repeatedly pushes-then-rolls-back the same scratch space, and
  `apply_ref`'s *first* call for a given arity, triggered from inside one
  of those temporary scopes, memoized a position that then got rolled
  back while the memo entry stayed — silently going stale. `kernel::check`'s
  own final re-verification caught it immediately (a lambda-domain
  mismatch), not a silent acceptance; fixed by pre-pushing every needed
  arity once, before any temporary scope gets the chance, and confirmed
  via a dedicated regression test (mixed `Clo`/`Int` parameters, needed
  since the bug isn't observable when every parameter happens to be
  `Int`) that fails the same way when the fix is reverted (the pre-push
  and `apply_ref` itself are both removed in stage 4: a push inside a
  scope stopped panicking, and `clo_ty` no longer pushes, so there is no
  memo entry left to go stale, `RELATED_WORK.md` §72).

  A self-call *argument* may also genuinely *create* a closure and call it
  right there, e.g. `f(n-1, (\y. acc+y)(n))` — exactly the shape
  `compile.rs`'s own `self_recursion_creating_a_fresh_capturing_closure_every_iteration_compiles`
  test and `capturing_closure_loop` benchmark already exercise, previously
  compiled but never proven. `denote_closure_typed` (the self-call-argument
  denotation `new_params_for` uses) mirrors `denote_closure`'s own
  `Term::Abs`/`Term::Rec` handling almost verbatim, now that the induction
  pipeline's own postulate-and-combinator bookkeeping is a full
  `ClosureCombinators` (not just `ClosurePostulates`) — registering a
  combinator, calling one directly, or partially applying one (still never
  a *recursive* root, matching `pap_ref`'s own restriction) all reuse the
  exact same methods `prove_closure_expr` does. A leaf's own *top-level*
  expression gets the identical treatment (`denote_with_placeholders`/
  `find_self_calls`, widened the same way) — e.g. `(\y. n+y)(5) + f(n-1)`,
  a closure-call's result combined arithmetically with the recursive call
  directly, not nested inside any self-call's own argument list. Caught
  the *same class* of staleness bug a second time, in a new place:
  `register`/`call_ref`/`pap_ref`, and transitively `mk_env_ref`/`env_ty`
  for a capturing one, are all lazily memoized exactly like `apply_ref`,
  and could just as easily be triggered for the first time from inside a
  temporary scope. Since these registrations depend only on a combinator's
  hash and a capture *count* — never the actual parameter values —
  `prime_closure_postulates` pre-triggered every one a self-call argument
  *or a leaf's own expression* would need via a lightweight structural walk
  (no parameter values needed at all), the same upfront-priming fix
  widened to cover closure creation, not just a call through a parameter —
  removed in stage 4, once a push inside a scope stopped panicking
  (`RELATED_WORK.md` §72).
  Also honestly scoped: the *instance* (per-call) specialization remains
  untouched and still rejects a self-call argument or leaf expression that
  creates a closure — `kernel_verified` doesn't depend on that, so this
  doesn't weaken what actually gets verified, only what gets additional,
  call-specific evidence.
- **Closures, non-capturing, capturing, and partially applied**: `prove_closure_expr` gives a
  closed, non-recursive closures term one kernel proof covering every
  input, the same `refl`-on-a-shared-translation argument `prove_pure_expr`
  makes for straight-line arithmetic — nothing here evaluates anything
  concrete, so it needs no `assume_prim_fact`-style grounding either. A
  closure value is postulated opaque (`Clo : Sort(0)`, `Int`'s own
  "postulated type" pattern). Calling one *through a parameter*
  (`call_indirect`) goes through `apply_k : Clo -> Int^k -> Int`, one per
  distinct arity actually used that way — unaffected by whether the
  underlying closure captures anything, the same way `lower_wat.rs`'s own
  `call_indirect` dispatch doesn't need to know either. A combinator's own
  *body* is never unfolded or denoted (no walk over every registered
  combinator the way `compile::build` needs): a *non-capturing* one gets one fixed
  `Clo`-typed constant (`combinator_value`, referenced by identity) and one
  signature-specific `call_h : T_0 -> .. -> T_{k-1} -> Int` for a direct
  call — needed because a combinator like `twice` takes a mix of closure-
  and `Int`-typed arguments, which the uniform `apply_k` can't express. A
  *capturing* one can't use one fixed constant honestly — `compile.rs`
  builds a fresh environment at every creation site, so the same
  combinator denotes differently depending on where it's referenced — so
  instead `mk_clo_h : Env -> Clo` (a function of the environment) and
  `call_h : Env -> T_0 -> .. -> T_{k-1} -> Int` (environment prepended,
  mirroring `lower_wat.rs`'s own `$env`-first calling convention; a
  lambda-lifted combinator gets the same values as separate parameters), where
  `Env : Sort(0)` is postulated once *per capture signature* (`capture_sig`
  — which slots are `Clo`-typed, which are `Int`; shared across every
  combinator whose captures match that exact signature, the same way
  `apply_k` is shared by arity) with constructor `mk_env : T_0 -> .. ->
  T_{n-1} -> Env`; `build_env_expr` builds the actual environment argument
  fresh at each creation site, mirroring `lower_wat.rs`'s
  `push_closure_env` at the proof level — including a `Clo`-typed capture
  (e.g. capturing a closure-typed loop-carried parameter), not just `Int`.
  Scope, honestly: the *main*, top-level term must still
  be non-recursive (proving a self-recursive function's own body is
  `prove_tail_recursive_universal`'s job, not this one's — see its own
  row above); every `If` branch must denote as `Int`, or *both* as `Clo`
  (via `ite_clo : Int -> Clo -> Clo -> Clo`, postulated lazily since a
  term never choosing between two closures shouldn't pay for it) —
  reachable both when the `If`'s own result is used as a value (an
  argument to a closure-typed parameter, say) *and* when the `If` is a
  directly-called literal lambda's own top-level body: `call_ref`'s
  postulated return type is no longer a blanket `Int` assumption
  (`combinator_return_type` classifies it structurally, per `Hash`, once
  — see the "Future work" section below for how), so a combinator whose
  own body resolves to `Clo` gets an honest proof whether it's used as a
  bare *value* or *called* directly (including over-applied — see
  `lower_wat.rs`'s row above and its "Over-application" docs); and for a capturing
  combinator specifically, each captured value must resolve *directly* to
  one of the calling function's own parameters, freely `Int`- or
  `Clo`-typed (`Env`/`mk_env` keyed by the whole capture *signature*, not
  just a count, so a mixed-type environment gets its own honestly-typed
  postulate). A captured value that's itself a capture of the *calling*
  scope isn't a deferred restriction at all — it can't arise: a call is
  always postulated opaque (this fragment never enters a registered
  combinator's own body), and `compile::peel` always folds consecutive
  `Abs` layers into one combinator before it's ever registered, so there's
  no way to encounter one combinator's own body containing *another*,
  separately-registered one — every capture list is always relative to
  the one flat ambient scope currently being denoted. Caught a real bug while building this:
  `ClosureCombinators::call_ref`'s own type construction read `int_ty`/
  `clo_ty` in a loop *before* possibly pushing a fresh `Env` postulate
  afterward, silently invalidating those earlier reads — the same
  staleness class `Anchored` existed to prevent (removed in stage 4,
  `RELATED_WORK.md` §72), just inside one function's own type construction
  rather than across `denote_closure`'s recursive calls. Caught by the `#[cfg(debug_assertions)]` `debug_assert_has_type`
  checks on the very first test exercising a direct call to a capturing
  combinator, before it could reach anything outside this module. A
  literal lambda applied to *fewer* arguments than its own arity (a
  partial application, `compile.rs`'s own `register_partial_app`) also
  gets a value, `mk_pap_h_k : T_0 -> .. -> T_{k-1} -> Clo`, postulated once
  per `(h, k)` pair the same way `register_partial_app` itself dedups —
  the `k` supplied arguments are ordinary call-site subexpressions, denoted
  the normal recursive way rather than through any `Env`-style
  machinery, which makes this piece simpler than the capturing-closures
  one above. Now covers a *capturing* root too, mirroring `lower_wat.rs`'s
  `Lowering::pap_env`: when the root captures, `mk_pap_h_k`'s postulated
  type takes the root's own `Env` as an extra leading parameter
  (`Env -> T_0 -> .. -> T_{k-1} -> Clo`, the same environment-first
  convention `call_h` uses), and every call site builds that environment
  via `build_env_expr` and prepends it to the supplied arguments. Caught
  the same class of indexing bug this fragment already had one
  example of: the postulate's own parameter types must be sliced from the
  *last* `k` entries of `h`'s `param_types` (the first-`k`-applied
  positions), not the first `k` — an initially-mis-drafted `param_types[..k]`
  slice, caught before being written by re-deriving `call_ref`'s existing
  wrap-order convention, and independently confirmed by a regression test
  built specifically to exercise it (mixed `Clo`/`Int` parameter types,
  where the two slices actually disagree — `add`'s own two `Int`
  parameters can't tell them apart). A combinator called or used as a bare
  value may itself be self-recursive (`Term::Rec`, not just `Term::Abs`
  — e.g. `let fact = rec f n = .. in fact 10`, or a direct `fact(10)`) —
  `register`/`call_ref`/`param_types_for` never look inside a combinator's
  own body regardless of whether it recurses (a call is always postulated
  opaque), so this needed only a wider match pattern, no new proof
  machinery; `compile::peel`/`compile::free_vars`/`compile::infer_closure_arities`
  were already generic over `is_rec` (`prove_tail_recursive_universal`'s own
  fragment already relied on that). `pap_ref` now covers a self-recursive
  root too, the same way: `compile.rs`'s `register_partial_app`/
  `lower_wat.rs`'s `emit_pap_wrapper` never special-cased `is_rec` either (a PAP wrapper only
  ever forwards a static call to its root, indifferent to whether that
  root's own codegen happens to loop), so `pap_ref`'s own extra `is_rec`
  check was the only thing left rejecting it. Widening the capturing-PAP case
  surfaced a real bug in `prime_closure_postulates`'s own pre-priming pass:
  its partial-application branch primed `pap_ref` but not the transitive
  `mk_env_ref` a capturing root's `build_env_expr` call also needs, so
  that lazy push could still happen for the first time from inside a
  rolled-back `params_and_close_typed` scope — the exact staleness class
  this whole pre-priming mechanism existed to prevent (both the priming
  pass and the scope-open panic it guarded against are gone as of stage 4,
  `RELATED_WORK.md` §72), caught by
  `compile_fuzz`'s random-term fuzzing (not by any hand-written test) via
  a `debug_assert_has_type` panic in `denote_closure_typed`'s own partial
  application case.

Installing a compiled form takes three checks. The term must be simply
typed (`typing::well_typed`; compiled code can't tell an `Int` from a
closure, RELATED_WORK §38). `jit.rs` runs the candidate against the
interpreter on a battery of sample inputs, *and* requires `proof.rs` to
have produced a kernel-checked theorem covering every input. A term that
passes the samples but has no such theorem is cached as
`NoUniversalProof` and served by the interpreter from then on
(`Stats::declined_no_universal_proof`).

The last two cover different things, which is why both are required.
The sample battery is the only check that touches the WAT wasmtime
actually runs. The kernel theorem is the only one that says anything
about inputs outside the battery — but it is stated over `proof.rs`'s
`denote`, which *models* the compiler (`build_node` and the `lower_wat`
templates) rather than reading its output.
The pair is strictly stronger than either alone, and still short of
end-to-end soundness.

What counts as "a theorem covering every input" is reported by
`JitEngine::proof_strength` as a `ProofStrength`:

- `Universal` — `prove_pure_expr`, `prove_closure_expr` or
  `prove_tail_recursive_universal`: one theorem covering every input. This
  is genuinely stronger than the sample battery. Every input means every
  `Int`, which is all the JIT passes: a theorem that types a called
  parameter as a closure doesn't count (RELATED_WORK §42).
- `Samples` — the `prove_tail_recursive_call` /
  `prove_closure_expr_instance` fallbacks: a real kernel-checked `Id`
  proof, but built *per concrete call*, once for each vector in
  `sample_arg_vectors`. That is precisely the finite set `verify()`
  already checked, so it is not additional input coverage at all — it
  says nothing about an argument outside the battery. (At arity 0 the
  battery *is* the entire input space, so a per-call certificate there is
  classified `Universal`, which it genuinely is.)

`is_kernel_verified` means `Universal` specifically, and so does the
installation gate. A `Samples`-only term would otherwise serve arbitrary
`i64` arguments on the strength of certificates covering nine sampled
points, which is the whole reason the gate exists.

The price is real and worth stating plainly: the JIT is now withdrawn
from the inconsistent-arity curried-dispatch shapes the `Samples`
fallbacks exist for — the capability `compile.rs` went to genuine
trouble to support — whenever they take arguments. A closed (arity-0)
one still installs, since its one certificate covers its one input, but
only while its trace fits the 200-step budget. Measured against this
repo's own corpus: zero demo terms, two tests, and one benchmark, which
now runs its loop at 150 iterations instead of 20,000 to stay installed
(§30 of `RELATED_WORK.md`). It is a capability regression, and the way to undo it is to widen the universal
fragment rather than to relax the gate. See §28 of `RELATED_WORK.md` for
what that would take.

## Benchmarks

`benches/` has two [criterion](https://docs.rs/criterion) suites (`cargo
bench`, or `cargo bench --bench execution` / `--bench proofs` for one):

- `execution.rs` — interpreter vs. JIT, cold (compile + verify) vs. warm
  (cache hit), for a non-tail-recursive term (naive `fib`), a
  tail-recursive one (`gcd`, compiled to a loop), and straight-line
  `factorial`. Shows both the steady-state speedup and how much of it the
  one-time compile+verify cost eats into — `fib`'s cold-compile cost
  includes building its (two-self-call) universal proof. That number,
  29 ms, idle, on 2026-09-25, also included 3 concrete instances of the
  theorem, which `JitEngine::prove_instances` now leaves off by default
  (`RELATED_WORK.md` §73; it is 12.8 ms at fbc988b, §74, and 6.1 ms once `verify`
  stopped interpreting `fib(20)`, §71; it was about 140 ms
  before `subst_top` substituted in one pass, `RELATED_WORK.md` §53; ~15ms with
  no kernel proof involved at all); the warm (cached) case is unaffected
  either way, since none of this runs again for a hash already in the cache.
  Also `capturing_closure_loop` — a tail-recursive term that creates and
  immediately calls a fresh capturing closure every iteration, isolating
  the closure-conversion path's own cost (the bump allocator, not
  `call_indirect`'s unpacking). Building this benchmark surfaced a real
  bug, not just a number: warmed up, it ballooned to several GB and never
  finished within criterion's default sample window, because the bump
  allocator's pointer was never being reset between the many separate
  calls this cache makes to one compiled instance (see `jit.rs`'s table
  row above) — fixed, and now warm calls (20,000 iterations each) run at
  ~87µs total with memory staying bounded regardless of call count
  (about 7µs since closure specialisation, `RELATED_WORK.md` §37). Also
  `partial_application_loop`
  — the same idea for the compile-time partial-application desugaring
  (`register_partial_app`/`Lowering::pap_env`): each iteration partially
  applies a literal lambda and completes it through a wrapper, so the
  synthesized wrapper combinator compiles once but its environment (the
  partially-applied function's own, empty, environment plus the
  newly-supplied argument) gets allocated fresh every time. Ran clean —
  no repeat of the capturing-closure bug, memory stays bounded across
  250k+ warm iterations — but noticeably slower than a plain capturing
  closure's warm call (~194µs vs. ~87µs, both 20,000 iterations, before
  §37's specialisation removed most of both: 8µs vs. 7µs now), the expected cost of the
  extra indirection: creating the underlying function's own environment,
  then the wrapper's own, then a call through the wrapper on top of the
  real one. Also `closure_typed_loop_carried_parameter_loop` — the
  opposite shape from `capturing_closure_loop`: a closure-typed
  *parameter* (`inc`, non-capturing) threaded through every iteration and
  called via `call_indirect` each time, rather than a fresh closure
  created per iteration, isolating `call_indirect`'s own unpacking cost
  from closure-conversion's allocation cost. On this machine, warm calls
  (same 20,000 iterations) run at ~56µs, cheaper than either loop above (no
  environment to build at all, every iteration). The self-recursive function itself
  (`prove_tail_recursive_universal` covers a closure-typed loop-carried
  parameter, see "Proof strategies" above) gets the universal theorem,
  checked directly against it — but since a `Clo`-typed parameter can't be
  supplied through `jit.apply`'s plain-`i64` args from the outside, the
  benchmark itself bakes an initial closure in and calls through a
  wrapper, and `is_kernel_verified` on *that* wrapped term actually
  reflects `prove_closure_expr`'s own, separate "self-recursive combinator
  called directly" postulate (opaque either way) rather than the
  universal theorem — an honest distinction, not a weaker guarantee:
  either way it is a theorem over every input, which is what the
  installation gate requires.
- `proofs.rs` — the cost of building each kind of kernel proof from
  `proof.rs`: one `refl` for a straight-line term, one relational
  (per-execution) proof per call, and the one-time universal
  proof. Includes a direct N-relational-calls-vs.-one-universal-proof
  comparison, since that crossover is the actual argument for building the
  universal proof at all — on this machine it lands around 150-200 sample
  points (a universal proof ≈ 5ms once vs. ≈ 25µs per relational call), so
  which is cheaper depends entirely on how many sample points
  `jit.rs` would otherwise verify against. Also `closures_fragment_proof`
  — `prove_closure_expr`'s own cost across the closures fragment's shapes,
  none of which touch `build_universal`'s induction machinery at all (the
  top-level term must be non-recursive for this fragment): on this
  machine, `twice_inc_5` (non-capturing, the same term `main.rs`'s own
  demo uses) is the cheapest at ~10.3µs; a directly-called capturing
  closure costs ~14.4µs (the extra `Env` value); a non-capturing partial
  application ~11.8µs; a capturing one ~21.8µs (paying for both the PAP
  wrapper postulate and its own `Env`, on top of everything the
  non-capturing PAP case already does). Also
  `closure_typed_recursion_universal_proof` — `prove_tail_recursive_universal`'s
  own cost for a closure-typed loop-carried parameter (`iterate`'s
  shape, see the closures-fragment table row above), which unlike
  `closures_fragment_proof`'s own group *does* go through
  `build_universal`'s full induction pipeline (`denote_closure_typed`, not
  just `denote_closure`): at ~13.7ms, noticeably more than the same 2-leaf
  shape's plain-arithmetic counterpart (`gcd_2_leaves`, ~9.0ms above) —
  the closure-typed pipeline's extra bookkeeping costs something even on
  a term, like this one, that never actually creates a closure inside the
  loop.

## Fuzzing

**Differential**: `tests/compile_fuzz.rs` (`cargo test --test compile_fuzz`) generates
random terms — biased toward the closure/capture/self-recursion
interactions two real indexing bugs turned up in earlier, hand-derived
rather than found by any test failure — and checks that `jit::JitEngine`
(compiled, whenever `compile.rs` accepts the term) and `eval::apply_term`
(the reference interpreter) agree, across a battery of argument values
per term, not just the fixed small sample set `jit.rs`'s own internal
`verify()` checks before trusting a compile. Every `gen_program` term is
built to be well-typed on both readings (a generated closure sub-
expression always gets fully resolved back to an `Int` before it's used
anywhere an `Int` is expected), so a mismatch here means a genuine
divergence, not one side being fed a value it doesn't know how to
interpret. A tiny deterministic PRNG (splitmix64, no new dependency),
seed-scanned rather than relying on one lucky draw — a failure prints the
seed and argument trial that triggered it. Currently: 1000 seeds × 12
argument trials each, ~99% of generated terms actually compile (the rest
fall outside the fragment by construction, e.g. curried-application
ambiguity), zero mismatches found so far. A separate test wraps a term
that goes wrong (ill-typed, or a closure of the wrong arity) in a branch
taken only at an input no sample reaches, in plain functions, loops and
recursion, so only the JIT's static gates
(the type check and the universal-proof requirement) can keep it out;
disabling either one fails it (RELATED_WORK §41).

One of the four program shapes it picks from, `gen_closure_typed_recursive`
(`rec f g n x = if n <= 0 then x else f(g, n-1, (g x) OP payload)`), is
also the only way this fuzzer's random bodies ever reach `proof.rs`'s
closure-typed-parameter pipeline directly: wrapping a fresh initial
closure in so the term is runnable through `jit.apply` (there's no way to
hand a real `Clo` value in through a plain-`i64` arg otherwise) means
`jit.rs`'s own `kernel_verify` cascade is satisfied by `prove_closure_expr`'s
opaque "self-recursive combinator called directly" postulate before it
ever reaches `prove_tail_recursive_universal` — so the test checks the
bare self-recursive combinator against `prove_tail_recursive_universal`
directly too, on every trial that generates this shape (~25% of seeds).
This generator's `payload` can itself be a `gen_closure_block`, so it
sometimes combines a loop-carried closure *parameter* with a second,
independently created-and-called closure in the same self-call argument —
a shape nothing else here produces. `gen_tail_recursive`'s own
`gen_closure_block` payload is what originally surfaced the
`prime_closure_postulates`/`mk_env_ref` staleness bug documented in "Proof
strategies" above, this fuzzer's first genuine catch (not by any
hand-written test) — `gen_closure_typed_recursive` widens the same kind of
coverage to a recursion shape that generator can't produce at all.

The same file's second test, `compile_rejects_out_of_scope_terms_cleanly`,
checks the complementary property: terms deliberately built *outside* the
fragment must always come back `None` from `try_compile`, never get
silently accepted and miscompiled — a property the first test's
generator, which only ever produces in-fragment terms, has nothing to
say about. Originally covered both a parameter called with inconsistent
arities and a genuinely unbound variable, verified to actually have teeth
(not just vacuously passing) by deliberately weakening the
inconsistent-arity checks (`scan_for_closure_calls`'s and
`compile_node`'s, now `build_node`'s, own per-call-site check) together, which immediately
failed the test on the first seed, as expected. The inconsistent-arity
case moved out once `try_compile` stopped rejecting that shape
altogether (see the curried-dispatch mechanism, "Generic closure
dispatch" in `lower_wat.rs`'s module docs) — its own soundness property (jit.rs's
verification/fallback still agrees with the interpreter for whatever
garbage value such a call site is actually fed) is checked instead by
`inconsistently_called_parameters_still_agree_with_the_interpreter`,
right next to `over_applied_ill_typed_terms_still_agree_with_the_interpreter`,
which already covered the analogous property for over-application; only
the unbound-variable check is left here now. A third generator in the
same file, `gen_over_applied`, covers
a *different* property now that `try_compile` compiles an over-applied
literal lambda's *shape* unconditionally (see `lower_wat.rs`'s "Over-
application" module docs): its own bodies are always plain arithmetic, never a
further closure, so every term it generates is genuinely ill-typed;
`over_applied_ill_typed_terms_still_agree_with_the_interpreter` confirms
`jit.rs` declines every one of these as ill-typed (`typing.rs`, §38 of
`RELATED_WORK.md`) and falls back to the interpreter, rather than
`try_compile` rejecting the shape outright.

The same file's `specialisation_is_checked_and_preserves_meaning_on_random_terms`
extends this fuzzer's generators (adding `Div`/`Mod`) to check `specialise.rs`
and `spec_check.rs` (§37 of `RELATED_WORK.md`): every one of 1000 random
terms is specialised and checked, `spec_check::check` must accept every
trace produced, and `eval` on the original and specialised term must agree
exactly on the sample arguments — including which error variant, not just
whether one occurred. One seed in five is an open term
(`gen_unbound_variable`, bare or under a redex): it must get the empty
trace, and the checker must reject it. Every term also goes through
`compile_specialised`, and its fragment is run directly (no `verify()` in
between) against `eval` on the same arguments, for every term
`typing::well_typed` accepts (compiled code assumes well-typedness, and
`gen_redex_rich` can use a closure as an `Int`). For those terms it also
checks type safety: `eval` must never give `TypeError`, `NotAFunction` or
`UnboundVariable`. And `JitEngine` must agree with `eval` on every term,
typed or not (§38 of `RELATED_WORK.md`). 645 of the 1000 seeds specialise, 564 compile
(213 from `h'`), and 4400 compiled runs are compared. Verified test teeth by two planted bugs: a
specialiser bug that produces a wrong term is caught by `spec_check`
rejecting its trace; making both the checker and the specialiser agree on
an unsound step (treating a `Prim` expression as a value) passes the
certificate check but is still caught, by the `eval` comparison
disagreeing on a `Div` term.

**Robustness**: `tests/kernel_fuzz.rs` fuzzes a different layer entirely: `kernel.rs`'s
own type-checker, directly, with no well-typedness discipline on the
generated terms at all (unlike `compile_fuzz.rs`, whose terms are built
to be meaningful to both the interpreter and the compiler). Random `Expr`
trees — `Var`s sometimes genuinely in scope, sometimes deliberately just
past it, sometimes wildly unbound; `Sort`s occasionally at `u32::MAX` —
are checked only for one property: `infer`/`check`/`typecheck` never
panic, whatever nonsense they're asked to type-check; almost every
generated tree is simply rejected with an ordinary `Err`, which is the
expected, uninteresting outcome. A second test targets `check`'s own
top-level `Lam`-against-`Pi` special case directly (an independently
generated lambda checked against an independently generated `Pi`), since
nothing built on `typecheck` alone (a bare `infer` call at the root) ever
reaches it. This fuzzer's first run caught a real bug immediately: `infer`'s
`Sort(i) => Sort(i + 1)` case overflowed (a checked-in-debug-builds panic,
not a clean type error) for `Sort(u32::MAX)` — fixed with `checked_add`,
returning an honest `Err` ("universe overflow") instead. Verified test
teeth by reverting the fix: the fuzzer catches it again immediately (seed
16 out of 5,000, on the very first run at that seed count). Stress-tested
at 100,000 seeds (release) and 30,000 (debug, where the now-fixed overflow
check would have fired) with zero further failures before settling back
on the file's own 5,000-seed default.

**Soundness**: `tests/kernel_soundness_fuzz.rs` fuzzes a different property
than `kernel_fuzz.rs`'s own crash-safety — the one every "kernel-checked
equivalence proof" this project produces actually rests on: given two
postulated constants of the same type with *nothing* in the context
relating them, `kernel::check` must never accept *any* term as a proof
that they're propositionally equal (`Id(A, a, b)`). This is deliberately
not "is `a` `def_eq` `b`" — a *postulated* equality is legitimately
`Id`-provable without being computationally equal at all (that's the
whole point of postulating axioms rather than deriving everything from
nothing) — the property under test is narrower and sharper: can the
kernel be talked into deriving a false proposition from an unrelated
pair? Two strategies, both checked against the same unrelated pair's
claim: pure random generation (as `kernel_fuzz.rs`'s own generator does),
and — the sharper one — random single-point mutation (a structural
subtree swap, or a wildly different `Var`/`Sort` substituted in) of a
proof that's genuinely valid for a *different*, actually-related pair,
since starting from a well-typed skeleton is far more likely to land
near a real checker bug than blind generation is. Verified test teeth by
deliberately injecting two different bugs and confirming each is caught:
an off-by-one in `ctx_lookup`'s own de Bruijn shift (too blunt — it broke
typechecking universally, caught only by this file's own "the seed pool
itself is valid" sanity check, not the soundness property specifically)
and, more precisely, weakening `check`'s final comparison to only compare
an `Id`-type's own domain when both sides are `Id`-typed, ignoring the
two endpoints entirely — caught immediately by both dedicated soundness
tests (seed 7 and seed 97 respectively, out of 20,000), while the sanity
check kept passing, confirming these tests actually discriminate a real,
narrow false-equality bug rather than merely reacting to wholesale
breakage.

**Round-trip**: `tests/syntax_fuzz.rs` fuzzes a third property, on a third
layer: `syntax.rs`'s own `parse(print(h)) == h` (exact content-hash
equality) for a random, well-scoped term across every constructor
(`Prim` with all eight operators, `If`, `Abs`, `App`, `Rec` of random
arity), with random right/left nesting — the same kind of shape
`syntax.rs`'s own hand-written tests cover with a handful of hand-picked
precedence traps (a right-nested subtraction a left-associative parser
would never itself produce, a nested comparison, an application argument
that's itself an application), generated far more broadly than anyone
would think to hand-pick. Deliberately stays inside `print`'s own
documented contract — every generated `Var` is genuinely bound (`print`
isn't written to handle an out-of-scope one; it isn't even a `Result`-
returning function) and every literal is non-negative (the one
documented, accepted round-trip gap, since this grammar has no negative-
literal syntax at all). Passed clean on its first run and stress-tested
at 200,000 seeds and, separately, depth 10 (up from the file's own
default of 6) with zero failures — confirmed real teeth anyway by
deliberately weakening `print_at`'s own right-hand-side strictness rule
for left-associative operators (`(p, p + 1)` → `(p, p)`, exactly the bug
class `round_trips_arithmetic_with_mixed_precedence_and_right_nesting`
guards against by hand): caught immediately, at seed 22.

## Design notes

- **Why hash-consing, not just a tree**: two independently-built terms that
  are structurally identical hash to the same value, so the JIT cache and
  the kernel's proof cache are keyed by *content*, not by which piece of
  code happened to construct the term.
- **`kernel::Expr`'s recursive fields are `Rc`, not `Box`**: `Expr` is built
  once and then threaded through many `.clone()` calls as it's composed into
  larger proof terms (`proof.rs`'s pre-stage-4 `Anchored` reshifting
  pattern especially, `RELATED_WORK.md` §72, but also plain composition
  like `cong_n`'s per-argument accumulation) —
  with `Box`, every one of those clones was a full deep copy, cost scaling
  with however large the accumulated term had grown by that point, not with
  what actually changed. With `Rc`, `#[derive(Clone)]` clones each field by
  bumping a refcount, so cloning an `Expr` of any size is O(1) and its
  children are genuinely shared. This is deliberately *not* full
  hash-consing — there's no intern table, so two independently-built but
  equal subterms still get distinct allocations — but it removes the real
  cost this crate was paying, worth ~2x on `fib`'s cold-compile time (see
  Benchmarks). On its own it didn't fix branching-leaf instance proofs
  being slow — that cost turned out to live in `shift` (see the next
  entry), not cloning.
- **No `shift` cache**: `kernel.rs` once had a thread-local cache scoped
  around instance proofs (`with_shift_cache`), engaged from a dry run of
  how many nodes an instance visits. It won ~2x on `fib(8)` by recovering
  reshifts that eager substitution caused. Once `subst_top` shifted its
  argument only where used (`RELATED_WORK.md` §53), the cache cost more
  to fill and drop than it saved on every term measured, so it was
  removed (§54), along with its hidden state in the kernel.
- **Why a predicative kernel with exactly these five primitives**: see
  `kernel.rs`'s module docs for the full argument, but briefly — `W`-types
  are load-bearing (not derivable from `Pi`/`Sort`/`Id` alone with
  definitional computation, which an interpreter's hot path needs), and
  bootstrapping finite base types (`Bool`, `Nat`) from nothing hits a real,
  expected wall in a predicative system (a "vacuous eliminator" always
  needs a witness-extractor one universe above what it eliminates into).
  Base types like `Int` are postulated accordingly — the same approach
  real kernels take, not a shortcut specific to this project. `Sigma` is
  the fifth, added separately: `W`'s own children function maps back into
  `W` itself, so it can only stand in for a payload that's *another
  instance of the same inductive type*, not an arbitrary, independently-
  chosen one — a genuine dependent sum needs its own primitive, and a
  Church/impredicative encoding of one from `Pi` alone was rejected for
  the same computation-preserving reason `W` itself was chosen over that
  route.
- **Why sample verification never goes away**: it is the only check in
  the system that touches the WAT wasmtime actually executes. Every
  kernel proof is stated over `proof.rs`'s `denote`, which models
  the compiler (`build_node`, the `lower_wat` templates) rather than
  reading its output, so a theorem covering
  every input still says nothing about a mistake in WAT emission. Sample
  verification is simple, total, and always applicable, so it stays the
  first half of the installation gate regardless of how far proof
  coverage grows — the proof is what extends coverage beyond the
  battery, not what replaces it.
- **Why the per-execution fallbacks stay anyway**: `prove_tail_recursive_
  call` and `prove_closure_expr_instance` certify one concrete execution
  each, which the gate treats as no better than the battery itself. They
  are kept for reporting (`proof_strength`), not for installation. That
  per-execution limit is a property of *these* checks, not of translation
  validation as the literature means it — a genuine per-compilation
  validator's success would cover every input, and building one is a
  route tatic hasn't taken (see §28).
- **`Anchored`, and a staleness bug it doesn't automatically prevent**
  (history; the type is gone as of stage 4, `RELATED_WORK.md` §72): back
  when a postulate's `Expr` reference was a `Var` index, only valid
  relative to the postulate context's length *at the moment it's
  resolved*, `Anchored` reshifted one held across further pushes, but
  nothing stopped code from resolving a plain `Expr` and holding it
  unwrapped instead. That exact mistake caused two real bugs in this
  project (the `Ev`-witness builder, then `denote_closure`), each only
  surfacing as an opaque kernel type-mismatch far from the actual cause.
  Stage 3 made the whole class structurally impossible — `Postulates::get`
  now returns a `Const`, which no push shifts (§69) — so `Anchored` had
  nothing left to do and was deleted. `proof.rs` still has
  `debug_assert_has_type`
  (debug-only, zero-cost in release), called at the return point of every
  function that composes an `Expr` from more than one recursive sub-call,
  to turn a future instance of this bug class into an immediate,
  precisely-located panic instead of a slow bisection.

## Future work

- Combining closures with self-recursion more fully in one proof.
  `prove_tail_recursive_universal` now covers a closure-typed *parameter*
  threaded through recursion, *and* a closure genuinely created and
  called anywhere in the body — a self-call argument (`f(n-1, (\y.
  acc+y)(n))`, the `capturing_closure_loop` shape) or a leaf's own
  top-level expression (`(\y. n+y)(5) + f(n-1)`) alike — and
  `prove_closure_expr` now covers a self-recursive combinator called or
  used as a value from a non-recursive main term (see the table rows
  above). `eval_and_prove`/`build_ev_witness` now cover a concrete
  *instance* proof for the fully-applied case too (`call_eq_ref`, a
  computation-rule axiom postulated once per combinator from its own real
  body via `denote`, then used through `cong_n`/`cong1`/`trans_proof`
  congruence at each concrete call — the same move `build_universal`
  already makes for `loop_val`/`Ev`), as long as the closure created and
  called is a literal lambda whose own body stays in the `Var`/`Lit`/
  `Prim`/`If` fragment (no further nested `Abs`/`App`, which would need a
  fixpoint-queue redesign this module was deliberately built without).
  `eval_and_prove` now also covers the *over-applied* case
  (`AppShape::LitLambdaOver`: `root`'s own saturated call returns a
  further `Clo_k`, then the extra arguments dispatch against it directly
  — a `Clo_k`-typed value is itself the real curried `Int -> .. -> Int`
  arrow type, so no `apply_ref` axiom mediates the call, see
  `RELATED_WORK.md` section 11) for the canonical shape — `root`'s own
  body an `If` choosing between two same-arity literal lambdas (e.g. `f =
  \a b. if 0<a then (\c. a+b+c) else (\c. a-b+c)`, called as `f(a,b,c)`)
  — via two more computation-rule axioms in the same idiom: `clo_eq_ref`
  (a `Clo_k`-typed sibling of `call_eq_ref`) and `apply_clo_eq_ref` (ties
  whichever closure value is concretely produced, called directly, to
  `call_ref`'s own value), plus a small `ite_clo_eq_ref` bridge for the
  concrete branch selection. A *PAP-producing* `root` (`root`'s own body
  a partial application of a further literal lambda `g`, e.g. `f = \a.
  g(a)` for a 2-ary `g`, then over-applied as `f(a)(c)`) is covered too
  now — `clo_eq_ref_pap`, a sibling of `clo_eq_ref_if_tree` sharing
  `clo_eq_ref`'s own dispatch, states `root`'s call equals `pap_ref(g,
  s)` applied to the supplied args' own denoted values, and a new
  `apply_pap_eq_ref` ties that `Clo_k` value, called directly on the
  remaining `k` arguments, down to a direct call on `g` with all `s + k`
  arguments together (mirroring `apply_clo_eq_ref`'s
  role, but for a partial-application value instead of a directly-
  registered combinator's) — restricted, for now, to `g`'s own params all
  being `Int`-typed. A further-nested `If` inside either branch is
  covered too now — `clo_eq_ref_if_tree` generalizes the original flat,
  depth-1 `If`-between-two-closures construction (`clo_eq_ref_if_between`)
  to an arbitrary-depth decision tree (reusing `DecisionTree`, the type
  `build_universal`'s own arithmetic-fragment tail recursion already used,
  via a new unrestricted classifier rather than that module's own
  comparison-restricted one), with the axiom RHS and the concrete-instance
  resolution both built recursively over the tree instead of in one flat
  step. A *further nested-call-producing* `root` is covered too, for a
  statically-known indirection chain of any depth — `root`'s own body a
  *saturated* call to a further literal lambda `g` whose own saturated
  call is itself `Clo_k`-typed (e.g. `middle = \b. h(b)` a PAP of a 2-ary
  `h`, `root = \a. middle(a)`, over-applied as `root(a)(c)`) —
  `clo_eq_ref_call`, a third sibling of `clo_eq_ref_pap`/
  `clo_eq_ref_if_tree`, states `root`'s call equals `call_ref(g)` applied
  to `args`'s own denoted values, deliberately opaque about `g`'s own
  definition (exactly like `Pap`'s own `g`); concrete resolution
  (`resolve_closure_shape_to_leaf`, generalized from the `IfTree`/`Pap`
  arms `eval_and_prove_call_over` used to inline directly) recurses
  through however many further `Call` links this reaches, each one
  building `g`'s own bridge (`build_clo_call_bridge`, itself a shared
  extraction of what was `eval_and_prove_call_over`'s own `root`-specific
  preamble) and continuing into `g`'s own shape — terminating because
  hash-consing makes the "calls" relation between distinct combinators a
  strict partial order, the same well-foundedness argument
  `combinator_return_type`'s own recursion already relies on. A `Pap`-shaped
  `IfTree` leaf (a branch that's itself a *partially*-applied closure
  creation, e.g. `if c then g(a) else h`) is covered too now —
  `classify_closure_if_tree_leaf` classifies each leaf independently
  (`Abs` or `Pap`, mirroring `clo_eq_ref_pap`'s own classification, keyed
  per leaf instead of per `root`), and `resolve_closure_if_tree`'s own
  return grew a leaf-specific supplied-args prefix so a chosen `Pap` leaf's
  own `g` gets called with its own supplied args *and* the outer
  over-application's extra ones, not just the extra ones. A `Call`-shaped
  leaf (a branch reached only through a further *saturated* indirect call
  to a further literal lambda `g` whose own saturated call is itself
  `Clo_k`-typed) is covered too now — `classify_closure_if_tree_leaf`
  classifies it the same way `clo_eq_ref_call` classifies a root-level
  `Call`, and `resolve_closure_if_tree`'s own return grew an
  `IfTreeLeafResolution::Direct`/`Indirect` split: a `Call`-shaped leaf's
  own further indirection is resolved recursively, via the same
  `resolve_closure_shape_to_leaf` the root-level `Call` arm already uses
  (mirroring it exactly, one level deeper inside an `If`), reusing its
  own already-complete "call with all args" fact rather than building a
  second one. A self-recursive
  `root` (compiled via `Term::Rec`) is covered too now — `clo_eq_ref_if_tree`/
  `clo_eq_ref_call`/`clo_eq_ref_pap` each thread `root`'s own `is_rec` flag
  into `compile::free_vars` instead of hardcoding `false`, since the
  downstream machinery (`param_types_for`, `combinator_return_type`,
  `return_type_of`'s own self-call classification) was already `is_rec`-safe;
  the blanket decline in `clo_eq_ref` was the only thing blocking it, and
  lifting it needed fixing the three sites that would otherwise have
  mis-counted a self-binder as an ordinary capture. No longer open, closed
  out after investigation: a `root` with a `Clo`-typed *parameter* (as
  opposed to `Int`-typed) looked like a missing universal-axiom case, but
  turned out to be two separate findings instead — `clo_eq_ref`'s own
  decline on it is a permanent, correct property of its own construction
  (its one call site, `build_clo_call_bridge`, is only ever reached through
  `eval_and_prove_call_over`, whose own `(i64, Expr, Expr)` return type has
  no way to carry a concrete `Clo` value in the first place, so no path
  that reaches `clo_eq_ref` could ever instantiate a widened axiom there,
  even after actually building one); and the real capability — proving a
  call made *through* such a parameter — was already covered elsewhere, by
  `eval_dyn_direct_call`'s existing per-instance path (its `(Some(_),
  DynDenoted::Clo(e, _)) => e` arm, denoting through `call_ref` exactly as
  `clo_eq_ref`'s own callee-side construction would), confirmed end to end
  by `proof.rs`'s
  `branching_non_tail_self_calls_carrying_an_inconsistently_classified_closure_parameter_get_a_per_instance_proof`
  and `jit.rs`'s
  `a_tail_recursive_loop_compiles_and_is_kernel_verified_once_its_own_closure_parameter_turns_inconsistent`
  — see `RELATED_WORK.md` section 12 for the full investigation and its
  correction. No longer fully open: a callee reached only through a
  captured/parameter variable rather than a further statically-known
  combinator (genuinely unknown at proof-construction time which literal
  lambda underlies it) is now covered per instance — `eval_dyn`'s own
  `Var`-root case (`src/proof.rs`) resolves the concrete `ConcreteClo`
  such a value actually carries regardless of whether it reached the
  frame as a parameter or a capture, the same `eval_dyn`-style tracing
  this paragraph used to name as a hypothetical fix; see
  `RELATED_WORK.md` §9's own "Since covered, per instance" finding and
  `proof.rs`'s
  `a_captured_value_reached_through_an_inlined_call_gets_a_per_instance_proof`.
  `clo_eq_ref`'s own *universal* axiom still can't cover it — that would
  need a real dependent sum (an honest single kernel type for "either
  `Clo_1` or `Clo_2`"), the separate, larger research question §9 already
  scoped out — but that's "sound, not complete", the same standing
  tradeoff this fragment makes everywhere else; doesn't affect
  `kernel_verified`, only weaker, call-specific evidence.
- `prove_closure_expr` now covers an `If` choosing between two closures
  too (`ite_clo`, lazily postulated — see the table row above), when the
  `If`'s own result is used as a *value* — and, separately, `call_ref`'s
  own postulated return type is no longer a blanket `Int` assumption:
  `combinator_return_type` structurally classifies a literal lambda's own
  saturated-call return type (`Int` or `Clo`) once per `Hash`, without
  denoting its body in the usual (postulate-building) sense — well-founded
  since a self-call is always `Int` by this fragment's own convention and
  calling *any* closure value (a parameter, a capture, or another
  directly-called combinator's own result) is too, so the classifier only
  ever needs to look at each combinator's own declared parameters and its
  own `If`/literal-lambda-call shape, never a captured free variable's
  actual type. This closes two previously-open cases at once: a
  *directly-called* combinator whose own body is an `If` between two
  closures (see the table row above), and over-application of a literal
  lambda (`root`'s own saturated call, now denoted via the same
  `call_ref`, dispatched on the extra arguments directly, exactly like
  calling a closure-typed variable — see `lower_wat.rs`'s
  "Over-application" module docs for the compiled-code-level counterpart).
- Widening the compilable fragment further: more primitives. (Capturing
  closures and partial application of a literal lambda — real closure
  conversion, an environment representation, calling a closure reached
  through a captured free variable, a compile-time-desugared synthesized
  wrapper for an under-applied literal — landed, as has over-application
  of a literal lambda — dispatching a saturated call's own result through
  `call_indirect`, the same as calling a closure-typed variable; see
  `lower_wat.rs`'s module docs. A variable called with inconsistent
  arities across sites — a genuinely different, harder problem than
  over-application, since there's no fixed arity to desugar around at all
  — has landed too, via a curried, one-argument-at-a-time dispatch
  mechanism generated once any such inconsistency is found anywhere in
  the compiled fragment; see `lower_wat.rs`'s module docs and
  `TYPES.md`.)
- `prove_closure_expr` now covers *capturing* closures too (`mk_clo_h`/
  `Env`/`build_env_expr` — see the table row above and `proof.rs`'s own
  section docs), including a captured `Clo` value (e.g. capturing a
  closure-typed loop-carried parameter), not just `Int` — `Env`/`mk_env`
  are keyed by the whole capture signature (`capture_sig`), not a count,
  so a mixed-type environment gets its own honestly-typed postulate.
  Each captured index must still resolve directly to one of the calling
  scope's own parameters; a captured value that's itself a capture of
  that scope (`build_read`'s own recursive case, for a function
  that's itself a capturing closure) has no proof-side counterpart, not
  because it's deferred, but because it can't arise here: `denote_closure`
  never enters a registered combinator's own body, and `compile::peel`
  always folds consecutive `Abs` layers into one combinator before it's
  ever registered, so there's no way for this fragment to encounter one
  combinator's own body containing another, separately registered one —
  every capture list is always relative to the one flat ambient scope
  currently being denoted.
- `prove_closure_expr` now covers partial application of a literal lambda
  too (`mk_pap_h_k`/`pap_ref` — see the table row above and `proof.rs`'s
  own section docs), including a *capturing* root: `pap_ref`'s postulated
  type takes the root's own `Env` as a leading parameter (mirroring
  `call_ref`'s own environment-first convention) when the root captures,
  and every call site builds that environment via `build_env_expr` and
  prepends it, mirroring `lower_wat.rs`'s `Lowering::pap_env`, which composes
  a PAP wrapper's own environment with a copy of the root's. Also covers
  partial application of a *self-recursive* combinator, the same opaque-call
  reasoning `register`/`call_ref` already use for a direct call or bare
  value (`compile.rs`'s `register_partial_app`/`lower_wat.rs`'s
  `emit_pap_wrapper` never special-cased `is_rec` either). Over-application (more arguments than
  arity) stays out of scope on both readings.
- The closures fragment's kernel-checked proof now verifies closure
  *arity*, not just structural agreement: `Clo` was a single, arity-blind
  postulate (`TYPES.md` section 6.2's own finding), so an `If` choosing
  between two literal-lambda values of genuinely different arity
  kernel-typechecked despite being unsound. `Clo` is now `Clo_k`, a family
  postulated lazily per distinct arity (`ClosurePostulates::clo_ty`,
  mirroring how a capture signature was already postulated per shape, not
  a global count) — `Clo_k`/`Clo_j` are definitionally distinct whenever
  `k ≠ j`, so `kernel::check` rejects an arity mismatch on its own, for
  every rule that already tracked the correct `k` in Rust (a parameter's
  declared arity, a literal lambda's own peeled arity,
  `combinator_return_type`'s own classification). See `TYPES.md` section 7
  for the full design and
  `a_literal_lambda_picking_between_two_different_arity_closures_is_out_of_scope`
  (`proof.rs`) for the regression test confirming the previously-unsound
  shape is now rejected.
- `prove_closure_expr` now covers a `Clo`-typed *top-level* result too --
  previously hardcoded to require the whole function's own body to denote
  `Int` (`.int()?` at its own entry point), regardless of whether
  everything beneath it already supported `Clo` (an `If` between two
  closures, a bare closure-typed parameter read, ...). Now picks
  `EquivalenceProof`'s own `result_ty` from `denote_closure`'s `Denoted`
  tag directly -- `Int`'s postulate, or the specific `Clo_k` (re-derived
  via `return_type_of` applied to the whole body), covering e.g. `\x. \y.
  x+y` used bare or `\f. if (f 0) then f else f`. See
  `a_whole_functions_result_being_a_closure_now_gets_a_closure_proof`/
  `a_bare_closure_typed_parameter_read_gets_a_closure_proof` (`proof.rs`).
- REPL hint bug (`src/bin/repl.rs`, the `EvalError::TypeError` arm): a
  line that evaluates to a function prints the hint
  ``e.g. `{printed} 1 2` ``, which is invalid syntax whenever the printed
  term is a lambda/`rec`/`if` -- `\x. x + -5` yields `\v0. v0 + -5 1 2`
  instead of `(\v0. v0 + -5) 1 2`. Fix: bracket the printed term there
  (e.g. print it at application precedence).
- The type system, taken as a whole (`RELATED_WORK.md` §44). Five notions
  of type (`typing.rs`, compile's `ArityUse`, the provers' `Denoted`, the
  kernel's `Clo_k`, and `calls_a_parameter`) must agree. `try_compile`'s
  IR has no `let`, so it emits one copy of a shared subterm per use. It
  now declines terms over 16384 nodes as a tree (§47). Most of the cost
  is the kernel, not the IR (§48). `whnf` now keeps its pointer cache
  working and `denote` shares subterms (§49), so one proof went from
  217 to 56 ms. `subst_top` no longer shifts an unused argument (§51),
  which took it to 9.4 ms and the universal-proof benches 2 to 4 times
  faster, and substitutes a used argument in one pass (§53), which made
  the over-application instance proofs about 7 times faster. `def_eq`
  was then about half of an instance proof's `infer` (§55). It now
  skips syntactically equal sides (§56) and compares weak head normal
  forms instead of full ones (§57), which halved `kernel::check` on the
  `fib` instance proofs. `whnf` keeps a stuck term's own pointers, so
  deep stuck spines normalise in linear time (§59), and it remembers
  the pairs `==` found unequal, so a chain that differs only at the
  bottom is compared in linear time too (§61). What's left is a
  per-node constant times the proof's size (§60). The instance proofs
  had almost no sharing, because the witness memo returned shifted
  copies. A prepass now pushes every postulate the witness needs before
  it's built, so memo hits share, which halved `fib(12)`'s instance
  proof (§62). The kernel's `infer` now memoises shared nodes by (node,
  context id), which made that proof 73% faster again and leaves
  unshared proofs unchanged (§63). A spike took `fib(16)`'s instance
  proof from 1.9 s to 19 ms and its DAG from 265k nodes to 10.5k (§64).
  Its stage 1 is built: kernel nodes cache their loose-variable range, so
  `shift` and `instantiate` keep closed subterms by pointer. That made
  `fib(16)`'s build and check each 11% faster and its DAG 14% smaller
  (§65). mimalloc is the allocator: it halves every proof bench and
  speeds up the interpreter by 13% and the cold JIT by 21% (§66). Stage
  2 is built: the kernel types `Const`s from a global environment and
  rejects `Free`s, at no measurable cost, and nothing produces either
  until stage 3 (§67). The kernel now checks that a claim is a type,
  which exposed an ill-typed `Ev` in closure-typed universal proofs
  (§68; it costs universal proofs 11-30%). Stage 3 is built: the proof
  builder emits postulates as constants, which took `fib(16)`'s DAG from
  227k to 10.5k nodes and its build and check from ~150 ms to ~3-4 ms
  each, and made large proofs 44-58% faster (§69), and a scope's
  parameters as free levels, so a leaked parameter fails the check
  (§70). The µs-scale proofs are 51-83% slower across stage 3: checking
  every pushed postulate costs ~4 µs a proof (§69). Stage 4 is built (§72):
  `push_ev_facts`, the closure priming, `Anchored`, and `Params` are gone,
  and a push may now happen while a scope is open. If the proof gate is ever relaxed, the next step
  is a typed IR that `ir::check` checks (§46's B5): it closes the arity
  and Int-vs-closure agreements for compiled code in one place.
