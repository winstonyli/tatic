### v0.7's first steps: the census and the emit spike (2026-11-08)

The questions: how much of the corpus could an emitted-code proof cover with church-bv's wasm machine
(then in church-bv; now `crates/tatic-wasm/src/wasm.rs#Ins`), and can the kernel check an `If (a < b)` program against its source at n = 64?

**Today's install gate proves the model, not the code.** `kernel_verify` (`crates/tatic/src/jit.rs#try_install`) accepts
`prove_pure_expr` (`crates/tatic/src/proof.rs#prove_pure_expr`) for a straight-line term: `refl(denote) : Id(Int, denote,
denote)` over a postulated `Int` with eight bare operators and no axioms. Both sides are the same expression; no
instruction list or WAT is consulted, and `verify()` (wasmtime against eval on samples) is the only check that touches
emitted code. There is no instruction list in tatic: `lower_wat` writes WAT text from the IR tree (`ir.rs#Node`).

**Census (38 terms: 23 in `samples::corpus`, 15 in `test_corpus.rs`).** Measured by running each term through the real
pipeline (`compile_specialised`, the three provers on the compiled term, `JitEngine::apply` at all arguments 3) and
bucketing the instruction kinds of the WAT it emits (patch `docs/superpowers/spikes/2026-11-08-b1-corpus-census.patch`,
run `2026-11-08-b1-census`), against the machine as it stands (Push, Bin, Cmp, Dup, If, Loop, Br, Store, Load; closed
`add`, `sub`, `lt_u`; no locals, no calls, no signed compare, `eq_bv` a `Bool0` rather than a one-bit word):

| class | WAT kinds | terms | needs |
|---|---|---|---|
| A | `local.get`, `i64.const`, add, sub | 5: inc `v0 + 1`, doubling, and three after specialisation: `\v0. v0 + 5`, `3 + 4`, `\v0. 3 + 4 + v0` | parameter reads (`Push i; Load` or a new instruction); `3 + 4` needs nothing |
| B | A plus compares, mul, rem, `if`, `local.set`, `br` | 6: `straight_line`, `5 * 10 + 3` (specialised), gcd, gcd with two base cases, and two loops that specialise to `rec v0 v1 v2 = if v1 <= 0 then v2 else v0 (v1 - 1) (v2 + v1)` | `lt_s`, `le_s`, `eq` as a one-bit word, `mul`, `rem_s`; the four loops also locals and fuelled loops |
| C | calls, `call_indirect`, memory, globals | 26, plus `open_redex_probe`, which does not compile | calls, closure records |

All but 8 of the 37 compiled terms install today; every A and B term installs. The prove_pure_expr fragment is exactly the
five with `pure`: inc, doubling, `straight_line`, `\v0. v0 + 5` and `\v0. 3 + 4 + v0` (the arity-0 constants are
proved by `prove_closure_expr`). So the one straight-line term with a branch or a multiply and a parameter is
`straight_line`; the others are an add chain or a constant. Mul appears in 7 terms, Mod only in gcd, Div in none.

**Spike: the continuation form proves by refl at n = 64; the value form does not.** Patch
`docs/superpowers/spikes/2026-11-08-j1-emit-spike.patch` (a test module in church-bv), runs `2026-11-08-j1-spike-head2`
(HEAD 461fa5f) and `2026-11-08-j1-spike-all` (base c37d273, within 1 ms of these at n = 64). Parameters live in memory: `local.get
$p_i` is `Push i; Load` over `upd 0 a (upd 1 b mu)`. `lt_s x y = lt_u (x ^ m) (y ^ m)` with `m` the sign bit, and `mul`
is `bits_circuit(n, mul_bits)`. The statement for `straight_line` (`\a b. if a < b then a * 2 else b + 1`) is
`run(code) S R k s mu = choose R (lt_s a b) (k (a*2, s) mu) (k (b+1, s) mu)`, closed by `refl`.

| n | inc | `a+a` arm | `a*2` arm | value form | doubling d = 16 |
|---|---|---|---|---|---|
| 8 | 0.4 | 0.9 | 0.7 | FAIL | - |
| 16 | 0.6 | 1.2 | 2.3 | FAIL | - |
| 64 | 1.6-1.7 | 4.9-5.5 | 12.8 | FAIL | 1.7 |

(ms, check only; building the statement adds 8-17 ms at n = 64.) Every control is rejected at n = 8, 16 and 64: arms
swapped, the else arm's add changed to sub, the constant 2 changed to 3, `lt_s` changed to `lt_u`. The value form
(`ite_w (lt_s a b) (a*2) (b+1)`) fails because a symbolic comparison bit is neutral: `ite_w` cannot reduce it, while the
program's `If` reads it through `choose` with the continuation copied into both arms, so the two sides never meet by
conversion. A gate states its claim in continuation form.

**What it proves: wiring, not operators.** Both sides use the same `lt_s` and `mul` terms, so the proof says the
instruction list computes the source's expression tree over these operator terms. That `lt_s` is signed less-than and
`mul` is 64-bit multiplication, and that both agree with eval's i64 semantics and wasm's i64 ops, needs separate
operator lemmas (or a trusted operator table). The design choices this left (where the code lives, how it meets
`proof.rs`'s `Int`, where the list comes from, operators) are decided in ROADMAP v0.7.

