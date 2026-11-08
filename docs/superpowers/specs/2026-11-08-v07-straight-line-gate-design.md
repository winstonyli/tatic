---
status: draft
---

# v0.7: emitted code in the kernel (the straight-line gate)

ROADMAP v0.7. Today the JIT installs a straight-line term after the kernel proves a *model of the compiler*: `proof.rs#prove_pure_expr` (or `proof/closures.rs#prove_closure_expr`, which also accepts every non-recursive `Var`/`Lit`/`Prim`/`If` body) maps the term to postulated `Int` operators and proves it by `refl`. Nothing proved touches the emitted wasm; `jit.rs#verify` (samples against wasmtime) is the only check of the code. This milestone makes the kernel prove the **instruction list that is printed as the installed WAT**, run on church-bv's wasm machine over 64-bit words, equal to the source term on every input, and gates install on that proof.

Goal 1 (a JIT on proved equivalence). Facts were read from the tree on 2026-11-08 at `3957661`; "inference" marks what was not run.

## Decided (ROADMAP v0.7, 2026-11-08)

- **w1 Home:** church-bv's encodings and `wasm.rs` move to a new crate that tatic and church-bv both depend on.
- **x1 List source:** the lowering emits `Ins`; WAT is printed from it one-to-one. The printer is trusted and must reproduce the golden WAT.
- **y1 `Int`:** the gate replaces `prove_pure_expr` for the straight-line fragment; `Int` stays for the closure and recursive provers.
- **z1 Parameters:** a new `LocalGet` instruction, defined as a load from a frame in memory.
- **a1 Operators:** a trusted table (`lt_s`, `le_s`, `mul`, `eq` as a one-bit word, beside the existing `add`, `sub`), each checked against eval and wasmtime exhaustively at n = 8 and on samples at n = 64.

## D1-D3 (decided 2026-11-08: the user took (a) for each, as recommended; recorded in ROADMAP v0.7)

The options are kept below as the record of what was weighed.

- **D1 How far the lowering emits `Ins`.** (a) *Every function body, with `Raw` lines* (recommended): every function body the lowering emits (today's `node()` output) becomes a `Vec<Ins>`. The instructions the machine interprets are structured variants; every other line is `Ins::Raw(String)`, printed verbatim. The fixed module-level templates (`emit_allocator`, the pap wrapper, the curried stages) stay text. One lowering path; the machine rejects any list containing `Raw`. (b) *A variant per opcode*: the same, with typed variants for every instruction (`LocalSet`, `Call`, `CallIndirect`, i32 ops, ...): more types the machine does not use until v0.8. (c) *Fragment only*: straight-line bodies go through `Ins`, everything else keeps text emission: two lowerings that can drift, which x1 was chosen to avoid.
- **D2 What `Ins` carries.** (a) *Data* (recommended): `Push(i64)` and `Op(Op)`, where the enum `Op` names a row of the operator table (its kernel term at width n, its WAT mnemonic, its result kind). (b) *Terms* as today (`Push(Expr)`, `Bin(Expr)`, `Cmp(Expr)`): the printer would have to recognise which closed term is which operator and decode Church words, a reverse mapping inside trusted code.
- **D3 How the gate routes installs.** `kernel_verify` today tries provers in an `||` chain (`jit.rs:312-316`), and `prove_closure_expr` proves all 5 fragment terms (census: `closure true` on all 5 rows). If the gate only replaces `prove_pure_expr` in that chain, a term whose list the gate rejects still installs through the closure prover, and goal 2 holds at the gate but not at install. (a) *Route by a predicate; the gate's verdict is final* (recommended): a term is **in the fragment** when it is non-recursive, has arity ≥ 1, its body is `Var`/`Lit`/`Prim`/`If` only, every `Var i` has i < arity, every `Prim` has a table row (`Add`, `Sub`, `Mul`, `Lt`, `Le`, `Eq`), every `If` condition is a comparison `Prim`, and every `If` is in **tail position** (the body itself, or an arm of a tail `If`); subject to a size bound or a `Mul` restriction if the section 8 measurements call for one. The tail rule is what bounds the gate: the machine's `seq` and the source-side `cps` both copy the rest of the program into each arm of an `If`, so k `If`s in operand position give a term of size 2^k while the tree stays linear and far under `MAX_TREE_NODES`. A tail `If` has nothing after it to copy. `try_install` routes: for a term in the fragment it takes the gate's verdict and tries nothing else; every other term goes to `kernel_verify`, the existing chain without `prove_pure_expr`. A straight-line term that divides, or has an `If` in an operand, then has to install through `prove_closure_expr`. That prover has never been the one used for such terms (`prove_pure_expr` runs first), so a first task checks it accepts every corpus, test and `ir_fuzz` term that `prove_pure_expr` accepts outside the fragment (among them `jit/tests.rs`'s `\a b. a / b`, which asserts it compiles). If it rejects any, that comes back to the user as a decision before `prove_pure_expr` is deleted. (b) *Final for every straight-line term*: the same with `Div`/`Mod` inside the fragment; such terms stop installing (`jit/tests.rs`'s `\a b. a / b` test, which asserts it compiles, changes). (c) *Advisory*: the gate first, the old chain as fallback; nothing the gate rejects is kept out, so the milestone's "Done when" is not met.

Searched (deletion pass): every type, field and check in the first draft was tried for removal by a reviewer briefed only for that (2026-11-08). Removed: the ninth Church constructor (`LocalGet` expands in `seq` to the existing `push` and `load`); the `Bin`/`Cmp` split in `Ins` (one `Op` variant; the row's kind picks the constructor); the `LocalGet`-with-`Store` rejection (the kernel already fails such a proof); the table's reference column (the term is checked against eval and wasmtime directly); the separately stored WAT text (the fragment carries `Ins` and prints from it); the `lower.rs`/`print_wat.rs` split (the body printer is small and lives beside `Ins`); `prove_pure_expr`, `finish` and their tests and bench row; an `Option<&[Ins]>` parameter on `kernel_verify` (`try_install` routes instead, round 3). Tried and kept: the source-side `cps` builder (deriving the right side from the IR or the list would prove the lowering against itself); the `upd` frame (the only lookup the memory type has); `Dup` (the countdown law uses it on a changing counter, which a frame read cannot replace); fuel 1 on the `loop $L` wrapper (stripping it would add a trusted wasm fact). Fixing the start stack to drop the `S` and `s` binders was not adopted: small gain, untested.

## Goals

1. The 5 terms in the fragment today install through the gate at n = 64: `inc`, `doubling` (d = 4), `straight_line`, and the specialised `\v0. v0 + 5` (`a_capturing_closure_call`) and `\v0. 3 + 4 + v0` (`a_pap_capturing`). (Census run `2026-11-08-b1-census`; doc 15, "v0.7's first steps: the census and the emit spike".)
2. The gate rejects mutated lists, each mutation applied to every one of the 5 terms that has the instruction it changes: arms swapped (`straight_line`), a comparison changed `LtS` to `LtU` (`straight_line`), an operator changed `Add` to `Sub` (all 5) or `Mul` to `Add` (`straight_line`), a constant changed (`inc`, `straight_line`, the two specialised terms), a `LocalGet` index changed (`straight_line`, the only term of arity ≥ 2; in an arity-1 term another index reads an unbound frame slot, which says nothing about the gate). These are tests of the gate fn on the unmutated term and the mutated body. At install they would never reach the gate: `try_install` runs `verify` (wasmtime against eval on samples) first, and each of these mutations fails it (`FailedVerification`).
3. The printer reproduces the 25 golden WAT files byte for byte (`crates/tatic/tests/golden/`: 25 modules and 5 `REJECTED` stubs). Three goldens are added for fragment modules that have none: `doubling` (d = 4; `test_corpus::doubling` is `pub(crate)`, so the integration test builds the term itself) and the two specialised modules (`inc` and `straight_line` already have goldens; the existing `a_capturing_closure_call` and `a_pap_capturing` goldens are the unspecialised closure modules).
4. The table's terms agree with eval and wasmtime: all 65,536 pairs at n = 8, the edge set squared at n = 64.
5. `prove_pure_expr` is deleted; `try_install` routes by D3.

## Non-goals

- Recursion, closures and calls in the kernel (v0.8 on). Under D1a their bodies are `Ins` with `Raw` lines; the machine rejects them.
- `Div` and `Mod` in the gate (no table row; `Div`'s `emit_wrapping_div` also needs locals and i32 logic). Under D3a such terms install through `prove_closure_expr` (also `Int`-based), pending the first-task check.
- Kernel proofs that the operators mean signed less-than or 64-bit multiplication (a1: trusted table).
- The `h ≡ h'` link for specialised terms stays certificate-checked (`spec_check`), as today.
- The function scaffolding outside the body (`(func`, params, the `$t*` and scratch local declarations, export, `(module`) is printed by trusted code and not proved.

## Design

### 1. The shared crate (w1)

New package `crates/tatic-wasm` (name: my call; `crates/<name>`, workspace version, added to the explicit `[workspace] members` list in the root `Cargo.toml` and its comment, a `[workspace.dependencies]` path entry). The encoding files use `use super::*` against church-bv's `lib.rs` glob, so the new crate gets its own small prelude; the size-allowlist rows of moved files are re-keyed to their new paths. Graph: `tatic -> tatic-wasm -> tatic-kernel`; `church-bv -> tatic-wasm, tatic-kernel, tatic-rng`. No cycle.

It holds:
- `encoding/` (cx, gates, good, division, proofs, tables, tests; 2118 lines with `encoding.rs`) and `wasm.rs` (934 lines), plus `ops.rs` (section 4) and the body printer (section 5).
- `BitPair` and `Bits4` from church-bv's `lib.rs` (`good.rs:193`).
- `bits_circuit`, `add_rows`, `mul_bits` and the `BitsFn` alias from `search.rs` (gates only), for the table's `Mul`.
- Dependencies: `tatic-kernel`, `hashbrown` (`tables.rs:57`); dev: `mimalloc` with a `#[cfg(test)]` global allocator, as `tatic-kernel` has (`countdown_invariant_is_not_exponential` asserts a time).

Cuts at the boundary:
- The 10 `OP_INFO[i].truth` uses in the encoding (`good.rs` 159-161 and 230-232, `proofs.rs:269`, `tables.rs` 185-187) call three truth-table fns that move into the encoding; church-bv's `OP_INFO` rows (`rewrite/term.rs:317`) call those same fns, so each table has one home.
- 33 tests sit in the moving files (30 encoding, 3 wasm). The 4 that use `Job` and `Setup` (all `#[ignore]`: the `scaling_scoped` callers and `profile_add_zero`) stay in church-bv as a test file over the new crate; 29 move. church-bv's count falls from 390 to 361; the workspace total is unchanged.
- `tele` and `constant` become `pub`; `ty!` gets `#[macro_export]`.
- church-bv's 14 lines naming `crate::encoding` and its `use encoding::*` glob are edited to the new crate (no re-export shim).

`wasm.rs` would pass 1000 lines with the changes below; the move splits it into the machine (`Ins`, `out_stack`, `prog`, `seq`, `interp`, `meaning`) and the laws and their tests (`append_law`, `if_law`, `loop_law`, `countdown_law`, `run_wasm_checks`).

### 2. `Ins` (D1a, D2a)

```rust
pub enum Ins {
    Push(i64),               // i64.const v
    LocalGet(u32),           // local.get $p{i}
    Op(Op),                  // i64.add, i64.lt_s, ...
    Dup,                     // machine only (the countdown law); never emitted or printed
    If(Vec<Ins>, Vec<Ins>),  // if (result i64) .. else .. end
    Loop(Vec<Ins>),          // (loop $L (result i64) .. ) — folded form, as the goldens have it
    Br(usize),               // br $L (depth 0 only; the printer asserts it)
    Store, Load,             // machine only (existing memory tests); never emitted
    Raw(String),             // any other line the lowering emits, without indent; printed at its depth
}
```

- `Ins` derives `Clone`, `Debug`, `PartialEq`, `Eq` (the mutation tests compare and print lists); `Item` and `CompiledFragment` gain what they then need.

- The printer panics on `Dup`, `Store` and `Load` (the lowering never emits them; the goldens and `ir_fuzz` exercise every emitted body).
- The machine interprets every variant but `Raw`. The gate rejects an ill-formed list with an up-front check (`fn well_formed(&[Ins]) -> bool`, recursing into `If` arms and `Loop` bodies: no `Raw`, and the stack shape `out_stack` asserts holds) before calling `prog`, so a mutated list answers false instead of panicking; `prog`, `out_stack` and `seq` keep their signatures and treat both as internal invariants, as today.
- The lowering emits `br $L` as `Br(0)`.
- `Push(v)` is `lit(n, v as u64 as u128 mod 2^n)` in the machine and `i64.const {v}` in the printer.
- `Op(o)`: a word-result row uses the existing `bin` constructor and a bit-result row the `cmp` constructor; `out_stack` takes the stack effect from the row's kind. The machine's laws and controls that pass an operator `Expr` today (`countdown_law`'s `dec`, the `if_law` and `loop_law` controls) take an `Op`; a control uses a wrong row (`Add` for `Sub`).
- `If` in an emitted body always has a result and an else (the bare `if` in the allocator is in a text template, not a body).

### 3. `LocalGet` and the frame (z1)

- No new Church constructor: `seq` expands `LocalGet(i)` to the existing `push (lit n i)` and `load`. The printer prints `local.get $p{i}`.
- Frame: slot i at address `lit(n, i)`, as in the spike. The statement binds parameters `q_0 .. q_{m-1} : V` (q_j is `$p{j}`) and starts from `frame = upd 0 q_0 (upd 1 q_1 (... mu))`.
- A list that stores into the frame computes something else, and the kernel check fails; no separate rejection.

### 4. The operator table (a1, D2a)

`tatic-wasm/src/ops.rs` holds the enum with `mnemonic()`, `kind()` and `term(n)`; `term` calls the circuits, which live in `encoding/gates.rs` beside `add`, `sub` and `lt_u`. The new circuits take the `a b C k` shape `lt_u(n)` has, so the `cmp` constructor accepts them. `lt_s` flips bit n-1 of each operand (`lit` puts bit i at position i; `gates.rs` has only per-bit xor, so this is a new term) and calls `lt_u`. `mul` closes `bits_circuit` over n to fit `BitsFn`.

| `Op` | kind | kernel term at n | WAT |
|---|---|---|---|
| `Add` | word | `add(n)` | `i64.add` |
| `Sub` | word | `sub(n)` | `i64.sub` |
| `Mul` | word | `bits_circuit(n, mul_bits)` | `i64.mul` |
| `LtS` | bit | `\x y C k. lt_u (x xor m) (y xor m) C k`, m the sign bit | `i64.lt_s` |
| `LeS` | bit | `\x y C k. lt_s y x C (\b. k (not_ b))` | `i64.le_s` |
| `Eq` | bit | `\x y C k. k (eq_bv(n) x y)`; `eq_bv(n)` answers a `Bool0`, the kind `lt_u` passes to `k` | `i64.eq` |
| `LtU` | bit | `lt_u(n)` | `i64.lt_u` |

`LtU` stays for the countdown tests and the `LtS`-to-`LtU` control; no source op maps to it.

tatic has one map `PrimOp -> Option<Op>`, in `jit/shape.rs` (so `shape` stops importing from `lower_wat`, which ends the `ir -> shape -> lower_wat -> ir` cycle; the `PARKED.md` entry is edited in the same commit to keep its other cycle, `compile <-> lower_wat` through `CompiledFragment`, which this design leaves) (Add, Sub, Mul; Lt to LtS, Le to LeS, Eq to Eq; Div and Mod none: their `i64.div_s` and `i64.rem_s` lines become literal `Raw` in the lowering, and the `ir::check` `expect` messages that cite `arith_instr`/`cmp_instr` cite the map). The lowering, the source-side builder (section 6) and the fragment predicate (D3a) use it, and `shape::is_comparison` becomes "maps to a bit-result row" (it is `cmp_instr(op).is_some()` today, `shape.rs:163`). Because both sides of the proof read the same map, the gate cannot catch a wrong row; the table check (section 8) is the guard.

### 5. The lowering and the printer (x1, D1a)

- `lower_wat.rs`'s `node()` and its helpers build a `Vec<Ins>` per function body instead of text. Lines the machine does not interpret (`local.set`, `call`, `call_indirect`, `i32.*`, loads and stores at offsets) are `Raw`. `emit_wrapping_div` is a body emitter like the rest (it emits inside `node()`): its `if` is an `Ins::If`, its `i64.const` a `Push`, its other lines `Raw`.
- Every function `function()` emits wraps its body in `Ins::Loop` (as `lower_wat.rs:423` does today); the module-level templates (`emit_allocator`, `emit_pap_wrapper`, `emit_curried_stages`) have no wrapper and stay text.
- The body printer is in `tatic-wasm` beside `Ins` and the mnemonics: each variant prints one fixed line shape at its depth, `If` flat (`if (result i64)` / `else` / `end`) with its arms at +2, `Loop` folded (`(loop $L (result i64)` ... `)`), `Raw` indented to its depth. Module scaffolding stays in tatic.
- `CompiledFragment` keeps its other fields and replaces `wat: String` with `module: Vec<Item>`, where `enum Item { Text(String), Func { name: String, header: String, body: Vec<Ins> } }`, in print order (assembled after every function is lowered, since the type lines and the allocator depend on state `function()` mutates; `$f` is lowered first but printed last): templates, `(type ..)`, `(table ..)`/`(elem ..)` lines and export are `Text`; each emitted function is a `Func` whose header is its signature and local declarations (and whose closing paren is printed after the body). `pub fn wat(&self) -> String` prints it; its readers (about 57 `.wat` hits; `instantiate` in `jit.rs`, `golden_wat.rs`, `compile_fuzz.rs`, `testing/ir_fuzz.rs`, `lower_wat.rs` and `jit/tests.rs` tests) call `wat()` in place of the field. `pub fn entry(&self) -> &[Ins]` returns the body of the `Func` named `f`, the wrapping `Loop` included; it is what the gate proves, so the list proved is the list printed.
- `lower_wat.rs` (1109 lines, on the size allowlist) is split by topic: the module-level templates and their tests (about 170 + 100 lines) go to their own file. Whether that brings it under 1000 after the `Ins` conversion is measured at the split; if not, its allowlist max is lowered to the new size, not raised.

### 6. The gate statement

For a term h' in the fragment (D3a; after `specialise`), with `code = frag.entry()` (a fragment term compiles to one function, `$f`, with no combinators; `code` is `[Loop(body)]`):

```
Pi S R k z q_0 .. q_{m-1} s mu.
  Id(R, M (prog code) 1 R k z s (frame q mu), rhs)
```

- Fuel 1: the `loop $L` wrapper with no `Br` reduces to its body with the timeout as the unused label, and falls through (`wasm.rs#loop_`, `seq`). The spike never ran a `Loop`, so its cost is measured first. Fallback, if fuel 1 is too slow: prove the body without the wrapper and record "a `loop` with no `br` equals its body" as a trusted printer fact.
- `rhs` is built from the **source term**, never from `code`: `cps(e, K)` with a Rust-level meta-continuation K (no kernel lambdas), so `rhs` is a closed term with `choose` at each `If`:
  - `Lit v` gives `K (lit v)`.
  - `Var i` gives `K q_{m-1-i}`: de Bruijn 0 is the last parameter. This mapping is written in the gate, independently of `shape::local_index`, as `verify/decompile.rs` is independent of `shape`.
  - `Prim op a b` (word row) gives `cps(a, \x. cps(b, \y. K (op x y)))`.
  - `If (Prim cmp a b) t e` gives `cps(a, \x. cps(b, \y. choose(R, cmp x y, cps(t, K), cps(e, K))))`. K is copied into both arms, as `seq` copies the rest; in the fragment every `If` is in tail position, so K is only the final continuation and nothing grows.
  - The final K is `\v. k (v, s) frame`.
- Comparisons occur only as `If` conditions: the compiler rejects them elsewhere (`compile.rs:247-252, 306-309`).
- The proof is `refl`, checked by `holds`. Spike costs at n = 64: `inc` 1.6-1.7 ms, the `straight_line` shape with its `a*2` arm 12.8 ms (the full term was not run), statement build 8-17 ms more.
- Evaluation order: the lowering emits `a`, `b`, then the operator; `cps` follows the same order.
- An `If` in an operand (`\a b. 1 + (if a < b then a else b)`) is outside the fragment; a test checks it installs through the existing chain.
- Lives in tatic (it needs `lang::Term`): `proof/gate.rs`.

### 7. Install path

- `try_install` routes on the specialised `(store, term)`: `in_fragment(term, arity)` sends it to `gate(store, term, arity, frag.entry())`, else to `kernel_verify(store, term, arity)`, whose signature is unchanged and whose chain loses `prove_pure_expr`. Its direct callers in `jit/tests.rs`: lines 64, 89 and 125 (the unspecialised `(\g. g) (\x. x + 1) n`) expect false and stay as they are; line 126 (the specialised `\n. n + 1`) is a fragment term, so it calls `compile_specialised` and then `gate` with `frag.entry()`, expecting true.
- The gate runs inside `tatic_kernel::scoped` and returns `bool`, as the church-bv tests and benches wrap build-and-check, so an install leaves no n = 64 terms behind.
- Deleted: `prove_pure_expr`, `finish` (`proof.rs:401`, only its caller), the 3 tests in `proof/tests/basics.rs` that call it (the two "out of scope" checks at lines 155 and 162 move to the fragment predicate), and the bench row `straight_line_refl_proof` (`benches/proofs.rs:21`), whose time is recorded first as the baseline. `denote` stays (`proof/universal.rs` uses it).
- Docs that name `prove_pure_expr` or say `verify` is the only check of emitted code are updated in the same commit: `docs/TOUR.md` (35, 87, 109 and the encoding/wasm lines 33-41, cites 132, 133, 158, 198), `docs/proven.md` (222, 355; and 16, whose `cargo test -p church-bv` command names a test that moves), `scripts/experiments/lemma_times.sh` (names `encoding::`), the doc comments in `jit.rs` (module doc 21 and 43, the block at about 244-257, 281, 297-309), `proof.rs`'s module doc and comments at 259 and 357, `proof/universal.rs:355`, `proof/closures.rs:68`; and the comments naming `cmp_instr`/`arith_instr` (`compile.rs:247`, `lower_wat.rs:703`, `shape.rs:161`).

### 8. Checks

- **Operator table** (a tatic test; it has eval and wasmtime). For each row at n = 8 and all 65,536 pairs (x, y): the kernel term on `lit(8, x), lit(8, y)` is `def_eq` to `lit(8, r)` for word rows and to `lit(1, r)` for bit rows, where r is read from eval (`apply_term` on the row's source term, at sign-extended inputs, masked to 8 bits; `apply_prim` is private) and must equal wasmtime running that term compiled and printed by the production path. The source term is `\a b. a op b` for word rows and `\a b. if a op b then 1 else 0` for bit rows (a bare comparison does not compile: `compile.rs:306-309`). `LtU` has no source op; it is checked against Rust's `<` on `u8`/`u64` only. At n = 64: the `ir_fuzz` edge set `{MIN, MIN+1, -7, -1, 0, 1, 7, MAX}` squared. Cost unmeasured (the largest kernel sweep today is 64 pairs); measured first, and reported if over a minute.
- **Gate:** each of the 5 terms installs (`CacheEntry::Compiled`) at n = 64 through the gate; the gate fn rejects each mutated body (Goal 2); the operand-`If` term installs through the chain.
- **Printer:** the 25 goldens byte for byte, the 3 new fragment goldens, `ir_fuzz` green; a test that the 5 fragment bodies contain no `Raw`.
- **Move:** the workspace test count is unchanged (church-bv 390 to 361, the new crate 29); the guards (`size_check`, `test_placement_check`, `tour_check`, `cite_check`, `layout_check`).
- **Gate time against tree size:** with tail-only `If`s the kernel term is linear in the tree, which the lowering emits (a shared subterm once per use) up to `MAX_TREE_NODES` (16,384; `doubling(13)` is at the cap, `compile/tests.rs:714`). Measured first: the gate's time on `doubling(d)`, d = 1..13; on `Mul` of two parameters; and on `Mul` inside a tail `If` arm (doc 15 records 8-10x growth per bit for `mul(n)` on stuck symbolic bits in other statement shapes). The JIT path was sized for about 0.4 s in total. If `doubling` exceeds that below the cap, the fragment predicate gains a tree-size bound read off the curve. If `Mul` of two non-literal operands (neither a `Lit` node after `specialise`, which folds constants) exceeds it (its cost grows with how symbolic the operands are, not with node count, so a tree bound would not catch it), `Mul` with two non-literal operands leaves the fragment (`straight_line`'s `a*2` stays in). Either way the excluded terms take the existing chain (D3a).
- **Stack depth at the cap:** `Wasm::seq` recurses once per instruction through its continuation, and `cps` recurses over the tree; neither runs under the kernel's stack growth (`tatic-kernel/src/stack.rs`). Measured first with the timings: build and prove `doubling(13)` on a default-size thread. If it overflows, the builders run under that stack growth.

## End-state fit

| Change | Lives in | Replaces | Deletes |
|---|---|---|---|
| encodings, machine, table, body printer | `crates/tatic-wasm` | church-bv's `encoding/`, `wasm.rs`, 3 `search.rs` fns | the church-bv copies |
| `Ins` as data, `LocalGet`, `Op`, `Raw` | `tatic-wasm` | `Push(Expr)`, `Bin(Expr)`, `Cmp(Expr)` | the `Expr` payloads |
| IR to `Ins`; `CompiledFragment.module` | `tatic/src/jit/lower_wat.rs` (+ a templates file) | text emission in `node()`; the `wat` field (now a method) | the `wat` field; `lower_wat.rs`'s allowlist row if under 1000 |
| gate and fragment predicate (`gate`, `in_fragment`) | `tatic/src/proof/gate.rs`; routing in `try_install` | `prove_pure_expr` and the `\|\|` chain for fragment terms | `prove_pure_expr`, `finish`, 3 tests, a bench row |
| `PrimOp -> Option<Op>` | tatic, one fn | `cmp_instr`, `arith_instr` | both fns |

## Risks

- **Gate time at the tree cap and on `Mul`** (section 8): unmeasured; may add a size bound to the fragment. The 2^k blow-up of operand `If`s is ruled out by the tail rule, not measured.
- **Fuel 1 and `Loop` cost**: unmeasured; fallback stated (section 6).
- **n = 8 sweep cost**: unmeasured.
- **D1a breadth**: every body moves to `Ins` at once; the goldens catch any text change.
- **The shared `PrimOp -> Op` map**: the gate cannot catch a wrong row; only the table check does.
- **Large-page wander**: moving timing tests to a new test exe moves where mimalloc large pages make counts wander (ICOUNT.md). Inference.

## Left to the builder

Task order and commits (first: the closure-prover check in D3a, and the measurements in sections 6 and 8: fuel 1, the n = 8 sweep, gate time on `doubling` and `Mul`, stack depth); file names inside `tatic-wasm` beyond those named; which `node()` lines become which variants beyond those named; where the table check's harness lives in tatic's tests; whether the 4 Job/Setup encoding tests get their own file.
