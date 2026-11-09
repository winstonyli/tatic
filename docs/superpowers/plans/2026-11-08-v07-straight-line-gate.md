---
status: done
---

# v0.7 straight-line gate: implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** For the straight-line fragment, the JIT installs a compiled term only after the kernel has proved, at n = 64, that the instruction list printed as its WAT equals the source term on every input.

**Architecture:** church-bv's encodings and wasm machine move to a new crate `tatic-wasm`. There `Ins` carries data (`Push(i64)`, `LocalGet(u32)`, `Op(Op)`, `Raw(String)`), beside a trusted operator table and a body printer. tatic's lowering builds a `Vec<Ins>` per function body and prints WAT from it. A new `proof/gate.rs` proves `M (prog entry) 1 ... = cps(source)` by refl, and `try_install` sends fragment terms to it alone.

**Tech Stack:** Rust 2024 workspace; `tatic-kernel` (Church-encoded CoC kernel); wasmtime and `wat` (existing tatic deps); criterion bench `benches/proofs.rs`.

**Spec:** `docs/superpowers/specs/2026-11-08-v07-straight-line-gate-design.md` (D1-D3 decided as (a)). "Section N" below means the spec's section. Where this plan says "per section N", the spec's text is the requirement and is not repeated here.

## Global Constraints

- Crate graph: `tatic -> tatic-wasm -> tatic-kernel`; `church-bv -> tatic-wasm, tatic-kernel, tatic-rng`. No cycle, and no re-export shim in church-bv.
- The new crate takes the workspace version, edition and license. It goes in the explicit `[workspace] members` list (update the comment above it) and gets a `[workspace.dependencies]` path entry.
- The gate works at width n = 64. Frame slot i lives at address `lit(n, i)`.
- Fuel is 1 on the `loop $L` wrapper unless T6 triggers the fallback in section 6.
- `Push(v)` means `lit(n, (v as u64 as u128) & low_bits(n))` in the machine and prints as `i64.const {v}`.
- Every function body becomes `Ins`, with `Raw` lines where needed. The module-level templates (`emit_allocator`, `emit_pap_wrapper`, `emit_curried_stages`) stay text.
- The printer must reproduce the 25 existing goldens byte for byte, from a test run without `UPDATE_GOLDEN`. Only the 3 new goldens are blessed, from their own test fn.
- `rhs` is built from the source term, never from `code`. The gate's de Bruijn-to-parameter mapping is written in `gate.rs`, independently of `shape::local_index`.
- A fragment term's install takes the gate's verdict and tries nothing else. Every other term goes to `kernel_verify`, minus `prove_pure_expr`.
- `well_formed` rejects `Raw`, stack-shape errors and an out-of-range `Br` before `prog` is called. `prog`, `out_stack` and `seq` keep their signatures.
- Run these guards before every commit that touches their scope, each as `bash scripts/check/<name>.sh`: `size_check`, `test_placement_check`, `tour_check`, `cite_check`, `layout_check` and `front_matter_check`. Below, "the guard loop" means `for g in size_check test_placement_check tour_check cite_check layout_check front_matter_check; do bash scripts/check/$g.sh || break; done`.
- Runs over a minute go through `~/.claude/runs/run.ps1` (a row in `docs/runs.md`, launched from the main checkout). Findings go in doc 15 (`docs/tier-cycle/15-the-jit-and-the-target-machine.md`) with their run ids, in a new section "v0.7's build: measurements and checks" that T1 creates (its heading starts a line). ROADMAP, TOUR and PARKED cite it as `docs/tier-cycle/` ("v0.7's build: measurements and checks"), never by file name, or `cite_check` fails.
- Never let python read stdin. Commit trailer: `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`. Never push or tag.

## Review Focus

1. **Negative and extreme literals** (`i64::MIN`, `-1`). The machine word must be the two's-complement mask, and the printer must print what the goldens print. Pinned in T6: the accept table includes a literal `i64::MIN`.
2. **Parameter order.** De Bruijn 0 is the *last* parameter, so a reversed mapping would prove `\a b. b - a` for `\a b. a - b`. Pinned in T6: `\a b. a - b` and `\a b c. c` are accepted, and a swapped `LocalGet` is rejected.
3. **An `If` outside tail position** (in an operand, or in a condition's operand). It must leave the fragment and still install through the chain. Pinned in T1 (the closure prover accepts the term), T6 (`in_fragment` false) and T7 (it installs).
4. **Stack depth off the test harness's thread.** `seq` and `cps` recurse once per instruction and once per node. Measured in T6 on a fresh 2 MB thread for `doubling(13)`. On overflow, the builders run under `tatic_kernel::grow`, and that test stays as the pin.
5. **A wrong `PrimOp -> Op` row.** Both sides of the proof read it, so the gate is blind to it. Pinned in T5: the source term runs through eval and through the production print path to wasmtime, against the row's kernel term.

---

### Task 1: Check that the closure prover covers what `prove_pure_expr` accepted

This is D3a's precondition. A miss outside the fragment is the user's decision before T7 deletes `prove_pure_expr`, so it runs first. The check is temporary and recorded rather than kept, because it dies with `prove_pure_expr`.

**Files:**
- Temporary (reverted): `crates/tatic/src/jit.rs` (`kernel_verify`), `crates/tatic/src/testing/ir_fuzz.rs` (`run_reference`)
- Modify: doc 15, to create the section named in Global Constraints with this result

**Interfaces:**
- Consumes: `proof::prove_pure_expr` (`proof.rs:420`) and `proof::prove_closure_expr` (`closures.rs:887`).
- Produces: a list of misses in doc 15.

- [ ] **Step 1: Insert the probe.** Add it at the top of `kernel_verify` (after `calls_a_parameter`) and in `ir_fuzz.rs`'s `run_reference` (after `decompile`):
  `if proof::prove_pure_expr(s, h).is_some() { let ok = proof::prove_closure_expr(s, h).is_some(); eprintln!("PURE {} {}", if ok { "covered" } else { "MISS" }, <term as text>); }`
  For the term as text, use whatever printer `syntax.rs` exports; `{h:?}` plus the test name will do if there is none. It prints rather than asserts, so one run lists every miss.
  Also add a temporary `#[test] fn c1_probe_terms()` in `jit/tests.rs`. It parses the terms T6 and T7 rely on to install through the chain and asserts `prove_closure_expr(..).is_some()` for each: `\a b. 1 + (if a < b then a else b)`, `\a b. if (if a < b then a else b) < 1 then 1 else 0` and `\a b. a / b`.
- [ ] **Step 2: Run everything that reaches it.**
  Run (bash, main checkout): `powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind probe -Name v07-c1-closure-covers -Affinity CFF -Command "cargo test -p tatic -- --nocapture"`
  Expected: exit 0, with `c1_probe_terms` passing; a failure there counts as an outside-the-fragment miss. In the run folder's `out.log`/`err.log`, count the `PURE covered` and `PURE MISS` lines.
- [ ] **Step 3: Classify, record, revert.**
  - Mark each `MISS` term in or out of the fragment by section D3a's rule (by hand; `in_fragment` comes in T6).
  - In-fragment misses are a note: the gate will take them.
  - **If any miss is outside the fragment, stop** and bring it to the user as a Decide group.
  - Record the counts and the misses in doc 15, then run `git checkout crates/tatic/src`.
  ```bash
  git add docs/tier-cycle/15-the-jit-and-the-target-machine.md docs/runs.md
  git commit -m "docs: v0.7 check that prove_closure_expr accepts what prove_pure_expr accepted outside the fragment"
  ```

### Task 2: Move the encodings and machine into `crates/tatic-wasm`

This is a mechanical move: no behaviour changes, and the workspace test count stays the same.

**Files:**
- Create: `crates/tatic-wasm/Cargo.toml`, `crates/tatic-wasm/src/lib.rs`
- Move with `git mv`: `crates/church-bv/src/encoding.rs` and `encoding/` to `crates/tatic-wasm/src/`
- Split `crates/church-bv/src/wasm.rs` in two:
  - Machine, to `crates/tatic-wasm/src/wasm.rs`: `choose`, `K`, `Ins`, `out_stack`, and `impl Wasm` up to line 486.
  - Laws and their 3 tests, to `crates/tatic-wasm/src/wasm/laws.rs`: `Ctl` and `if_inv` (lines 22-65), `append_law`, `if_law`, `loop_law`, `countdown`, `countdown_law`, `mem_prog`, `run_wasm_checks`.
- Move `BitPair` and `Bits4` (church-bv `lib.rs:45-49`, private aliases today) to `crates/tatic-wasm/src/encoding/good.rs` as `pub type`.
- Move `bits_circuit`, `add_rows`, `BitsFn` and `mul_bits` (`search.rs:345-410`) to `crates/tatic-wasm/src/encoding/gates.rs`. `circuit_law` and the mul tests stay in `search.rs` and import them.
- Keep the 4 `#[ignore]` Job/Setup tests and their `scaling_scoped` helper in church-bv as `#[cfg(test)] mod encoding_scaling;` (new file `crates/church-bv/src/encoding_scaling.rs`). `Job` and `Setup` are private to church-bv, so an integration test cannot reach them.
- Modify:
  - Root `Cargo.toml`: members, the comment above them, and `tatic-wasm = { path = "crates/tatic-wasm" }`.
  - `crates/church-bv/Cargo.toml`: add `tatic-wasm.workspace = true`.
  - church-bv `lib.rs`: drop `mod encoding`, `mod wasm`, `BitPair` and `Bits4`; change `use encoding::*` to `use tatic_wasm::encoding::*`.
  - The 14 `crate::encoding` lines:
    - `job.rs` 290 and 295
    - `uniform/{bitwise,mul,shift,symmul}.rs`: write `use tatic_wasm::encoding;` so the `encoding::` call sites stay as they are
    - `width.rs` 611-656, `wfold.rs:15`, `wnat.rs:20`
  - `job.rs`'s `hidden_state_is_classified` (660-740): its `THREAD_LOCAL` rows for `encoding/gates.rs` `CONSTANTS` and `encoding/tables.rs` `BODIES` now sit in tatic-wasm. The scan walks both `crates/church-bv/src` and `crates/tatic-wasm/src` (resolving `tatic-wasm` beside `CARGO_MANIFEST_DIR`). Those two rows name the tatic-wasm files, so the memos stay classified and the "listed statics that no longer exist" assert holds.
  - `rewrite/term.rs`: rows 1-3 of `OP_INFO` call `and_truth`, `or_truth` and `xor_truth`.
  - `docs/proven.md:16` becomes `-p tatic-wasm`.
  - This plan's front matter becomes `status: active` (VERSIONING: active when work starts).
  - `docs/TOUR.md`: the encoding/wasm lines 33-41 and cites 132, 133, 158 and 198.
  - `scripts/experiments/lemma_times.sh`: gitignored, so this is a local edit only.

**Interfaces:**
- Produces:
  - `tatic_wasm::encoding::*`: everything church-bv's glob saw, plus `pub` `BitPair`/`Bits4`, `tele` and `constant`.
  - `tatic_wasm::wasm::{Wasm, Ins, K, out_stack, choose}` and `tatic_wasm::wasm::laws::run_wasm_checks`.
  - `pub fn and_truth(a: bool, b: bool) -> bool`, plus `or_truth` and `xor_truth`, in `encoding/gates.rs`.
  - `ty!` with `#[macro_export]`, used as `tatic_wasm::ty!`.
- tatic-wasm dependencies are `tatic-kernel` and `hashbrown`, with `mimalloc` as a dev-dependency. `lib.rs` sets `#[cfg(test)] #[global_allocator]`, as `tatic-kernel/src/lib.rs:67-71` does. The `lib.rs` prelude carries what the moved files' `use super::*` needs (`tatic_kernel::*`, `std::sync::Arc`, and `std::time::Instant` for tests).

- [ ] **Step 1: Count the tests before the move.**
  Run: `cargo test --workspace -- --list 2>/dev/null | grep -c ': test$'`, then the same with `-p church-bv`. `--list` includes ignored tests.
  Expected: two numbers. Write them in the commit message. The spec says church-bv has 390; trust the run.
- [ ] **Step 2: Move and edit as listed;** then `cargo build -p tatic-wasm -p church-bv --tests`.
  Expected: builds with no new warnings. Remove any import that church-bv `lib.rs:5`'s `cfg_attr(not(test), allow(...))` was hiding and that a `--tests` build flags.
- [ ] **Step 3: Count again and run.**
  Run: the Step 1 commands, plus `cargo test -p tatic-wasm -- --list | grep -c ': test$'`, then `cargo test -p tatic-wasm`.
  Expected: the workspace count equals Step 1's. church-bv falls by tatic-wasm's count (29 by the spec). All tatic-wasm tests pass, including `countdown_invariant_is_not_exponential` (< 2.0 s).
- [ ] **Step 4: Full church-bv suite.**
  Run: `powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind gate -Name v07-move-churchbv -Affinity CFF -Command "cargo test -p church-bv"`
  Expected: exit 0.
- [ ] **Step 5: Guard loop, then commit.** No size-allowlist row moves, since no moved file is listed.
  ```bash
  git add -A crates/tatic-wasm crates/church-bv Cargo.toml Cargo.lock docs/proven.md docs/TOUR.md
  git commit -m "tatic-wasm: move church-bv's encodings and wasm machine into a shared crate (no behaviour change)"
  ```

### Task 3: `Ins` as data, `LocalGet`, the operator table, `well_formed`

**Files:**
- Create: `crates/tatic-wasm/src/ops.rs`, with inline tests
- Modify:
  - `crates/tatic-wasm/src/encoding/gates.rs`: the new circuits
  - `crates/tatic-wasm/src/wasm.rs`: `Ins`, `out_stack`, `seq` and `well_formed`, with their tests
  - `crates/tatic-wasm/src/wasm/laws.rs`: the laws take `Op`

**Interfaces:**
- Consumes: `add`, `sub`, `lt_u`, `bits_circuit`, `mul_bits`, `eq_bv`, `not_`, `bitwise`, `xor`, `lit`, `low_bits` (`tatic_wasm::encoding`).
- Produces:
  - `pub enum Op { Add, Sub, Mul, LtS, LeS, Eq, LtU }`, deriving `Clone, Copy, Debug, PartialEq, Eq`, with `pub fn term(self, n: usize) -> Expr`, `pub fn mnemonic(self) -> &'static str` and `pub fn kind(self) -> K` (`K::W` for Add, Sub and Mul). Terms and mnemonics are the section 4 table.
  - New closed circuits in `gates.rs`, built per section 4: `pub fn lt_s(n)`, `le_s(n)`, `eq_bit(n)` and `mul(n)`, all `-> Expr`. `lt_s` is the spike's: `bitwise(n, &xor)` with `m = lit(n, 1 << (n-1))`, then `lt_u`.
  - `pub enum Ins` per section 2, deriving `Clone, Debug, PartialEq, Eq`.
  - A private `fn shape(code: &[Ins], st: Vec<K>, loops: &[Vec<K>]) -> Result<Option<Vec<K>>, String>` holds the one stack analysis.
    - It errors on `Raw`, on a pop that lacks its kinds, on `If` arms that end on different stacks, on `Br(j)` with j ≥ `loops.len()`, and on a `Br` whose stack differs from loop j's entry stack.
    - `out_stack(code, st)` becomes `shape(code, st, &[]).unwrap_or_else(|e| panic!("{e}"))`, with the same signature.
    - `pub fn well_formed(code: &[Ins], st: &[K]) -> bool` is `matches!(shape(code, st.to_vec(), &[]), Ok(Some(_)))`: it must fall through.
  - `seq`:
    - `Push(v)`: constructor 0 with the masked `lit`.
    - `Op(o)`: constructor 1 or 2 by `o.kind()`, with `o.term(n)`.
    - `LocalGet(i)`: constructor 0 with `lit(n, i)`, then constructor 7.
    - `Raw`: unreachable, because `out_stack` runs first in `prog`.
  - `countdown_law(w, dec: Op)` and the controls pass an `Op`, with `Op::Add` as the wrong row. Its hard-coded `lt_u`/`sub` goodness (old lines 821/823) stays.

- [ ] **Step 1: Write the failing tests.**
  ```rust
  // ops.rs
  #[test] fn op_rows_are_closed_and_typed() // each Op at n = 8: infer(&Ctx::new(), &term) is def_eq to arrow(V, arrow(V, V)) for kind W, arrow(V, arrow(V, bv_ty(1))) for B
  // wasm.rs
  #[test] fn well_formed_rejects_raw_underflow_bad_br_and_mismatched_arms()
  //   from []: [Raw("x")] false; [Op(Add)] false; [Loop(vec![Br(1)])] false;
  //   [Push(1), Push(2), Op(LtS), If(vec![Push(1)], vec![])] false (arms differ);
  //   [Push(1), Push(2), Op(LtS), If(vec![Push(1)], vec![Push(2)])] true; [Loop(vec![LocalGet(0)])] true
  #[test] fn local_get_reads_the_frame()
  //   n = 8, code [LocalGet(1), LocalGet(0), Op(Sub)] (= q1 - q0) over frame upd(0, a, upd(1, b, mu)):
  //   the spike's sym_law shape (docs/superpowers/spikes/2026-11-08-j1-emit-spike.patch) with rhs kont(sub b a),
  //   proved by refl; and with rhs kont(sub a b), refl fails (the order is observable)
  ```
  Run: `cargo test -p tatic-wasm`
  Expected: compile errors (`Op`, `LocalGet` not found).
- [ ] **Step 2: Implement the Interfaces.** Convert `laws.rs`'s programs: `countdown` becomes `Dup, Push(1), Op(LtU), If(..), Op(dec), Br(0)` as before, and `mem_prog` uses the new variants.
- [ ] **Step 3: Run.**
  Run: `cargo test -p tatic-wasm`
  Expected: everything passes, including the 3 moved wasm tests.
- [ ] **Step 4: Guard loop** (add `Op` and `LocalGet` to the TOUR glossary), then commit.
  ```bash
  git add crates/tatic-wasm docs/TOUR.md
  git commit -m "tatic-wasm: Ins carries data (Push i64, LocalGet, Op, Raw); operator table; well_formed"
  ```

### Task 4: The lowering emits `Ins`, and WAT is printed from it

First split (the tripwire: `lower_wat.rs` is past 1000 lines), then convert.

**Files:**
- Create:
  - `crates/tatic/src/jit/lower_wat/templates.rs`: `emit_allocator`, `emit_pap_wrapper`, `emit_curried_stages`, and their tests
  - `crates/tatic-wasm/src/print.rs`: the body printer and its test
  - 3 goldens in `crates/tatic/tests/golden/`: `doubling_4.wat`, `a_capturing_closure_call_specialised.wat`, `a_pap_capturing_specialised.wat`
- Modify:
  - `crates/tatic/Cargo.toml`: add `tatic-wasm.workspace = true`
  - `jit/lower_wat.rs`: `node`, `read`, `function`, `lower`, `emit_wrapping_div`; delete `arith_instr` and `cmp_instr`, and fix the comment at 703
  - `jit/shape.rs`: the map, and the comment at 161
  - `jit/compile.rs`: `CompiledFragment` and `Item`, and the comment at 247
  - every reader of `.wat`: about 52 (`rg '\.wat\b' crates/tatic`)
  - `tests/golden_wat.rs`: a new test fn
  - `PARKED.md`: the import-cycle entry keeps only `compile <-> lower_wat`
  - `scripts/check/size_allowlist.txt`: the `lower_wat.rs` row

**Interfaces:**
- Consumes: `tatic_wasm::wasm::{Ins, K}` and `tatic_wasm::ops::Op`.
- Produces:
  - In `jit/shape.rs`: `pub fn op_of(op: PrimOp) -> Option<Op>`, mapping Add, Sub, Mul to themselves, Lt to LtS, Le to LeS, Eq to Eq, and Div and Mod to None. `is_comparison(op)` becomes `op_of(op).is_some_and(|o| o.kind() == K::B)`.
  - In `tatic-wasm/src/print.rs`: `pub fn print_body(code: &[Ins], depth: usize, out: &mut String)`, printing the line shapes of section 5. It panics on `Dup`, `Store`, `Load` and `Br(j != 0)`.
  - In `jit/compile.rs`:
    - `pub enum Item { Text(String), Func { name: String, header: String, body: Vec<Ins> } }`
    - `CompiledFragment { pub arity, pub module: Vec<Item>, pub needs_hp_reset }`
    - `pub fn wat(&self) -> String` prints `Text` verbatim, and each `Func` as its header, `print_body(body, 4, ..)` (today's indents: `loop` at 4, its body at 6), then `"  )\n"`.
    - `pub fn entry(&self) -> &[Ins]` returns the body of the `Func` named `"f"`.
  - The lowering's variant mapping (section 5, made explicit):
    - `Node::Lit(v)` → `Push(v)`
    - `Read::Param(li)` → `LocalGet(li)`
    - `Node::Arith(op, a, b)` with `op_of(op).filter(|o| o.kind() == K::W)` = `Some(o)` → a, b, `Op(o)`. Div → a, b, then the existing `emit_wrapping_div`. Mod → a, b, `Raw("i64.rem_s")`. A comparison here hits the `expect("ir::check: Arith carries an arithmetic op")` as today.
    - `Node::If(cmp, a, b, t, e)` → a, b, `Op(o)`, `If(t, e)`, where `o = op_of(cmp).filter(|o| o.kind() == K::B).expect(..)`
    - tail `SelfCall`'s `br $L` → `Br(0)`
    - in `emit_wrapping_div`: its `if` → `If`, its `i64.const` operands → `Push`
    - everything else → `Raw(line without indent)`: Env reads, `local.set`/`local.tee`, calls, `call_indirect`, closure allocation, `i64.const 32` and table-index constants outside the fragment, `i32.*`, `i64.div_s`

- [ ] **Step 1: Split out the templates (its own commit).** Move the three emitters and their tests to `lower_wat/templates.rs` (`mod templates;`, `pub(super)` as needed). Set the `lower_wat.rs` allowlist row to its new `wc -l` count, or delete the row if the file is under 1000 lines.
  Run: `cargo test -p tatic --lib lower_wat && cargo test -p tatic --test golden_wat`, then the guard loop
  Expected: pass, and the guards are OK.
  ```bash
  git add crates/tatic/src/jit/lower_wat.rs crates/tatic/src/jit/lower_wat/templates.rs scripts/check/size_allowlist.txt docs/TOUR.md
  git commit -m "lower_wat: move the module-level templates to their own file"
  ```
- [ ] **Step 2: Record the new goldens from the old emitter, then write the failing tests.**
  - `tests/golden_wat.rs`: a new `#[test] fn fragment_modules_lower_to_their_golden_wat()` with the same `update`/`changed` pattern. It reads `frag.wat` for now and switches to `.wat()` in Step 3.
    - Run it once without `UPDATE_GOLDEN`. It should panic on the missing files, which is its RED.
    - Then bless it before any conversion: `UPDATE_GOLDEN=1 cargo test -p tatic --test golden_wat fragment_modules`.
    - Read each new file, checking for one `(func` named `$f`, `(loop $L` and no `call`.
    - Commit the 3 files with the test fn, so the converted printer is checked against the old emitter's output: `git add crates/tatic/tests/golden_wat.rs crates/tatic/tests/golden && git commit -m "golden: record the three fragment modules from the text emitter"`.
    - `doubling_4` is built inline as `\x. t_4` with `t_{i+1} = t_i + t_i` via `TermStore` calls (`test_corpus::doubling` is `pub(crate)`).
    - The two `_specialised` goldens come from `compile_specialised` on `samples::a_capturing_closure_call` and `samples::a_pap_capturing`, asserting `specialised.is_some()`.
  - `jit/compile/tests.rs`: `#[test] fn fragment_bodies_contain_no_raw()`. For `inc`, `doubling(4)`, `straight_line` and the two specialised terms, assert that `frag.entry()` is `[Ins::Loop(_)]` with no `Raw` at any depth.
  - `print.rs`: `#[test] fn print_body_shapes()`. `[Loop(vec![LocalGet(0), Push(-1), Op(Add), Push(0), Push(1), Op(LtS), If(vec![Push(1)], vec![Push(2)])])]` at depth 4 prints exactly the section 5 shapes (write the expected string out).
  Run: `cargo test -p tatic --lib fragment_bodies_contain_no_raw`
  Expected: compile error (`entry` not found).
- [ ] **Step 3: Convert** by the mapping above. Then `.wat` becomes `.wat()` at every reader. Replace `arith_instr` and `cmp_instr` with `op_of`, and update the `ir::check` `expect` messages and the three comments.
- [ ] **Step 4: Goldens and fuzzers.**
  - Run `cargo test -p tatic --test golden_wat` with no `UPDATE_GOLDEN`; all 28 goldens are compared.
  - Then `cargo test -p tatic --lib` (the lib suite includes `ir_fuzz`).
  Expected: all pass, and `git status --short crates/tatic/tests/golden` is empty.
- [ ] **Step 5: Size check, guard loop, commit.** Set the allowlist row to the new `wc -l` count (≤ the Step 1 value), or delete it if the file is under 1000 lines.
  ```bash
  git add crates/tatic crates/tatic-wasm Cargo.toml Cargo.lock scripts/check/size_allowlist.txt PARKED.md docs/TOUR.md
  git commit -m "jit: the lowering emits Ins and prints WAT from it; CompiledFragment.module; PrimOp -> Op map"
  ```

### Task 5: Operator table check against eval and wasmtime

**Files:**
- Create: `crates/tatic/src/jit/op_table_tests.rs` (`#[cfg(test)] mod op_table_tests;` in `jit.rs`)

**Interfaces:**
- Consumes:
  - `shape::op_of` and `Op::{term, kind}`
  - `compile::try_compile`, `CompiledFragment::wat()` and wasmtime (follow `ir_fuzz.rs`'s `run_wasm` pattern: instantiate once per row)
  - `lang::eval::apply_term` (`eval.rs:165`) and `syntax::parse` (`syntax.rs:580`)
  - `tatic_kernel::def_eq` and `tatic_wasm::encoding::lit`
- Produces: tests only.

- [ ] **Step 1: Write the tests.** They share one helper, `fn agree(n: usize, pairs: &mut dyn Iterator<Item = (u64, u64)>)`. For each `PrimOp` p with `op_of(p) = Some(o)`:
  - The source is `\a b. a OP b` for word rows and `\a b. if a OP b then 1 else 0` for bit rows. It is compiled and printed by the production path.
  - For each pair, sign-extend x and y from n bits to i64, then read r_eval from `apply_term` and r_wasm from wasmtime, both masked to n bits.
  - Assert `r_eval == r_wasm`.
  - Assert that `app2(o.term(n), lit(n,x), lit(n,y))` is `def_eq` to `lit(n, r)` (word) or `lit(1, r)` (bit).
  - Then check `Op::LtU`. It has no source op, so there is no eval or wasm side: only its kernel term against r = Rust's unsigned `<` on the masked values.
  ```rust
  #[test] fn op_table_agrees_at_n64_on_edges()            // EDGES (copy ir_fuzz.rs:18) squared, n = 64
  #[test] #[ignore] fn op_table_agrees_at_n8_exhaustive() // all 65,536 pairs, n = 8; prints "row <op> done <ms>" per row
  ```
- [ ] **Step 2: Show the check can fail, then run.**
  - Show each assertion failing on its own, with `cargo test -p tatic --lib op_table_agrees_at_n64`, reverting after each:
    - Map `Lt` to `LtU` in `op_of`: the eval-vs-wasm assertion fails.
    - Make `Op::LtS.term` return `lt_u(n)`: the `def_eq` assertion fails.
  - Run it again and time it. It stays a default test, since it is the only always-on guard on the table. If it takes over 1 s, cut the edge set to `{MIN, -1, 0, 1, MAX}`, and record that in doc 15.
  - Then: `powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind probe -Name v07-op-table-n8 -Affinity CFF -Command "cargo test -p tatic --lib op_table_agrees_at_n8_exhaustive -- --ignored --nocapture"`.
  - If it takes over a minute, report the time in the closing report, as the spec asks. If the per-row prints project past 10 min, stop the run and report it to the user before going on.
  Expected: each mutation fails its own assertion, and the test passes once reverted. The n = 8 run exits 0. Record its time and the n = 64 test's time in doc 15.
- [ ] **Step 3: Commit.**
  ```bash
  git add crates/tatic/src/jit.rs crates/tatic/src/jit/op_table_tests.rs docs/tier-cycle/15-the-jit-and-the-target-machine.md docs/runs.md
  git commit -m "jit: operator table checked against eval and wasmtime (n = 64 edges; n = 8 exhaustive, ignored)"
  ```

### Task 6: The gate, the fragment predicate, and its cost measurements

The measurements run on the production gate. Their results set the bounds by section 8's rules, so they come before `in_fragment` is final.

**Files:**
- Create: `crates/tatic/src/proof/gate.rs`, with tests in `crates/tatic/src/proof/tests/gate.rs` (the `proof/tests/` layout)
- Modify: `crates/tatic/src/proof.rs` (`pub mod gate;`), `crates/tatic/src/proof/tests.rs` (`mod gate;` beside `mod basics;` at 28-31), doc 15; `crates/tatic-wasm/src/wasm.rs` only if Step 4's stack rule triggers

**Interfaces:**
- Consumes:
  - `Wasm { n: 64 }` with `prog`, `meaning`, `upd`, `v` and `g`; also `choose`, `well_formed`, `Op::term`, `shape::op_of`
  - `tatic_kernel::{scoped, check, def_eq, grow}`
  - `lang::term::{Term, TermStore, PrimOp}`, and for tests `compile::compile_specialised`, `CompiledFragment::entry`
  - The statement and lhs follow the spike's `sym_law` (patch), with fuel 1 and the frame of section 3.
- Produces:
  - `pub fn in_fragment(store: &TermStore, h: Hash, arity: usize) -> bool`, by section D3a's rule:
    - the term is non-recursive, arity ≥ 1, and has `arity` leading `Abs`
    - the body holds only `Var i` (i < arity), `Lit`, and `Prim` with `op_of` `Some`
    - every `If` condition is a bit-result `Prim` whose operands contain no `If`
    - every `If` is in tail position: the body itself, or an arm of a tail `If`
    - no comparison appears outside an `If` condition
    - plus T6 Step 4's bounds, if triggered; "tree size" is `compile::tree_size` (make it `pub(crate)`)
  - `pub fn gate(store: &TermStore, h: Hash, arity: usize, code: &[Ins]) -> bool` is `gate_with(store, h, arity, code, 1, false)`.
  - `pub(crate) fn gate_with(store, h, arity, code, fuel: u32, strip_loop: bool) -> bool`. With `strip_loop`, it asserts `code` is `[Loop(body)]` and proves `body`. It works as follows:
    - false if `!well_formed(code, &[])`
    - otherwise, inside `scoped`, it builds section 6's statement at n = 64 and returns whether `refl` has that type
    - the frame is a private fold of `Wasm::upd` over the parameters
    - `cps` is a Rust recursion over `Term` with a meta-continuation `&dyn Fn(&mut Cx, Expr) -> Expr`, evaluating a, then b, then the op
    - `Var i` maps to `q_{m-1-i}`
    - the fuel-1 fallback (Step 4) changes only what `gate` passes, to `(0, true)`

- [ ] **Step 1: Write the failing tests** in `proof/tests/gate.rs`. Accepting cases compile with `compile_specialised` and call `gate(store, h', arity, frag.entry())`. A `pub(crate) fn mutate(code: &[Ins], f: &dyn Fn(&Ins) -> Option<Ins>) -> Vec<Ins>` helper replaces the first match, recursing into `If` and `Loop`. It goes in `crates/tatic/src/testing/ins_mutate.rs`, declared in `testing`'s module list, because T7's `jit/tests.rs` uses it too.
  ```rust
  #[test] fn gate_accepts_the_fragment_table()
  //   [(inc,1), (doubling(4),1), (straight_line,2), (specialised \v0. v0+5,1), (specialised \v0. 3+4+v0,1),
  //    (\a b. a - b, 2), (\a b c. c, 3), (\a. a + MIN built with s.lit(i64::MIN), 1)]; each also in_fragment
  #[test] fn gate_rejects_mutations()   // spec Goal 2, each on every term that has the instruction it changes:
  //   swap If arms (straight_line); LtS->LtU (straight_line); Add->Sub (all 5); Mul->Add (straight_line);
  //   Push(v)->Push(v+1) (inc, straight_line, both specialised); LocalGet(0)<->LocalGet(1) (straight_line);
  //   and Raw("nop") appended inside the Loop (returns false, no panic)
  #[test] fn in_fragment_rejects_the_rest()
  //   factorial (recursive) and twice (higher-order) [from basics.rs 150-162]; \a b. a / b (Div);
  //   \a b. 1 + (if a < b then a else b) (operand If); \a b. if (if a < b then a else b) < 1 then 1 else 0 (If in a condition);
  //   the arity-0 term `5`; \f. f 1
  ```
  Run: `cargo test -p tatic --lib gate`
  Expected: compile error (`proof::gate` missing).
- [ ] **Step 2: Implement `in_fragment` (without bounds) and `gate`.**
  Run: `cargo test -p tatic --lib gate`
  Expected: all pass.
- [ ] **Step 3: Write the measurements** in the same file, as two `#[ignore]` tests that print `name ms` lines:
  - `measure_gate_costs` covers three things:
    - Fuel: `inc` through `gate_with(.., 1, false)` against `gate_with(.., 0, true)`.
    - Doubling: `doubling(d)` for d = 1..13, each on a fresh `std::thread::Builder::new().stack_size(256 << 20)` thread, printing the build ms and the check ms. It skips the rest once one d passes 60 s.
    - Mul: `\a b. a * b`, and `\a b. if a < b then a * b else a`.
  - `measure_stack_2mb`: `doubling(13)` on a 2 MB thread. It runs alone, because an overflow aborts the exe.
  Run each through the wrapper: `run.ps1 -Kind probe -Name v07-gate-<test> -Affinity CFF -Command "cargo test -p tatic --lib <test> -- --ignored --nocapture"`.
  Expected: exit 0. For `measure_stack_2mb`, an overflow is a result rather than a failure.
- [ ] **Step 4: Apply section 8's rules and record them in doc 15** with the run ids:
  - Fuel 1 over 2x the bare body: take section 6's fallback (`gate` strips the wrapper), and add the trusted fact "a `loop` with no `br` equals its body" to doc 15 and to `gate.rs`'s doc.
  - `doubling` over 0.4 s at some d < 13: `in_fragment` gains `tree_size(h) <= B`, where B is the largest passing tree size. Add `\x. t_d` at the edge to the two tests (accepted at the passing d, rejected above it).
  - Either `Mul` measurement over 0.4 s: `Mul` with two non-`Lit` operands leaves the fragment. Add both `Mul` terms to `in_fragment_rejects_the_rest`; `straight_line`'s `a*2` stays accepted.
  - 2 MB overflow: put `tatic_kernel::grow(|| ..)` at the top of each recursive step of `Wasm::seq` (tatic-wasm) and of `cps` (`gate.rs`). `grow` only switches segments when the current one is nearly full, so a single wrap at the top would not help. Then rerun `measure_stack_2mb`, and drop its `#[ignore]` once it passes in under 2 s (else keep it ignored, run at the T7 workspace run).
  Each triggered rule's change has a test that failed before it.
- [ ] **Step 5: Guard loop** (TOUR gets `proof/gate.rs` with `in_fragment` and `gate` in the data flow), then commit.
  ```bash
  git add crates/tatic/src/proof.rs crates/tatic/src/proof/gate.rs crates/tatic/src/proof/tests.rs crates/tatic/src/proof/tests crates/tatic/src/testing crates/tatic/src/jit/compile.rs crates/tatic-wasm docs/TOUR.md docs/tier-cycle/15-the-jit-and-the-target-machine.md docs/runs.md
  git commit -m "proof: the straight-line gate (emitted Ins proved equal to the source at n = 64), the fragment predicate, its costs"
  ```

### Task 7: Route installs, delete `prove_pure_expr`, update docs

**Files:**
- Modify:
  - `crates/tatic/src/jit.rs`: `try_install` (204-275), `kernel_verify` (305-319), and the doc comments at 21, 43, about 244-257, 281 and 297-309
  - `crates/tatic/src/jit/tests.rs`: line 126, plus new tests
  - `crates/tatic/src/proof.rs`: delete `prove_pure_expr` (420) and `finish` (401), plus `setup` (377) and `LitScope::Arith` (279-281, doc at 259) if they become dead; also the module doc and the comment at 357
  - `proof/tests/basics.rs`: delete the 3 `prove_pure_expr` tests (44, 155, 162; the last two were re-homed in T6), but keep `a_shared_subterm_is_denoted_once` (24-37): it is the only pin of `denote`'s subterm sharing, and `denote` stays. If `setup` goes, rewrite that test over a hand-built `ArithPostulates`; if that cannot be done in a few lines, keep `setup` as `#[cfg(test)]`
  - `benches/proofs.rs`: delete `fn straight_line_proof` (17, its bench id `straight_line_refl_proof`), its entry in `criterion_group!` (169), and the `prove_pure_expr` import (10)
  - `proof/universal.rs:355` and `proof/closures.rs:68`
  - docs: `docs/TOUR.md` (35, 87, 109), `docs/proven.md` (222, 355), `ROADMAP.md` v0.7 (an evidence line under "Done when"), and doc 15 (a closing line)

**Interfaces:**
- Consumes: `proof::gate::{in_fragment, gate}`, `Compiled { frag, specialised }` (`compile.rs:451`), `CompiledFragment::entry`.
- Produces:
  - `fn prove_install(store: &TermStore, h: Hash, arity: usize, code: &[Ins]) -> bool` (a `JitEngine` associated fn beside `kernel_verify`): `if in_fragment(store, h, arity) { gate(store, h, arity, code) } else { kernel_verify(store, h, arity) }`. That one fn holds the routing, so its tests pin "the gate's verdict is final".
  - `try_install` calls `prove_install(s, h, arity, frag.entry())` where it called `kernel_verify`, with `let (s, h) = specialised.as_ref().map_or((store, term), |(s, h)| (s, *h));`.
  - `kernel_verify` without `prove_pure_expr`, signature unchanged.

- [ ] **Step 1: Record the bench baseline before its row is deleted.**
  Run: `cargo bench -p tatic --bench proofs -- straight_line_refl_proof --warm-up-time 0.3 --measurement-time 0.5 --sample-size 10`
  Expected: about 3.7-4.3 µs. Record it in doc 15 beside T6's gate times.
- [ ] **Step 2: Write the failing tests** in `jit/tests.rs`:
  ```rust
  #[test] fn the_gates_verdict_is_final_for_fragment_terms()
  //   straight_line, specialised: prove_install(.., frag.entry()) is true; with the If arms swapped
  //   (T6's mutate) it is false, although kernel_verify(s, h, 2) alone is true for the same term
  #[test] fn fragment_terms_install()                    // each of the five: try_install gives CacheEntry::Compiled
  #[test] fn an_operand_if_installs_through_the_chain() // \a b. 1 + (if a < b then a else b): Compiled, and in_fragment is false
  ```
  Change line 126 to `compile_specialised` then `prove_install(.., frag.entry())`, expecting true. Lines 64, 89 and 125 stay as they are, and the `\a b. a / b` test (254, asserts `compiled == 1`) must stay green.
  Run: `cargo test -p tatic --lib jit::tests`
  Expected: compile error (`prove_install` missing).
- [ ] **Step 3: Route and delete.**
  - Wire `prove_install` and `try_install` as in Produces.
  - Delete `prove_pure_expr` and `finish`, then whatever `cargo build -p tatic --all-targets` reports dead. Grep each before deleting. `denote` stays (`universal.rs:378`).
  - Delete T1's `c1_probe_terms` if it was committed; it should have been reverted.
  Run: `cargo build -p tatic --all-targets 2>&1 | grep -cE "^(warning|error)"`, then `cargo test -p tatic --lib`
  Expected: 0, and all pass.
- [ ] **Step 4: Run the whole workspace.**
  Run: `powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind gate -Name v07-workspace -Affinity CFF -Command "cargo test --workspace"`
  Expected: exit 0. `cargo test --workspace -- --list | grep -c ': test$'` should equal T2 Step 1's count, minus the deleted basics tests, plus the tests this plan added (count them from the diff).
- [ ] **Step 5: Docs, the stale-claim grep, guard loop, commit.**
  - Update the docs listed above.
  - Run `rg -n "only check of|prove_pure_expr|cmp_instr|arith_instr|crate::encoding|church_bv::encoding|church-bv/src/(encoding|wasm)" docs crates ROADMAP.md PARKED.md` and fix every hit (known: `PARKED.md:183`; doc 15's 613, 614, 649 and 702 are dated history unless the section is live) outside dated history (doc 15's dated sections, `docs/runs/`, specs and plans).
  - Set this plan's and the spec's front matter to `status: done`.
  - Run the guard loop.
  ```bash
  git add crates/tatic docs ROADMAP.md PARKED.md
  git commit -m "jit: fragment terms install on the gate's verdict alone; prove_pure_expr deleted"
  ```

## End-state fit

| Change | Lives in | Replaces | Deletes |
|---|---|---|---|
| encodings, machine (`wasm.rs`), laws (`wasm/laws.rs`) | `crates/tatic-wasm` (T2) | church-bv `encoding/`, `wasm.rs`, `BitPair`/`Bits4`, 4 `search.rs` items | the church-bv copies and their `mod` lines |
| `and_truth`/`or_truth`/`xor_truth` | `tatic-wasm/src/encoding/gates.rs` (T2) | 3 inline closures in `OP_INFO` | the closures |
| `Ins` as data, `LocalGet`, `Op`, `Raw`, `shape`/`well_formed` | `tatic-wasm/src/wasm.rs`, `ops.rs` (T3) | `Push(Expr)`, `Bin(Expr)`, `Cmp(Expr)`; `out_stack`'s own walk | the `Expr` payloads; the assert-based walk |
| `lt_s`, `le_s`, `eq_bit`, `mul` | `tatic-wasm/src/encoding/gates.rs` (T3) | the spike's copies (patch only) | nothing in tree |
| `print_body` | `tatic-wasm/src/print.rs` (T4) | text emission in `node()`/`read` | the line pushing |
| `CompiledFragment.module`, `Item`, `wat()`, `entry()` | `tatic/src/jit/compile.rs` (T4) | the `wat: String` field | the field |
| templates | `tatic/src/jit/lower_wat/templates.rs` (T4) | the same code in `lower_wat.rs` | `lower_wat.rs`'s allowlist row if under 1000 |
| `op_of` | `tatic/src/jit/shape.rs` (T4) | `arith_instr`, `cmp_instr` | both fns; the `ir -> shape -> lower_wat` cycle |
| table check | `tatic/src/jit/op_table_tests.rs` (T5) | nothing (a new guard on the trusted table) | none |
| `gate`, `in_fragment`, cost tests | `tatic/src/proof/gate.rs`, `proof/tests/gate.rs` (T6) | `prove_pure_expr` for fragment terms | none here |
| routing (`prove_install`) | `jit.rs`, called by `try_install` (T7) | the `\|\|` chain for fragment terms | `prove_pure_expr`, `finish`, dead `setup`/`LitScope::Arith`, 3 tests, a bench row |

Stopgaps: none planned. A bound T6 adds to `in_fragment` is a spec rule, with its curve in doc 15.

Calls made here that the spec left to the builder:
- The measurements run on the production gate in T6, not first on the spike's machine. Nothing in T2-T5 depends on them, and every outcome changes only `gate` and `in_fragment`. The closure check stays first.
- The routing lives in one fn, `prove_install`, which takes the code, so a mutated list can test that the gate's verdict is final. (At install, `verify` would catch the mutation first.)
- `out_stack` and `well_formed` share one private `shape` walk.
- The file names: `ops.rs`, `print.rs`, `wasm/laws.rs`, `lower_wat/templates.rs`, `op_table_tests.rs`, `encoding_scaling.rs`, `proof/tests/gate.rs`.
