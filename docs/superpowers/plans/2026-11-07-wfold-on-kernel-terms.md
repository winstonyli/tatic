---
status: done
---

# The width-free fold on kernel terms (w1) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** `wnat.rs` and `wfold.rs` build the kernel's interned `Expr` through the `Cx` builder instead of the named tree `T`, share
one proof-step builder (`StepProof`) with `machine.rs#tree_proof`, and move to `crates/church-bv/src/`, so naming `T` in them is a
compile error.

**Architecture:** five commits in the spec's order, then a measurement commit. `Cx` moves to `encoding/cx.rs`; `constant` is keyed
by its build function; `StepProof` is extracted from `tree_proof` with no change to the terms it builds (a gate run shows the counts
unchanged); wnat and wfold are ported together in one commit; then `git mv` to `src/`. The verdict is a retired-instruction count on
the 1-in-97 sweep sample and the full sweep's 45621 proofs.

**Tech Stack:** Rust (`crates/church-bv`, `crates/tatic-kernel`), `cargo test`, bash guards in `scripts/check/`, `~/.claude/runs/run.ps1`,
`~/.claude/samply/icount.ps1`, `scripts/gate/gate.sh`.

**Spec:** `docs/superpowers/specs/2026-11-07-wfold-on-kernel-terms-design.md` (decisions z1 a1 b1 c1 d1 e1, 2026-11-07). The spec is
the authority; section names below ("Design, The law" and so on) are its sections.

## Global Constraints

- Paths are relative to `crates/church-bv/src/` unless they start with `crates/`, `docs/`, `scripts/`, `tools/` or `~`.
- Unit-test loop: `cargo test -j 10 -p church-bv --lib -- <filter>`; the whole lib suite (`cargo test -j 10 -p church-bv --lib`, 334
  tests today, about 12 s once built) at the end of each task. A build or run expected over about a minute (release builds, a second
  target dir, the gate, the sweep, the counts) goes through
  `powershell -NoProfile -File "$USERPROFILE/.claude/runs/run.ps1" -Kind <probe|gate|sweep> -Name <n> -Affinity CFF -Command "..."`,
  called from bash, with 8.3 paths inside `-Command`.
- Guards before every commit, from the repo root: `bash scripts/check/cite_check.sh`, `tour_check.sh`, `layout_check.sh`,
  `size_check.sh`, `test_placement_check.sh`, `script_header_check.sh`, `front_matter_check.sh` (each prints no failure).
- Imports (spec, "Left to the plan" 4): no glob over `width` or `wnat`. In Task 4, while the files sit in `uniform/` (whose parent has no
  `use` lines), each starts `use crate::*;` (the root re-exports `tatic_kernel::*` and `encoding::*`) and names what it takes from
  siblings: `use super::wnat::{..};`, `use crate::machine::{..};`. These lines need no change in Task 5 (from a child of the crate
  root `super` is `crate`). The root glob-imports `tatic_kernel`, `encoding`, `rewrite`, `search`, `machine` and `host`; look there
  first on an ambiguity. Names wnat defines itself (`add`, `shl`, `carry`, `eqb`) shadow the glob. `Node` is ambiguous
  under the glob (`tatic_kernel::Node` and `rewrite::Node`): wfold keeps its explicit `use crate::rewrite::{Node, Term, ..}` and
  writes the kernel's as `tatic_kernel::Node::Pi`.
- A rule or helper the port needs that no task lists is reported in the commit body, never added to `encoding/` silently.
- No builder in `wnat.rs` or `wfold.rs` computes a de Bruijn index by hand or uses a reserved free name (spec, Goals): after Task 4,
  `var(` and `v("` appear in neither file (`StepProof` and `lemma_n` keep their indices).
- Tests call `tatic_kernel::check(&Ctx::new(), &proof, &stmt)` directly, and add `typecheck(&stmt)` only where the statement is built
  by hand (spec, "Tests and regions"); no shared check helper. Each proof is built and checked inside its own
  `tatic_kernel::scoped(|| ..)` (one region per proof, so a test over several pairs opens one per pair).
- No python. Perl or bash for any script, in the scratchpad.
- Commits: small and topical, explicit pathspecs (never `git add -A`; the `docs/runs.md` rows a task's runs wrote go in that task's
  commit), after `git diff --stat`, ending with the session's attribution line. No push, tag or bump.
- Memory caps: `run.ps1`'s default 12 GB, the gate `-MaxMemGB 24`. Before Task 6's second target dir, `(Get-PSDrive C).Free/1GB` is at
  least 5, else stop and report.

## Review Focus

- A goodness proof or the invariant used at a depth other than the one it was bound at: the kernel accepts it but rechecks it per use
  (spec, Design, "The proof root"). Expect every use to go through the bound `h`; `w_fold_proof_type_is_the_statement` prints the
  proof's `term_sizes`, and asserts the inferred type's distinct-node count stays within twice the statement's (a proof leaking
  into a type inflates it). Pinned in Task 4 step 11.
- A witness paired with the wrong operand (`g_i` for `x_j`): the statement never mentions `g_i`, so `def_eq` on instances cannot see
  it. Expect rejection by a full `check` at a mixed assignment, after the same `check` passes with the witnesses paired. Pinned in Task
  4 step 10.
- `constant` given two different build functions: expect two entries. Pinned in Task 2 step 1; a capturing closure is
  ruled out by the `fn() -> Expr` type, not by a test.
- `StepProof` changing `tree_proof`'s terms or its `shared_lemma` keys: the main prover would re-prove or mis-share lemmas. Expect equal
  outer and discharged proof sizes and lemma counts before and after (Task 3 steps 1 and 4); the gate (Task 3 steps 7-8) shows the
  prover's counts unchanged.
- A placeholder witness for a later carry leaking into a returned witness: expect the kernel to reject it (ill-typed), never a silent
  accept. Pinned by the full sweep (Task 6 step 5) and the controls of Task 4 step 7; no dedicated test (spec, Design, "Witnesses of
  later carries").

---

### Task 1: Move `Cx` to `encoding/cx.rs`

**Files:**
- Create: `encoding/cx.rs` (inline `#[cfg(test)] mod tests`)
- Precondition: this plan and the spec's review amendments are already committed (the planning commit), so Task 1's commit carries
  only the `status: active` lines of the two front matters.
- Modify: `encoding.rs` (add `mod cx;` and `pub use cx::*;`), `wasm.rs:13-73` (delete the moved block; the rest of `wasm.rs` reaches
  the items through `use super::*`), `docs/TOUR.md` line 39 (`encoding/` gains "`cx` (the binder-depth builder `Cx`/`At`, telescopes
  `law`/`statement`)"), front matter of the spec and this plan (`status: active`)

**Interfaces:**
- Produces (re-exported through `encoding.rs`, so in scope crate-wide):
  - `pub struct At(Expr, u32)` (`Clone, Copy`); `pub struct Cx(u32)` (`Default`).
  - `Cx::at(&self, a: At) -> Expr`, subtracting with `checked_sub(..).expect("an At used below its birth depth")`;
    `Cx::mark(&self, e: Expr) -> At`; `pub fn under(&mut self, body: impl FnOnce(&mut Cx, At) -> Expr) -> Expr` (today's private
    `bind`, renamed); `Cx::lam(&mut self, ty: Expr, body) -> Expr`; `Cx::pi(&mut self, ty: Expr, body) -> Expr`.
  - `pub type Ty<'a> = Box<dyn Fn(&mut Cx, &[At]) -> Expr + 'a>`; `macro_rules! ty` followed by `pub(crate) use ty;` in `cx.rs`, so
    `ty!(|c, x| e)` resolves through the `pub use cx::*` glob.
  - `pub(crate) fn tele(c: &mut Cx, lambda: bool, tys: &[Ty], xs: &mut Vec<At>, body: &mut dyn FnMut(&mut Cx, &[At]) -> Expr) -> Expr`:
    `wasm.rs` calls it at lines 268 (`ctors`) and 514 besides `law` and `statement`.
  - `pub fn statement(tys: &[Ty], stmt: impl FnMut(&mut Cx, &[At]) -> Expr) -> Expr` (the Pi telescope alone).
  - `pub fn law(tys: &[Ty], stmt, proof) -> (Expr, Expr)`, its statement half `statement(tys, stmt)`.

- [ ] **Step 1: Write the failing tests** in `encoding/cx.rs`:

```rust
#[test]
fn under_binds_a_variable_with_no_lambda() {
    let mut cx = Cx::default();
    assert!(cx.under(|cx, x| cx.at(x)) == var(0));
    let s = sigma(bool0(), Cx::default().under(|cx, x| id(bool0(), cx.at(x), t())));
    assert!(tatic_kernel::typecheck(&s).is_ok());
}
#[test]
#[should_panic(expected = "below its birth depth")]
fn an_at_used_below_its_birth_depth_panics() {
    let mut cx = Cx::default();
    let mut leaked = None;
    cx.lam(bool0(), |_, x| { leaked = Some(x); t() });
    cx.at(leaked.unwrap());
}
#[test]
fn statement_is_the_laws_statement() {
    let tys = [ty!(|_c, _x| bool0()), ty!(|c, x| id(bool0(), c.at(x[0]), c.at(x[0])))];
    let stmt = |c: &mut Cx, x: &[At]| id(bool0(), c.at(x[0]), c.at(x[0]));
    let (_, s) = law(&tys, stmt, |c, x| refl(c.at(x[0])));
    assert!(s == statement(&tys, stmt));
}
```

- [ ] **Step 2: Run them.** `cargo test -j 10 -p church-bv --lib -- cx::`. Expected: compile error (no `encoding::cx`, no `under`,
  no `statement`).
- [ ] **Step 3: Move the block** to `encoding/cx.rs`, rename `bind` to `under`, add `statement`, rebuild `law` on it, checked depth.
  Header comment: one line (binder depth while a term is built; terms written with names). Expected: `cargo check -j 10 -p church-bv`
  clean.
- [ ] **Step 4: Run** `cargo test -j 10 -p church-bv --lib -- cx:: wasm`. Expected: the three new tests and every `wasm` test pass.
- [ ] **Step 5: Whole lib suite and guards.** Expected: `test result: ok. 337 passed`; guards clean.
- [ ] **Step 6: Commit** `encoding/cx.rs encoding.rs wasm.rs docs/TOUR.md` and the two front matters: "church-bv: Cx and its
  telescopes move to encoding/cx.rs, with statement, a public under and a checked depth (w1 step 1)".

### Task 2: Key `constant` by its build function

**Files:**
- Modify: `encoding/gates.rs:42-75`, `encoding/division.rs:10,16`, `encoding/good.rs:7`, `job.rs:685`
- Test: `encoding/tests.rs`, after `constants_are_built_once_per_generation`

**Interfaces:**
- Produces: `pub(crate) fn constant(build: fn() -> Expr) -> Expr` (reaches the crate root through `pub use gates::*`), memoized in `CONSTANTS: GenMemo<usize, Expr>` under
  `build as usize`. All nine call sites, slots 0-8, drop theirs.

- [ ] **Step 1: Write the failing test**:

```rust
/// Two build functions are two entries; one build function is one entry however often it is called.
#[test]
fn constants_are_keyed_by_their_build_function() {
    tatic_kernel::scoped(|| {
        let (a, b) = (constant(|| lam(bool0(), var(0))), constant(|| lam(bool0(), lam(bool0(), var(1)))));
        assert!(a == lam(bool0(), var(0)) && b == lam(bool0(), lam(bool0(), var(1))), "a second build function got the first's term");
        let k = || lam(sort(0), var(0));
        assert!(tatic_kernel::node_key(&constant(k)) == tatic_kernel::node_key(&constant(k)));
    })
}
```

- [ ] **Step 2: Run it.** `cargo test -j 10 -p church-bv --lib -- constants_are`. Expected: compile error (`constant` takes two
  arguments).
- [ ] **Step 3: Change `constant`** to the signature above; drop the slot at the nine call sites (`gates.rs` 53, 56, 59, 69, 72, 75;
  `division.rs` 10, 16; `good.rs` 7); `job.rs:685` reads `"gen_memo: closed constants by build function"`. The doc comment says a
  duplicate address (two codegen units) only rebuilds an equal term.
- [ ] **Step 4: Run** `cargo test -j 10 -p church-bv --lib -- constants_are encoding`. Expected: both `constants_are_*` and the
  encoding tests pass.
- [ ] **Step 5: Whole lib suite and guards.** Expected: 338 passed.
- [ ] **Step 6: Commit** the five files: "church-bv: encoding::constant is keyed by its build function, not a hand-numbered slot (w1
  step 2)".

### Task 3: Extract `StepProof` from `tree_proof`

**Files:**
- Modify: `machine.rs:256-385` (`tree_proof`; its closures sit at 263-375), `docs/TOUR.md` (glossary entry before **Stragglers**:
  "**StepProof**: one bit position's step proof over two machines and an encoding, shared by `tree_proof` and the width-free fold.
  `crates/church-bv/src/machine.rs#StepProof`")
- Run record: `docs/runs.md` (rows written by `run.ps1`)

**Interfaces:**
- Produces, in `machine.rs`:

```rust
type Step = std::rc::Rc<(Expr, Vec<Expr>, Vec<Expr>)>; // (output, next carries, phi of the carries)
pub(crate) struct StepProof<'a> {
    pub(crate) machines: &'a [Machine; 2],
    pub(crate) enc: &'a Encoding,
    pub(crate) k: usize,
    pub(crate) gops: GoodOps,
    steps: std::cell::RefCell<hashbrown::HashMap<(usize, Vec<bool>), Step>>,
}
impl<'a> StepProof<'a> {
    pub(crate) fn new(machines: &'a [Machine; 2], enc: &'a Encoding, k: usize) -> Self;
    pub(crate) fn phi(&self, side: usize, j: usize, s: &[Expr]) -> Expr;   // table_app over enc.phi[side][j]
    fn g(&self, j: usize, v: &[Expr]) -> Expr;                             // table_app over enc.g[j]
    pub(crate) fn step_of(&self, side: usize, v: &[Expr]) -> (Expr, Vec<Expr>);
    fn side_f(&self, side: usize, j: usize, v: &[Expr]) -> Expr;
    fn step_at(&self, side: usize, v: &[Expr], bits: Option<&[bool]>) -> Step;
    pub(crate) fn lemma(&self, side: usize, j: usize) -> (Expr, Expr);     // (closed lemma over nv bits, its type)
    pub(crate) fn eq(&self, j: usize, lem: [&Expr; 2], ug: &[Gb], st: [&[Gb]; 2], ip: &[Expr]) -> (Expr, Expr, Expr);
}
```

  `m` is `self.enc.phi[0].len()` and `nv` is `self.k + self.machines[side].carries()`, written where used. `lemma` is the body that
  `by_cases` builds inside `shared_lemma` today (statement by `lemma_n_ty`, leaves `refl` of `step_at(.., Some(bits))`). `eq` is
  `core`'s `eq` closure with its free variables made parameters: `lemmas[side][j]` becomes `lem[side]`, and the enclosing `ug`, `st`
  and `ip` arrive as arguments; it returns `(fl, fr, proof)`. `g` and `side_f` are private because only `lemma` and `eq` use them;
  `enc`, `k`, `phi` and `step_of` are `pub(crate)` for wfold's `agree` and `pred` (spec, "Visibility").
- Consumes: nothing from Tasks 1-2.

- [ ] **Step 1: Pin the terms before extracting.** Add to `machine.rs`' tests:

```rust
/// tree_proof's terms, its lemmas' statements and bodies, and its shared_lemma keys, pinned across the StepProof extraction
/// (w1 step 3). Each law gets a fresh Job, since discharge empties job.lemmas.
#[test]
fn tree_proof_terms_are_pinned() {
    let v = |i: usize| Term::v(i);
    let op = |a: Term, b: Term| Term::op(ADD, a, b);
    let laws = [ // the three of state_encoding_search_proves_three_leaf_sum_laws
        (op(op(v(0), v(1)), v(1)), op(v(0), op(v(1), v(1)))),
        (op(op(v(1), v(1)), Term::ONES), op(v(1), op(v(1), Term::ONES))),
        (op(op(v(0), Term::ONES), Term::ONES), op(v(0), op(Term::ONES, Term::ONES))),
    ];
    let mut pin = vec![];
    for (t1, t2) in laws {
        let job = &mut Job::new(Setup::process());
        tatic_kernel::scoped(|| {
            let (p, _) = add_tree_law(job, 4, 2, &t1, &t2).unwrap();
            let mut bound: Vec<(String, (usize, u128))> =
                job.lemmas.bound.iter().map(|(k, (_, s))| (k.clone(), tatic_kernel::term_sizes(&s.get()))).collect();
            bound.sort();
            let whole = tatic_kernel::term_sizes(&discharge(job, p));
            println!("PIN outer {:?} whole {whole:?} statements {bound:?}", tatic_kernel::term_sizes(&p));
            pin.push((tatic_kernel::term_sizes(&p), whole, bound.len()));
        })
    }
    assert_eq!(pin, vec![/* recorded at Task 2's commit */]);
}
```

  `whole` is the proof with every lemma body discharged into it, so it covers what `StepProof::lemma` and `step_at` build; the
  statement sizes go to the printed list. Run it alone, `cargo test -j 10 -p church-bv --lib -- tree_proof_terms_are_pinned --nocapture
  --test-threads=1` (no `LEMMA_CACHE` set: `discharge` needs every body), at Task 2's commit; write each law's (outer sizes, whole
  sizes, number of statements) into the assertion, and save the `grep '^PIN'` lines to the scratchpad. Expected: the test passes with
  the recorded values.
- [ ] **Step 2: Baseline gate exe** at Task 2's commit: `mkdir -p "$LOCALAPPDATA/claude-runs/tatic/w1-exes"`, then
  `run.ps1 -Kind probe -Name w1-release-a -Command "cargo build --release -j 10 -p church-bv"` and copy
  `target/release/church-bv.exe` to `w1-exes/a.exe`. Expected: exit 0, the copy exists. The gate also needs
  `tools/runs/target/release/runs.exe` (present; `streams_ab.sh` says so if not).
- [ ] **Step 3: Extract.** Write `Step` and `StepProof` above `tree_proof`. `tree_proof` builds `let sp = StepProof::new(&machines, enc, k);`
  and its `lemmas` vec of wrappers (callers own the lemmas):
  `shared_lemma(job, format!("tree|{}|{k}|{nv}|F{j}|{:?}|{:?}", machines[side].key(), enc.g[j], enc.phi[side]), |_| sp.lemma(side, j)).0`
  with `nv = k + machines[side].carries()`, the same key string `by_cases` builds today. `core` calls
  `sp.eq(j, [&lemmas[0][j], &lemmas[1][j]], &ug, [&st[0], &st[1]], &ip)` and runs `machines[side].step(&sp.gops, ..)`. Delete the
  local `gops`, `phi_expr`, `g_expr`, `step_of`, `side_f`, the local
  `Step`, `steps`, `step_at`, `CaseFn`, `by_cases` and the `eq` closure; `step_at`'s comment loses "and its P lemma". Expected:
  `cargo check -j 10 -p church-bv` clean.
- [ ] **Step 4: Run** `cargo test -j 10 -p church-bv --lib -- machine`, then the pin alone as in step 1. Expected: every `machine`
  test passes, including `tree_proof_terms_are_pinned`, and its `grep '^PIN'` lines equal the saved ones (`diff` prints nothing).
- [ ] **Step 5: Whole lib suite and guards.** Expected: 339 passed (the pin added); `size_check.sh` clean (`machine.rs` stays under
  1000 lines).
- [ ] **Step 6: B exe:** the same wrapped release build (`-Name w1-release-b`), copied to `w1-exes/b.exe`. Expected: exit 0.
- [ ] **Step 7: Run the gate:** `run.ps1 -Kind gate -Name w1-stepproof-gate -Affinity CFF -MaxMemGB 24 -Command "bash scripts/gate/gate.sh C:/Users/WINSTO~1/AppData/Local/claude-runs/tatic/w1-exes/a.exe C:/Users/WINSTO~1/AppData/Local/claude-runs/tatic/w1-exes/b.exe 1 2 3"`.
  Expected last line: `streams_ab: rules same in 9 of 9 loops; 0 of 6 arms failed`.
- [ ] **Step 8: Read the counts.** Per salt, A and B have equal M, equal held-out M and equal summed WORK counts (job CPU is load noise,
  not compared). The WORK counters are the rewriter's, so this shows the prover unchanged; the pin (steps 1 and 4) is what shows
  the terms, lemma bodies and keys unchanged. Any difference is an extraction bug: stop and debug, never accept it as noise.
- [ ] **Step 9: Commit** `machine.rs docs/TOUR.md docs/runs.md`: "church-bv: StepProof, one position's step proof, extracted from
  tree_proof; the gate's counts are unchanged (w1 step 3)", with the run id in the body.

### Task 4: Port wnat and wfold to `Expr`

The files stay in `uniform/`; Task 5 moves them. wnat is ported whole and its tests pass before wfold is touched (step 3): wnat is
one file whose stage proofs call the builders being ported, so it compiles only once all of it is on `Expr`. One commit at the end,
since a wfold on `T` cannot compile against a wnat on `Expr`.

**Files:**
- Modify: `uniform/wnat.rs` (whole), `uniform/wfold.rs` (whole), `uniform/width.rs` (delete `W`, `Sup`, `WRec` and their `comp`
  arms; the merged `Pi | Lm | Sig | W` arm loses `W` and its inner match; `Sig`, `Pair`, `SigRec` stay), `PARKED.md` (one entry)
- Test: the inline test modules of both files

**Interfaces:**
- Consumes: Task 1 (`Cx`, `At`, `Ty`, `ty!`, `law`, `statement`, `under`), Task 2 (`constant`), Task 3 (`StepProof`, its pub(crate)
  fields and methods); `encoding::{Gb, GoodOps, bit, good_bit, good_bool, bool0, t, f}`; kernel `sigma`, `pair`, `sigrec`, `wty`,
  `sup`, `wrec`, `id`, `refl`, `sym`, `trans_proof`, `cong1`, `check`, `typecheck`, `def_eq`, `infer`, `term_sizes`, `Ctx`, `Node`.
- Produces in `wnat.rs` (`pub(super)` where wfold uses them, else private):
  - closed constants through `constant`: `unit()`, `star()`, `empty()`, `tag_ty()`, `nw()`, `bw()`, `zero_w()`, `zero_tag()`,
    `succ_tag()`, `carry_fn()`, `add_fn()`, `zw()`; `shl_fn(fill: bool)` and `mul_fn(fill: bool)` return `constant(..)` of a fn item
    for `false` and build `true` directly.
  - closed values: `num(j: usize) -> Expr`, `stream_of(val: u128, nb: usize) -> Expr`.
  - applications of the constants (no binder, no `Cx`): `carry(a, c, i)`, `add(a, c)`, `shl(a)`, `eqb(a, c)` (`id(bool0(), a, c)`),
    `xor3(a, c, d)`; builders that bind take `&mut Cx` first: `succ_w`, `good_stream` (`Pi i:nw. good_bool() (a i)`), `maybe`,
    `just`, `goodmaybe`, `rec_w`, `shr`, `tmask`, `carry_at`, `ptw`, and the `tag_*` accessors as needed.
  - `pub(super) struct Tag { pub(super) x_ty: At, pub(super) m: At, pub(super) f: At, pub(super) ih: At }`.
  - `pub(super) fn tag_case(cx: &mut Cx, tag: &Tag, k: &dyn Fn(&mut Cx, Expr, Expr) -> Expr, z: Expr) -> Expr` (`k` gets `f w` and
    `ih w`; `w` never leaves).
  - `pub(super) fn ind(cx, tele, body, target, pred, hj, hn) -> Expr` with the spec's signature (Design, "`ind`").
  - `fn cases2(cx: &mut Cx, ..) -> Expr`: `width::cases2`'s parameters with a leading `cx`, `T` replaced by `Expr` and its binders
    by `cx.lam`.
- Produces in `wfold.rs` (private: only its own tests call them):
  - `fn encode(k: usize, t1: &Term, t2: &Term) -> Option<([Machine; 2], Encoding)>`
  - `fn proof(k: usize, machines: &[Machine; 2], enc: &Encoding) -> (Expr, Expr)` (proof, statement)
  - `fn operands(k: usize) -> Vec<Ty<'static>>`
  - `fn side(cx: &mut Cx, machine: &Machine, xs: &[At]) -> (Expr, Vec<Expr>)` (root, carry streams)
  - `fn agree(sp: &StepProof, l: &[Expr], r: &[Expr]) -> Vec<Expr>` (`eqb(sp.phi(0, q, l), sp.phi(1, q, r))` for `q < m`)
  - `fn sigmas(cx: &mut Cx, ts: &[Expr]) -> Expr`, `fn pack(cx: &mut Cx, ts: &[Expr], ps: &[Expr]) -> Expr`,
    `fn unpack(cx: &mut Cx, ts: &[Expr], t: Expr) -> Vec<Expr>`

- [ ] **Step 1: Port the wnat tests** to the new API, names and assertions kept: stage 1 types (`unit` and `empty` Sort1; `tag_ty`,
  `nw`, `bw` Sort2; `zero_w`, `num(1)`, `add_fn`, `shl_fn(false)`, `mul_fn(false)` at their types); stage 2's `product_bit_is` and the
  fill mutant; stages 3, 4a, 4b with their controls through `check`/`check(..).is_err()`; stage 4b's instantiation. `bit_of(v, p)`
  becomes `bit((v >> p) & 1 == 1)`, and 4b's local `let bit = ..` is renamed `want` so it does not shadow `bit`. The control
  `stmt_mul_shl(false, &noop)` passes `&|_cx, t| t`.
- [ ] **Step 2: Run** `cargo test -j 10 -p church-bv --lib -- w_index_`. Expected: compile errors (the API does not exist yet).
- [ ] **Step 3: Port the whole of wnat.** Comment `mod wfold;` out of `uniform.rs` in the working tree only (today's wfold imports
  wnat's `T` builders; restored in step 5, never committed commented). Two parts, one compile:
  - Constants and closed values: the constants, `num`, `stream_of`, `carry`/`add`/`shl`/`eqb`/`xor3`; `good_case` goes,
    `zero_tag`/`succ_tag` inline its `\P hj hn.` with body `hn` or `hj star`; `zero_w` and `succ_w` add only the `Sup` and its child
    lambda. Each constant's build function opens its own `Cx::default()` and binds with `lam`/`pi`/`under`, never `var(` (unlike
    `gates.rs`). The file's header comment is rewritten in `Expr` terms (today's lines 1-17 name `W(..)` and `WRec` in `T`).
  - Tag split, `ind`, stage proofs: `Tag`/`tag_case` replace `sel` and `selm`; `ind` builds the motive
  `\n. Pi tele. body(n, tele)` and the introductions as lambdas over `tele`, passing `tele`'s `At`s to `body`, `pred`, `hj`, `hn`;
  `noop`, `fw`, `sym`, `trans`, `cong3`, every `K(ex(..))` and every `T` builder go. The six stage-proof `rew` sites (today's lines
  253, 262, 307, 316, 334, 352) take the spec's two shapes: `trans_proof(&bool0(), &fl, &fr, &c, cong1(&bool0(), &bool0(), &F, l, r, p), h)`,
  or `cong1(..)` alone where the base is `refl` (253 and 262 by computation, 334 syntactically); line 352
  `cong1(&bool0(), &bool0(), &F, r, l, sym(&bool0(), &l, &r, p))`; `F = cx.lam(bool0(), ..)`, with `F l`, `F r`, `C` built explicitly.
  Telescopes: stage 3 `[y: bw, i: nw]`, stage 4b `[x: bw, y: bw, i: nw]`, the rest empty. `cases2` on `Cx` for `proof_add_comm`.

  Expected: `cargo test -j 10 -p church-bv --lib -- w_index_stage1 w_index_stage2` passes first, then `-- w_index_` runs all seven,
  each control rejected.
- [ ] **Step 4: Write the wfold tests** (replacing today's; names kept except where marked new):
  - `w_fold_add_associates`: `encode(3, (x+y)+z, x+(y+z))`, `proof`, `check` ok; a hand statement
    `statement(&operands(3), |cx, xs| ..)` = `Pi i:nw. eqb(add(add(x0,x1),x2) i, add(x0,add(x1,x2)) i)` over the `At`s is `def_eq`
    to `stmt`; the right side `add(x0, add(x1, x1))` is rejected.
  - `w_fold_a_false_table_is_rejected`: flip `enc.g[1][0]` in the returned `Encoding`, then `proof`: rejected; `encode(2, x+y, x)` is
    `None`.
  - `w_fold_the_law_families`: the 17 `proved(..)` lines unchanged; `proved` is `encode`, `proof`, `check`.
  - `w_fold_a_comparison_is_its_own_law`: `x < y = ~y < ~x` accepted; a hand statement over `side` of `Machine::parse(lt(x,y))` and
    of `Machine::parse(lt(y,x))` rejects that proof; `encode(2, x<y, y<x)` is `None`.
  - `w_fold_lt_outside_the_root_has_no_law`: the four `encode(..).is_none()`.
  - `w_fold_streams_compute_the_words`: as today, with `let mut cx = Cx::default(); let xs = [cx.mark(stream_of(a, nb)),
    cx.mark(stream_of(c, nb))];` and `side(&mut cx, &Machine::parse(t).unwrap(), &xs).0`; `bit_of` becomes `bit(..)`.
  - `w_fold_every_encoded_pair`: as today, with `encode`/`proof`/`check` in `prove`.
  - `w_fold_a_theorem_applies_to_good_streams` (rewritten, step 10) and `w_fold_proof_type_is_the_statement` (new, step 11).
- [ ] **Step 5: Sides.** Restore `mod wfold;`. `side` per the spec, with `ones`, `nat_`, `at_n` as `Cx` helpers; `encode` and
  `operands` written; `proof` a `todo!()` stub. Expected: `cargo test -j 10 -p church-bv --lib --no-run` compiles, and
  `-- w_fold_streams_compute_the_words w_fold_lt_outside` passes (neither calls `proof`).
- [ ] **Step 6: Goodness proofs.** Per side and carry, `ind` with telescope `$P, $ht, $hf` (`good_bool()`'s
  binders) and body `n ↦ P (carry n)`; `pred` is `tag_case` on `sp.step_of`; `hj` runs `sp.machines[side].step(&sp.gops, ..)` with
  real witnesses for the operands and earlier carries, `ih w` for this carry, and the placeholder `f()` for later ones (the spec's
  comment kept); `Goods.konst(b).g` becomes `cx.lam(nw(), |_, _| good_bit(b))`, `Terms.konst(b)` becomes `bit(b)`. Expected:
  `cargo check -j 10 -p church-bv` clean.
- [ ] **Step 7: Invariant and roots.** `lemmas[side][j] = sp.lemma(side, j).0` for `j` in `0..=m`, both sides. The invariant is
  `ind` with an empty telescope: `pred` is `sigmas` of `agree` at the tag-split carries, `hj` is `pack` of `sp.eq(1 + q,
  [&lemmas[0][1+q], &lemmas[1][1+q]], ..)` over `unpack` of `ih w`, `hn` is `pack` of the `refl`s. Each goodness proof and the
  invariant are bound once as `app(cx.lam(ty, |cx, h| rest), proof)`; the final equation is `sp.eq(0, [&lemmas[0][0],
  &lemmas[1][0]], ..)` at position `i`. The proof root is `law(&operands(k), ..)`'s proof; the statement root is
  `statement(&operands(k), ..)` over `side`'s roots. Expected: `cargo test -j 10 -p church-bv --lib -- w_fold_add_associates` passes,
  then `-- w_fold` passes the step-4 tests (steps 10 and 11 still to write), every control rejected.
- [ ] **Step 7b: Deletions and header.** Delete everything the spec's End-state fit lists for `wfold.rs`; rewrite the header comment
  (what the file proves, the two roots, `StepProof`; no q2 history). Expected: `cargo check -j 10 -p church-bv --tests` clean with no
  dead-code warning from wfold (a plain `cargo check` cannot show one: `lib.rs` allows `dead_code` outside test builds).
- [ ] **Step 8: Dead `T` variants.** Delete `W`, `Sup`, `WRec` from `uniform/width.rs` with their `comp` arms. Expected:
  `git grep -nE "\b(W|Sup|WRec)\(" crates/church-bv/src/uniform` prints nothing; `cargo check` clean.
- [ ] **Step 9: Stale wording.** `git grep -n "Law::new\|Law::proof\|wnat.rs#add" -- crates docs/TOUR.md` lists the comments to fix in
  this commit (e.g. the `wfold.rs` test-comment one). Expected: prints nothing (doc 15's and PARKED's wording is Task 5's).
- [ ] **Step 10: The widened theorem test** `w_fold_a_theorem_applies_to_good_streams`, at `n = 3`:

```rust
// pairs (k, left, right): (3, sub(x, add(y, z)), sub(sub(x, y), z)); (2, lt(x, y), lt(not y, not x)); (2, and(x, or(x, y)), x)
// (not a = xor(a, ONES)). Streams: all-ones is the constant stream cx.lam(nw(), |_, _| t()) (today's `ones()`), all-zeros zw();
// stream_of cannot be used: good_bool(x i) does not reduce to good_bool(bit c) on a stuck `i`. Witness for a constant-c operand:
// cx.lam(nw(), |_, _| good_bit(c)). Every all-ones/all-zeros assignment, positions p in {0, last}: last = n - 1 for a word, n for lt.
let ty = tatic_kernel::infer(&Ctx::new(), &proof).unwrap(); // once per pair, in that pair's own scoped region
fn instance(ty: &Expr, args: &[Expr]) -> Expr; // test helper, described below
// instance(ty, args): peel args.len() Pis off ty (tatic_kernel::Node::Pi(d, b)), wrap the remaining codomain Id(bool0, L, R) back in lam(d, ..)
// in the same order, and apply to args = streams ++ witnesses ++ [num(p)]; def_eq does the beta steps.
assert!(def_eq(&instance(&ty, &args), &eqb(bit(e), bit(e))));
assert!(!def_eq(&instance(&ty, &args), &eqb(bit(!e), bit(!e))));
// e: a word root's bit p of t.interp(3, &vals), vals[i] = 7 or 0; an lt root's (a & low_p) < (c & low_p), a and c the interps of its
// two argument terms (as w_fold_streams_compute_the_words computes it).
// Per pair, at the mixed assignment (operand i all-ones iff i is even), first the paired check passes, then the mispaired one fails:
check(&Ctx::new(), &apps(proof, args.clone()), &eqb(bit(e), bit(e))).unwrap();
assert!(check(&Ctx::new(), &apps(proof, args_with_first_two_witnesses_swapped), &eqb(bit(e), bit(e))).is_err());
```

  Run it with `--nocapture` and time it; settle the grid then (spec, Checks: "timed once it is written"). If it exceeds 10 s, reduce the
  assignments (keep both positions), and record the grid in a comment. Expected: passes, every paired check accepted and every
  mispaired one rejected.
- [ ] **Step 11: The size test** `w_fold_proof_type_is_the_statement`: for `(x+y)+z = x+(y+z)` at `k = 3`, `infer(&Ctx::new(), &proof)`
  is `def_eq` to `stmt`; print both components of `term_sizes(&proof)`, `term_sizes(&ty)` and `term_sizes(&stmt)` (distinct nodes and
  tree count); assert `term_sizes(&ty).0 <= 2 * term_sizes(&stmt).0` (the factor is this plan's: an inferred type that carries a
  goodness proof is far larger). Expected: passes; the printed numbers go into Task 6's record.
- [ ] **Step 12: PARKED entry**, after the family-deletion entry: **what** `cases2` exists twice, on `T` in `uniform/width.rs` and on
  `Expr` in `wnat.rs`; **why parked** the families stay on `T` until a bridge to `Bv_n` exists; **trigger** the families are deleted
  (the `T` copy goes with `width.rs`); **evidence** `uniform/width.rs#cases2` and `uniform/wnat.rs#cases2`, 2026-11-07; **status**
  parked.
- [ ] **Step 13: Whole lib suite, guards, and the no-index check.** Expected: 340 passed (the size test added); guards clean (both
  files stay under `size_check.sh`'s 1000 lines; their tests are top-level `#[test]` fns, which `test_placement_check.sh` does not
  measure); `git grep -nE "\bvar\(|\bv\(\"|\bT::|[:>] T\b|<T>" crates/church-bv/src/uniform/wnat.rs crates/church-bv/src/uniform/wfold.rs`
  prints nothing.
- [ ] **Step 14: Commit** `uniform/wnat.rs uniform/wfold.rs uniform/width.rs PARKED.md` and any comment step 9 fixed: "church-bv: wnat
  and wfold build kernel terms through Cx; the fold's steps go through StepProof (w1 step 4)", listing in the body what was deleted
  and any helper added beyond the plan.

### Task 5: Move the modules to `src/` (c1)

**Files:**
- Move: `git mv crates/church-bv/src/uniform/wnat.rs crates/church-bv/src/wnat.rs`, same for `wfold.rs`
- Modify: `lib.rs` (`mod wnat; mod wfold;` beside `mod machine;`), `uniform.rs` (drop its two lines); imports and visibility need no
  change (Global Constraints; `pub(super)` from a child of the crate root is crate-wide), `docs/TOUR.md` (line 42 loses both `wnat`
  and `wfold`; a new top-level line after line 41 names `crates/church-bv/src/wnat.rs#ind` and `crates/church-bv/src/wfold.rs#proof`
  in the tour's cite form), `docs/tier-cycle/`, "One generator proves stream laws at
  all widths" and "The level wall is Church's" (doc 15's paragraphs): new paths; the `Law::new`/`Law::proof` and wnat-`add` description becomes
  `encode`/`proof`; the x2 paragraph's "still in `T`" gets "until the w1 port"), `PARKED.md` (goal D entry; the family-deletion entry
  says `T` serves only the families; the Task 4 `cases2` entry's path), comments in `uniform/mul.rs` (two `wnat.rs` mentions) and
  `crates/tatic-kernel/src/postulates.rs` (`uniform/wnat.rs`)

- [ ] **Step 1: Move and rewire** as listed. Expected: `cargo check -j 10 -p church-bv` clean.
- [ ] **Step 2: The guard.** Add `use crate::uniform::width::T;` at the top of `src/wfold.rs` and run
  `cargo check -j 10 -p church-bv`. Expected: error E0603, module `width` is private. Remove the line.
- [ ] **Step 3: Stale paths.** `git grep -nE "uniform/w(nat|fold)|uniform::w(nat|fold)"`. Expected: hits only in `docs/runs.md` rows,
  `docs/runs/` dated folders, the 2026-09-30 bitvector spec, the x2 spike patch (a record, left as is), this plan and the w1 spec.
  Then `git grep -n "Law::new\|Law::proof" -- docs/tier-cycle PARKED.md`: only doc 15's profile frame names in "Where a sweep's time
  goes" and "A port spike on kernel terms" remain (history).
- [ ] **Step 4: Whole lib suite and guards.** Expected: 340 passed; `cite_check.sh` and `tour_check.sh` clean.
- [ ] **Step 5: Commit**: "church-bv: wnat and wfold move to src/, out of reach of the named tree T (w1 step 5)".

### Task 6: Count and sweep, then record

The spec lists the port's counts under doc 15 in End-state fit without tying them to a commit; they are measured on the moved code,
so they land here in a docs commit.

- [ ] **Step 1: Baseline exe.** Disk check (Global Constraints). `git worktree add "$LOCALAPPDATA/claude-runs/tatic/w1-base" b52c265`;
  in that worktree `git apply docs/superpowers/spikes/2026-11-07-x2-kernel-table-lemma.patch` (from the main checkout's path) and build
  `run.ps1 -Kind probe -Name w1-base-build -Command "cd C:/Users/WINSTO~1/AppData/Local/claude-runs/tatic/w1-base && set CARGO_TARGET_DIR=C:/Users/WINSTO~1/AppData/Local/claude-runs/tatic/w1-base-target&& cargo test -j 10 -p church-bv --lib --no-run"`
  (only the `Winston Li` component is shortened; cargo creates the target dir);
  copy the printed test exe to `w1-exes/base-test.exe`. Build this branch's test exe the same way in the default target dir, copy to
  `w1-exes/port-test.exe`. Expected: both exist.
- [ ] **Step 2: Env files.** The exe reads `<canonical exe path>.env`: write `base-test.exe.env` and `port-test.exe.env` with
  `WFOLD_STRIDE=97` and `WFOLD_THREADS=1`.
- [ ] **Step 3: Verdicts**, untimed: `run.ps1 -Kind probe -Name w1-verdict-<arm> -Command "<exe> w_fold_every_encoded_pair --nocapture"`
  per arm. Expected both: `pairs=<P> stride=97 threads=1 tried=469 no-encoding=1`, `test result: ok`.
- [ ] **Step 4: Counts** per `ICOUNT.md` (`-Cpu 4` if a timed run holds CPU 8):
  `& "$env:USERPROFILE\.claude\samply\icount.ps1" -Exe <exe> -Runs 4 -ExeArgs w_fold_every_encoded_pair`.
  - A/A: one batch of 4 per arm first; its spread (median, max/best) is each arm's tolerance.
  - A/B: rotate base, port, base, port, each a batch of 4; compare medians with max/best beside them (large pages: never best-of-N).
  - Fixed cost: copies `base-fixed.exe` and `port-fixed.exe` whose `.env` sets one stride, found once on the base arm and used for
    both, so both arms sample the same pair: scan `s = P, P-1, ..` from step 3's `pairs=` (every `s` in `(P/2, P]` samples exactly
    one pair) and take the first whose verdict run exits 0 with `tried=1`; one batch of 4 each.
  - Report per arm: median, the fixed count (enumeration plus that one pair, as the spec's Checks say), and the build span (median
    minus fixed); the verdict is the build-span ratio. Expected
    (inference): the port's span well under the base's.
- [ ] **Step 5: Full sweep**:
  `run.ps1 -Kind sweep -Name w1-full-sweep -Affinity CFF -Command "set WFOLD_STRIDE=1&& set WFOLD_THREADS=10&& cargo test -j 10 -p church-bv --lib -- w_fold_every_encoded_pair --nocapture"`
  (the form of row `2026-11-07-x1-full-sweep`). Expected: `tried=45621 no-encoding=56`, exit 0; wall and `peak_commit_mb` set beside
  that row's 405 s and 4502 MB.
- [ ] **Step 6: Record** in doc 15, section "One generator proves stream laws at all widths", a paragraph after "A port spike on kernel
  terms": the A/A spreads, the medians, the fixed counts, the build-span ratio, Task 4 step 11's sizes, the full sweep and the run
  ids. Set the spec's and this plan's front matter to `done`. Remove the worktree
  (`git worktree remove --force`, since the applied patch leaves it modified; it holds nothing else) and its target dir.
- [ ] **Step 7: Guards and commit** doc 15, `docs/runs.md`, the spec and this plan: "docs: w1 port counted, <ratio> on the 1-in-97
  sample; full sweep 45621 proved".

## End-state fit

| Change | Lives in | Replaces | Deletes |
|---|---|---|---|
| `Cx`, `At`, `Ty`, `ty!`, `tele`, `law`, `statement`, `under`, checked depth | `encoding/cx.rs` | `wasm.rs:13-73` | the private `bind` name |
| `constant(build)` | `encoding/gates.rs` | `constant(slot, build)` | slots 0-8 in `gates.rs`, `division.rs`, `good.rs` |
| `CONSTANTS` text "by build function" | `job.rs` | "by slot" | |
| `StepProof`, module-level `Step` (guarded by `tree_proof_terms_are_pinned`) | `machine.rs` | `tree_proof`'s `phi_expr`, `g_expr`, `step_of`, `side_f`, `steps`, `step_at`, `by_cases` body, `eq`; `lemmas` stays as `tree_proof`'s vec of `shared_lemma` wrappers | `CaseFn`, the local `Step`, wfold's `Law::{step, m, f, phi, g, lemma}` and `eq` |
| wnat on `Expr` (`Tag`, `tag_case`, `ind` with `tele`/`body`, `zero_tag`/`succ_tag`, `Cx` `cases2`; ported `stream_of`, `num`, `zw`, `ptw`, `tag_*`) | `src/wnat.rs` | `uniform/wnat.rs` on `T` | `good_case`, `sel`, `selm`, `fw`, `noop`, `sym`, `trans`, `cong3`, `K(ex(..))`, the `rew` uses, the reserved names |
| wfold on `Expr` (`encode`, `proof`, `operands`, `side`, `agree`, `sigmas`/`pack`/`unpack`) | `src/wfold.rs` | `uniform/wfold.rs` on `T`; `conj`/`pair`/`projections` renamed | `Law`, `Terms`, `Goods`, `Good`, `gate`, `good_lams`, `pick`, `p_of`, `mux`, `table`, `by_cases`, `cong`, `over`, `closed`, `held`, `XS`, `GS`, `CB`, `CG`, `Side`, the closed invariant |
| every `bit_of` use in wnat and wfold | `encoding::bit((v >> j) & 1 == 1)` | `uniform/mul.rs#bit_of` (stays for the families) | |
| `T` without `W`/`Sup`/`WRec` (`Sig`, `Pair`, `SigRec` stay) | `uniform/width.rs` | | three variants and their `comp` arms |
| `mod wnat; mod wfold;` | `lib.rs` | `uniform.rs`'s two lines | `mod wfold; mod wnat;` in `uniform.rs` |
| docs | TOUR, doc 15, PARKED, comments in `uniform/mul.rs` and `postulates.rs` | old paths and the `Law` wording | |

Stopgaps: one, the second `cases2`, parked in Task 4 step 12 with its trigger.

## Review log

Round 1 (4 Sonnet lenses: code facts, feasibility, spec coverage, fewer concepts and format): 2 material, about 30 minor.
Material: the all-ones operand was `stream_of`, whose goodness cannot take a constant witness, so the paired `check` would have failed
and the mispairing control passed vacuously (now the constant stream, paired check first); a shared `accepted` test helper contradicted
the spec's "no twin of `width::run`" (deleted). Minor: imports while in `uniform/`, every `j` needs its lemma, test-snippet API errors,
`tree_proof`'s range, the gate line's prefix, `tele` private, no visibility widening in Task 5, tracked-file grep and its leftovers,
stale doc-15 wording, front matter `active`, wrapped builds, the A/A procedure, `.exe.env` naming and the fixed-cost stride, PARKED
entry form, `term_sizes` components, Task 4 steps split with their own Expected lines.

Round 2 (same lenses): 2 material, about 15 minor. Material: `tele` must be `pub(crate)` (round 1's "private" was wrong: `wasm.rs`'
`ctors` calls it at 268 and 514; spec corrected); wnat's stage proofs call the builders being ported, so a "stages 1-2 first" step
could not compile (wnat now ports in one step). Minor: `Node` is ambiguous under `crate::*`; the gate's WORK counts cannot see a
changed term (a term-size and lemma-key pin test added to Task 3); `mod wfold` restored before wfold code is written; the fixed-cost
stride shared by both arms; 8.3 paths; size test asserts a 2x bound; stale-name greps widened; spec amended where the plan was right
(constant-only builders take no `Cx`, `lemmas` stays, extra `StepProof` visibility); test counts 339/340.

Round 3 (same lenses): 1 material, about 20 minor. Material: the pin test saw only the outer proof, whose lemmas are `Postulates`
parameters, so a changed lemma body would pass it (now each law runs on a fresh `Job` and the pin includes `discharge`'s whole
term). Minor: `core` uses `sp.gops`; the fixed-cost stride scan steps down by one (halving can skip `tried=1`); one region per proof;
constants build through their own `Cx`; the wnat header rewritten; wfold's functions private; no import change on the move; step 7
split; greps with reachable Expected lines; spec Checks amended for the shared stride, the pin and the 2x bound. Rejected: "slots 0-5"
in the spec is right (its next line covers 6-8).

Round 4 (same lenses): 0 material, 6 minor, folded: dead-code checks use `--tests` (`lib.rs` allows `dead_code` outside tests); the
pin runs alone and its `PIN` lines are diffed; `git worktree remove --force` for the patched baseline; `Law::m` in the table; the plan
and the round 1-3 spec amendments are committed before Task 1, not inside it.
