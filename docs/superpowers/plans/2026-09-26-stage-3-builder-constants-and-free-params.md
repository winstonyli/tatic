---
status: done
---

# Stage 3: the builder emits constants and free parameters — implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** `proof.rs` refers to postulates by `Expr::Const(level)` and to its builder scopes' parameters by `Expr::Free(level)`, so proof terms keep their sharing and a leaked parameter fails the check instead of acting as an axiom.

**Architecture:** Two halves, each shipped and measured alone (decided 2026-09-26).
- **3a (Tasks 1-4):** globals become `Const`. `Postulates` keeps one `ctx` vector, but records where the outermost open scope starts: `get` returns `Const(pos)` below it and a `Var` at or above it (the scope's locals, as today). Checks split the vector into `Globals` and a local `Ctx` and call `kernel::check_in`/`infer_in`. This is the spike's "both" configuration (§64: `fib(16)` 1.9 s → 18.5 ms, DAG 265k → 10.5k).
- **3b (Tasks 5-8):** parameters become `Free`. `bind(ty)` returns a fresh `Free` level. A scope's `close` abstracts its levels into binders. Globals are never truncated, and `push` panics while a scope is open.

**Tech Stack:** Rust (edition as in `Cargo.toml`), `im::Vector`, cargo test/criterion, `scripts/quiet_ab` for A/B timing.

**Spec:** `docs/superpowers/specs/2026-09-25-kernel-constants-and-loose-ranges-design.md` (sections "Stage 3", "Testing → Stage 3", "Risks"). Background: `RELATED_WORK.md` §64 (spike), §65 (stage 1), §67 (stage 2), §68 (claim checks; the `Ev` bug that motivates Task 3).

## Decisions (user-approved 2026-09-26)

1. **3a then 3b.** 3a carries the whole measured payoff in a small diff. 3b's A/B then shows that the safety change is free. About 20 lines of 3a (`scope_base`) are replaced in 3b.
2. **Every `push` checks that its type is a type (infers to a `Sort`), always on, measured.** This catches §68's class of bug (an ill-formed context entry) at the push, as Lean's `add_decl` and Coq's `infer_definition` do.
3. **3b's in-scope debug checks use `Postulates::check_open`.** It abstracts the live parameters into a kernel `Ctx` and checks there, keeping `debug_assert_has_type`'s per-call bug localisation.
4. **In 3b, `push` panics while a scope is open.** A missed `push`→`bind` conversion can't leave a silent axiom. Stage 4's removal of the closure priming must relax this.

## Global Constraints

- **Trust boundary:** Stage 3 is untrusted. Do not change the type checker in `src/kernel.rs` (`infer_rc`, `check_rc`, `whnf`, `def_eq`, `shift`, `instantiate`, the `Const`/`Free` rules). Only these may change there:
  - the `Postulates` section (`pub struct Postulates` and what this plan adds beside it);
  - `close_pi`/`close_lam`;
  - kernel tests.
  If a task seems to need a type-checker change, stop and report `BLOCKED`.
- **Line endings:** files are CRLF except `*.sh` (LF). Edit with the Edit tool or Python with `newline=''`. Never `sed -i`. Never run `cargo fmt`.
- **Builds:** `CARGO_BUILD_JOBS=12`. Run tests with `cargo test -q --lib` (plus `--release` where a step says so).
- **Hands off:**
  - Never touch other sessions' processes: `selfplay*`, `java`/Gradle, `manifold`, or other `cargo` jobs.
  - Never touch the worktrees `.claude/worktrees/goofy-sammet-171d91` and `target/bench-ab/base`.
  - Never touch anything under `target/ab/` (an A/B may be running there).
- **Comments:** match the surrounding density. Cite `RELATED_WORK.md` sections for "why", and state facts plainly.
- **Commits:** one commit per task, message ending with `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`. Don't push; the controller pushes.
- **Timing guards:** use bounds with at least 5× headroom over the post-change time, since other sessions load this machine.
- **Every task ends green:** `cargo test -q --lib` passes, and `cargo clippy --all-targets -- -D warnings` is clean.

## File structure

- `src/kernel.rs`: the `Postulates` section (around line 1520). It gains the `Scope`/`Binder` API and `check`/`infer`, then (3b) `bind`/`check_open`/`abstract_frees`. Its test module adapts.
- `src/proof.rs`: the builder. Scopes are `params_and_close` (~1700), `params_and_close_typed` (~1729) and the `ev_rec_ty` scope in `build_universal` (~2084-2139). It has 65 `kernel::check` sites, 1 `kernel::infer` site, and 36 `debug_assert_has_type` sites. The proof records' `ctx` fields are at lines 457, 2348, 3873, 6802 and 7587.
- `tests/kernel_soundness_fuzz.rs`: builds a `Postulates` context (lines ~363-430) and checks against `ctx.p.ctx`.
- Docs: `RELATED_WORK.md` gets §69 (3a) and §70 (3b); also `README.md` (the §64-§68 paragraph near line 1100) and the spec's status line and Stage 3/4 text.

---

## 3a: globals as constants

### Task 1: `Postulates` scope and check API, with no behaviour change

Pure refactor: every scope and every check goes through `Postulates`, so Task 2 can change the representation in one place.

**Files:**
- Modify: `src/kernel.rs` (`Postulates` section; kernel tests that check against `p.ctx`)
- Modify: `src/proof.rs` (three scopes; all check sites; `debug_assert_has_type`)
- Modify: `tests/kernel_soundness_fuzz.rs`

**Interfaces:**
- Produces (in `kernel`):
  - `pub struct Scope { base: usize, outer_base: usize }`, marked `#[must_use]` (fields private).
  - `#[derive(Clone, Copy, Debug, PartialEq, Eq)] pub enum Binder { Pi, Lam }`.
  - The `Postulates` methods:
    - `pub fn open(&mut self) -> Scope`
    - `pub fn close(&mut self, s: Scope, binder: Binder, body: Expr) -> Expr`
    - `pub fn abandon(&mut self, s: Scope)`
    - `pub fn check(&self, e: &Expr, ty: &Expr) -> Result<(), String>`
    - `pub fn infer(&self, e: &Expr) -> Result<Expr, String>`
  - A private field `scope_base: usize` (`usize::MAX` while no scope is open).
- Produces (in `proof`): `fn debug_assert_has_type(p: &Postulates, e: &Expr, expected: &Expr, label: &str)`, which now takes `&Postulates`.
- Changes: `params_and_close` and `params_and_close_typed` take `binder: kernel::Binder` in place of `close: fn(usize, &Ctx, Expr) -> Expr`. Callers pass `kernel::Binder::Pi` where they passed `kernel::close_pi`, and `kernel::Binder::Lam` for `kernel::close_lam`.

- [ ] **Step 1: Write the failing test** (kernel test module, next to `close_pi_matches_hand_built_dependent_pi_chain`)

```rust
    /// `open`/`close` wrap exactly the entries pushed inside the scope and
    /// roll them back; `abandon` rolls back without closing.
    #[test]
    fn a_scope_closes_over_what_it_pushed_and_rolls_it_back() {
        let mut p = Postulates::new();
        let a = p.push(sort(0));
        let s = p.open();
        let x = p.push(p.get(a));
        let body = id(p.get(a), p.get(x), p.get(x));
        let closed = p.close(s, Binder::Pi, body);
        assert_eq!(p.ctx.len(), 1);
        assert!(p.check(&closed, &sort(0)).is_ok());
        let s = p.open();
        p.push(p.get(a));
        p.abandon(s);
        assert_eq!(p.ctx.len(), 1);
    }
```

- [ ] **Step 2: Run it to verify it fails**

Run: `cargo test -q --lib a_scope_closes_over_what_it_pushed`
Expected: compile error (`open`, `close`, `Binder`, `check`, `abandon` not found).

- [ ] **Step 3: Implement the API** (in `src/kernel.rs`, replacing `pub struct Postulates { pub ctx: Ctx }` and its `new`)

```rust
#[derive(Clone)]
pub struct Postulates {
    pub ctx: Ctx,
    /// Where the outermost open builder scope starts (`usize::MAX` while
    /// none is open). Entries below it are postulates, entries at or above
    /// it the open scopes' locals (`open`, `close`).
    scope_base: usize,
}

/// A builder scope from `Postulates::open` to `close` or `abandon`.
#[must_use]
pub struct Scope {
    base: usize,
    outer_base: usize,
}

/// Which binders `Postulates::close` wraps: `Pi` to build a type that
/// quantifies over the scope's entries, `Lam` for a value of that type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Binder {
    Pi,
    Lam,
}

impl Postulates {
    pub fn new() -> Self {
        Postulates { ctx: Ctx::new(), scope_base: usize::MAX }
    }
    // push and get unchanged in this task
    pub fn open(&mut self) -> Scope {
        let base = self.ctx.len();
        let s = Scope { base, outer_base: self.scope_base };
        self.scope_base = self.scope_base.min(base);
        s
    }
    /// Wraps a binder around `body` for each entry pushed since `s` was
    /// opened, outermost first, then rolls those entries back.
    pub fn close(&mut self, s: Scope, binder: Binder, body: Expr) -> Expr {
        let closed = match binder {
            Binder::Pi => close_pi(s.base, &self.ctx, body),
            Binder::Lam => close_lam(s.base, &self.ctx, body),
        };
        self.abandon(s);
        closed
    }
    /// Rolls back what was pushed since `s` was opened, closing nothing
    /// (for a build that gave up).
    pub fn abandon(&mut self, s: Scope) {
        self.ctx.truncate(s.base);
        self.scope_base = s.outer_base;
    }
    pub fn check(&self, e: &Expr, ty: &Expr) -> Result<(), String> {
        check(&self.ctx, e, ty)
    }
    pub fn infer(&self, e: &Expr) -> Result<Expr, String> {
        infer(&self.ctx, e)
    }
}
```

- [ ] **Step 4: Migrate `proof.rs`**
  - `params_and_close` and `params_and_close_typed`:
    - Replace `let base_len = arith.p.ctx.len();` with `let s = arith.p.open();`.
    - Replace the final three lines with the following, dropping the `close` parameter:

      ```rust
      match build(arith, &pp) {
          Some(b) => Some(arith.p.close(s, binder, b)),
          None => {
              arith.p.abandon(s);
              None
          }
      }
      ```

    - Update their doc comments (`close_pi`/`close_lam` → `Binder::Pi`/`Binder::Lam`).
  - The `ev_rec_ty` scope in `build_universal` (`p_base_len`, around lines 2084-2139):
    - `let p_scope = arith.p.open();` goes before `arith.p.push(motive_ty)`.
    - `let ev_rec_ty = arith.p.close(p_scope, kernel::Binder::Pi, ev_rec_ty_body);` replaces the `close_pi` + `truncate` pair.
    - Any `?` between open and close that returns early must call `arith.p.abandon(p_scope)` first. Read the region and restructure it if there is one.
  - Every `kernel::check(&<X>.p.ctx, a, b)` → `<X>.p.check(a, b)`, where `<X>` is `arith`, `combinators.cp.arith`, `scaffold.combinators.cp.arith`, and so on. Also the multi-line calls whose first argument is `&combinators.cp.arith.p.ctx,` (lines ~2799, 3422, 3570, 7973-8751): the whole call becomes `combinators.cp.arith.p.check(...)`.
  - `kernel::infer(&scaffold.combinators.cp.arith.p.ctx, &applied)` (~3865) → `scaffold.combinators.cp.arith.p.infer(&applied)`.
  - `debug_assert_has_type(ctx: &Ctx, ...)` → `(p: &Postulates, ...)`, calling `p.check(e, expected)` (both cfg variants). Each call site's first argument, `&<X>.p.ctx`, becomes `&<X>.p`.
  - Leave `kernel::check(&proof.ctx, ...)` on the proof records (`proof.ctx`, `instance.ctx`, `gcd_proof.ctx`) alone in this task. Task 2 changes them.
- [ ] **Step 5: Migrate the other `Postulates` users**
  - In `src/kernel.rs` tests, every `check(&p.ctx, ...)`/`infer(&p.ctx, ...)` on a `Postulates` named `p` → `p.check(...)`/`p.infer(...)`.
  - Where a test opens a scope by hand (`let base_len = p.ctx.len(); ... close_pi(base_len, &p.ctx, ...); p.ctx.truncate(base_len)`), use `p.open()` and `p.close(...)`. That's `close_pi_matches_hand_built_dependent_pi_chain` and `close_lam_builds_a_value_of_the_close_pi_type`. In the latter, which closes twice over one scope, close the type with `p.close`, reopen, push `x` again, and close the value.
  - Leave tests that pass a hand-built `Ctx` (not `p.ctx`) alone, and leave `memo_test_ctx` alone.
  - In `tests/kernel_soundness_fuzz.rs`, `kernel::check(&ctx.p.ctx, ...)` → `ctx.p.check(...)`.
- [ ] **Step 6: Run everything**

Run: `cargo test -q --lib` and `cargo test -q --release --test kernel_soundness_fuzz --test kernel_fuzz`, then `cargo clippy --all-targets -- -D warnings`.
Expected: all pass, including the new test. The answers are unchanged, since `get` and the checks still use the one `Var` context.

- [ ] **Step 7: Confirm nothing bypasses the API**

Run each of these greps on `src/proof.rs`:
- `grep -n "p\.ctx\.truncate\|close_pi(\|close_lam(" src/proof.rs`: expect no scope code left. Only doc comments may still mention them.
- `grep -n "kernel::check(&[a-z_.]*p\.ctx\|kernel::infer(&[a-z_.]*p\.ctx" src/proof.rs`: expect nothing.

- [ ] **Step 8: Commit**

```bash
git add src/kernel.rs src/proof.rs tests/kernel_soundness_fuzz.rs
git commit -m "Postulates: scopes (open/close/abandon) and check/infer go through Postulates; no behaviour change (stage 3a)"
```

### Task 2: postulates are `Const`s

**Files:**
- Modify: `src/kernel.rs` (`Postulates::get`/`check`/`infer`; tests)
- Modify: `src/proof.rs` (proof-record check sites; DAG and timing tests)
- Modify: `tests/kernel_soundness_fuzz.rs` (only if it breaks)

**Interfaces:**
- Consumes: Task 1's API.
- Produces:
  - `Postulates::get(pos)` returns `Expr::Const(pos as u32)` for `pos < scope_base`, and otherwise `var(len - 1 - pos)` as before.
  - `Postulates::check`/`infer` call `check_in`/`infer_in` with `globals = ctx[..min(scope_base, len)]` and `locals = ctx[that..]`.
  - A proof record's `ctx` holds postulates only, so it is checked with `kernel::check_in(&proof.ctx, &Ctx::new(), e, ty)`.

- [ ] **Step 1: Write the failing tests**

In `src/kernel.rs` tests:

```rust
    /// Outside a scope a postulate is `Const(pos)`; inside one, the
    /// scope's own entries are `Var`s and the postulates stay `Const`s.
    #[test]
    fn postulates_are_consts_and_a_scopes_entries_are_vars() {
        let mut p = Postulates::new();
        let a = p.push(sort(0));
        assert_eq!(p.get(a), Expr::Const(0));
        let s = p.open();
        let x = p.push(p.get(a));
        assert_eq!(p.get(a), Expr::Const(0));
        assert_eq!(p.get(x), var(0));
        assert!(p.check(&p.get(x), &p.get(a)).is_ok());
        let closed = p.close(s, Binder::Lam, p.get(x));
        assert_eq!(closed, lam(Expr::Const(0), var(0)));
        assert!(p.check(&closed, &pi(Expr::Const(0), Expr::Const(0))).is_ok());
    }
```

In `src/proof.rs` tests, tighten `a_fibonacci_instance_proof_shares_its_repeated_witnesses`:
- Use `fib(8)` and `fib(16)`.
- Assert `2 * large < 5 * small` (under 2.5×). The spike measured 5,445 and 10,501 nodes (RELATED_WORK §64).
- Update its doc comment: with postulates as constants the DAG grows linearly (§69).

Add a timing guard beside it:

```rust
    /// `fib(16)`'s instance proof, built and re-checked. With postulates
    /// as constants it's a linear DAG (§69); before, it was 227k nodes and
    /// seconds of work.
    #[test]
    fn fib16_instance_proof_builds_and_checks_quickly() {
        // same fib TermStore setup as fib16_instance_proof_cost
        let t = std::time::Instant::now();
        let proof = prove_tail_recursive_instance(&s, fib, &[16]).unwrap();
        kernel::check_in(&proof.ctx, &Ctx::new(), &proof.proof, &kernel::id(proof.int_ty.clone(), proof.lhs.clone(), proof.rhs.clone()))
            .expect("fib(16)'s instance proof re-checks");
        let took = t.elapsed();
        assert!(took < std::time::Duration::from_secs(3), "took {took:?}");
    }
```

Copy the `TermStore` setup lines verbatim from `fib16_instance_proof_cost`; don't factor them out.

- [ ] **Step 2: Run them to verify they fail**

Run: `cargo test -q --lib -- postulates_are_consts a_fibonacci_instance_proof_shares fib16_instance_proof_builds`
Expected: the kernel test fails, since `get(a)` is `var(0)`. The DAG test fails with `large` around 18× `small`. Record the timing test's `took` before the change. If it is under 3 s, set the bound to half of it, keeping at least 5× headroom over the post-change time from Step 5. If both can't hold, report it as a concern.

- [ ] **Step 3: Flip the representation**

```rust
    pub fn get(&self, pos: usize) -> Expr {
        if pos < self.scope_base {
            Expr::Const(pos as u32)
        } else {
            var((self.ctx.len() - 1 - pos) as u32)
        }
    }
    /// The postulates (`Globals`) and the open scopes' entries (`Ctx`).
    fn split(&self) -> (Globals, Ctx) {
        let mut globals = self.ctx.clone();
        let locals = globals.split_off(self.scope_base.min(self.ctx.len()));
        (globals, locals)
    }
    pub fn check(&self, e: &Expr, ty: &Expr) -> Result<(), String> {
        let (g, l) = self.split();
        check_in(&g, &l, e, ty)
    }
    pub fn infer(&self, e: &Expr) -> Result<Expr, String> {
        let (g, l) = self.split();
        infer_in(&g, &l, e)
    }
```

Update `Postulates`' doc comment:
- Postulates are referred to by `Const(level)` and checked as `Globals`.
- A scope's entries are `Var`s, as before (RELATED_WORK §69).

- [ ] **Step 4: Fix what the flip breaks**
  - Every `kernel::check(&proof.ctx, ...)`, `kernel::check(&instance.ctx, ...)` and `kernel::check(&gcd_proof.ctx, ...)` in `src/proof.rs` → `kernel::check_in(&<same>.ctx, &Ctx::new(), ...)`. Find them with `grep -n "kernel::check(&[a-z_]*\.ctx" src/proof.rs`; there are about 26.
  - `memo_test_ctx` in `src/kernel.rs` must keep building a `Var` context, because the memo tests use `var(k)` for its entries. Build it by hand:

    ```rust
        fn memo_test_ctx() -> Ctx {
            let mut ctx = Ctx::new();
            ctx.push_back(sort(0));
            ctx.push_back(var(0));
            ctx.push_back(arrow(var(1), arrow(var(1), var(1))));
            ctx.push_back(arrow(var(2), var(2)));
            ctx
        }
    ```

    (These are exactly the terms `Postulates::get` produced there before the flip.)
  - `infer_is_linear_in_the_dag_of_a_shared_term` builds its postulates as `Const`s, per the spec's stage 3 testing:
    - Use a `Postulates` with `A`, `a`, `f`, `g` pushed as in the old `memo_test_ctx`.
    - Start from `d = Rc::new(p.get(1))` and wrap it in `App(App(p.get(2), d), d)`.
    - Assert `p.infer(&d) == Ok(p.get(0))`, keeping the 500 ms bound.
  - Any other test that now fails:
    - If it wrote a `var(k)` for a postulate, replace it with `p.get(pos)`.
    - If it passes `p.ctx` to `check`/`infer`, use `p.check`/`p.infer`.
    - If it pushes entries that are really a scope's binders without `open`, add `open`/`close`.
    - Record each such fix in the report.
  - `tests/kernel_soundness_fuzz.rs`: if it builds terms from `ctx.p.get(...)` and checks them against a hand-built context, keep them consistent the same way. If a property there becomes vacuous (it checks nothing now), report it rather than weakening it silently.
- [ ] **Step 5: Run everything**

Run:
- `cargo test -q --lib`
- `cargo test -q --release --lib fib16_instance_proof_cost -- --ignored --nocapture`: note `dag=` (expect about 10.5k) and the times.
- `cargo test -q --release --test kernel_soundness_fuzz --test kernel_fuzz --test compile_fuzz`
- `cargo clippy --all-targets -- -D warnings`

Expected: all pass. The DAG and timing tests now pass.

- [ ] **Step 6: Mutation check**

Change `get`'s condition to `pos < self.scope_base && false`, so it always returns a `Var`. Run the three new or tightened tests and confirm each fails, then restore the condition. Put the output in the report.

- [ ] **Step 7: Commit**

```bash
git add src/kernel.rs src/proof.rs tests/kernel_soundness_fuzz.rs
git commit -m "Postulates are Consts: get returns Const below the open scope, checks split Globals from the scope's locals (stage 3a)"
```

### Task 3: `push` checks each entry

**Files:**
- Modify: `src/kernel.rs` (`Postulates::push`, a private helper `consts_below`, tests)

**Interfaces:**
- Consumes: Task 2's `Postulates` (`scope_base`, `infer`).
- Produces: `push(ty)` panics when any of these holds:
  - (a) `ty` doesn't infer to a `Sort` in the current `Globals` + locals;
  - (b) for a postulate (`pos < scope_base`), `ty` has a loose `Var` or a `Free`;
  - (c) for a postulate, `ty` mentions `Const(j)` with `j >= pos`.

- [ ] **Step 1: Write the failing tests**

```rust
    #[test]
    #[should_panic(expected = "isn't a type")]
    fn push_rejects_an_entry_that_isnt_a_type() {
        let mut p = Postulates::new();
        let a = p.push(sort(0));
        let x = p.push(p.get(a));
        p.push(p.get(x)); // x : A is an element, not a type
    }

    #[test]
    #[should_panic(expected = "closed")]
    fn push_rejects_a_postulate_with_a_loose_var() {
        let mut p = Postulates::new();
        p.push(sort(0));
        p.push(var(0));
    }

    #[test]
    #[should_panic(expected = "closed")]
    fn push_rejects_a_postulate_with_a_free() {
        let mut p = Postulates::new();
        p.push(Expr::Free(0));
    }

    #[test]
    #[should_panic(expected = "earlier")]
    fn push_rejects_a_forward_const() {
        let mut p = Postulates::new();
        p.push(sort(0));
        p.push(Expr::Const(1)); // its own level
    }

    /// Inside a scope an entry's type may mention the scope's earlier
    /// entries, and it's still checked to be a type.
    #[test]
    fn push_accepts_a_scope_entry_typed_by_an_earlier_one() {
        let mut p = Postulates::new();
        let a = p.push(sort(0));
        let s = p.open();
        let x = p.push(p.get(a));
        p.push(id(p.get(a), p.get(x), p.get(x)));
        p.abandon(s);
    }
```

The "closed" tests put their check before the `Sort` inference, so they panic with the closedness message rather than an inference error. Keep the checks in the order Step 3 gives.

- [ ] **Step 2: Run them to verify they fail**

Run: `cargo test -q --lib -- push_rejects push_accepts`
Expected: the four `push_rejects_*` tests fail (no panic), and `push_accepts_*` passes.

- [ ] **Step 3: Implement**

```rust
    pub fn push(&mut self, ty: Expr) -> usize {
        let pos = self.ctx.len();
        if pos < self.scope_base {
            assert!(
                loose_of(&ty) == 0 && free_of(&ty) == 0,
                "a postulate's type must be closed: {ty:?}"
            );
            assert!(consts_below(&ty, pos as u32), "a postulate's type may mention only earlier postulates: {ty:?}");
        }
        // RELATED_WORK §68: an ill-formed entry sat in the context unchecked
        // until a claim that used it failed.
        if let Err(err) = self.infer(&ty).and_then(|t| expect_sort(&t).map(|_| ())) {
            panic!("a postulate's type isn't a type: {err}\n  type: {ty:?}");
        }
        self.ctx.push_back(ty);
        pos
    }
```

```rust
/// Whether every `Const` in `e` is below `bound`.
fn consts_below(e: &Expr, bound: u32) -> bool {
    match e {
        Expr::Const(j) => *j < bound,
        _ => same_shape(e, e, |c, _| consts_below(c, bound)),
    }
}
```

(Check `expect_sort`'s signature in `kernel.rs` and adapt the `map`. `same_shape(e, e, f)` calls `f` on each pair of children and returns whether it returned true for all.)

- [ ] **Step 4: Run everything**

Run: `cargo test -q --lib`, then `cargo test -q --release --test kernel_soundness_fuzz --test kernel_fuzz --test compile_fuzz`, then clippy.
Expected: all pass. If an existing test fails because it deliberately postulates an ill-formed entry (an adversarial kernel test), build that context by hand as a `Ctx`/`Globals` instead of through `Postulates`, and list it in the report. If a proof test fails, stop and report the entry. That is a real builder bug, as in §68, and the controller decides how to fix it.

- [ ] **Step 5: Mutation check**

Remove each of the three checks in turn and confirm the matching test fails, then restore it. Report the output.

- [ ] **Step 6: Commit**

```bash
git add src/kernel.rs
git commit -m "Postulates::push checks each entry: a type, and for a postulate closed and mentioning only earlier ones (stage 3a)"
```

### Task 4 (controller): measure 3a, document, push

- [ ] Build the base (the commit before Task 1) and head binaries with the scratchpad `abbuild.sh`. Use a fresh `target/ab/base-tree` worktree at the base commit; remove the old one first with `git worktree remove`.
- [ ] Run `scripts/quiet_ab/ab.sh` in fresh DIRs:
  - `fib16_instance_proof_cost`: 10 pairs.
  - `cargo bench --bench proofs`: 5 pairs, with `--noplot --warm-up-time 2 --measurement-time 5` and a separate `CRITERION_HOME` per side.
  - Log RTP and the CPU load.
- [ ] Watch with an exiting poll loop, never `tail -F`.
- [ ] `scratchpad/validate.sh`: every step `rc=0`.
- [ ] `RELATED_WORK.md` §69:
  - what was built, and the decisions above (with the options they beat);
  - DAG sizes at `fib(8/12/16)`, the A/B table, and Task 3's cost on its own if visible;
  - what the flip broke and how it was fixed.
- [ ] Other docs:
  - README paragraph: stage 3a built, with the headline numbers.
  - Spec: update the status line, and split Stage 3 into 3a (built) and 3b.
- [ ] Commit, push, and report to the user with the next steps.

---

## 3b: parameters as free levels

### Task 5: `bind`, level-based `close`, and `check_open` in the kernel module

The kernel side only. Nothing in `proof.rs` calls `bind` yet.

**Files:**
- Modify: `src/kernel.rs` (`Postulates` section; tests)

**Interfaces:**
- Consumes: Tasks 1-3.
- Produces:
  - `Postulates` gains the private fields `params: Vec<(u32, Expr)>` (the live `Free` levels and their types, in increasing level order), `next_free: u32` and `scopes: u32` (the open-scope depth).
  - `Scope` gains `params_len: usize` and `first: u32`.
  - `pub fn bind(&mut self, ty: Expr) -> Expr` returns `Expr::Free(level)`. It panics outside a scope, or when `ty` isn't a type.
  - `pub fn check_open(&self, e: &Expr, ty: &Expr) -> Result<(), String>`
  - `pub fn infer_open(&self, e: &Expr) -> Result<Expr, String>`
  - `close` also abstracts the scope's `Free`s.
  - The private helper `fn abstract_frees(e: &Expr, first: u32, levels: &[u32], d: u32) -> Expr`.

- [ ] **Step 1: Write the failing tests**

```rust
    /// The spec's stage 3 test: closing over `Free`s gives exactly the
    /// hand-built dependent `Pi` chain.
    #[test]
    fn close_over_frees_matches_hand_built_dependent_pi_chain() {
        let mut p = Postulates::new();
        let a = p.push(sort(0));
        let s = p.open();
        let x = p.bind(p.get(a));
        let y = p.bind(p.get(a));
        let closed = p.close(s, Binder::Pi, id(p.get(a), x, y));
        assert_eq!(closed, pi(Expr::Const(0), pi(Expr::Const(0), id(Expr::Const(0), var(1), var(0)))));
        assert!(p.check(&closed, &sort(0)).is_ok());
    }

    /// A later parameter's type mentioning an earlier one becomes a `Var`
    /// in its binder's domain.
    #[test]
    fn close_abstracts_a_parameter_in_a_later_parameters_type() {
        let mut p = Postulates::new();
        let a = p.push(sort(0));
        let s = p.open();
        let x = p.bind(p.get(a));
        let e = p.bind(id(p.get(a), x.clone(), x));
        let closed = p.close(s, Binder::Lam, e);
        assert_eq!(closed, lam(Expr::Const(0), lam(id(Expr::Const(0), var(0), var(0)), var(0))));
    }

    /// The teeth of "levels are never reused": a `Free` that escapes its
    /// scope is left alone by a later scope's `close` and fails the check.
    /// With reuse, the later scope would bind it silently.
    #[test]
    fn a_free_that_escapes_its_scope_is_left_by_a_later_close_and_rejected() {
        let mut p = Postulates::new();
        let a = p.push(sort(0));
        let s = p.open();
        let leaked = p.bind(p.get(a));
        let _ = p.close(s, Binder::Lam, leaked.clone());
        let s = p.open();
        let _y = p.bind(p.get(a));
        let closed = p.close(s, Binder::Lam, leaked);
        assert!(p.check(&closed, &pi(Expr::Const(0), Expr::Const(0))).is_err());
    }

    /// An inner scope's `close` leaves the outer scope's parameters free.
    #[test]
    fn an_inner_close_leaves_outer_parameters_free() {
        let mut p = Postulates::new();
        let a = p.push(sort(0));
        let outer = p.open();
        let x = p.bind(p.get(a));
        let inner = p.open();
        let y = p.bind(p.get(a));
        let inner_closed = p.close(inner, Binder::Lam, id(p.get(a), x.clone(), y));
        assert_eq!(inner_closed, lam(Expr::Const(0), id(Expr::Const(0), x, var(0))));
        let closed = p.close(outer, Binder::Lam, inner_closed);
        assert!(p.check(&closed, &pi(Expr::Const(0), pi(Expr::Const(0), id(Expr::Const(0), var(1), var(0))))).is_ok());
    }

    #[test]
    fn check_open_types_the_live_parameters() {
        let mut p = Postulates::new();
        let a = p.push(sort(0));
        let s = p.open();
        let x = p.bind(p.get(a));
        assert!(p.check(&x, &p.get(a)).is_err()); // the kernel rejects Free
        assert!(p.check_open(&x, &p.get(a)).is_ok());
        assert!(p.check_open(&refl(x.clone()), &id(p.get(a), x.clone(), x)).is_ok());
        p.abandon(s);
    }

    #[test]
    #[should_panic(expected = "isn't a type")]
    fn bind_rejects_a_type_that_isnt_one() {
        let mut p = Postulates::new();
        let a = p.push(sort(0));
        let _s = p.open();
        let x = p.bind(p.get(a));
        p.bind(x);
    }
```

- [ ] **Step 2: Run them to verify they fail**

Run: `cargo test -q --lib -- close_over_frees close_abstracts a_free_that_escapes an_inner_close check_open_types bind_rejects`
Expected: compile error (`bind`, `check_open` not found).

- [ ] **Step 3: Implement**
  - `abstract_frees`:
    - Under `d` binders of `e`, `Free(l)` with `l` in `levels` at index `j` becomes `Var(d + (levels.len() - 1 - j) as u32)`. Other `Free`s are left alone.
    - Follow `shift`'s structure exactly: the same variants, the same `cutoff + 1` children, `grow`, and a child-by-pointer fast path. Here the skip test is `free_of(e) <= first` (for a child, `x.free() <= first`), not `loose`.
    - Put the Sigma family inline or out of line, as `shift` does.
    - Find `j` by `levels.binary_search(l)`; the levels are increasing.

    ```rust
    /// Under `d` binders of `e`, `Free(levels[j])` becomes the `Var` for the
    /// `j`-th of `levels.len()` binders wrapped outside `e`, outermost
    /// first. A `Free` not in `levels` (an enclosing scope's, or one that
    /// escaped a closed scope) is left for the final check to reject.
    fn abstract_frees(e: &Expr, first: u32, levels: &[u32], d: u32) -> Expr {
        if free_of(e) <= first {
            return e.clone();
        }
        let go = |x: &Rc<Expr>, d: u32| if x.free() <= first { x.clone() } else { Rc::new(abstract_frees(x, first, levels, d)) };
        grow(|| match e {
            Expr::Free(l) => match levels.binary_search(l) {
                Ok(j) => Expr::Var(d + (levels.len() - 1 - j) as u32),
                Err(_) => Expr::Free(*l),
            },
            Expr::Var(k) => Expr::Var(*k),
            Expr::Sort(i) => Expr::Sort(*i),
            Expr::Const(l) => Expr::Const(*l),
            Expr::Pi(a, b) => Expr::Pi(go(a, d), go(b, d + 1)),
            // ... every other variant exactly as in `shift`, with `d` for `cutoff`
        })
    }
    ```

  - `bind`:

    ```rust
    pub fn bind(&mut self, ty: Expr) -> Expr {
        assert!(self.scopes > 0, "bind outside a scope");
        if let Err(err) = self.infer_open(&ty).and_then(|t| expect_sort(&t).map(|_| ())) {
            panic!("a parameter's type isn't a type: {err}\n  type: {ty:?}");
        }
        let l = self.next_free;
        self.next_free = l.checked_add(1).expect("Free levels ran out");
        self.params.push((l, ty));
        Expr::Free(l)
    }
    ```

  - `open`: as before, plus `params_len: self.params.len(), first: self.next_free`, and `self.scopes += 1`.
  - `abandon`: as before, plus `self.params.truncate(s.params_len); self.scopes -= 1;`. It never restores `next_free` (spec constraint, RELATED_WORK §67).
  - `close`:
    - `assert!(self.ctx.len() == s.base || self.params.len() == s.params_len, "a scope mixes pushed locals and bound parameters")`. Legacy `Var` scopes stay until Task 6 converts them.
    - If `self.params.len() > s.params_len`, abstract:

      ```rust
      let levels: Vec<u32> = self.params[s.params_len..].iter().map(|(l, _)| *l).collect();
      let mut acc = abstract_frees(&body, s.first, &levels, 0);
      for i in (0..levels.len()).rev() {
          let dom = abstract_frees(&self.params[s.params_len + i].1, s.first, &levels[..i], 0);
          acc = match binder { Binder::Pi => pi(dom, acc), Binder::Lam => lam(dom, acc) };
      }
      ```

    - Otherwise, use the legacy `close_pi`/`close_lam` over `ctx[s.base..]`.
    - Then `abandon(s)`.
  - `check_open`/`infer_open`: abstract every live parameter (`first = 0`, all of `self.params`).
    - The local context is `locals[i] = abstract_frees(&params[i].1, 0, &levels[..i], 0)`.
    - `e` and `ty` are abstracted with all `levels` at `d = 0`.
    - Then call `check_in(&globals, &locals, ..)` / `infer_in`, where `globals` is `self.split().0`.
    - `infer_open`'s result mentions parameters as `Var`s. Document that it's for `expect_sort`-style uses only.
  - Update `Postulates`' doc comment: parameters are `Free` levels from a counter that never reuses one (RELATED_WORK §70).
- [ ] **Step 4: Run everything**

Run: `cargo test -q --lib`, the release fuzzers, and clippy.
Expected: all pass, and `proof.rs` is untouched and unaffected.

- [ ] **Step 5: Mutation checks**
  - Make `abandon` restore `next_free` (add `self.next_free = s.first;`, and store nothing extra if `first` already holds it). `a_free_that_escapes_its_scope_...` must fail.
  - Make `abstract_frees` use `j` in place of `levels.len() - 1 - j`. The closing tests must fail.

  Restore both after checking, and report the output.
- [ ] **Step 6: Commit**

```bash
git add src/kernel.rs
git commit -m "Postulates: bind parameters as Free levels, close abstracts them, check_open types them (stage 3b, kernel side)"
```

### Task 6: the builder binds its parameters

The large, mostly mechanical migration. Use a capable model.

**Files:**
- Modify: `src/proof.rs`
- Modify: `src/kernel.rs` (only `push`'s in-scope panic)

**Interfaces:**
- Consumes:
  - Task 5's `bind`, `check_open`, `Scope`, `Binder`;
  - `push` panics while a scope is open (added in Step 1).
- Produces:
  - `struct Params(Vec<Expr>)` holds the `Free`s. `Params::at(&self, _arith: &ArithPostulates) -> Vec<Expr>` returns a clone; keep the signature so call sites don't change, and let stage 4 remove it.
  - `push_path`, `push_calls` and every local in a `build` closure (`v`, `e`, motives, ih, premises) are `Expr`s from `bind`, not positions.

- [ ] **Step 1: Make the tests fail**

Add to `Postulates::push` in `src/kernel.rs`, first line:

```rust
        assert!(self.scopes == 0, "push while a scope is open: bind a scope's entries (RELATED_WORK §70)");
```

Add the test:

```rust
    #[test]
    #[should_panic(expected = "push while a scope is open")]
    fn push_panics_inside_a_scope() {
        let mut p = Postulates::new();
        let a = p.push(sort(0));
        let _s = p.open();
        p.push(p.get(a));
    }
```

Update Task 3's `push_accepts_a_scope_entry_typed_by_an_earlier_one` to use `bind`, and rename it `bind_accepts_a_parameter_typed_by_an_earlier_one`.

Run `cargo test -q --lib`. Expected: every proof test that opens a scope panics with "push while a scope is open". Record the count.

- [ ] **Step 2: Convert the scopes**
  - `params_and_close`: `let positions: Vec<usize>` pushes → `let params: Vec<Expr> = (0..n).map(|_| { let ty = arith.int_ty(); arith.p.bind(ty) }).collect();`, then `Params(params)`.
  - `params_and_close_typed`: the same, with `clo_ty`/`int_ty` per `param_types`.
  - `ev_rec_ty` scope: `let p_ref = arith.p.bind(motive_ty);`. `p_of` then uses `p_ref.clone()` in place of `arith.p.get(p_pos)`.
- [ ] **Step 3: Convert every local push inside a scope**
  - These are the pushes inside `build` closures and between `open` and `close`. In `build_universal` they include:
    - `push_path` (`positions.push(arith.p.push(pf_ty))`), which now returns `Vec<Expr>`;
    - `push_calls` (`v_positions`, `e_positions`), which now returns `(Vec<Expr>, Vec<Expr>)`;
    - the `v_pos`/`e_pos` pairs in the motive, `concl_ty`, `const_int_motive_expr` and `id_motive_expr` closures;
    - `ih_positions`.
  - Each `let x_pos = arith.p.push(ty)` becomes `let x = arith.p.bind(ty)`, and each later `arith.p.get(x_pos)` becomes `x.clone()`.
  - Pushes outside any scope stay `push`, for example `ev_leaf_positions.push(arith.p.push(ty))` after `params_and_close_typed` returns. Step 1's panic tells the two apart.
  - Use `grep -n "p\.push(" src/proof.rs` to walk every site and classify each. The report must list each site as bind or push.
- [ ] **Step 4: Convert the in-scope debug checks**

`debug_assert_has_type` calls `p.check_open(e, expected)`. It's correct inside and outside scopes, since outside one no parameters are live. Its callers don't change.

- [ ] **Step 5: Run everything**

Run: `cargo test -q --lib`, then `cargo test -q --release --lib fib16_instance_proof_cost -- --ignored --nocapture` (note `dag=`), the release fuzzers, and clippy.
Expected: all pass, with the DAG within a few % of Task 2's figure. If a proof fails its final check with "free parameter escaped its scope", a term built inside a scope is used after it closed. Report it, since a leak is exactly what 3b makes loud. Fix it at the source (build that term inside the scope, or rebuild it after), never by rebinding.
- [ ] **Step 6: Mutation check**

Change one converted `bind` back to a `push` (for example the `e : Ev(..)` binder in `concl_ty`). Confirm that `push_panics_inside_a_scope`'s assertion fires in the proof tests, then restore it.
- [ ] **Step 7: Commit**

```bash
git add src/kernel.rs src/proof.rs
git commit -m "Builder binds its scopes' parameters as Free levels; push panics inside a scope (stage 3b)"
```

### Task 7: remove the `Var`-scope path, rename `ctx` to `globals`

**Files:**
- Modify: `src/kernel.rs`, `src/proof.rs`, `tests/kernel_soundness_fuzz.rs`

**Interfaces:**
- Produces:
  - `pub struct Postulates { pub globals: Globals, params, next_free, scopes }`, with no `scope_base`.
  - `get(pos)` is always `Expr::Const(pos as u32)`.
  - `check`/`infer` are `check_in`/`infer_in` with `&self.globals` and `&Ctx::new()`.
  - `Scope { params_len, first }`.
  - The proof records' field `ctx: Ctx` is renamed `globals: Globals` (`EquivalenceProof`, `UniversalTailProof`, `UniversalInstanceProof` and the records at lines ~457, 2348, 3873, 6802, 7587).

- [ ] **Step 1: Write the failing test**

```rust
    /// Globals are never truncated: a postulate pushed after a scope closed
    /// takes the next level, and a scope's `close` never wraps one.
    #[test]
    fn closing_a_scope_keeps_every_postulate() {
        let mut p = Postulates::new();
        let a = p.push(sort(0));
        let s = p.open();
        let x = p.bind(p.get(a));
        let _ = p.close(s, Binder::Lam, x);
        let b = p.push(sort(0));
        assert_eq!((a, b), (0, 1));
        assert_eq!(p.globals.len(), 2);
    }
```

Run it. Expected: compile error (`globals` not found).

- [ ] **Step 2: Remove and rename**
  - Delete `scope_base`, `split`, `Scope::base`/`outer_base`, `close`'s legacy branch and its mixing assert.
  - Rename `ctx` to `globals` throughout.
  - Delete `kernel::close_pi`/`close_lam` if nothing uses them any more. The Task 1 tests that used them (`close_pi_matches_hand_built_dependent_pi_chain`, `close_lam_builds_a_value_of_the_close_pi_type`) are superseded by Task 5's `close_over_frees_*`, so delete them too. Grep first; if anything else uses the functions, keep them and say why.
  - Rename the record fields, and update every `kernel::check_in(&proof.ctx, ...)` → `&proof.globals`.
  - `Anchored`:
    - `depth` reads `arith.p.globals.len()`.
    - `at` gains `debug_assert_eq!(kernel::loose_of(&self.expr), 0, "Anchored term has a loose Var: a scope local escaped bind (RELATED_WORK §70)")` before its shift. Its shift is now the identity; stage 4 removes `Anchored`.
  - Update the doc comments that describe `arith.p.ctx` growing or being truncated (`Anchored`, `Params`, `params_and_close*`, the `ite_clo_ref` priming comment in `build_universal`, `UniversalTailProof`'s docs). They now say:
    - globals only grow;
    - a scope's parameters are `Free`s;
    - the priming is kept until stage 4 because `push` panics inside a scope.
- [ ] **Step 3: Run everything**

Run: `cargo test -q --lib`, the release fuzzers, `cargo run --release`, and clippy.
Expected: all pass. Then run `grep -n "p\.ctx\|\.ctx\b" src/proof.rs src/kernel.rs tests/kernel_soundness_fuzz.rs`: only kernel type-checker uses of a local `ctx` remain, and no `Postulates` field.
- [ ] **Step 4: Commit**

```bash
git add src/kernel.rs src/proof.rs tests/kernel_soundness_fuzz.rs
git commit -m "Postulates holds globals only (never truncated); records carry Globals; drop the Var-scope path (stage 3b)"
```

### Task 8 (controller): measure 3b, document, push

- [ ] Run the A/B as in Task 4, with Task 4's commit as base and HEAD as head. Expect no change; a regression beyond noise gets investigated before the docs.
- [ ] `scratchpad/validate.sh`: every step `rc=0`.
- [ ] `RELATED_WORK.md` §70:
  - what was built;
  - what the in-scope push panic and the escaped-`Free` check found during the migration;
  - the A/B.
- [ ] Other docs:
  - README: stage 3 built.
  - Spec: status line; Stage 4 notes that the push-in-scope panic must be relaxed if the closure priming goes.
  - `TYPES.md`: only if it describes the postulate context (grep `postulat` in it).
- [ ] Commit, push, and report to the user with the next steps (stage 4 is the natural one).

---

## Self-review notes

- **Spec coverage (Stage 3 bullets):**
  - `Postulates` holds globals, the params stack and the next level: Tasks 5 and 7.
  - Check sites move to `check_in`/`infer_in`: Tasks 1, 2 and 7.
  - `push` checks closedness and ordering: Task 3.
  - `get` → `Const`: Task 2.
  - `bind`: Task 5.
  - A scope records the length and the level: Task 5.
  - The three scopes and their locals bind: Task 6.
  - `Params` holds `Free`s: Task 6.
  - A local pushed by mistake fails loudly: Task 6 (stronger than the spec: any in-scope push panics).
  - Constraints from §67:
    - levels are monotonic: Task 5's mutation test;
    - the ordering walk: Task 3;
    - a check left on `check` fails loudly: the kernel already does this;
    - the claim check: §68, done;
    - `InferCache` stays per call: unchanged;
    - the `close` pointer skip: `abstract_frees`' fast path.
- **Spec coverage (Testing → Stage 3):**
  - every proof re-checks: all tasks;
  - `close_pi` over `Free`s: Task 5;
  - an escaped `Free` is rejected: Task 5;
  - `push` panics on a `Free` and on a forward `Const`: Task 3;
  - `infer_is_linear_*` uses `Const`s: Task 2;
  - the tightened fib DAG test and the timing guard: Task 2.
- **Beyond the spec:** Task 3's `Sort` check (decision 2), `check_open` (decision 3), and the push-in-scope panic (decision 4).
