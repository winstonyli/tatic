---
status: done
---

# Kernel constants and free parameters (stage 2): implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Give the kernel `Expr::Const(level)` (a postulate, typed by a
global environment) and `Expr::Free(level)` (a builder parameter, never
typed), with the rules in the spec's Semantics section. Nothing produces
either yet, so every answer is unchanged.

**Architecture:**
- Two leaf variants. `Const` and `Free` have no loose `Var`, so stage 1's
  fast paths already make `shift`, `instantiate` and `is_var_free` the
  identity on them. `same_shape` matches each only against itself, so
  `==` and `def_eq` treat both as neutral atoms.
- Each node caches a second range, `free` (one more than its largest
  `Free` level), in the padding stage 1 left: `Node` stays 56 bytes.
- The global environment is a separate vector, `Globals`, passed beside
  today's `Ctx`: `infer_in(globals, ctx, e)` and `check_in(globals, ctx,
  e, ty)`. `Const(l)` resolves only against `globals`, `Var(k)` only
  against `ctx`. Today's `infer(ctx, e)` and `check(ctx, e, ty)` are
  these with no globals, so no caller changes in this stage.
- A term, an expected type, or a context entry with a `Free` in it is
  rejected. The cached `free` range makes each of these tests O(1).

**Tech Stack:** Rust (edition 2024), cargo tests, criterion benches.

**Spec:** `docs/superpowers/specs/2026-09-25-kernel-constants-and-loose-ranges-design.md`
(stage 2, and its Semantics, Testing and Risks sections). Background:
`RELATED_WORK.md` §64 (spike), §65 (stage 1), §66 (re-baseline).

## Decisions this plan makes (read before Task 1)

The spec leaves three things open or states them loosely. The rulings:

1. **`Globals` beside `Ctx`, not `Ctx { globals, locals }`.** The spec
   says "`Ctx` becomes a struct with two public fields", and also that
   callers don't change. They conflict: `proof.rs` uses `Ctx` as an
   `im::Vector` (`len`, `truncate`, `clone`, `close_pi`'s iteration, and
   `Postulates::push`), so a struct breaks those call sites in a stage
   meant to touch none of them. Keeping `Ctx` as the locals, adding
   `pub type Globals = im::Vector<Expr>`, and adding `infer_in` and
   `check_in` gives the same separation the spec asks for (a `Const` can
   never resolve to a kernel binder) with no caller changes. Stage 3 moves
   `Postulates` to `Globals` and the check sites to `check_in`.
   - Cost if wrong: stage 3 renames two functions at its 64 check sites,
     which it edits anyway.
2. **The kernel threads `globals` as an explicit parameter**, `g:
   &Globals`, on `infer_rc`, `infer_node`, `check_rc`, `infer_sigma`,
   `infer_pair`, `infer_sigrec` and `infer_sup`. The alternative, a field
   on `InferCache`, changes no signatures. But that struct is a memo, and
   the typing rules should read as "Σ; Γ ⊢ e", with Σ visible.
   - Cost if wrong: about 40 mechanical call-site edits to revert.
3. **`Free` is rejected at the door, not only at the leaf.** The spec's
   rule is "`infer` and `check`: an error". A leaf arm alone doesn't cover
   it, because `infer` doesn't visit every subterm:
   - `check`'s `Lam` rule compares the lambda's domain by `def_eq` and
     never infers it.
   - `WRec`'s `children_ty` is only compared.
   - Nothing infers the expected type.

   In each of these places, a `Free` under a redex (`(λx:Free(0). A) a`)
   reduces away, and the term would be accepted with a `Free` still in
   it. So:
   - `infer_in` and `check_in` reject `e` (and `check_in` also rejects
     `expected`) when `free_of` is nonzero, which is O(1).
   - `ctx_lookup` rejects a context entry with a `Free`.
   - `Const` rejects a global whose type has a `Free` or a loose `Var`.
   - `infer_node`'s `Free` arm errors too, though the door makes it
     unreachable.
   - Cost if wrong: none to soundness. It rejects more, and only terms
     that nothing produces yet.

## Global Constraints

- **Trusted kernel code.** This stage changes `src/kernel.rs`. Nothing is
  executed without the user's explicit go-ahead on this plan.
- **Start from a clean tree.** Stage-2 commits contain stage-2 changes
  only. (mimalloc is committed, 77ba201, and lib tests use it too, so the
  `fib(16)` probe measures the shipped allocator.)
- **No change to any answer.** Every existing test and fuzzer passes. The
  only edits to existing tests are new match arms and the generators'
  new leaves (Tasks 1 and 3).
- **CRLF files.** Every file in this repo uses CRLF line endings. Edit with
  the Edit tool, or with Python using `newline=''` and `\r\n`. Never use
  `sed -i`. Don't run `cargo fmt`.
- **LONG_RUNS.** At most 12 build threads (`CARGO_BUILD_JOBS=12`),
  below-normal priority for long runs, CPU under ~20% before any timing
  (or report the load), and `(Get-MpComputerStatus).RealTimeProtectionEnabled`
  logged with every timing. Never touch other sessions' processes (e.g.
  `selfplay-burn*`) or the worktree `.claude/worktrees/goofy-sammet-171d91`.
- **TDD with mutation checks.** Each new test must fail on the mutation
  its step names. Revert the mutation after checking, and say in the
  report which mutations were run.
- **Commits** go to `main`, one per task. End each message with
  `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`. Push after
  Task 4.
- **Validation script.** Tasks 1–4 run the session scratchpad's
  `validate.sh`. If it's missing, recreate it from this text:

```bash
#!/usr/bin/env bash
# README's validation routine; cargo bench runs in criterion's --test mode
# (each bench once) since timing is done separately.
set -u
cd "C:/Users/Winston Li/Documents/GitHub/tatic"
powershell -NoProfile -Command "(Get-Process -Id $(cat /proc/$$/winpid)).PriorityClass = 'BelowNormal'"
export CARGO_BUILD_JOBS=12 RUST_TEST_THREADS=12
step() { echo "=== $*"; "$@" > /tmp/v.out 2>&1; st=$?; grep -E "^test result|^error|warning:|FAILED|panicked" /tmp/v.out | sort | uniq -c | head -20; echo "rc=$st"; }
step cargo build --all-targets
step cargo test --lib --bins
step cargo clippy --all-targets -- -D warnings
step cargo test --release --test compile_fuzz --test kernel_fuzz --test kernel_soundness_fuzz --test syntax_fuzz --test golden_wat
step cargo test --release --lib ir_fuzz -- --ignored
step cargo bench -- --test
step cargo run --release
```

  Every step must print `rc=0`.

---

### Task 1: The two variants, their `free` range, and the structural rules

Every function that matches on `Expr` gains the two leaves. Typing rejects
both for now; Task 2 gives `Const` its rule.

**Files:**
- Modify: `src/kernel.rs`: `Node` and `impl Rc<Expr>` (~49–66),
  `loose_of` (~117), `enum Expr` (~240), `same_shape` (~336), `Drop`
  (~386), `Debug` (~429), `shift` (~526), `instantiate` (~608),
  `is_var_free` (~658), `nf_whnf` (~908), `infer_node` (~1233).
- Modify: `src/kernel.rs` test module: the reference functions `subst`
  (~1800), `is_var_free_ref` (~1893), `shift_ref` (~1913),
  `instantiate_ref` (~1944), and `random_term`'s leaves (~1867).
- Modify: `tests/kernel_soundness_fuzz.rs`: `count_nodes` (~108),
  `nth_subterm` (~124), `replace_nth` (~208) gain the leaf arms.

**Interfaces:**
- Produces: `Expr::Const(u32)`, `Expr::Free(u32)`; `pub fn free_of(e:
  &Expr) -> u32`; `Rc<Expr>::free(&self) -> u32`.

- [ ] **Step 1: Add the variants and the range.** In `enum Expr`, right
  after `Sort(u32)`:

```rust
    /// A postulate: entry `l` of the global environment (`Globals`),
    /// numbered from the first, so neither a binder nor a later global
    /// renumbers it. Typed by `globals[l]`, which must be closed.
    Const(u32),
    /// A builder scope's parameter, by a level no other parameter reuses.
    /// Never typed: `infer` and `check` reject any term, expected type or
    /// context entry with one in it, so a parameter that escapes its
    /// scope fails the check instead of acting as an axiom.
    Free(u32),
```

  `Node` gains `free`, and `Rc::new` fills it:

```rust
struct Node<T> {
    loose: u32,
    free: u32,
    val: T,
}

impl Rc<Expr> {
    pub fn new(e: Expr) -> Self {
        Rc(std::rc::Rc::new(Node { loose: loose_of(&e), free: free_of(&e), val: e }))
    }

    /// One more than the largest loose `Var` index in this node, 0 when
    /// it's closed (saturating at `u32::MAX`, as [`loose_of`]).
    pub fn loose(&self) -> u32 {
        self.0.loose
    }

    /// One more than the largest `Free` level in this node, 0 when it has
    /// none (saturating, as [`free_of`]).
    pub fn free(&self) -> u32 {
        self.0.free
    }
}
```

  Update the section comment above `pub struct Rc<T>` ("with the child's
  loose-variable range cached beside it") to say "with the child's
  loose-variable and free-level ranges cached beside it", and the struct's
  doc to "A shared node, and its [`loose_of`] and [`free_of`] computed when
  it was built."

  `loose_of`'s leaf arm becomes:

```rust
        Expr::Var(k) => k.saturating_add(1),
        Expr::Sort(_) | Expr::Const(_) | Expr::Free(_) => 0,
```

  Add `free_of` right after `loose_of`:

```rust
/// One more than the largest `Free` level in `e`, 0 when it has none, from
/// its children's cached ranges. Binders don't change it: a `Free` is a
/// level, not an index. Saturating, as [`loose_of`].
pub fn free_of(e: &Expr) -> u32 {
    let f = |c: &Rc<Expr>| c.free();
    match e {
        Expr::Free(l) => l.saturating_add(1),
        Expr::Var(_) | Expr::Sort(_) | Expr::Const(_) => 0,
        Expr::Pi(a, b) | Expr::Lam(a, b) | Expr::App(a, b) | Expr::W(a, b) | Expr::Sup(a, b) | Expr::Sigma(a, b) => f(a).max(f(b)),
        Expr::Id(a, b, c) | Expr::Pair(a, b, c) | Expr::SigRec { motive: a, step: b, target: c } => f(a).max(f(b)).max(f(c)),
        Expr::Refl(a) => f(a),
        Expr::J { motive, base, a, b, p } => f(motive).max(f(base)).max(f(a)).max(f(b)).max(f(p)),
        Expr::WRec { motive, children_ty, step, target } => f(motive).max(f(children_ty)).max(f(step)).max(f(target)),
    }
}
```

- [ ] **Step 2: Give every other match the leaves.**
  - `same_shape`: `(Var(i), Var(j)) | (Sort(i), Sort(j)) | (Const(i),
    Const(j)) | (Free(i), Free(j)) => i == j,`
  - `Drop for Expr`: `Expr::Var(_) | Expr::Sort(_) | Expr::Const(_) |
    Expr::Free(_) => {}`
  - `Debug`: `Expr::Const(l) => write!(f, "@{l}"),` and `Expr::Free(l) =>
    write!(f, "${l}"),` after the `Sort` arm.
  - `shift` and `instantiate`: after `Expr::Sort(i) => Expr::Sort(*i),`
    add `Expr::Const(l) => Expr::Const(*l),` and `Expr::Free(l) =>
    Expr::Free(*l),`. (Their fast path returns first, since both have
    `loose` 0. The arms are there for exhaustiveness.)
  - `is_var_free`: `Expr::Sort(_) | Expr::Const(_) | Expr::Free(_) =>
    false,`
  - `nf_whnf`: after the `Sort` arm, `Expr::Const(l) => Expr::Const(*l),`
    and `Expr::Free(l) => Expr::Free(*l),`
  - `infer_node`, after the `Sort` arm (Task 2 replaces the `Const` arm):

```rust
        Expr::Const(l) => Err(format!("unknown constant @{l}")),
        Expr::Free(l) => Err(free_escaped(*l)),
```

  and next to `sup_codomain_depends_on_own_argument`:

```rust
/// The error for a `Free` reaching the type checker, out of line and
/// `#[cold]` (see `infer_sigma`).
#[cold]
#[inline(never)]
fn free_escaped(l: u32) -> String {
    format!("free parameter ${l} escaped its scope")
}
```

  - Test module: `subst`, `shift_ref` and `instantiate_ref` gain
    `Expr::Const(l) => Expr::Const(*l),` and `Expr::Free(l) =>
    Expr::Free(*l),` after their `Sort` arm. `is_var_free_ref`'s leaf arm
    becomes `Expr::Sort(_) | Expr::Const(_) | Expr::Free(_) => false,`.
  - `tests/kernel_soundness_fuzz.rs`: `count_nodes` and `nth_subterm` add
    `| Expr::Const(_) | Expr::Free(_)` to their `Var`/`Sort` leaf arm, and
    `replace_nth` adds `Expr::Const(l) => Expr::Const(*l),` and
    `Expr::Free(l) => Expr::Free(*l),`.
  - Any other non-exhaustive match the compiler reports gets the same
    leaf treatment, and is listed in the report.

  Run `cargo build --all-targets`. Expected: builds with no warnings.

- [ ] **Step 3: Put `Const` and `Free` in the random terms.** In
  `random_term`, make the pool's leaves `Var(0..4)`, `Sort(0)`,
  `Const(0)`, `Const(1)`, `Free(0)` and `Free(2)`, and update its doc to
  say so:

```rust
        let mut pool: Vec<Rc<Expr>> = (0..4)
            .map(|k| Rc::new(var(k)))
            .chain([Rc::new(sort(0)), Rc::new(Expr::Const(0)), Rc::new(Expr::Const(1)), Rc::new(Expr::Free(0)), Rc::new(Expr::Free(2))])
            .collect();
```

  `loose_matches_a_walk` and `shift_and_instantiate_match_a_reference`
  now cover both leaves. Run them. Expected: pass.

- [ ] **Step 4: Write the new tests** (test module, after
  `shift_keeps_closed_children_by_pointer`):

```rust
    /// The largest `Free` level a walk of the whole term finds, plus one
    /// (0 with none): the reference for the cached `free` range.
    fn free_ref(e: &Expr) -> u32 {
        grow(|| match e {
            Expr::Free(l) => l + 1,
            _ => {
                let mut m = 0;
                same_shape(e, e, |c, _| {
                    m = m.max(free_ref(c));
                    true
                });
                m
            }
        })
    }

    /// Every node's cached `free` range is the one a walk finds, and a
    /// binder doesn't lower it (a `Free` is a level, not an index).
    #[test]
    fn free_matches_a_walk() {
        let mut next = splitmix(31);
        let mut with_free = 0;
        for _ in 0..20_000 {
            let e = random_term(&mut next);
            let walk = free_ref(&e);
            with_free += (walk > 0) as usize;
            assert_eq!(Rc::new(e.clone()).free(), walk, "{e:?}");
            assert_eq!(free_of(&e), walk, "{e:?}");
        }
        assert!(with_free > 2_000, "only {with_free} terms had a Free");
    }

    /// The two new leaves are neutral atoms: each is equal only to itself,
    /// and never to the other kind or to a `Var` with the same number.
    #[test]
    fn const_and_free_are_equal_only_to_themselves() {
        let (c0, c1, f0, f1) = (Expr::Const(0), Expr::Const(1), Expr::Free(0), Expr::Free(1));
        assert!(def_eq(&c0, &Expr::Const(0)));
        assert!(def_eq(&f0, &Expr::Free(0)));
        for (x, y) in [(&c0, &c1), (&f0, &f1), (&c0, &f0), (&c0, &var(0)), (&f0, &var(0))] {
            assert!(!def_eq(x, y), "{x:?} vs {y:?}");
            assert!(x != y, "{x:?} == {y:?}");
        }
    }

    /// Beta reduction substitutes for the bound `Var` only: a `Const` or a
    /// `Free` in the body, or in the argument, comes through unchanged.
    #[test]
    fn beta_leaves_const_and_free_alone() {
        let body = app(Expr::Const(0), var(0));
        assert_eq!(whnf(&app(lam(sort(0), Expr::Const(0)), sort(0))), Expr::Const(0));
        assert_eq!(whnf(&app(lam(sort(0), body), Expr::Free(3))), app(Expr::Const(0), Expr::Free(3)));
        assert_eq!(nf(&app(lam(sort(0), Expr::Free(1)), var(5))), Expr::Free(1));
    }

    /// Both ranges fit the padding stage 1 left (`RELATED_WORK.md` §64):
    /// a node is a 48-byte `Expr` and two `u32`s.
    #[test]
    fn a_node_is_56_bytes() {
        assert_eq!(std::mem::size_of::<Expr>(), 48);
        assert_eq!(std::mem::size_of::<Node<Expr>>(), 56);
    }
```

- [ ] **Step 5: Run the new tests.**
  Run: `cargo test --lib kernel::tests::free_matches_a_walk kernel::tests::const_and_free kernel::tests::beta_leaves kernel::tests::a_node_is_56_bytes`
  (or one filter at a time). Expected: all pass.

- [ ] **Step 6: Mutation checks.** Apply each mutation, confirm the named
  test fails, then revert it:
  - In `free_of`, change the `Pi`/`Lam`/... arm to `f(a)`:
    `free_matches_a_walk` fails.
  - In `free_of`, lower a binder's body the way `loose_of` does
    (`f(a).max(f(b).saturating_sub(1))` for `Pi | Lam | W | Sigma`, split
    out of the arm): `free_matches_a_walk` fails.
  - In `same_shape`, change the `Const` pair arm to `(Const(_), Const(_))
    => true`: `const_and_free_are_equal_only_to_themselves` fails.
  - In `Node`, make `free` a `u64`: `a_node_is_56_bytes` fails.
  - `beta_leaves_const_and_free_alone` has no single-line mutation that
    reaches it, since stage 1's fast path returns before the new `shift`
    and `instantiate` arms run. It pins the behaviour in case that fast
    path ever changes. Say so in the report.

- [ ] **Step 7: Validate and commit.** Run `validate.sh`; every step
  `rc=0`. Commit:

```bash
git add src/kernel.rs tests/kernel_soundness_fuzz.rs
git commit -m "Kernel: Const and Free leaves with a cached free-level range; typing rejects both (stage 2 of RELATED_WORK §64)

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

---

### Task 2: The global environment and the typing rules

**Files:**
- Modify: `src/kernel.rs`: after `pub type Ctx` (~1035): `Globals`;
  `ctx_lookup` (~1068); `infer_sigma`, `infer_pair`, `infer_sigrec`,
  `infer_sup`, `infer`, `infer_rc`, `infer_node`, `check`, `check_rc`
  (~1123–1393).
- Test: `src/kernel.rs` test module, after `refl_typechecks_for_a_postulated_element` (~3067).

**Interfaces:**
- Consumes: `Expr::Const`, `Expr::Free`, `free_of`, `free_escaped` (Task 1).
- Produces: `pub type Globals = im::Vector<Expr>`;
  `pub fn infer_in(globals: &Globals, ctx: &Ctx, e: &Expr) -> Result<Expr, String>`;
  `pub fn check_in(globals: &Globals, ctx: &Ctx, e: &Expr, expected: &Expr) -> Result<(), String>`.
  `infer` and `check` keep their signatures.

- [ ] **Step 1: Write the failing tests** (they don't compile until
  Step 3, which counts as failing):

```rust
    /// `A : Type0` and `a : A` as globals: the environment the tests below
    /// type constants in.
    fn two_globals() -> Globals {
        let mut g = Globals::new();
        g.push_back(sort(0));
        g.push_back(Expr::Const(0));
        g
    }

    #[test]
    fn a_const_has_its_globals_type() {
        let g = two_globals();
        let a = Expr::Const(1);
        assert_eq!(infer_in(&g, &Ctx::new(), &a), Ok(Expr::Const(0)));
        assert_eq!(check_in(&g, &Ctx::new(), &refl(a.clone()), &id(Expr::Const(0), a.clone(), a)), Ok(()));
        // No shift: the same `Const` has the same type under a binder.
        assert_eq!(infer_in(&g, &Ctx::new(), &lam(sort(0), Expr::Const(1))), Ok(pi(sort(0), Expr::Const(0))));
    }

    #[test]
    fn a_const_past_the_environment_is_rejected() {
        assert!(infer_in(&two_globals(), &Ctx::new(), &Expr::Const(2)).is_err());
        assert!(infer(&Ctx::new(), &Expr::Const(0)).is_err(), "no globals at all");
    }

    /// `Const(l)` names a global, never a binder the kernel pushed. With one
    /// global, `Const(1)` under a binder would be that binder if constants
    /// and binders shared one vector, and `(λx:A. Const(1)) a` would then
    /// reduce to a `Const(1)` that refers to nothing.
    #[test]
    fn a_const_at_a_binders_position_is_rejected() {
        let mut g = Globals::new();
        g.push_back(sort(0));
        assert!(infer_in(&g, &Ctx::new(), &lam(Expr::Const(0), Expr::Const(1))).is_err());
        let mut ctx = Ctx::new();
        ctx.push_back(Expr::Const(0));
        assert!(infer_in(&g, &ctx, &Expr::Const(1)).is_err(), "a caller's local isn't a global either");
    }

    /// A global's type must be closed: no loose `Var` (it would mean a
    /// different thing at every depth) and no `Free`.
    #[test]
    fn a_global_whose_type_is_open_is_rejected() {
        for bad in [var(0), Expr::Free(0), pi(sort(0), var(1))] {
            let mut g = Globals::new();
            g.push_back(bad.clone());
            assert!(infer_in(&g, &Ctx::new(), &Expr::Const(0)).is_err(), "{bad:?}");
        }
    }

    /// A `Free` fails the check wherever it sits, including where `infer`
    /// never looks: a lambda's domain under `check` (compared by `def_eq`
    /// only) and the expected type, each under a redex that reduces the
    /// `Free` away.
    #[test]
    fn a_free_is_rejected_everywhere() {
        let g = two_globals();
        let none = Ctx::new();
        let hide = |x: Expr| app(lam(Expr::Free(0), x), Expr::Const(1)); // reduces to x
        assert!(infer_in(&g, &none, &Expr::Free(0)).is_err());
        assert!(infer_in(&g, &none, &lam(sort(0), Expr::Free(0))).is_err(), "under a binder");
        assert!(infer_in(&g, &none, &pi(Expr::Free(0), sort(0))).is_err(), "in a type");
        assert!(check_in(&g, &none, &Expr::Const(1), &hide(Expr::Const(0))).is_err(), "in the expected type");
        let lam_hidden_dom = lam(hide(Expr::Const(0)), Expr::Const(1));
        assert!(check_in(&g, &none, &lam_hidden_dom, &pi(Expr::Const(0), Expr::Const(0))).is_err(), "in a checked lambda's domain");
        let mut ctx = Ctx::new();
        ctx.push_back(Expr::Free(0));
        assert!(infer_in(&g, &ctx, &var(0)).is_err(), "in a context entry");
        // The same terms without the `Free` are fine, so the rejections
        // above are the `Free`'s doing.
        let unhide = |x: Expr| app(lam(Expr::Const(0), x), Expr::Const(1));
        assert_eq!(check_in(&g, &none, &Expr::Const(1), &unhide(Expr::Const(0))), Ok(()));
        assert_eq!(check_in(&g, &none, &lam(unhide(Expr::Const(0)), Expr::Const(1)), &pi(Expr::Const(0), Expr::Const(0))), Ok(()));
    }
```

- [ ] **Step 2: Run to see them fail.**
  Run: `cargo test --lib kernel::tests::a_`. Expected: compile errors for
  `Globals`, `infer_in` and `check_in`.

- [ ] **Step 3: Implement.** After `pub type Ctx = im::Vector<Expr>;`:

```rust
/// The global environment: constant `l`'s type is `globals[l]`, closed, so
/// no binder or later global changes what it means. Kept apart from
/// [`Ctx`], the kernel's own binders, so a `Const` can never resolve to
/// one: with a single vector, `(λx:A. Const(L)) a` would reduce to a
/// `Const(L)` that no longer refers to anything.
///
/// Trusted like `Ctx`: nothing checks that an entry is a type, and a
/// constant is an axiom.
pub type Globals = im::Vector<Expr>;
```

  `ctx_lookup` returns an error for a context entry with a `Free`. Its
  only caller is `infer_node`'s `Var` arm (confirm with `grep -n
  ctx_lookup src/kernel.rs`), which drops its `ok_or_else`:

```rust
fn ctx_lookup(ctx: &Ctx, k: u32) -> Result<Expr, String> {
    let k_usize = k as usize;
    if k_usize >= ctx.len() {
        return Err(format!("unbound variable #{k}"));
    }
    let idx = ctx.len() - 1 - k_usize;
    let ty = &ctx[idx];
    if free_of(ty) > 0 {
        return Err(free_escaped(free_of(ty) - 1));
    }
    // (keep the existing comment on the shift)
    Ok(shift(ty, 0, k as i32 + 1))
}
```

  Add the `Const` rule next to `ctx_lookup`:

```rust
/// Constant `l`'s type: `globals[l]` as is, since a closed type has no
/// variable to shift. An error when `l` is past the environment, or when
/// the type isn't closed.
fn const_type(g: &Globals, l: u32) -> Result<Expr, String> {
    match g.get(l as usize) {
        Some(ty) if loose_of(ty) == 0 && free_of(ty) == 0 => Ok(ty.clone()),
        Some(ty) => Err(format!("constant @{l}'s type isn't closed: {ty:?}")),
        None => Err(format!("unknown constant @{l}")),
    }
}
```

  Thread `g: &Globals` as the first parameter of `infer_rc`, `infer_node`,
  `check_rc`, `infer_sigma`, `infer_pair`, `infer_sigrec` and `infer_sup`,
  and pass `g` at every call among them. In `infer_node`:

```rust
        Expr::Var(k) => ctx_lookup(ctx, *k),
        Expr::Sort(i) => /* unchanged */,
        Expr::Const(l) => const_type(g, *l),
        Expr::Free(l) => Err(free_escaped(*l)),
```

  Replace the public entry points:

```rust
/// `e`'s type, with constants typed by `globals` and variables by `ctx`.
/// A `Free` anywhere in `e` is an error; so is one in a `ctx` entry, when
/// `e` uses it.
pub fn infer_in(globals: &Globals, ctx: &Ctx, e: &Expr) -> Result<Expr, String> {
    if free_of(e) > 0 {
        return Err(free_escaped(free_of(e) - 1));
    }
    infer_node(globals, &mut InferCache::default(), ctx, 0, &Rc::new(e.clone()))
}

/// [`infer_in`] with no globals.
pub fn infer(ctx: &Ctx, e: &Expr) -> Result<Expr, String> {
    infer_in(&Globals::new(), ctx, e)
}
```

  and, keeping `check`'s existing doc comment on `check_in`:

```rust
pub fn check_in(globals: &Globals, ctx: &Ctx, e: &Expr, expected: &Expr) -> Result<(), String> {
    // Checked here, not only at the leaf: `check`'s `Lam` rule never
    // infers the lambda's domain, `WRec`'s `children_ty` is only compared,
    // and nothing infers `expected`, so a `Free` under a redex in any of
    // them would reduce away unseen. `free_of` is O(1).
    for t in [e, expected] {
        if free_of(t) > 0 {
            return Err(free_escaped(free_of(t) - 1));
        }
    }
    check_rc(globals, &mut InferCache::default(), ctx, 0, &Rc::new(e.clone()), expected)
}

/// [`check_in`] with no globals.
pub fn check(ctx: &Ctx, e: &Expr, expected: &Expr) -> Result<(), String> {
    check_in(&Globals::new(), ctx, e, expected)
}
```

  Keep the parameter order `(g, ic, ctx, cid, ...)` on the internal
  functions.

- [ ] **Step 4: Run the tests.**
  Run: `cargo test --lib kernel::tests`. Expected: all pass, old and new.

- [ ] **Step 5: Mutation checks.** Each must make the named test fail;
  revert after:
  - `const_type`: `None => Ok(sort(0))`: `a_const_past_the_environment_is_rejected`.
  - `const_type` resolving against a combined vector: replace its body's
    `g.get(l as usize)` with
    `g.iter().chain(ctx.iter()).nth(l as usize)` (pass `ctx` in for the
    mutation): `a_const_at_a_binders_position_is_rejected`.
  - `const_type`: drop `loose_of(ty) == 0 &&`: `a_global_whose_type_is_open_is_rejected`.
  - `const_type`: drop `&& free_of(ty) == 0`: `a_global_whose_type_is_open_is_rejected`.
  - `check_in`: check only `[e]`, not `expected`: `a_free_is_rejected_everywhere`
    ("in the expected type").
  - `check_in`: check only `[expected]`: `a_free_is_rejected_everywhere`
    ("in a checked lambda's domain").
  - `ctx_lookup`: drop the `free_of` test: `a_free_is_rejected_everywhere`
    ("in a context entry").
  - `infer_in`: drop its `free_of` test. Expected: **no** test fails,
    because `infer` visits every subterm and the leaf arm rejects it. Say
    so in the report; the door on `infer_in` is kept for symmetry with
    `check_in`, and costs O(1).
    (Wrong: see RELATED_WORK §67. The final review found a term the door
    alone rejects; the test now covers it.)

- [ ] **Step 6: Validate and commit.** `validate.sh`, every step `rc=0`.

```bash
git add src/kernel.rs
git commit -m "Kernel: a global environment types Const; Free is rejected in terms, expected types and context entries (stage 2)

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

---

### Task 3: The fuzzers generate both

Arms alone leave the new rules unfuzzed (spec, Risks). Three properties:
- `kernel_fuzz` (crash safety): the generators emit `Const`s and `Free`s,
  and run in an environment. Any term with a `Free` comes back `Err`.
- `kernel_soundness_fuzz` (no false equality), in the constant form of
  its context: no random term proves the unrelated claim, and no term
  with a `Free` checks.
- `kernel_soundness_fuzz`, differential: moving the context's postulates
  into `Globals` changes no answer.

**Files:**
- Modify: `tests/kernel_fuzz.rs`
- Modify: `tests/kernel_soundness_fuzz.rs`

**Interfaces:**
- Consumes: `kernel::Globals`, `kernel::infer_in`, `kernel::check_in`,
  `Expr::Const`, `Expr::Free` (Tasks 1–2).

- [ ] **Step 1: `kernel_fuzz.rs`.**
  - `Rng` gains `made_free: bool`. `Rng::new` sets it false.
  - `gen_leaf` gains two cases (widen `rng.below(4)` to `rng.below(6)`):
    `4 => Expr::Const(rng.below(GLOBALS + 2))` (in range, or just past it)
    and `5 => { rng.made_free = true; Expr::Free(rng.below(3)) }`, with
    `const GLOBALS: u32 = 4;`.
  - Add the environment. Its last entry is deliberately open, so the
    rejection path runs:

```rust
/// A small environment for the generated `Const`s: `A : Type0`, `a : A`,
/// `f : A -> A`, and one deliberately open entry (`#0`), which the kernel
/// must reject when a `Const` uses it.
fn globals() -> kernel::Globals {
    let mut g = kernel::Globals::new();
    g.push_back(kernel::sort(0));
    g.push_back(Expr::Const(0));
    g.push_back(kernel::arrow(Expr::Const(0), Expr::Const(0)));
    g.push_back(Expr::Var(0));
    g
}
```

  - The first test keeps its `typecheck(&e)` call (no globals: every
    `Const` is unknown) and adds a second call,
    `kernel::infer_in(&g, &kernel::Ctx::new(), &e)`, under the same
    `catch_unwind` and assertion. The second test calls
    `kernel::check_in(&g, &kernel::Ctx::new(), &e, &expected)` in place
    of `check`. After each no-panic assertion, add (for the `infer_in`
    and `check_in` results):

```rust
        if rng.made_free {
            assert!(matches!(result, Ok(Err(_))), "a term with a Free was accepted on seed={seed}: {e:?}");
        }
```

  - Update the module doc's first paragraph to mention `Const`s past the
    environment, an open global, and `Free`s, which must never check.

- [ ] **Step 2: `kernel_soundness_fuzz.rs`: constant form and generators.**
  - `Rng` gains `consts: bool` (false from `Rng::new`). `gen_leaf` starts
    with `if rng.consts && rng.below(3) == 0 { return
    Expr::Const(rng.below(GLOBALS + 2)); }`, with `const GLOBALS: u32 =
    7;` (the context's length). The branch draws no random number when
    `consts` is false, so the existing tests keep their exact streams.
    `Free`s are spliced in by `replace_nth` in the third test below, not
    generated.
  - Add the conversion and the constant-form context:

```rust
/// `e` with its references to an `n`-entry context turned into constants.
/// Under `d` binders, `Var(d + i)` for `i < n` is entry `n - 1 - i`, so it
/// becomes `Const(n - 1 - i)`. A `Var` past the context drops by `n`,
/// still unbound. Bound variables stay.
fn to_consts(e: &Expr, n: u32, d: u32) -> Expr {
    let go = |x: &Expr, d: u32| to_consts(x, n, d);
    match e {
        Expr::Var(k) if *k < d => Expr::Var(*k),
        Expr::Var(k) if *k - d < n => Expr::Const(n - 1 - (*k - d)),
        Expr::Var(k) => Expr::Var(*k - n),
        Expr::Sort(i) => Expr::Sort(*i),
        Expr::Const(l) => Expr::Const(*l),
        Expr::Free(l) => Expr::Free(*l),
        Expr::Pi(a, b) => kernel::pi(go(a, d), go(b, d + 1)),
        Expr::Lam(a, b) => kernel::lam(go(a, d), go(b, d + 1)),
        Expr::App(f, a) => kernel::app(go(f, d), go(a, d)),
        Expr::Id(a, x, y) => kernel::id(go(a, d), go(x, d), go(y, d)),
        Expr::Refl(a) => kernel::refl(go(a, d)),
        Expr::J { motive, base, a, b, p } => kernel::jelim(go(motive, d), go(base, d), go(a, d), go(b, d), go(p, d)),
        Expr::W(a, b) => kernel::wty(go(a, d), go(b, d + 1)),
        Expr::Sup(a, f) => kernel::sup(go(a, d), go(f, d)),
        Expr::WRec { motive, children_ty, step, target } => kernel::wrec(go(motive, d), go(children_ty, d + 1), go(step, d), go(target, d)),
        Expr::Sigma(a, b) => kernel::sigma(go(a, d), go(b, d + 1)),
        Expr::Pair(fam, a, b) => kernel::pair(go(fam, d + 1), go(a, d), go(b, d)),
        Expr::SigRec { motive, step, target } => kernel::sigrec(go(motive, d), go(step, d), go(target, d)),
    }
}

/// The context's postulates as globals: entry `i` was written under `i`
/// earlier entries.
fn to_globals(ctx: &kernel::Ctx) -> kernel::Globals {
    ctx.iter().enumerate().map(|(i, ty)| to_consts(ty, i as u32, 0)).collect()
}
```

  (If `kernel::sigma`, `pair` or `sigrec` aren't exported, check
  `src/kernel.rs` ~502–508: they're `pub fn`.)

- [ ] **Step 3: The three new tests.**

```rust
/// Moving the context's postulates into the global environment changes no
/// answer: every candidate, random or a mutant of a valid proof, checks
/// against the claim in constant form exactly when it checks in the
/// original.
#[test]
fn the_global_environment_agrees_with_the_context() {
    const SEEDS: u64 = 20_000;
    let ctx = build_ctx();
    let n = ctx.p.ctx.len() as u32;
    let g = to_globals(&ctx.p.ctx);
    let pool = valid_seed_pool(&ctx);
    let (mut agreed_ok, mut agreed_err) = (0, 0);
    for seed in 0..SEEDS {
        let mut rng = Rng::new(0xD1FF_u64 ^ seed);
        let claim = if seed % 2 == 0 { kernel::id(ctx.a_ty.clone(), ctx.a.clone(), ctx.c.clone()) } else { kernel::id(ctx.a_ty.clone(), ctx.a.clone(), ctx.a.clone()) };
        let candidate = if seed % 3 == 0 {
            gen_expr(&mut rng, n, MAX_DEPTH)
        } else {
            let base = &pool[rng.below(pool.len() as u32) as usize];
            mutate_once(&mut rng, base, n)
        };
        let by_vars = kernel::check(&ctx.p.ctx, &candidate, &claim).is_ok();
        let by_consts = kernel::check_in(&g, &kernel::Ctx::new(), &to_consts(&candidate, n, 0), &to_consts(&claim, n, 0)).is_ok();
        assert_eq!(by_vars, by_consts, "seed={seed}: {candidate:?} against {claim:?}");
        if by_vars { agreed_ok += 1 } else { agreed_err += 1 }
    }
    assert!(agreed_ok > 200, "only {agreed_ok} candidates checked; the differential has too few positive cases");
    assert!(agreed_err > 200, "only {agreed_err} candidates were rejected");
}

/// The core soundness property in constant form: with the postulates as
/// globals and candidates free to name any constant (or one past the
/// environment), nothing proves `Id(A, a, b)`.
#[test]
fn kernel_never_accepts_a_random_term_as_proving_an_unrelated_equality_in_constant_form() {
    const SEEDS: u64 = 20_000;
    let ctx = build_ctx();
    let n = ctx.p.ctx.len() as u32;
    let g = to_globals(&ctx.p.ctx);
    let claim = to_consts(&kernel::id(ctx.a_ty.clone(), ctx.a.clone(), ctx.b.clone()), n, 0);
    for seed in 0..SEEDS {
        let mut rng = Rng::new(0xC0DE_C0DE_u64 ^ seed);
        rng.consts = true;
        let candidate = gen_expr(&mut rng, 0, MAX_DEPTH);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| kernel::check_in(&g, &kernel::Ctx::new(), &candidate, &claim)));
        match result {
            Ok(Err(_)) => {}
            Ok(Ok(())) => panic!("SOUNDNESS BUG: seed={seed} accepted {candidate:?} as proof of {claim:?}"),
            Err(_) => panic!("kernel::check_in panicked on seed={seed}: {candidate:?}"),
        }
    }
}

/// A `Free` never checks: mutants of valid proofs (in constant form) with
/// a `Free` spliced in are rejected against their own true claims, which
/// they'd otherwise often still prove.
#[test]
fn a_term_with_a_free_never_checks() {
    const SEEDS: u64 = 20_000;
    let ctx = build_ctx();
    let n = ctx.p.ctx.len() as u32;
    let g = to_globals(&ctx.p.ctx);
    let claims = [
        kernel::id(ctx.a_ty.clone(), ctx.a.clone(), ctx.a.clone()),
        kernel::id(ctx.a_ty.clone(), ctx.a.clone(), ctx.c.clone()),
        kernel::id(ctx.a_ty.clone(), ctx.c.clone(), ctx.a.clone()),
        kernel::id(ctx.a_ty.clone(), ctx.a.clone(), ctx.a.clone()),
        kernel::id(ctx.b_ty.clone(), kernel::app(ctx.f.clone(), ctx.a.clone()), kernel::app(ctx.f.clone(), ctx.c.clone())),
    ];
    let pool = valid_seed_pool(&ctx);
    for seed in 0..SEEDS {
        let mut rng = Rng::new(0xF3EE_u64 ^ seed);
        let i = rng.below(pool.len() as u32) as usize;
        let proof = to_consts(&pool[i], n, 0);
        let claim = to_consts(&claims[i], n, 0);
        let total = count_nodes(&proof);
        let mut c = 0;
        let mutant = replace_nth(&proof, rng.below(total), &mut c, &Expr::Free(rng.below(3)));
        let result = kernel::check_in(&g, &kernel::Ctx::new(), &mutant, &claim);
        assert!(result.is_err(), "seed={seed}: {mutant:?} with a Free checked against {claim:?}");
    }
}
```

  `claims[i]` must be the claim `pool[i]` proves. Check it against
  `valid_seed_pool`'s order: refl(a), pac, sym(pac), trans(pac, sym pac),
  cong1(f, pac). That's `Id(A,a,a)`, `Id(A,a,c)`, `Id(A,c,a)`,
  `Id(A,a,a)` and `Id(B,f a,f c)`. Assert it once, before the loop: each
  unmutated `proof` checks against its `claim` in constant form.

- [ ] **Step 4: Run the fuzzers.**
  Run: `cargo test --release --test kernel_fuzz --test kernel_soundness_fuzz`.
  Expected: all pass. If `the_global_environment_agrees_with_the_context`
  finds a disagreement, **stop and report it with the seed**. Don't
  weaken the property: a disagreement is a kernel finding, since the two
  forms should be the same judgement.

- [ ] **Step 5: Mutation checks.** Each must make the named fuzzer test
  fail; revert after:
  - `const_type` resolves against the wrong end
    (`g.get(g.len().wrapping_sub(1 + l as usize))`):
    `the_global_environment_agrees_with_the_context`. (Shifting the type
    isn't a useful mutation: a closed type shifts to itself.)
  - `infer_node`'s `Free` arm returns `Ok(sort(0))` **and** the doors in
    `infer_in` and `check_in` are removed: at least one of
    `a_term_with_a_free_never_checks` and `kernel_fuzz`'s `made_free`
    assertions fails. Report which.
  - `same_shape`'s `Const` pair arm ignores the index: expected to break
    the differential or the constant-form soundness test. Report which.

- [ ] **Step 6: Validate and commit.** `validate.sh`, every step `rc=0`.
  Record the three fuzzers' run times in the report (they run in the
  release fuzz step).

```bash
git add tests/kernel_fuzz.rs tests/kernel_soundness_fuzz.rs
git commit -m "Fuzz: kernel fuzzers generate Const and Free; the global environment agrees with the context on every candidate (stage 2)

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

---

### Task 4: Measure, document, push

Stage 2 claims no speedup. Measure only that it costs nothing: one more
`max` per `Rc::new`, one more parameter per `infer` frame, and the O(1)
doors.

**Files:**
- Modify: `RELATED_WORK.md` (new §67 before `## Sources`), `README.md`
  (the paragraph citing §65 and §66, ~1100–1112), the spec (status
  line, stage 2 bullet).

- [ ] **Step 1: Interleaved A/B with `scripts/quiet_ab/`.** Other
  sessions' jobs load this machine in bursts, and one binary's own
  `fib(16)` runs spread 24–28% (RELATED_WORK §66), so 3 runs per side
  can't show "within noise". Use the runner (its header has the usage;
  run `scripts/quiet_ab/test_clean.sh` first):
  1. Build both sides into a worktree so `HEAD`'s tree isn't touched:
     `git worktree add --detach target/ab/base-tree BASE`, then in each
     tree `CARGO_BUILD_JOBS=12 cargo bench --bench proofs --no-run` and
     `cargo test --release --lib --no-run`, both with
     `--message-format=json`. Each binary's path is the `executable` of
     its `compiler-artifact` line (it may sit under
     `target/release/build/`, not `deps/`). Copy the four executables to `target/ab/bin/` as
     `proofs-base.exe`, `proofs-head.exe`, `probe-base.exe` and
     `probe-head.exe`, since a rebuild would overwrite them.
  2. Probe, 10 clean pairs:
     `p=scripts/quiet_ab/pin.sh; t="fib16_instance_proof_cost --ignored --nocapture"`,
     `scripts/quiet_ab/ab.sh target/ab/fib 10 3 -- $p target/ab/bin/probe-base.exe $t -- $p target/ab/bin/probe-head.exe $t`.
  3. Proof benches, 5 clean pairs, with `CRITERION_HOME=target/ab/crit`:
     `scripts/quiet_ab/ab.sh target/ab/proofs 5 4 -- $p target/ab/bin/proofs-base.exe --bench --noplot --warm-up-time 2 --measurement-time 5 -- $p target/ab/bin/proofs-head.exe --bench --noplot --warm-up-time 2 --measurement-time 5`.
  4. `python scripts/quiet_ab/clean.py DIR/samples.log DIR/runs.log` per
     run; use only rounds where both runs are clean. From each clean
     `A.N.txt`/`B.N.txt` take the probe's `fib16 dag= build= check=` line
     and criterion's middle `time:` estimate per bench.
  Report per metric: best and median of each side, the change in each,
  each side's own spread (slowest clean run over best), other processes'
  load range from `clean.py`, and Defender RTP from `runs.log`.
  Expected: every change within the sides' own spread, and the DAG
  unchanged (227,157 nodes). If a change exceeds the spread in best *and*
  median, investigate before documenting. Remove the worktree after
  (`git worktree remove target/ab/base-tree`).

- [ ] **Step 2: Docs.**
  - `RELATED_WORK.md` §67 "Stage 2: constants and free parameters in
    the kernel":
    - what was built;
    - the three decisions above, and why (the `Ctx`/`Globals` split vs
      the spec's struct, the explicit parameter, the doors);
    - the mutation results, including the ones no test catches and why;
    - the differential fuzzer;
    - the A/B numbers, with CPU load and RTP state.
  - `README.md`: in the paragraph citing §65 and §66, after the stage-1 sentence,
    say stage 2 is built: the kernel types `Const`s from a global
    environment and rejects `Free`s, and nothing produces either until
    stage 3 (§67). Adjust "The rest of §64 is designed but not built" to
    name only stages 3 and 4.
  - Spec: the status line gets "stage 2 built (§67)"; the stage 2 bullet
    gets "Built" and the `Globals` ruling (one sentence, pointing to §67).
  - `TYPES.md`: no change expected (it describes source types). Check
    `grep -n "kernel::check\|Postulates" TYPES.md` for anything stage 2
    falsifies; report none, or fix it.

- [ ] **Step 3: Commit and push.**

```bash
git add RELATED_WORK.md README.md docs/superpowers/specs/2026-09-25-kernel-constants-and-loose-ranges-design.md
git commit -m "Docs: stage 2 of §64 built and measured (RELATED_WORK §67)

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
git push origin main
```
