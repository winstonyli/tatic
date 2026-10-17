---
status: done
---

# Kernel loose ranges (stage 1): implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Cache each kernel node's loose-variable range, so `shift`,
`instantiate` and `is_var_free` skip subterms they would leave unchanged
and keep those children by pointer. No answer changes.

**Architecture:**
- `src/kernel.rs` gets its own `Rc<T>`, a newtype over
  `std::rc::Rc<Node<T>>` where `Node { loose: u32, val: T }`. `Rc::new`
  computes `loose` from the children's cached values in O(arity) with
  `loose_of`. Every existing `Rc::new`, `Rc::ptr_eq`, `Rc::strong_count` and
  `Rc::as_ptr` in the kernel keeps compiling unchanged, because the new
  type has the same names.
- `shift` and `instantiate` return `e.clone()` when `loose_of(e)` shows
  nothing to change. They build nodes directly from child `Rc`s, keeping
  each child that has nothing to change. `is_var_free` returns `false`
  early the same way.
- Nothing outside `kernel.rs` builds `Rc<Expr>`. `proof.rs` only has two
  test helpers that name `Rc::ptr_eq`/`Rc::as_ptr` on kernel children;
  they switch to `kernel::Rc`.

**Tech Stack:** Rust (edition 2024), criterion benches, cargo tests.

**Spec:** `docs/superpowers/specs/2026-09-25-kernel-constants-and-loose-ranges-design.md`
(stage 1, and its Testing and Risks sections). Background and spike
numbers: `RELATED_WORK.md` §64.

## Global Constraints

- **Trusted kernel code.** Stage 1 changes `src/kernel.rs`. Nothing is
  executed without the user's explicit go-ahead on this plan.
- **No change to any answer.** Every existing test and fuzzer passes
  unmodified, except `infer_memo_changes_no_answer`'s copy line (Task 4)
  and the two `proof.rs` test imports (Task 2).
- **CRLF files.** Every file in this repo uses CRLF line endings. Edit with
  the Edit tool, or with Python using `newline=''` and `\r\n`. Never use
  `sed -i`. Don't run `cargo fmt`.
- **LONG_RUNS.** At most 12 build threads (`CARGO_BUILD_JOBS=12`), below-normal
  priority for long runs, and CPU under ~20% before any timing, or report
  the load. Never touch other sessions' processes (e.g. `selfplay-burn`),
  or the worktree `.claude/worktrees/goofy-sammet-171d91`.
- **TDD with mutation checks.** Each new test must fail on the mutation
  its task names. Revert the mutation after checking.
- **Commits** go to `main`, one per task. End each message with
  `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`. Push after
  Task 5.
- **Validation script.** Tasks 2–5 run `validate.sh` (below). It lives in
  the session scratchpad. If it's missing, recreate it from this text:

```bash
#!/usr/bin/env bash
# Full validation; one line per step with its exit status.
cd "C:/Users/Winston Li/Documents/GitHub/tatic"
step() { local name=$1; shift; "$@" > "$LOG.$name" 2>&1; echo "$name exit=$?"; }
export CARGO_BUILD_JOBS=12
step build cargo build --all-targets
step test cargo test --lib --bins
step clippy cargo clippy --all-targets -- -D warnings
step fuzz cargo test --release --test compile_fuzz --test kernel_fuzz --test kernel_soundness_fuzz --test syntax_fuzz --test golden_wat
step ir_fuzz cargo test --release --lib ir_fuzz -- --ignored
step run cargo run --release
echo done
```

  Run it as `LOG=<scratchpad>/val bash <scratchpad>/validate.sh` at
  below-normal priority. Every step must print `exit=0`. Otherwise read
  `$LOG.<step>` for the failure.

---

### Task 1: A `fib(16)` probe, committed before any kernel change

The stage's headline number (spec: "about 20% on `fib(16)`") needs the
same probe on both sides of the A/B. So it lands first, and Task 5's
baseline is this commit.

**Files:**
- Modify: `src/proof.rs`, test module, right after
  `a_fibonacci_instance_proof_shares_its_repeated_witnesses` (~line 9492).

**Interfaces:**
- Consumes: `prove_tail_recursive_instance`, `dag_size` (test module, ~9452),
  `kernel::check`, `kernel::id`.
- Produces: `#[ignore] fn fib16_instance_proof_cost()`, printing one line
  `fib16 dag=<n> build=<dur> check=<dur>`.

- [ ] **Step 1: Add the probe**

```rust
    /// `fib(16)`'s instance proof: its DAG size, and the time to build it
    /// and to check it again. The headline number for the §64 stages.
    /// Ignored, since it takes seconds. Run with
    /// `cargo test --release --lib fib16_instance_proof_cost -- --ignored --nocapture`.
    #[test]
    #[ignore]
    fn fib16_instance_proof_cost() {
        let mut s = TermStore::new();
        let n = s.var(0);
        let f = s.var(1);
        let two = s.lit(2);
        let cond = s.prim(PrimOp::Lt, n, two);
        let one = s.lit(1);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one);
        let n_minus_2 = s.prim(PrimOp::Sub, n, two);
        let call1 = s.app(f, n_minus_1);
        let call2 = s.app(f, n_minus_2);
        let else_branch = s.prim(PrimOp::Add, call1, call2);
        let body = s.if_(cond, n, else_branch);
        let abs = s.abs(body);
        let fib = s.rec(abs);

        let t = std::time::Instant::now();
        let proof = prove_tail_recursive_instance(&s, fib, &[16]).unwrap();
        let build = t.elapsed();
        let t = std::time::Instant::now();
        kernel::check(&proof.ctx, &proof.proof, &kernel::id(proof.int_ty.clone(), proof.lhs.clone(), proof.rhs.clone()))
            .expect("fib(16)'s instance proof re-checks");
        println!("fib16 dag={} build={build:?} check={:?}", dag_size(&proof.proof), t.elapsed());
    }
```

- [ ] **Step 2: Run it once**

Run: `cargo test --release --lib fib16_instance_proof_cost -- --ignored --nocapture`
Expected: PASS, printing a line like `fib16 dag=265xxx build=1.9s check=...`
(§64 measured about 265k nodes and 1.9 s). Record the line in the ledger.

- [ ] **Step 3: Commit**

```bash
git add src/proof.rs
git commit -m "Test: an ignored fib(16) instance-proof probe (DAG size, build and check time)" -m "Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

Record this commit's hash as `BASE` in the ledger. Task 5 benches against it.

---

### Task 2: The kernel `Rc` with a cached `loose`, and `loose_of`

**Files:**
- Modify: `src/kernel.rs:39`. Replace `use std::rc::Rc;` with the new
  block below, just before `// --- stack growth`.
- Modify: `src/kernel.rs`, test module (`mod tests`, ~line 1698). Add the
  helpers and the test.
- Modify: `src/proof.rs:7609` (`Rc::ptr_eq`) and `src/proof.rs:9456`
  (`Rc::as_ptr`), both in `mod tests`.

**Interfaces:**
- Produces:
  - `pub struct Rc<T>`, with `Rc::<Expr>::new(Expr) -> Rc<Expr>` and
    `.loose() -> u32`, plus `Rc::ptr_eq(&Rc<T>, &Rc<T>) -> bool`,
    `Rc::strong_count(&Rc<T>) -> usize`, `Rc::as_ptr(&Rc<T>) -> *const T`,
    and `Clone`, `Deref<Target = T>`, `AsRef<T>`, `PartialEq`/`Eq` (for
    `T: Eq`) and `Debug`.
  - `pub fn loose_of(e: &Expr) -> u32`.
  - Test helpers:
    - `fn splitmix(seed: u64) -> impl FnMut() -> usize`;
    - `fn random_term(next: &mut impl FnMut() -> usize) -> Expr`;
    - `fn is_var_free_ref(e: &Expr, idx: u32) -> bool`, a verbatim copy of
      today's `is_var_free`.
- Consumes: nothing new.

- [ ] **Step 1: Write the failing test and its helpers**

Add to `mod tests` in `src/kernel.rs`, after the `subst` helper:

```rust
    /// A splitmix64 stream, for the randomised tests below.
    fn splitmix(mut seed: u64) -> impl FnMut() -> usize {
        move || {
            seed = seed.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = seed;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            (z ^ (z >> 31)) as usize
        }
    }

    /// A random term with every `Expr` shape, built from a pool of nodes so
    /// children are shared. Its leaves are `Var(0..4)` and `Sort(0)`, so it
    /// has both open and closed subterms at every binder depth.
    fn random_term(next: &mut impl FnMut() -> usize) -> Expr {
        let mut pool: Vec<Rc<Expr>> = (0..4).map(|k| Rc::new(var(k))).chain([Rc::new(sort(0))]).collect();
        for _ in 0..12 {
            let kind = next() % 14;
            let mut c = || pool[next() % pool.len()].clone();
            let node = match kind {
                0 => Expr::Pi(c(), c()),
                1 => Expr::Lam(c(), c()),
                2 | 3 => Expr::App(c(), c()),
                4 => Expr::Id(c(), c(), c()),
                5 => Expr::Refl(c()),
                6 => Expr::J { motive: c(), base: c(), a: c(), b: c(), p: c() },
                7 => Expr::W(c(), c()),
                8 => Expr::Sup(c(), c()),
                9 => Expr::WRec { motive: c(), children_ty: c(), step: c(), target: c() },
                10 => Expr::Sigma(c(), c()),
                11 => Expr::Pair(c(), c(), c()),
                12 => Expr::SigRec { motive: c(), step: c(), target: c() },
                _ => Expr::Sort(1),
            };
            pool.push(Rc::new(node));
        }
        (**pool.last().unwrap()).clone()
    }

    /// Today's `is_var_free`, kept as the reference for the new one and for
    /// `loose_of`. It walks the whole term and reads no cached range.
    fn is_var_free_ref(e: &Expr, idx: u32) -> bool {
        let f = is_var_free_ref;
        grow(|| match e {
            Expr::Var(k) => *k == idx,
            Expr::Sort(_) => false,
            Expr::Pi(a, b) | Expr::Lam(a, b) | Expr::W(a, b) | Expr::Sigma(a, b) => f(a, idx) || f(b, idx + 1),
            Expr::App(a, b) | Expr::Sup(a, b) => f(a, idx) || f(b, idx),
            Expr::Id(a, x, y) => f(a, idx) || f(x, idx) || f(y, idx),
            Expr::Refl(a) => f(a, idx),
            Expr::J { motive, base, a, b, p } => f(motive, idx) || f(base, idx) || f(a, idx) || f(b, idx) || f(p, idx),
            Expr::WRec { motive, children_ty, step, target } => {
                f(motive, idx) || f(children_ty, idx + 1) || f(step, idx) || f(target, idx)
            }
            Expr::Pair(fam, a, b) => f(fam, idx + 1) || f(a, idx) || f(b, idx),
            Expr::SigRec { motive, step, target } => f(motive, idx) || f(step, idx) || f(target, idx),
        })
    }

    /// A term's cached range is one more than its largest free variable,
    /// as a walk of the whole term finds it (0 when closed). The
    /// pool's variables are below 4 and binders only lower them, so
    /// checking indices below 8 covers every one that can occur.
    #[test]
    fn loose_matches_a_walk() {
        let mut next = splitmix(11);
        for _ in 0..20_000 {
            let e = random_term(&mut next);
            let walk = (0..8u32).rev().find(|&i| is_var_free_ref(&e, i)).map_or(0, |i| i + 1);
            assert_eq!(Rc::new(e.clone()).loose(), walk, "{e:?}");
        }
    }
```

- [ ] **Step 2: Run it and see it fail**

Run: `cargo test --lib kernel::tests::loose_matches_a_walk`
Expected: compile error, `no method named loose found for struct std::rc::Rc<Expr>`.

- [ ] **Step 3: Add the kernel `Rc` and `loose_of`**

In `src/kernel.rs`, replace line 39 (`use std::rc::Rc;`) with:

```rust

// --- shared nodes ----------------------------------------------------------
//
// Every child of an `Expr` is a kernel `Rc`: `std::rc::Rc` with the
// child's loose-variable range cached beside it, computed once when the
// node is built. `shift`, `instantiate` and `is_var_free` read it to skip
// the subterms they would leave unchanged, and keep those by pointer
// (`RELATED_WORK.md` §64).

/// A shared node, and its [`loose_of`] computed when it was built.
pub struct Rc<T>(std::rc::Rc<Node<T>>);

struct Node<T> {
    loose: u32,
    val: T,
}

impl Rc<Expr> {
    pub fn new(e: Expr) -> Self {
        Rc(std::rc::Rc::new(Node { loose: loose_of(&e), val: e }))
    }

    /// One more than the largest loose `Var` index in this node, 0 when
    /// it's closed.
    pub fn loose(&self) -> u32 {
        self.0.loose
    }
}

impl<T> Rc<T> {
    pub fn ptr_eq(a: &Self, b: &Self) -> bool {
        std::rc::Rc::ptr_eq(&a.0, &b.0)
    }
    pub fn strong_count(a: &Self) -> usize {
        std::rc::Rc::strong_count(&a.0)
    }
    pub fn as_ptr(a: &Self) -> *const T {
        &a.0.val
    }
}

impl<T> Clone for Rc<T> {
    fn clone(&self) -> Self {
        Rc(self.0.clone())
    }
}
impl<T> std::ops::Deref for Rc<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.0.val
    }
}
impl<T> AsRef<T> for Rc<T> {
    fn as_ref(&self) -> &T {
        &self.0.val
    }
}
/// As `std::rc::Rc`'s for an `Eq` type: the same node is equal without a
/// walk.
impl<T: Eq> PartialEq for Rc<T> {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(self, other) || self.0.val == other.0.val
    }
}
impl<T: Eq> Eq for Rc<T> {}
impl<T: fmt::Debug> fmt::Debug for Rc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.val.fmt(f)
    }
}

/// One more than the largest loose `Var` index in `e`, 0 when it's
/// closed, from its children's cached ranges. A child one binder deeper
/// (the second field of `Pi`/`Lam`/`W`/`Sigma`, `WRec`'s `children_ty`,
/// `Pair`'s `fam`) has one loose variable fewer out here. Saturating, so a
/// `Var(u32::MAX)` doesn't wrap to "closed".
pub fn loose_of(e: &Expr) -> u32 {
    let l = |c: &Rc<Expr>| c.loose();
    let u = |c: &Rc<Expr>| c.loose().saturating_sub(1);
    match e {
        Expr::Var(k) => k.saturating_add(1),
        Expr::Sort(_) => 0,
        Expr::Pi(a, b) | Expr::Lam(a, b) | Expr::W(a, b) | Expr::Sigma(a, b) => l(a).max(u(b)),
        Expr::App(a, b) | Expr::Sup(a, b) => l(a).max(l(b)),
        Expr::Id(a, b, c) | Expr::SigRec { motive: a, step: b, target: c } => l(a).max(l(b)).max(l(c)),
        Expr::Pair(fam, a, b) => u(fam).max(l(a)).max(l(b)),
        Expr::Refl(a) => l(a),
        Expr::J { motive, base, a, b, p } => l(motive).max(l(base)).max(l(a)).max(l(b)).max(l(p)),
        Expr::WRec { motive, children_ty, step, target } => l(motive).max(u(children_ty)).max(l(step)).max(l(target)),
    }
}
```

In `src/proof.rs`'s `mod tests`, `Rc` is `std::rc::Rc`, which it needs for
`ConcreteClo` and `eval::Env`. Only the two kernel-node sites change:
- line ~7609: `assert!(Rc::ptr_eq(f1, f2), ...)` becomes `assert!(kernel::Rc::ptr_eq(f1, f2), ...)`.
- line ~9456: `if seen.insert(Rc::as_ptr(p)) {` becomes `if seen.insert(kernel::Rc::as_ptr(p)) {`.

- [ ] **Step 4: Run the test and the whole kernel suite**

Run: `cargo test --lib kernel::tests::loose_matches_a_walk`
Expected: PASS.

Run: `cargo test --lib`
Expected: PASS, including `check_survives_a_term_far_deeper_than_the_native_stack_allows`
and `dropping_a_deep_term_does_not_overflow_the_stack`. The second drops a
100,000-deep `refl` chain on a 1 MB thread through the new `Rc`, so it
guards `Drop for Expr`'s `Rc::strong_count` reaching the inner count (spec,
Risks). (Corrected after Task 2: the first's 1,000-deep terms don't guard it.)

- [ ] **Step 5: Mutation checks** (revert each after it fails)

1. In `loose_of`, change the `Pi | Lam | W | Sigma` arm to `l(a).max(l(b))`.
   `loose_matches_a_walk` must FAIL.
2. In `loose_of`, change the `Pair` arm's `u(fam)` to `l(fam)`. It must FAIL.
3. In `loose_of`, change the `WRec` arm's `u(children_ty)` to `l(children_ty)`. It must FAIL.
4. In the wrapper's `strong_count`, return `std::rc::Rc::strong_count(&a.0) + 1`.
   `Drop for Expr` then never frees a child on a fresh segment.
   `dropping_a_deep_term_does_not_overflow_the_stack` must FAIL (a stack
   overflow aborts the test process). That shows it guards deep drops
   through the wrapper (spec, Risks). (Corrected after Task 2: this plan
   first named `check_survives_a_term_far_deeper_than_the_native_stack_allows`,
   which passes under this mutation, so the dedicated test was added in
   `d2e91b7`.)

Record each result (fails/passes) in the ledger.

- [ ] **Step 6: Validate and commit**

Run `validate.sh` (Global Constraints). Every step must print `exit=0`.

```bash
git add src/kernel.rs src/proof.rs
git commit -m "Kernel: nodes cache their loose-variable range (stage 1 of RELATED_WORK §64)" -m "Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

---

### Task 3: Fast paths in `shift`, `instantiate` and `is_var_free`

**Files:**
- Modify: `src/kernel.rs`: `shift` (~line 434 before Task 2; find it with
  `grep -n "pub fn shift(" src/kernel.rs`), `shift_sigma_family`,
  `instantiate` and `is_var_free`.
- Modify: `src/kernel.rs` `mod tests`: add `shift_ref`, `instantiate_ref`
  and two tests.

**Interfaces:**
- Consumes: `Rc::loose`, `loose_of`, `splitmix`, `random_term` and
  `is_var_free_ref` from Task 2.
- Produces:
  - test helpers `fn shift_ref(e: &Expr, cutoff: u32, amount: i32) -> Expr`
    and `fn instantiate_ref(e: &Expr, s: &Expr, d: u32) -> Expr`, verbatim
    copies of today's `shift` and `instantiate` that rebuild every node.
    Task 4 uses `shift_ref`.
  - no signature changes to `shift`, `instantiate` or `is_var_free`.

- [ ] **Step 1: Copy today's `shift` and `instantiate` into `mod tests` as references**

Add after `is_var_free_ref`:

```rust
    /// Today's `shift`, kept as the reference for the new one. It rebuilds
    /// every node, so it's also a deep copy that shares nothing.
    fn shift_ref(e: &Expr, cutoff: u32, amount: i32) -> Expr {
        let go = |x: &Rc<Expr>, c: u32| shift_ref(x, c, amount);
        grow(|| match e {
            Expr::Var(k) => {
                if *k >= cutoff {
                    Expr::Var((*k as i32 + amount) as u32)
                } else {
                    Expr::Var(*k)
                }
            }
            Expr::Sort(i) => Expr::Sort(*i),
            Expr::Pi(a, b) => pi(go(a, cutoff), go(b, cutoff + 1)),
            Expr::Lam(a, b) => lam(go(a, cutoff), go(b, cutoff + 1)),
            Expr::App(f, a) => app(go(f, cutoff), go(a, cutoff)),
            Expr::Id(a, x, y) => id(go(a, cutoff), go(x, cutoff), go(y, cutoff)),
            Expr::Refl(a) => refl(go(a, cutoff)),
            Expr::J { motive, base, a, b, p } => {
                jelim(go(motive, cutoff), go(base, cutoff), go(a, cutoff), go(b, cutoff), go(p, cutoff))
            }
            Expr::W(a, b) => wty(go(a, cutoff), go(b, cutoff + 1)),
            Expr::Sup(a, f) => sup(go(a, cutoff), go(f, cutoff)),
            Expr::WRec { motive, children_ty, step, target } => {
                wrec(go(motive, cutoff), go(children_ty, cutoff + 1), go(step, cutoff), go(target, cutoff))
            }
            Expr::Sigma(a, b) => sigma(go(a, cutoff), go(b, cutoff + 1)),
            Expr::Pair(fam, a, b) => pair(go(fam, cutoff + 1), go(a, cutoff), go(b, cutoff)),
            Expr::SigRec { motive, step, target } => sigrec(go(motive, cutoff), go(step, cutoff), go(target, cutoff)),
        })
    }

    /// Today's `instantiate`, kept as the reference for the new one.
    fn instantiate_ref(e: &Expr, s: &Expr, d: u32) -> Expr {
        let go = |x: &Rc<Expr>, d: u32| instantiate_ref(x, s, d);
        grow(|| match e {
            Expr::Var(k) => {
                if *k == d {
                    shift_ref(s, 0, d as i32)
                } else if *k > d {
                    Expr::Var(*k - 1)
                } else {
                    Expr::Var(*k)
                }
            }
            Expr::Sort(i) => Expr::Sort(*i),
            Expr::Pi(a, b) => pi(go(a, d), go(b, d + 1)),
            Expr::Lam(a, b) => lam(go(a, d), go(b, d + 1)),
            Expr::App(f, a) => app(go(f, d), go(a, d)),
            Expr::Id(a, x, y) => id(go(a, d), go(x, d), go(y, d)),
            Expr::Refl(a) => refl(go(a, d)),
            Expr::J { motive, base, a, b, p } => jelim(go(motive, d), go(base, d), go(a, d), go(b, d), go(p, d)),
            Expr::W(a, b) => wty(go(a, d), go(b, d + 1)),
            Expr::Sup(a, f) => sup(go(a, d), go(f, d)),
            Expr::WRec { motive, children_ty, step, target } => wrec(go(motive, d), go(children_ty, d + 1), go(step, d), go(target, d)),
            Expr::Sigma(a, b) => sigma(go(a, d), go(b, d + 1)),
            Expr::Pair(fam, a, b) => pair(go(fam, d + 1), go(a, d), go(b, d)),
            Expr::SigRec { motive, step, target } => sigrec(go(motive, d), go(step, d), go(target, d)),
        })
    }
```

Note: today's `shift` has `if amount == 0 { return e.clone(); }` first.
`shift_ref` leaves it out, so that it always rebuilds (Task 4 relies on
this). Both give the same result for amount 0.

- [ ] **Step 2: Write the two tests**

```rust
    /// The new `shift`, `instantiate` and `is_var_free` agree with today's
    /// on random terms, at several cutoffs and depths, and a shift up and
    /// back down is the identity.
    #[test]
    fn shift_and_instantiate_match_a_reference() {
        let mut next = splitmix(23);
        for _ in 0..20_000 {
            let e = random_term(&mut next);
            let s = random_term(&mut next);
            for c in 0..4 {
                for n in [1, 2] {
                    assert_eq!(shift(&e, c, n), shift_ref(&e, c, n), "shift({e:?}, {c}, {n})");
                }
                assert_eq!(shift(&shift(&e, c, 1), c, -1), e, "shift back ({e:?}, {c})");
                assert_eq!(instantiate(&e, &s, c), instantiate_ref(&e, &s, c), "instantiate({e:?}, {s:?}, {c})");
            }
            for i in 0..6 {
                assert_eq!(is_var_free(&e, i), is_var_free_ref(&e, i), "is_var_free({e:?}, {i})");
            }
        }
    }

    /// A child with nothing to change comes back as the same `Rc`, not a
    /// copy: a closed one always, and an open one when its variables are
    /// all below the cutoff or depth.
    #[test]
    fn shift_keeps_closed_children_by_pointer() {
        let closed = Rc::new(pi(sort(0), var(0)));
        let e = Expr::App(closed.clone(), Rc::new(var(0)));
        let Expr::App(f, a) = shift(&e, 0, 1) else { panic!() };
        assert!(Rc::ptr_eq(&f, &closed), "shift copied a closed child");
        assert_eq!(*a, var(1));
        let Expr::App(f, a) = instantiate(&e, &sort(1), 0) else { panic!() };
        assert!(Rc::ptr_eq(&f, &closed), "instantiate copied a closed child");
        assert_eq!(*a, sort(1));

        // Under cutoff 1, `Var(0)` is bound, so its child keeps its pointer
        // and only `Var(2)` moves.
        let low = Rc::new(var(0));
        let e = Expr::App(low.clone(), Rc::new(var(2)));
        let Expr::App(f, a) = shift(&e, 1, 1) else { panic!() };
        assert!(Rc::ptr_eq(&f, &low), "shift copied a child below the cutoff");
        assert_eq!(*a, var(3));
        let Expr::App(f, a) = instantiate(&e, &sort(1), 1) else { panic!() };
        assert!(Rc::ptr_eq(&f, &low), "instantiate copied a child below the depth");
        assert_eq!(*a, var(1));

        // A whole term with nothing to change keeps every child.
        let e = Expr::Pi(closed.clone(), Rc::new(var(0)));
        let Expr::Pi(dom, _) = shift(&e, 0, 5) else { panic!() };
        assert!(Rc::ptr_eq(&dom, &closed));
    }
```

- [ ] **Step 3: Run them and see which fail**

Run: `cargo test --lib kernel::tests::shift_`
Expected:
- `shift_keeps_closed_children_by_pointer` FAILS with "shift copied a
  closed child", since today's `shift` rebuilds every node.
- `shift_and_instantiate_match_a_reference` PASSES, since the code is
  still the same. It's a regression guard, and Step 6's mutations give it
  its teeth.

- [ ] **Step 4: Rewrite `shift`, `shift_sigma_family`, `instantiate` and `is_var_free`**

Replace `shift` and `shift_sigma_family` with the code below. It keeps
`shift_sigma_family` and ignores the spec's "goes". Its own doc (at
`infer_sigma`) says these extractions stay because "smaller hot frames
cost nothing, not because anything depends on them", and that still holds.
Task 5 records this in the spec.

```rust
pub fn shift(e: &Expr, cutoff: u32, amount: i32) -> Expr {
    // Adding 0 changes no index, and a term whose loose variables all sit
    // below `cutoff` has none to change: either way `e` comes back as is.
    if amount == 0 || loose_of(e) <= cutoff {
        return e.clone();
    }
    let go = |x: &Rc<Expr>, c: u32| shift_child(x, c, amount);
    grow(|| match e {
        Expr::Var(k) => {
            if *k >= cutoff {
                Expr::Var((*k as i32 + amount) as u32)
            } else {
                Expr::Var(*k)
            }
        }
        Expr::Sort(i) => Expr::Sort(*i),
        Expr::Pi(a, b) => Expr::Pi(go(a, cutoff), go(b, cutoff + 1)),
        Expr::Lam(a, b) => Expr::Lam(go(a, cutoff), go(b, cutoff + 1)),
        Expr::App(f, a) => Expr::App(go(f, cutoff), go(a, cutoff)),
        Expr::Id(a, x, y) => Expr::Id(go(a, cutoff), go(x, cutoff), go(y, cutoff)),
        Expr::Refl(a) => Expr::Refl(go(a, cutoff)),
        Expr::J { motive, base, a, b, p } => Expr::J {
            motive: go(motive, cutoff),
            base: go(base, cutoff),
            a: go(a, cutoff),
            b: go(b, cutoff),
            p: go(p, cutoff),
        },
        Expr::W(a, b) => Expr::W(go(a, cutoff), go(b, cutoff + 1)),
        Expr::Sup(a, f) => Expr::Sup(go(a, cutoff), go(f, cutoff)),
        Expr::WRec { motive, children_ty, step, target } => Expr::WRec {
            motive: go(motive, cutoff),
            children_ty: go(children_ty, cutoff + 1),
            step: go(step, cutoff),
            target: go(target, cutoff),
        },
        Expr::Sigma(..) | Expr::Pair(..) | Expr::SigRec { .. } => shift_sigma_family(e, cutoff, amount),
    })
}

/// `shift` of one child: the same `Rc` when it has nothing to shift.
fn shift_child(x: &Rc<Expr>, cutoff: u32, amount: i32) -> Rc<Expr> {
    if x.loose() <= cutoff { x.clone() } else { Rc::new(shift(x, cutoff, amount)) }
}

/// `shift`'s own `Sigma`/`Pair`/`SigRec` cases, out of line -- see
/// `infer_sigma`'s docs for why these extractions exist and why they
/// are kept.
#[inline(never)]
fn shift_sigma_family(e: &Expr, cutoff: u32, amount: i32) -> Expr {
    let go = |x: &Rc<Expr>, c: u32| shift_child(x, c, amount);
    match e {
        Expr::Sigma(a, b) => Expr::Sigma(go(a, cutoff), go(b, cutoff + 1)),
        Expr::Pair(fam, a, b) => Expr::Pair(go(fam, cutoff + 1), go(a, cutoff), go(b, cutoff)),
        Expr::SigRec { motive, step, target } => Expr::SigRec {
            motive: go(motive, cutoff),
            step: go(step, cutoff),
            target: go(target, cutoff),
        },
        _ => unreachable!("shift_sigma_family called on a non-Sigma-family Expr"),
    }
}
```

Keep the doc comment above `pub fn shift` as it is.

Replace `instantiate`'s body (keep its doc comment), adding one sentence
to the end of that doc: `A subterm with no loose variable at or above its depth is kept by pointer.`

```rust
fn instantiate(e: &Expr, s: &Expr, d: u32) -> Expr {
    if loose_of(e) <= d {
        return e.clone();
    }
    let go = |x: &Rc<Expr>, d: u32| if x.loose() <= d { x.clone() } else { Rc::new(instantiate(x, s, d)) };
    grow(|| match e {
        Expr::Var(k) => {
            if *k == d {
                shift(s, 0, d as i32)
            } else if *k > d {
                Expr::Var(*k - 1)
            } else {
                Expr::Var(*k)
            }
        }
        Expr::Sort(i) => Expr::Sort(*i),
        Expr::Pi(a, b) => Expr::Pi(go(a, d), go(b, d + 1)),
        Expr::Lam(a, b) => Expr::Lam(go(a, d), go(b, d + 1)),
        Expr::App(f, a) => Expr::App(go(f, d), go(a, d)),
        Expr::Id(a, x, y) => Expr::Id(go(a, d), go(x, d), go(y, d)),
        Expr::Refl(a) => Expr::Refl(go(a, d)),
        Expr::J { motive, base, a, b, p } => Expr::J { motive: go(motive, d), base: go(base, d), a: go(a, d), b: go(b, d), p: go(p, d) },
        Expr::W(a, b) => Expr::W(go(a, d), go(b, d + 1)),
        Expr::Sup(a, f) => Expr::Sup(go(a, d), go(f, d)),
        Expr::WRec { motive, children_ty, step, target } => Expr::WRec {
            motive: go(motive, d),
            children_ty: go(children_ty, d + 1),
            step: go(step, d),
            target: go(target, d),
        },
        Expr::Sigma(a, b) => Expr::Sigma(go(a, d), go(b, d + 1)),
        Expr::Pair(fam, a, b) => Expr::Pair(go(fam, d + 1), go(a, d), go(b, d)),
        Expr::SigRec { motive, step, target } => Expr::SigRec { motive: go(motive, d), step: go(step, d), target: go(target, d) },
    })
}
```

In `is_var_free`, add one line before `grow(|| match e {`:

```rust
    if loose_of(e) <= idx {
        return false;
    }
```

Also add a sentence to its doc comment: `A subterm whose cached range shows no variable at or above idx isn't walked.`

- [ ] **Step 5: Run the tests and the whole suite**

Run: `cargo test --lib kernel::tests::shift_`
Expected: both PASS.

Run: `cargo test --lib`
Expected: PASS. That includes `subst_top_*`,
`is_var_free_tracks_binder_depth_and_is_checked_against_normal_form_not_raw_syntax`,
`infer_memo_changes_no_answer` and the deep-stack test.

- [ ] **Step 6: Mutation checks** (revert each after it fails)

1. `shift_child`: `x.loose() <= cutoff` → `x.loose() <= cutoff + 1`.
   `shift_and_instantiate_match_a_reference` must FAIL.
2. `shift`'s top check: `loose_of(e) <= cutoff` → `loose_of(e) <= cutoff + 1`.
   It must FAIL.
3. `instantiate`'s `go`: `x.loose() <= d` → `x.loose() <= d + 1`. It must FAIL.
4. `is_var_free`: `loose_of(e) <= idx` → `loose_of(e) <= idx + 1`. It must FAIL.
5. `shift_child`: replace its body with `Rc::new(shift(x, cutoff, amount))`
   (always copy). `shift_keeps_closed_children_by_pointer` must FAIL.
6. `shift_sigma_family`'s `Pair` arm: `go(fam, cutoff + 1)` → `go(fam, cutoff)`.
   `shift_and_instantiate_match_a_reference` must FAIL.

Record each result in the ledger.

- [ ] **Step 7: Validate and commit**

Run `validate.sh`. Every step must print `exit=0`.

```bash
git add src/kernel.rs
git commit -m "Kernel: shift, instantiate and is_var_free skip subterms with nothing to change, keeping them by pointer" -m "Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

---

### Task 4: `infer_memo_changes_no_answer` gets a real deep copy

After Task 3, the test's `shift(&shift(&e, 0, 1), 0, -1)` keeps closed
subterms shared, such as the pool's `Sort(0)`. So its "unshared" copy is
partly shared, and the memo can engage on both sides. The test would still
pass, having silently lost its teeth (spec, Testing).

**Files:**
- Modify: `src/kernel.rs` `mod tests`, `infer_memo_changes_no_answer`
  (find it with `grep -n "fn infer_memo_changes_no_answer" src/kernel.rs`).

**Interfaces:**
- Consumes: `shift_ref` (Task 3) and `splitmix` (Task 2).
- Produces: `fn shares_nothing(e: &Expr) -> bool` (test helper).

- [ ] **Step 1: Add the assertion that exposes it**

Add the helper above the test:

```rust
    /// No node in `e` is reachable twice or held elsewhere: every child's
    /// count is 1, so `infer`'s memo, which only engages on shared nodes,
    /// never does.
    fn shares_nothing(e: &Expr) -> bool {
        let mut ok = true;
        same_shape(e, e, |c, _| {
            ok = ok && Rc::strong_count(c) == 1 && shares_nothing(c);
            true
        });
        ok
    }
```

In the test, directly after `let unshared = shift(&shift(&e, 0, 1), 0, -1);`, add:

```rust
            assert!(shares_nothing(&unshared), "the copy shares a node: {e:?}");
```

- [ ] **Step 2: Run it and see it fail**

Run: `cargo test --lib kernel::tests::infer_memo_changes_no_answer`
Expected: FAIL with "the copy shares a node".

- [ ] **Step 3: Use the rebuilding reference as the copy, and the shared RNG**

Replace the line with:

```rust
            let unshared = shift_ref(&shift_ref(&e, 0, 1), 0, -1);
```

Replace the test's inline RNG:

```rust
        let mut seed = 7u64;
        let mut next = move || {
            seed = seed.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = seed;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            (z ^ (z >> 31)) as usize
        };
```

with `let mut next = splitmix(7);`. It's the same stream, so the same terms.

Update the test's doc comment: "...give the same `infer` result as a
copy with no sharing (a full rebuild by `shift_ref`, since `shift` now
keeps closed subterms), which the memo never engages on
(`RELATED_WORK.md` §63)."

- [ ] **Step 4: Run it**

Run: `cargo test --lib kernel::tests::infer_memo_changes_no_answer`
Expected: PASS, with `typed > 1000` still true.

- [ ] **Step 5: Mutation check**

Apply §63's length-keyed mutation. In `infer_rc`, change
`let key = (PtrKey(e.clone()), cid);` to
`let key = (PtrKey(e.clone()), ctx.len() as u32);`.
`infer_memo_changes_no_answer` must FAIL, as it did before Task 3 (§63).
Revert, and record the result in the ledger. Step 2 already showed that
`shares_nothing` fails on the old copy.

- [ ] **Step 6: Commit**

```bash
git add src/kernel.rs
git commit -m "Test: infer_memo_changes_no_answer copies with a full rebuild, now that shift keeps closed subterms" -m "Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

---

### Task 5: Measure, validate, document, push

**Files:**
- Modify: `RELATED_WORK.md`: a new `## 65. Nodes cache their loose-variable range`
  section, inserted before `## Sources`.
- Modify: `README.md` (~line 1097, the passage ending "...its DAG from
  265k nodes to 10.5k (§64)."): one sentence on stage 1.
- Modify: `docs/superpowers/specs/2026-09-25-kernel-constants-and-loose-ranges-design.md`:
  the `shift_sigma_family` bullet under Stage 1.
- TYPES.md: no change (grep finds no `Rc`, `shift` or `instantiate` in it).
  Recheck with `grep -n "Rc\b\|shift\|instantiate" TYPES.md`.

**Interfaces:**
- Consumes: the `BASE` commit from Task 1, and `scripts/bench_ab.sh`.

- [ ] **Step 1: Check the machine**

Check for orphans: `Get-Process cargo, rustc, tatic* -EA 0`. Then check the
CPU, which must be under ~20%:
`(Get-Counter '\Processor(_Total)\% Processor Time' -SampleInterval 2 -MaxSamples 2).CounterSamples[-1].CookedValue`.
If another session's job is running, don't touch it. Wait, or record the
load next to each result.

- [ ] **Step 2: Three A/B rounds of the proof benches against BASE**

`bench_ab.sh` runs base, candidate and base again (noise) each time, and
overwrites its logs. So copy the logs after each round:

```bash
for r in 1 2 3; do scripts/bench_ab.sh <BASE> --bench proofs > <scratchpad>/s1-ab.$r.txt 2>&1; cp target/bench-ab/{base,candidate,noise}.log <scratchpad>/ 2>/dev/null; for f in base candidate noise; do mv <scratchpad>/$f.log <scratchpad>/s1-$f.$r.log; done; done
```

Run it in the background, since it takes a while. Per bench, take the
best of the 3 rounds for base and for candidate. A change is real only
where it clearly exceeds the base-again noise column.

- [ ] **Step 3: Three interleaved `fib(16)` probe runs on each side**

The base worktree is `target/bench-ab/base` (at BASE after Step 2), with
target dir `target/bench-ab/target`:

```bash
for r in 1 2 3; do (cd target/bench-ab/base && CARGO_TARGET_DIR="$PWD/../target" cargo test --release --lib fib16_instance_proof_cost -- --ignored --nocapture 2>&1 | grep fib16); cargo test --release --lib fib16_instance_proof_cost -- --ignored --nocapture 2>&1 | grep fib16; done
```

Expected: the DAG size is unchanged (stage 1 changes no term the builder
makes, only what the kernel's own traversals copy). The spec expects
`check` to be about 20% faster on `fib(16)`. Report what's measured, not
the expectation. If there's no gain, say so.
(Measured: the DAG shrank 265,366 -> 227,157, since the builder shifts
through the kernel, which now keeps closed subterms by pointer; build and
check were each 11% faster. See `RELATED_WORK.md` §65.)

- [ ] **Step 4: Full validation**

Run `validate.sh`. Every step must print `exit=0`.

- [ ] **Step 5: Documents**

Write `RELATED_WORK.md` §65 from the measured numbers:
- what changed: the kernel `Rc`; `loose_of`; the three fast paths; and
  children kept by pointer;
- node size, 64 → 72 bytes on the heap;
- the best-of-3 table from Step 2, with the noise column;
- the `fib(16)` numbers from Step 3;
- that `shift_sigma_family` stayed, and why;
- the tests, and the mutations each one caught.

Then, in the README passage, change "What's left is designed but not built: ..." to say
stage 1 (cached loose ranges) is built, with the measured `fib(16)`
change (§65), and that the rest of §64 is designed but not built.

In the spec's Stage 1, replace the bullet "`shift_sigma_family` goes: its reason ... one line each." with:
"`shift_sigma_family` stays. Rechecked in stage 1: its reason (at
`infer_sigma`) is only that smaller hot frames cost nothing, and that still
holds."

All three files are CRLF. Edit them with the Edit tool, or with Python
(`newline=''`).

- [ ] **Step 6: Commit and push**

```bash
git add RELATED_WORK.md README.md docs/superpowers/specs/2026-09-25-kernel-constants-and-loose-ranges-design.md docs/superpowers/plans/2026-09-25-kernel-loose-ranges-stage1.md
git commit -m "Docs: stage 1 of §64 measured (RELATED_WORK §65)" -m "Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
git push origin main
```
