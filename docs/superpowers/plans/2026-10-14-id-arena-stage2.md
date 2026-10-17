---
status: done
---

# Id arena Stage 2: `PExpr`, `persist`, `scoped` and `Escape` on today's nodes (plan)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task (the
> tasks depend on each other, so not subagent-driven; Task 4's site conversion may go to one Sonnet implementer). Steps
> use checkbox (`- [ ]`) syntax for tracking.

**Status:** done 2026-10-14 on branch `id-arena-stage2` (343a34f-108a704 plus the docs commit); results in doc "Id arena Stage 2".

**Goal:** Fix the types the id arena will need, with today's `Rc` representation underneath: a `PExpr` for terms that
outlive a scope, `persist` (the only way to make one), and `kernel::scoped` with an `Escape` trait. `scoped` replaces
`InternScope` at its 79 sites. Behaviour and timings are unchanged. Behind a feature, it also measures what the arena's
copy-out would cost, which is the largest risk the port still has unmeasured.

**Why now (decided 2026-10-14):** the narrower real prototype the spec put after Stage 1 cannot discriminate. Its
`Rc` boundary builds every new node twice. That cancels Stage 1's intern and node-build gains, and leaves about zero net
(spec, Stage 1 "Continue"). So the port decision rests on Stage 1's replay (20% at n=64, 33% at n=8, the rise unchanged)
plus the copy-out volume this stage measures. **After Task 5, stop for the Stage 3 decision.**

**Architecture:**
- `PExpr` is a newtype over `Expr`. `persist` clones nothing (it takes `Expr` by value) and, with feature
  `copy-volume`, counts.
- `scoped(f)` is today's `InternScope` (the table switched on at once) as a closure. The call that opens the scope passes
  `f`'s result through `Escape` before closing it. The kernel's own entries (`def_eq`, `infer_in`, `check_in`) open
  their scope the same way, without switching the table on (today's lazy `hc::Scope`), through the one function
  `hc::scoped(activate, f)`.
- Long-lived stores hold `PExpr`: `Globals`, `Postulates`'s parameters (so `PARAMS` and `proof.rs`'s `PRELUDE`, which
  hold a `Postulates`), `CLOSED`, `TREE_LAWS` and `PARAMS`' lemma proofs.
- `CONSTANTS` and `BODIES` (`encoding.rs` `gen_memo`) stay `Expr`. They are rebuilt per generation, and in the arena per
  region (spec, "Generation memos"). `TREE_ENCS`, `RewriteMemo` and `lemma_cache` hold no terms.

**Tech stack:** Rust (nightly, edition 2024), hashbrown, im. No new dependencies.

**Spec:** `docs/superpowers/specs/2026-10-14-id-arena-spec.md` (local, git-excluded), Stage 2, "The two id types",
"Scopes: `scoped` and `Escape`". Where this plan departs from it, it says so (see "Departures").

## Global Constraints

- **Behaviour unchanged:** every test that passes on the base, 4769775, passes. A salt-1 and salt-2 sweep's outputs
  are identical to the base's, apart from timings and their own paths.
- **Timings within noise:** `proof_cost_split` CPU, alternating pairs against the base, with `copy-volume` off.
- **The default build gains no work worth measuring:** without the feature, `persist` and a term's `escape` are moves.
  A `Vec`'s escape is one in-place map pass, made only by an outermost `scoped`. Every
  `copy-volume` field and call is under `#[cfg(feature = "copy-volume")]`, like `record-defeq`'s `canon`.
- **One mechanism:** no `InternScope` and no new scope guard type remain. The only guard is the private `hc::Scope`
  that `hc::scoped` uses (it keeps the close panic-safe), plus the six unit tests that use it directly today.
- **Stage 3 keeps the signatures:** public functions that take or return terms keep their signatures, except
  `Globals`' element type. `PExpr` exposes only what the arena can give: `get(&self) -> Expr` (a clone today, a copy
  in the port), `From<PExpr> for Expr`, `Clone`, `PartialEq`, `Eq` and `Debug`, and no `Deref` (the port cannot lend
  `&Expr` out of an id). No `Hash`: nothing keys a map by a term today (spec, "The two id types").
- **Work in a worktree:** `git worktree add ../tatic-s2 -b id-arena-stage2 4769775` (main's head when planned), with
  `CARGO_TARGET_DIR=target/s2` (separate target dirs; two checkouts sharing one rebuild unreliably). Worktree files
  are CRLF: change them with the Edit tool, or use `\r?\n` in any regex.
- **Builds:** `-j 8`. Runs pinned: `cmd //c start "" //b //belownormal //affinity FFF //wait <exe> ...`, or
  `cpu_ab.ps1` (which pins itself). Before timing, report CPU load (`\Processor(_Total)\% Processor Time`) and
  Defender's `RealTimeProtectionEnabled`.
- **Python:** never run python that reads stdin (`python -`, heredocs); write a file and run
  `python -P f.py < /dev/null`.
- **Commits:** one per task. Message through PowerShell, `@'...'@ | Out-File -Encoding ascii "$env:TEMP\msg.txt"`,
  then `git commit -q -F "$env:TEMP\msg.txt"`. Check `git diff --cached --stat` first, and delete msg.txt after.
  End with `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`. **No push** without the user's go-ahead.
- **Leave alone:** the untracked `tests/ring_spike.rs` and `tests/ring_loop_spike.rs` in main. Other sessions'
  processes. `$TEMP` files that aren't this plan's.

## Departures from the spec (each recorded in the spec in Task 5)

1. **What the counter counts.** The spec counts "reached nodes in the current generation". A generation exists only
   while the table is on, and 19-21% of the nodes built in a scope never enter the table (spec, "Measured for this
   spec"). In the arena every node built in a region is a region node. So under `copy-volume` each node records the
   *region* it was built in: the outermost scope, lazy or not, numbered per thread. `persist` gives each node it reaches
   an id in a simulated per-thread persistent table, once per node. It counts:
   - `copied`, nodes from the open region;
   - `outside`, nodes built outside any region, which are persistent already in the arena;
   - `stale`, nodes from an earlier region that were never persisted. In the arena these are dead handles. Each one
     points at a store that still keeps `Expr`, or at a `gen_memo` entry kept across table-off regions (generation 0
     spans those today), which the arena would not have.
   - `unique`, the simulated table's size. Equal nodes copied by different regions count once, as the arena's
     persistent hash-consing stores them once.
   - Root `Expr`s have no header, so a root is looked up on every call. It is counted in `unique` when new, and never
     in `copied`; `calls` bounds the error.
   - The kernel's entries escape too: an outermost `infer_in` (as in every `Postulates::push` outside a scope)
     persists the type it returns. That is no inflation, since the arena copies those results out as well (spec,
     "Kernel internals").
2. **`Postulates` holds `PExpr`.** The spec lists `Globals` and the church_bv stores. `Postulates` holds `Globals`
   plus its parameters, and `PARAMS` (church_bv) and `PRELUDE` (`src/proof.rs:180`) keep a `Postulates` for the
   thread's life. So `push` and `bind` persist the types they keep.
3. **`NO_SCOPE` and the other A/B toggles stay** (as `if c { scoped(f) } else { f() }`). They are deleted by the port,
   where everything interns (spec, "Generation memos"). Stage 2 changes no behaviour, including under a toggle.

## File map

| File | Change |
|---|---|
| `Cargo.toml` | feature `copy-volume` |
| `src/kernel.rs` | `PExpr`, `persist`, `Escape`, `scoped`, `hc::scoped`, `copy_volume`; entries through `hc::scoped`; `Globals = im::Vector<PExpr>`; `InternScope` deleted |
| `src/kernel/postulates.rs` | `cong1`, `trans_proof`, `cong_n` through `scoped`; `params: Vec<(u32, PExpr)>`; `push`/`bind` persist |
| `src/kernel/tests.rs` | two new tests; 3 sites; `Globals` builders |
| `src/kernel/bin.rs` | 1 site; module doc |
| `src/proof/tests.rs` | `globals[1]` reads |
| `tests/kernel_fuzz.rs` | `Globals` builder |
| `tests/kernel_soundness_fuzz.rs` | `to_globals` (354) persists; `&ctx.p.globals` read as a `Ctx` (548, 577, 600) |
| `tests/church_bv/{search,machine,encoding,rewrite}.rs` | 70 sites; `CLOSED`, `TREE_LAWS`, `PARAMS` hold `PExpr`; `COPYVOL` lines |
| `tests/proof_scope.rs` | 2 sites |
| `docs/runs/2026-10-12/scripts/stage2_seq.sh` | new: sequential sweep pair |
| `docs/tier-cycle.md`, `docs/runs/2026-10-12/README.md` | results (tracked) |
| the spec and this plan | results. Both are under the git-excluded `docs/superpowers/`, so they exist only in the main checkout: edit them there, never commit them |

---

### Task 1: the API and its checks

**Files:**
- Modify: `Cargo.toml` (`[features]`)
- Modify: `src/kernel.rs`: replace the `InternScope` block at lines 649-669 (keep `InternScope` itself until Task 4);
  the `Node` header and both constructors at lines 55-96; `hc` (`for_kids`, `key_of`, `Scope`)
- Test: `src/kernel/tests.rs`

**Interfaces:**
- Produces, in `tatic::kernel`:
  - `pub struct PExpr`, with `fn get(&self) -> Expr`, `From<PExpr> for Expr`, `Clone`, `PartialEq`, `Eq`, `Debug`;
  - `pub fn persist(e: Expr) -> PExpr`;
  - `pub trait Escape { fn escape(self) -> Self; }`;
  - `pub fn scoped<R: Escape>(f: impl FnOnce() -> R) -> R`;
  - `hc::scoped<R: Escape>(activate: bool, f: impl FnOnce() -> R) -> R` (private to the kernel);
  - feature `copy-volume`: `pub struct CopyVolume { pub calls, pub copied, pub outside, pub stale, pub unique: u64 }`
    with `Display` (`calls=.. copied=.. outside=.. stale=.. unique=..`), plus
    `pub fn copy_volume_thread() -> CopyVolume` and `pub fn copy_volume_process() -> CopyVolume`.

- [ ] **Step 1: Set up the worktree and the feature.**

```bash
cd "/c/Users/Winston Li/Documents/GitHub/tatic" && git worktree add ../tatic-s2 -b id-arena-stage2 4769775 && git worktree add --detach ../tatic-s2-base 4769775
```

The second worktree is the baseline for every gate (test counts, sweep identity, timing). It is not the main checkout,
which other sessions may move. Record its test counts now, before Task 1 builds anything (two `-j 8` builds at once
would pass the 12-thread cap):

```bash
cd "/c/Users/Winston Li/Documents/GitHub/tatic-s2-base" && CARGO_TARGET_DIR=target/base cargo test --release -j 8 2>&1 | grep -E "^test result|Running" > "$(cygpath -u "$TEMP")/s2_base_counts.txt"
```

Expected: about 5-8 minutes; lib 370 and church_bv 76 among the suites.

In `../tatic-s2/Cargo.toml`, under `[features]` after `record-defeq = []`:

```toml
# Counts what the id arena's copy-out would copy (`kernel::copy_volume_thread`/`_process`; spec
# docs/superpowers/specs/2026-10-14-id-arena-spec.md, Stage 2). Off by default; adds nothing to the default build.
copy-volume = []
```

- [ ] **Step 2: Write the failing tests** at the end of `src/kernel/tests.rs`:

```rust
/// `scoped` escapes its result only in the call that opened the scope, and a panic inside it still closes the scope.
#[test]
fn scoped_escapes_only_when_outermost() {
    struct Count(std::rc::Rc<std::cell::Cell<u32>>);
    impl Escape for Count {
        fn escape(self) -> Self {
            self.0.set(self.0.get() + 1);
            self
        }
    }
    let n = std::rc::Rc::new(std::cell::Cell::new(0));
    let _c = scoped(|| {
        assert_ne!(intern_generation(), 0, "scoped switches the table on");
        let inner = scoped(|| Count(n.clone()));
        assert_eq!(n.get(), 0, "a nested scoped escapes nothing");
        inner
    });
    assert_eq!((n.get(), intern_generation()), (1, 0));
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| scoped(|| -> () { panic!("inside scoped") })));
    assert!(r.is_err());
    assert_eq!(intern_generation(), 0, "a panic closes the scope");
    let _d = scoped(|| Count(n.clone()));
    assert_eq!(n.get(), 2, "after a panic, the next scoped opens the scope again");
}

/// `persist` counts what the arena would copy out of a region: each region node once, nodes built outside any region
/// apart, nothing for a nested `scoped`, and a node kept past its region without `persist` as stale.
#[cfg(feature = "copy-volume")]
#[test]
fn copy_volume_counts_each_region_node_once() {
    // Leaves no other test builds, so `unique` counts only these even if the harness reuses this thread.
    let v0 = copy_volume_thread();
    let outside = app(var(900), var(901));
    let e = scoped(|| {
        let x = app(outside.clone(), var(902));
        let inner = scoped(|| app(x.clone(), var(903)));
        app(app(x.clone(), x), inner)
    });
    let v1 = copy_volume_thread();
    // Region nodes: App(x, x), x, the node for `outside`, var 902, `inner`, var 903. Outside: var 900, var 901.
    // Distinct: those eight and the root.
    assert_eq!(
        (v1.calls - v0.calls, v1.copied - v0.copied, v1.outside - v0.outside, v1.stale - v0.stale, v1.unique - v0.unique),
        (1, 6, 2, 0, 9)
    );
    let _ = persist(e);
    let v2 = copy_volume_thread();
    assert_eq!((v2.calls - v1.calls, v2.copied - v1.copied, v2.unique - v1.unique), (1, 0, 0), "persisted nodes are not copied again");
    let kept = std::cell::RefCell::new(None);
    scoped(|| *kept.borrow_mut() = Some(app(var(904), var(905))));
    let _ = persist(kept.into_inner().unwrap());
    assert_eq!(copy_volume_thread().stale - v2.stale, 2, "a term kept past its region without persist");
}
```

- [ ] **Step 3: Run them to see them fail.**

```bash
cd "/c/Users/Winston Li/Documents/GitHub/tatic-s2" && CARGO_TARGET_DIR=target/s2 cargo test --release -j 8 --lib --features copy-volume -- scoped_escapes copy_volume_counts 2>&1 | tail -5
```

Expected: compile errors: `Escape`, `scoped`, `persist`, `copy_volume_thread` not found.

- [ ] **Step 4: Add the API.** In `src/kernel.rs`, before `pub struct InternScope` (line 649), insert this block. Move
`InternScope`'s doc text (lines 649-659) onto `scoped`, as shown:

```rust
/// A term kept past the scope it was built in: what long-lived stores hold. Made only by [`persist`]. Today it is the
/// term itself; in the id arena it is a persistent id that stays valid after the region closes (spec
/// `docs/superpowers/specs/2026-10-14-id-arena-spec.md`). So it lends no `&Expr`: [`PExpr::get`] hands out the term.
#[derive(Clone, PartialEq, Eq)]
pub struct PExpr(Expr);

impl PExpr {
    /// The term, for building and checking.
    pub fn get(&self) -> Expr {
        self.0.clone()
    }
}

impl From<PExpr> for Expr {
    fn from(p: PExpr) -> Expr {
        p.0
    }
}

impl fmt::Debug for PExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.0, f)
    }
}

/// `e` as a term that outlives the open scope. A move today; with the feature `copy-volume` it also counts what the
/// arena would copy ([`copy_volume_thread`]).
pub fn persist(e: Expr) -> PExpr {
    #[cfg(feature = "copy-volume")]
    copy_volume::persist(&e);
    PExpr(e)
}

/// What [`scoped`] applies to its result when it closes the scope: [`persist`] on every term in it. A type that holds
/// terms and is returned from `scoped` needs an impl, so returning one without it fails to compile.
pub trait Escape {
    fn escape(self) -> Self;
}

impl Escape for Expr {
    fn escape(self) -> Self {
        persist(self).into()
    }
}

macro_rules! escape_as_is {
    ($($t:ty),*) => { $(impl Escape for $t { fn escape(self) -> Self { self } })* };
}
escape_as_is!(PExpr, (), bool, char, u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize, f32, f64, String, std::time::Duration);

impl<T: Escape> Escape for Option<T> {
    fn escape(self) -> Self {
        self.map(T::escape)
    }
}
impl<T: Escape, E: Escape> Escape for Result<T, E> {
    fn escape(self) -> Self {
        self.map(T::escape).map_err(E::escape)
    }
}
impl<T: Escape> Escape for Vec<T> {
    fn escape(self) -> Self {
        self.into_iter().map(T::escape).collect()
    }
}
impl<T: Escape> Escape for Box<T> {
    fn escape(self) -> Self {
        Box::new((*self).escape())
    }
}
macro_rules! escape_tuple {
    ($($n:tt $t:ident),+) => {
        impl<$($t: Escape),+> Escape for ($($t,)+) {
            fn escape(self) -> Self { ($(self.$n.escape(),)+) }
        }
    };
}
escape_tuple!(0 A);
escape_tuple!(0 A, 1 B);
escape_tuple!(0 A, 1 B, 2 C);
escape_tuple!(0 A, 1 B, 2 C, 3 D);
escape_tuple!(0 A, 1 B, 2 C, 3 D, 4 E);
escape_tuple!(0 A, 1 B, 2 C, 3 D, 4 E, 5 F);

/// Runs `f` in the open scope, or in a new one. While a scope is open, terms built with this module's constructors
/// (`app`, `lam`, `pi`, ...) and the nodes `shift`/`instantiate` make are interned: structurally equal children are one
/// node, so a proof that repeats itself is a small DAG, and the checks run inside it (`check_in`, `infer_in`, `def_eq`)
/// find the terms already canonical. Build a proof and check it in one call. Tables and memos live until the call that
/// opened the scope returns; that call passes `f`'s result through [`Escape`] first. Per thread.
///
/// Worth it for large proofs and a loss for small ones: it halves the check and, at n=512, saves half the time and
/// memory of the whole build-and-check, but building inside it costs more per node, so a proof that checks in well
/// under a millisecond (the gcd proofs) is about 20% slower overall (doc sections 69 and 71). `check_in` already
/// interns large inputs by itself; this scope is for proofs big enough that the builder's own sharing matters.
pub fn scoped<R: Escape>(f: impl FnOnce() -> R) -> R {
    hc::scoped(true, f)
}
```

In `mod hc`, after `impl Scope { .. }` (line 940), add:

```rust
    /// `f` in the open scope, or in a new one, with the table switched on now when `activate` (else after `WARM_UP`
    /// calls, as the kernel's own entries want). The call that opens the scope escapes `f`'s result before closing it.
    /// A panic closes it through `Scope`'s `Drop`, without escaping.
    pub fn scoped<R: Escape>(activate: bool, f: impl FnOnce() -> R) -> R {
        let outermost = DEPTH.with(|d| d.get()) == 0;
        let _s = Scope::enter();
        if activate {
            self::activate();
        }
        let r = f();
        if outermost { r.escape() } else { r }
    }
```

Rewrite `InternScope::enter` (kept until Task 4) so it no longer carries the doc text moved above:

```rust
/// The guard form of [`scoped`], until its last callers move (Task 4 of the Stage 2 plan deletes it).
#[must_use]
pub struct InternScope(#[allow(dead_code)] hc::Scope);
```

(Its `impl` block at lines 663-669 stays as it is.)

- [ ] **Step 5: Add the counter.** In `struct Node<T>` after the `canon` field:

```rust
    /// `copy_volume`: the region (outermost scope, numbered per thread) this node was built in, 0 outside any.
    #[cfg(feature = "copy-volume")]
    region: u32,
    /// `copy_volume`: this node's id in the simulated persistent table, `u32::MAX` until `persist` reaches it.
    #[cfg(feature = "copy-volume")]
    pid: std::cell::Cell<u32>,
```

In both `Rc::new` and `Rc::with_ranges`, after the `canon:` initializer:

```rust
            #[cfg(feature = "copy-volume")]
            region: copy_volume::region(),
            #[cfg(feature = "copy-volume")]
            pid: std::cell::Cell::new(u32::MAX),
```

The two fields make the node 72 bytes under the feature, so `a_node_is_64_bytes` (`src/kernel/tests.rs:480-482`) gets
`#[cfg(not(any(feature = "record-defeq", feature = "copy-volume")))]`, and its doc says "checked without those
features".

In `mod hc`, make `for_kids` `pub(super)`. Split the tag out of `key_of` so `copy_volume` reuses it:

```rust
    /// A node's constructor tag and leaf value, as the table keys them.
    pub(super) fn tag_leaf(e: &Expr) -> (u8, u32) {
        match e {
            Expr::Var(k) => (0, *k),
            // ... the 16 arms now at lines 1051-1066, unchanged ...
            Expr::SigRec { .. } => (15, 0),
        }
    }
```

`key_of` then begins `let (tag, leaf) = tag_leaf(e);`, and the rest stays as it is.

In `Scope::enter` and `Drop for Scope`, number the regions:

```rust
        pub fn enter() -> Scope {
            DEPTH.with(|d| {
                #[cfg(feature = "copy-volume")]
                if d.get() == 0 {
                    super::copy_volume::open();
                }
                d.set(d.get() + 1)
            });
            Scope
        }
```

and, in `Drop`, first thing inside `if DEPTH.with(..) {`:

```rust
                #[cfg(feature = "copy-volume")]
                super::copy_volume::close();
```

After `mod hc { .. }` (line 1369), add:

```rust
/// Feature `copy-volume`: what the id arena's `persist` would copy out of a region (id-arena spec, Stage 2, and its
/// plan's "Departures"). Each node records the region it was built in. `persist` gives every node it reaches an id in a
/// simulated per-thread persistent table, once per node, and counts the node by where it came from.
#[cfg(feature = "copy-volume")]
mod copy_volume {
    use super::*;
    use std::cell::{Cell, RefCell};
    use std::sync::atomic::{AtomicU64, Ordering::Relaxed};

    /// `persist` calls; nodes copied out of the open region; nodes built outside any region (persistent already in the
    /// arena); nodes from an earlier region that were never persisted (dead handles in the arena); distinct nodes in the
    /// simulated persistent table. A root `Expr` has no header, so it is looked up on every call and never counted as
    /// copied.
    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
    pub struct CopyVolume {
        pub calls: u64,
        pub copied: u64,
        pub outside: u64,
        pub stale: u64,
        pub unique: u64,
    }

    impl fmt::Display for CopyVolume {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "calls={} copied={} outside={} stale={} unique={}", self.calls, self.copied, self.outside, self.stale, self.unique)
        }
    }

    const CALLS: usize = 0;
    const COPIED: usize = 1;
    const OUTSIDE: usize = 2;
    const STALE: usize = 3;
    const UNIQUE: usize = 4;

    static PROCESS: [AtomicU64; 5] = [const { AtomicU64::new(0) }; 5];

    thread_local! {
        static THREAD: Cell<[u64; 5]> = const { Cell::new([0; 5]) };
        /// The open region's number, 0 while none is open; never reused within the thread.
        static REGION: Cell<u32> = const { Cell::new(0) };
        static NEXT: Cell<u32> = const { Cell::new(1) };
        /// (tag, leaf, children's ids) -> id.
        static TABLE: RefCell<HashMap<(u8, u32, [u32; 5]), u32>> = RefCell::new(HashMap::new());
    }

    fn bump(i: usize) {
        PROCESS[i].fetch_add(1, Relaxed);
        THREAD.with(|t| {
            let mut c = t.get();
            c[i] += 1;
            t.set(c);
        });
    }

    fn of(c: [u64; 5]) -> CopyVolume {
        CopyVolume { calls: c[CALLS], copied: c[COPIED], outside: c[OUTSIDE], stale: c[STALE], unique: c[UNIQUE] }
    }

    pub fn thread() -> CopyVolume {
        of(THREAD.with(Cell::get))
    }

    pub fn process() -> CopyVolume {
        of(std::array::from_fn(|i| PROCESS[i].load(Relaxed)))
    }

    pub fn region() -> u32 {
        REGION.with(Cell::get)
    }

    pub fn open() {
        let n = NEXT.with(|c| c.replace(c.get().checked_add(1).expect("regions ran out")));
        REGION.with(|r| r.set(n));
    }

    pub fn close() {
        REGION.with(|r| r.set(0));
    }

    pub fn persist(e: &Expr) {
        bump(CALLS);
        intern(e);
    }

    fn intern(e: &Expr) -> u32 {
        let (tag, leaf) = hc::tag_leaf(e);
        let mut kids = [u32::MAX; 5];
        let mut i = 0;
        hc::for_kids(e, |c| {
            kids[i] = id(c);
            i += 1;
        });
        TABLE.with(|t| {
            let mut t = t.borrow_mut();
            let n = t.len() as u32;
            *t.entry((tag, leaf, kids)).or_insert_with(|| {
                bump(UNIQUE);
                n
            })
        })
    }

    fn id(x: &Rc<Expr>) -> u32 {
        let p = x.0.pid.get();
        if p != u32::MAX {
            return p;
        }
        bump(match x.0.region {
            0 => OUTSIDE,
            r if r == region() => COPIED,
            _ => STALE,
        });
        let p = grow(|| intern(x));
        x.0.pid.set(p);
        p
    }
}

#[cfg(feature = "copy-volume")]
pub use copy_volume::CopyVolume;

/// What `persist` has counted on this thread (feature `copy-volume`).
#[cfg(feature = "copy-volume")]
pub fn copy_volume_thread() -> CopyVolume {
    copy_volume::thread()
}

/// What `persist` has counted on every thread of the process (feature `copy-volume`).
#[cfg(feature = "copy-volume")]
pub fn copy_volume_process() -> CopyVolume {
    copy_volume::process()
}
```

- [ ] **Step 6: Run the tests, with and without the feature.**

```bash
cd "/c/Users/Winston Li/Documents/GitHub/tatic-s2" && CARGO_TARGET_DIR=target/s2 cargo test --release -j 8 --lib --features copy-volume -- scoped_escapes copy_volume_counts 2>&1 | tail -4 && CARGO_TARGET_DIR=target/s2 cargo test --release -j 8 --lib 2>&1 | tail -3
```

Expected: 2 passed with the feature. Then the whole lib suite passes without it: the base's 370 plus
`scoped_escapes_only_when_outermost`, so 371, with no warnings. If `copy_volume_counts_each_region_node_once`'s counts
differ, print the five deltas and reason them through by hand before changing the expected tuple. Each node in the
comment must be accounted for.

- [ ] **Step 7: Commit** ("kernel: PExpr, persist, scoped and Escape (id arena Stage 2); feature copy-volume counts
the arena's copy-out").

### Task 2: the kernel's own scopes

**Files:**
- Modify: `src/kernel.rs`: `def_eq` (2204), `infer_in` (2526), `check_in` (2746), and the constructors' doc (678).
- Modify: `src/kernel/postulates.rs`: `cong1` (311), `trans_proof` (336), `cong_n` (369).
- Modify: `src/kernel/tests.rs`: the sites at 254, 295, 351. `src/kernel/bin.rs`: the site at 180, and the doc at lines 1 and 4.

**Interfaces:**
- Consumes: `scoped`, `hc::scoped` (Task 1).
- Produces: no new names. The entries' signatures are unchanged.

- [ ] **Step 1: The entries.** `def_eq` becomes:

```rust
pub fn def_eq(a: &Expr, b: &Expr) -> bool {
    hc::scoped(false, || {
        #[cfg(feature = "record-defeq")]
        let _g = site(3);
        #[cfg(feature = "record-defeq")]
        SEEN.with(|m| m.borrow_mut().clear());
        conv(a, b, &mut ReductionCache::default())
    })
}
```

In `infer_in`, the line `let _hc = hc::Scope::enter();` and the `infer_node(..)` tail become
`hc::scoped(false, || infer_node(globals, &mut InferCache::default(), &mut CtxScope::new(ctx), 0, &Rc::new(e.clone())))`.
In `check_in`, the guard line and everything after it become one `hc::scoped(false, || { .. })`, whose body is the old
tail: `let large = ..; let (e, expected) = ..; let body = ..; if large { .. } else { body() }`.

- [ ] **Step 2: The builders.** In `cong1` and `trans_proof`, delete the guard line and wrap the remaining body in
`scoped(|| { .. })`. Keep the comment, reworded to "Shifted copies are shared through the interning table's shift memo
(a scope of their own outside one)". In `cong_n`, keep the two `assert_eq!`s outside, and wrap everything from
`let apply = ..` to the end in `scoped(|| { .. })`. The early `return refl(lhs_all);` then returns from the closure,
which is the function's value as before.

- [ ] **Step 3: The four test sites.** Each guard runs to the end of its function. Wrap the statements from the guard
to the end in `scoped(|| { .. });`, and delete the guard. At tests.rs:295, also delete the `hc::activate();` that follows
it (`scoped` switches the table on). The constructors' doc at kernel.rs:678 says "inside [`scoped`]", and bin.rs's
lines 1 and 4 say "built in a [`scoped`](crate::kernel::scoped) call" and "read inside `scoped`".

- [ ] **Step 4: Run.**

```bash
cd "/c/Users/Winston Li/Documents/GitHub/tatic-s2" && CARGO_TARGET_DIR=target/s2 cargo test --release -j 8 --lib 2>&1 | tail -3 && grep -n "InternScope" src/kernel.rs src/kernel/*.rs
```

Expected: every lib test passes. The grep shows only the `InternScope` definition and impl in kernel.rs.

- [ ] **Step 5: Commit** ("kernel: the checking entries and cong1/trans_proof/cong_n open their scope through
scoped").

### Task 3: long-lived stores in `src` hold `PExpr`

**Files:**
- Modify: `src/kernel.rs`: `Globals` (2324) and `const_type` (2375).
- Modify: `src/kernel/postulates.rs`: `params`, `push` (165), `bind` (188), `close` (202), `open_ctx` (229-231), and any
  other reader the compiler names.
- Modify: `src/kernel/tests.rs` (`Globals::new()` builders at 1691, 1719, 1732, 1786), `tests/kernel_fuzz.rs:58`,
  `src/proof/tests.rs:14`, and `tests/kernel_soundness_fuzz.rs`:
  - `to_globals` (354) collects `persist(to_consts(..))`;
  - lines 548, 577 and 600 pass `&ctx.p.globals` where a `&Ctx` is wanted, so each converts with
    `&ctx.p.globals.iter().map(PExpr::get).collect::<kernel::Ctx>()` (read each site first; keep its meaning).

**Interfaces:**
- Consumes: `PExpr`, `persist` (Task 1).
- Produces: `pub type Globals = im::Vector<PExpr>;`. `Postulates::push(ty: Expr)` and `bind(ty: Expr)` keep their
  signatures and persist `ty`.

- [ ] **Step 1: Change the types.** `pub type Globals = im::Vector<PExpr>;`, keeping the doc. `const_type`:

```rust
fn const_type(g: &Globals, l: u32) -> Result<Expr, String> {
    match g.get(l as usize).map(PExpr::get) {
        Some(ty) if loose_of(&ty) == 0 && free_of(&ty) == 0 => Ok(ty),
        Some(ty) => Err(format!("constant @{l}'s type isn't closed: {}", brief(&ty))),
        None => Err(format!("unknown constant @{l}")),
    }
}
```

In postulates.rs, `pub(super) params: Vec<(u32, PExpr)>`. `push` ends with `self.globals.push_back(persist(ty));`, and
`bind` pushes `(l, persist(ty))`. Readers take the term out with `.get()`, e.g. in `close`
`let dom = abstract_frees(&self.params[s.params_len + i].1.get(), ..)`, and in `open_ctx`
`.map(|(i, (_, ty))| abstract_frees(&ty.get(), 0, &levels[..i], 0))`.

- [ ] **Step 2: Fix every caller the compiler names.**

```bash
cd "/c/Users/Winston Li/Documents/GitHub/tatic-s2" && CARGO_TARGET_DIR=target/s2 cargo test --release -j 8 --no-run 2>&1 | grep -E "^(error|warning)" -A6 | head -80
```

Builders `g.push_back(ty)` become `g.push_back(persist(ty))`. Index reads `&x.globals[i]` become `&x.globals[i].get()`,
except where a pattern borrows from the read: `src/proof/tests.rs:14`'s `let .. else` would borrow a temporary dropped
at the end of the statement, so bind the terms first, `let (ga, gb) = (a.p.globals[1].get(), b.p.globals[1].get());`,
and match on `(&ga, &gb)`. Change no logic. If a site needs more than this, stop and report it.

- [ ] **Step 3: Run.**

```bash
cd "/c/Users/Winston Li/Documents/GitHub/tatic-s2" && CARGO_TARGET_DIR=target/s2 cargo test --release -j 8 --lib --test kernel_fuzz --test kernel_soundness_fuzz 2>&1 | grep -E "^test result|FAILED|panicked"
```

Expected: every `test result: ok`.

- [ ] **Step 4: Commit** ("kernel: Globals and Postulates' parameters hold PExpr").

### Task 4: the integration tests' scopes and stores; `InternScope` deleted

**Files:**
- Modify: `tests/church_bv/search.rs` (31 sites), `machine.rs` (18), `encoding.rs` (16), `rewrite.rs` (5), and
  `tests/proof_scope.rs` (2): the site list is the survey in the appendix.
- Modify: `tests/church_bv/rewrite.rs`: `CLOSED` (394), `memo` (398), `PARAMS` (411), `shared_lemma` (431), `discharge`
  (445). `tests/church_bv/machine.rs`: `TREE_LAWS` (350), `add_tree_law` (404).
- Modify: `src/kernel.rs`: delete `InternScope`.

**Interfaces:**
- Consumes: `scoped`, `PExpr`, `persist`, `CopyVolume` (Task 1), `Globals` and `Postulates` (Task 3).

- [ ] **Step 1: The stores.** `CLOSED: RefCell<HashMap<String, (PExpr, PExpr)>>`, and:

```rust
pub fn memo(key: String, build: impl FnOnce() -> (Expr, Expr)) -> (Expr, Expr) {
    if let Some(v) = CLOSED.with(|c| c.borrow().get(&key).map(|(p, s)| (p.get(), s.get()))) {
        return v;
    }
    let (p, s) = build();
    CLOSED.with(|c| c.borrow_mut().insert(key, (persist(p.clone()), persist(s.clone()))));
    (p, s)
}
```

`TREE_LAWS` holds `Option<(PExpr, PExpr)>`. In `add_tree_law`, the hit is read as
`.map(|l| l.as_ref().map(|(p, s)| (p.get(), s.get())))`, and the insert stores
`law.clone().map(|(p, s)| (persist(p), persist(s)))`. `PARAMS` holds
`Option<(Postulates, Vec<(Scope, Option<PExpr>)>)>`. `shared_lemma` pushes `(sc, p.map(persist))`, and `discharge`
unwraps with `p.expect(..).get()` (or `.into()`; keep the message).

- [ ] **Step 2: The sites.** Apply these rules, in order, to each site in the appendix:
  1. **A guard that runs to the end of its function or block** (`let _scope = tatic::kernel::InternScope::enter();`):
     delete it and wrap the statements after it, to the end of the enclosing block, in
     `tatic::kernel::scoped(|| { .. })`. The block's tail expression, if any, becomes the closure's. A `()` block ends
     with `});`.
  2. **Inside a loop body:** the same, within the iteration. A `continue` inside the wrapped part becomes `return`. A
     `break` inside it needs a returned flag (`if scoped(|| { ..; false /* or true to break */ }) { break; }`); report
     each such site. A `?` inside a wrapped part of a function returning `Result` stays only if the closure's type
     makes it valid; otherwise report the site.
  3. **An optional guard** (`cond.then(InternScope::enter)`, including `NO_SCOPE`, `SWEEP_SCOPE` and
     `proof_scope.rs`'s `scoped` flag): name the wrapped part `let body = || { .. };`, then
     `if cond { tatic::kernel::scoped(body) } else { body() }`. The condition expression is unchanged.
  4. **Drop order:** values whose `Drop` has effects keep their order relative to the scope's close.
     - `search.rs:461`, `let _save = lemma_cache::Save;`, is declared after the guard, so it drops (and saves) while the
       scope is open: it moves inside the closure.
     - `search.rs:1978`'s `_save` is declared before the guard: it stays outside.
     - `MachineBanner` guards (`_banner`) after a guard move inside with it.
  5. **`encoding.rs:283`** (`constants_are_built_once_per_generation`) returns children out of a scope, to test that
     the next scope rebuilds them. Make the first block `let first = tatic::kernel::scoped(|| { ..asserts..; and_() });`
     and take `let first = kids(&first);` after it, so the nodes stay alive and the test means what it did. Wrap the
     second scope as in rule 1.
  6. **Spawned workers** (`search.rs:742, 823, 935`, `encoding.rs:1036`): rule 1 inside the closure that runs on the
     thread. For example the worker at 935 becomes
     `let worker = move || tatic::kernel::scoped(|| { let mut memo = ..; loop { .. } });`.
  7. **A wrapped part's result type with no `Escape` impl.**
     - If it holds no term and is a std type (`Instant`, `&str`, a `HashMap` of numbers), add it to `escape_as_is!` in
       `src/kernel.rs`.
     - If it holds no term and is local to the test crate (`Term`, for example), write a one-line identity impl in
       that crate. `Escape` is foreign there but the type is local, so this is allowed.
     - If it holds terms, stop and report: that would be a return the arena must copy out.
  8. **`proof_scope.rs` names locals and parameters `scoped`** (lines 15, 36, 64), so there the call is always the
     full path, `tatic::kernel::scoped(..)`. Remove `InternScope` from its `use tatic::kernel::{..}` (line 4).

  After the sites, delete `InternScope` (its struct and impl) from `src/kernel.rs`. Its remaining mentions in doc
  comments become "`scoped`":
  - `encoding.rs:637, 794, 1033`;
  - `proof_scope.rs:1, 50`;
  - any left in `kernel.rs`.

- [ ] **Step 3: The counter's report.** In `search.rs`, after the `scoped(..)` call in each of `rule_miner`,
`rule_set_kernel_check` and `proof_cost_split`, as the function's last statement:

```rust
    #[cfg(feature = "copy-volume")]
    println!("COPYVOL {}", tatic::kernel::copy_volume_process());
```

- [ ] **Step 4: Run everything, then check that no guard is left.**

```bash
cd "/c/Users/Winston Li/Documents/GitHub/tatic-s2" && CARGO_TARGET_DIR=target/s2 cargo test --release -j 8 2>&1 | grep -E "^test result|FAILED|panicked|^warning" ; CARGO_TARGET_DIR=target/s2 cargo test --release -j 8 --lib --features copy-volume 2>&1 | grep -E "^test result|FAILED|^(warning|error)" ; CARGO_TARGET_DIR=target/s2 cargo test --release -j 8 --features copy-volume --no-run 2>&1 | grep -E "^(warning|error)" ; grep -rn "InternScope" src tests
```

Expected:
- every suite is `test result: ok`, with the counts in `$TEMP/s2_base_counts.txt` (Task 1 Step 1) plus the new lib
  test (lib 371, church_bv 76);
- the lib suite with the feature passes, 372 with `copy_volume_counts_each_region_node_once`;
- no warnings, and the grep is empty.

- [ ] **Step 5: Diff against the brief.** `git diff --stat 4769775` touches only the files in the file map. In
`git diff 4769775 -- tests/` every change is a guard rewrite, a store type, a `.get()`/`persist` or a `COPYVOL` line.

- [ ] **Step 6: Commit** ("tests: scoped replaces InternScope at its 79 sites; CLOSED, TREE_LAWS and PARAMS hold
PExpr; InternScope deleted").

### Task 5: gates, the copy-out volume, docs

**Files:**
- Create: `docs/runs/2026-10-12/scripts/stage2_seq.sh`
- Modify: `docs/tier-cycle.md` (a new entry after "The slot in front of bounds"), `docs/runs/2026-10-12/README.md`
  (rows), the spec (Stage 2 status, the departures; Stage 1's "Continue" finding is in it already).

- [ ] **Step 1: Build the three exes.**
  - The baseline from `../tatic-s2-base` (Task 1 Step 1, `CARGO_TARGET_DIR=target/base`), then the branch twice: the
    default build, and the `copy-volume` build.
  - For each, run `cargo test --release -j 8 --test church_bv --no-run`, read the `Executable` path it prints, and
    copy that literal path to `$TEMP/bv_s2_old.exe`, `$TEMP/bv_s2_new.exe` and `$TEMP/bv_s2_cv.exe`.
  - Expected: about 3-5 minutes per build (the baseline's is cached from Task 1).

- [ ] **Step 2: Identical outputs.** `stage2_seq.sh` is `bounds_seq.sh` with tags `s2_old`/`s2_new`, its done-file
`s2_done.txt` and the two exes above. Its header says what it compares. Run it in the background and notify on
`ALL` in the done-file (a loop that exits, no `tail -F`). Then diff each salt's pair:

```bash
k=$(cygpath -u "$TEMP")/kk; for s in 1 2; do echo "salt $s:"; diff -rq $k/s2_old_$s $k/s2_new_$s; done
```

Expected: about 1.5 minutes for the four runs. The same file count on both sides, as in the `bnd_*` pair (181 per run,
lemma caches included). Every file that differs must be a log, and the diff of each such log must contain only timings
and the run's own path. Check it with `diff <(sed -E 's/[0-9]+(\.[0-9]+)?(s|ms|µs)\b/T/g; s/s2_(old|new)/RUN/g' a)
<(same for b)`. Any other difference fails the gate.

- [ ] **Step 3: Timing.** Check CPU load and Defender RTP, then run:

```powershell
& "docs\runs\2026-10-12\scripts\cpu_ab.ps1" "$env:TEMP\bv_s2_old.exe" - 8 "$env:TEMP\bv_s2_new.exe"
```

Expected: about 1.5 minutes. The medians agree within the rotations' spread (earlier rotations: 3.63-3.84 s), and new wins
about half the pairs. A consistent loss (new slower in 6 or more of 8) fails the gate: find which change costs, before
going on.

- [ ] **Step 4: The copy-out volume.**
  - `proof_cost_split` once, in `cpu_ab.ps1`'s environment:

```bash
k=$(cygpath -u "$TEMP")/kk; mkdir -p $k; d="/c/Users/Winston Li/Documents/GitHub/tatic-s2/docs/runs/2026-10-12/scripts"; CHECK_FAMILY=cmp3d CHECK_RULES="$(cygpath -w "$d/cmp3d_own_rules.txt")" RULEMINER_LAWS=300 cmd //c start "" //b //belownormal //affinity FFF //wait "$TEMP/bv_s2_cv.exe" search::proof_cost_split --exact --ignored --nocapture > $k/s2_cv_pcs.txt 2>&1; grep '^COPYVOL' $k/s2_cv_pcs.txt
```
  - Run one salt-1 sweep with it (as `stage2_seq.sh`'s `run`, tag `s2_cv`). Sum its children's lines:

```bash
k=$(cygpath -u "$TEMP")/kk; grep -rh '^COPYVOL' $k/s2_cv_1 | awk '{for(i=2;i<=NF;i++){split($i,a,"=");s[a[1]]+=a[2]}} END{for(f in s) printf "%s=%d ", f, s[f]; print ""}'
```

  - The number of `COPYVOL` lines must equal the number of `rule_miner` and `rule_set_kernel_check` children in the
    sweep (count their logs). A missing line means a child's count is lost.
  - Set `copied` against the spec's probe, on an earlier build: 2.98 M nodes interned and 0.49 M alive after for
    `proof_cost_split`, and 10.8 M and 2.61 M for the sweep. This gives the order of magnitude, not a ratio to quote
    as measured.
  - If `stale` is nonzero, find which store or memo the nodes come from before writing the result.

- [ ] **Step 5: Docs.**
  - In `docs/tier-cycle.md`, an entry "Id arena Stage 2 (date)": what changed, the sweep identity, the timing table
    (with load and RTP), the copy-out volume table, and what it means for the port's risk "an outermost `scoped` copies
    out large results".
  - Rows in `docs/runs/2026-10-12/README.md` for `s2_*` and `s2_cv`.
  - In the spec, at the main checkout's path (git-excluded, so not in the worktree or any commit):
    - Stage 2 marked done, with the numbers;
    - the three departures above;
    - the `uses` section updated for the bounds memo (`bounds` keyed by `Ref`, beside the slot's side array);
    - `Globals`' and `Postulates`' new types under "What exists".

  Commit the two tracked docs ("Docs: id arena Stage 2 ...", with the numbers in the message, as earlier doc commits
  do). Then clean up:
  - remove the base worktree and both worktrees' target dirs, the `$TEMP/bv_s2_*.exe` and `$TEMP/s2_base_counts.txt`;
  - keep the run dirs;
  - check `Get-Process` for leftover test exes.

- [ ] **Step 6: Stop.** Report the gates and the copy-out volume, and ask for the Stage 3 decision and for push and
merge go-aheads.

## Appendix: the 79 sites (survey 2026-10-14, read-only, against 4769775)

Whole-function guards in `()` tests unless noted.

- **search.rs:**
  - 62;
  - 454 `rule_miner` (mid-function, to the end; `_save` at 461 after it);
  - 742 closure `prove` → `Vec<usize>`, on workers;
  - 823 closure `prove_any` → `bool`, on workers;
  - 935 worker loop on a spawned thread;
  - 1221, 1250, 1262, 1279, 1293, 1310, 1341;
  - 1439 and 1462 per loop iteration;
  - 1501, 1513, 1541, 1580;
  - 1627 optional `(!per_law)`, the whole function;
  - 1649 optional `per_law`, per law;
  - 1857, 1912, 1936;
  - 1979 `rule_set_kernel_check` (`_save` before it);
  - 2040 `proof_cost_split`, 2091, 2137, 2154, 2242, 2272, 2506.
- **machine.rs:**
  - 628, 651, 677;
  - 712 per iteration;
  - 725, 763;
  - 805 optional `NO_SCOPE`, per iteration;
  - 843, 1036, 1075, 1223, 1264, 1298, 1316, 1368, 1417, 1471, 1510.
- **encoding.rs:**
  - 259;
  - 283 and 288 (rule 5);
  - 643 optional `NO_SCOPE`, per iteration;
  - 786 optional `NO_SCOPE`, the whole function;
  - 806 optional `NO_SCOPE`, per iteration;
  - 1036 `profile_scoped`, on a 1 GiB thread;
  - 1221, 1334, 1499, 1604, 1735, 1748, 1858, 2191 per iteration;
  - 1842 per iteration, around an inner loop.
- **rewrite.rs:** 1878, 1910, 1954 (uses `PARAMS` and `CLOSED`), 2082, 2104.
- **postulates.rs:** 311, 336, 369 (Task 2).
- **kernel/tests.rs:** 254, 295, 351 (Task 2). **bin.rs:** 180 (Task 2).
- **proof_scope.rs:**
  - 20 optional, per iteration;
  - 65 optional, in a closure that returns sizes and holds no terms.

Not sites: the six `hc::Scope::enter` unit tests (tests.rs 540-641) stay; the kernel entries are Task 2.
`kernel_lazy`'s `MEMO` is per call (`def_eq_lazy_shared`), not a store.
