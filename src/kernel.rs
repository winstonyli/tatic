//! A minimal predicative dependent type theory kernel: Pure-Type-System-style
//! Pi + a stratified universe hierarchy, plus Id-types, W-types, and
//! Sigma-types as the additions beyond a bare PTS.
//!
//! Five primitive term/type formers, total:
//!   - `Sort(i)`: the universe hierarchy `Type_0 : Type_1 : Type_2 ...`
//!   - `Pi`/`Lam`/`App`: dependent function types
//!   - `Id`/`Refl`/`J`: propositional equality, with its eliminator
//!   - `W`/`Sup`/`WRec`: well-founded trees, i.e. *the* generic strictly
//!     positive inductive type former (Bool, Nat, lists, and eventually
//!     this crate's own `Term` AST are all instances of one `W`, not
//!     separate primitives)
//!   - `Sigma`/`Pair`/`SigRec`: dependent pairs. *Not* derivable from the
//!     other four here: `W`'s own children function maps back into `W`
//!     itself (`B(a) -> W(A,B)`), so it can only stand in for a payload
//!     that's *another instance of the same inductive type* -- it can't
//!     express an arbitrary, independently-chosen payload type `B(a)`
//!     the way a general dependent sum needs. The usual alternative,
//!     Church/impredicative-encoding `Sigma` from `Pi` alone, was rejected
//!     for the same reason Church-encoding inductive types was rejected in
//!     favor of `W`: it doesn't reduce by `refl`, only propositionally.
//!
//! Everything else (Bool, Nat, non-dependent pairs, ...) is a *definition*
//! built from these five, not a further primitive. See the tests at the
//! bottom for worked examples, including a proof that uses `J` (symmetry
//! of `Id`), a `WRec`-defined function whose defining equation holds by
//! `refl` alone (i.e. genuinely *computes*, which is the whole point of
//! choosing `W` over an impredicative/Church encoding), and a `SigRec`
//! projection that computes the same way.
//!
//! This module is intentionally free-standing: it does not (yet) replace
//! `term`/`eval`/`compile`/`jit`. Wiring the JIT's "found to be equivalent"
//! check through an actual `Id`-typed, kernel-checked proof term (instead
//! of empirical sampling) is the natural next step once this kernel is
//! trusted, not something folded into this pass.

use hashbrown::{HashMap, HashSet};
use std::fmt;

// --- shared nodes ----------------------------------------------------------
//
// Every child of an `Expr` is a kernel `Rc`: `std::rc::Rc` with the
// child's loose-variable and free-level ranges cached beside it, computed
// once when the node is built. `shift`, `instantiate` and `is_var_free`
// read it to skip the subterms they would leave unchanged, and keep those
// by pointer (`RELATED_WORK.md` §64).

/// A shared node, and its [`loose_of`] and [`free_of`] computed when it
/// was built.
pub struct Rc<T>(std::rc::Rc<Node<T>>);

struct Node<T> {
    loose: u32,
    free: u32,
    /// Probe: id of this node's structure in a simulated hash-cons table (`hc_probe`).
    #[cfg(feature = "record-defeq")]
    canon: u64,
    /// `hashcons`: the table generation this node is canonical in (0: not), see `hc`.
    #[cfg(feature = "hashcons")]
    generation: std::cell::Cell<u32>,
    val: T,
}

impl Rc<Expr> {
    pub fn new(e: Expr) -> Self {
        Rc(std::rc::Rc::new(Node {
            loose: loose_of(&e),
            free: free_of(&e),
            #[cfg(feature = "record-defeq")]
            canon: hc_probe::intern(&e),
            #[cfg(feature = "hashcons")]
            generation: std::cell::Cell::new(0),
            val: e,
        }))
    }

    /// As [`Rc::new`] with the ranges supplied by the caller, who must
    /// know them to equal `loose_of(&e)` and `free_of(&e)`.
    fn with_ranges(e: Expr, loose: u32, free: u32) -> Self {
        debug_assert!(loose == loose_of(&e) && free == free_of(&e));
        Rc(std::rc::Rc::new(Node {
            loose,
            free,
            #[cfg(feature = "record-defeq")]
            canon: hc_probe::intern(&e),
            #[cfg(feature = "hashcons")]
            generation: std::cell::Cell::new(0),
            val: e,
        }))
    }

    /// Whether this node and everything under it came from the current `hc` table, so that two
    /// canonical nodes are structurally equal exactly when they are the same node. Always false
    /// without the `hashcons` feature, or outside a scope.
    #[cfg(feature = "hashcons")]
    #[inline(always)]
    pub(crate) fn canonical(&self) -> bool {
        let g = self.0.generation.get();
        g != 0 && g == hc::generation()
    }
    #[cfg(not(feature = "hashcons"))]
    #[inline(always)]
    pub(crate) fn canonical(&self) -> bool {
        false
    }

    /// Probe: this node's id in the simulated hash-cons table.
    #[cfg(feature = "record-defeq")]
    pub fn canon(&self) -> u64 {
        self.0.canon
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


/// Probes for hash-consing and a global `instantiate` memo (bit-vector design doc section 58):
/// a simulated intern table gives each node the id its structure would have, from its constructor,
/// leaf value and children's ids. Nothing here changes any result.
#[cfg(feature = "record-defeq")]
mod hc_probe {
    use super::*;
    use std::cell::{Cell, RefCell};
    use std::hash::{Hash, Hasher};

    /// Repeat statistics per kind of operation: 0 `instantiate_n`, 1 `shift`, 2 `whnf_step`, 3
    /// `conv_whnf`.
    pub const KINDS: usize = 4;

    thread_local! {
        static TABLE: RefCell<HashMap<u64, u64>> = RefCell::new(HashMap::new());
        /// 0 nodes built, 1 of them new to the table.
        static BUILT: [Cell<u64>; 2] = const { [const { Cell::new(0) }; 2] };
        static SEEN: RefCell<[HashSet<u64>; KINDS]> = RefCell::new(Default::default());
        /// Per kind: 0 calls, 1 maximal repeated calls, 2 work inside them, 3 work in all depth-0
        /// calls, 4 depth-0 calls, 5 depth-0 repeats, 6 work inside depth-0 repeats.
        static STATS: [[Cell<u64>; 8]; KINDS] = const { [const { [const { Cell::new(0) }; 8] }; KINDS] };
        static DEPTH: [Cell<u32>; KINDS] = const { [const { Cell::new(0) }; KINDS] };
        static IN_REPEAT: [Cell<bool>; KINDS] = const { [const { Cell::new(false) }; KINDS] };
    }

    /// Work done so far, for the kind: its own walk's visits for `instantiate_n` and `shift`, the
    /// sum of all three walks for the others.
    fn work(kind: usize) -> u64 {
        WALKS.with(|w| match kind {
            0 => w[0].get(),
            1 => w[1].get(),
            _ => w[0].get() + w[1].get() + w[2].get(),
        })
    }

    fn structure_hash(e: &Expr) -> u64 {
        let mut h = std::collections::hash_map::DefaultHasher::new();
        std::mem::discriminant(e).hash(&mut h);
        match e {
            Expr::Var(k) | Expr::Sort(k) | Expr::Const(k) | Expr::Free(k) => k.hash(&mut h),
            _ => {
                same_shape(e, e, |p, _| {
                    p.canon().hash(&mut h);
                    true
                });
            }
        }
        h.finish()
    }

    fn id_of(e: &Expr, count: bool) -> u64 {
        let h = structure_hash(e);
        TABLE.with(|t| {
            let mut t = t.borrow_mut();
            let next = t.len() as u64;
            let new = !t.contains_key(&h);
            let id = *t.entry(h).or_insert(next);
            if count {
                BUILT.with(|b| {
                    b[0].set(b[0].get() + 1);
                    if new {
                        b[1].set(b[1].get() + 1);
                    }
                });
            }
            id
        })
    }

    pub fn intern(e: &Expr) -> u64 {
        id_of(e, true)
    }

    /// (nodes built, distinct structures among them new to the table) since the last call.
    pub fn take_built() -> (u64, u64) {
        BUILT.with(|b| (b[0].replace(0), b[1].replace(0)))
    }

    pub fn take_inst() -> [[u64; 8]; KINDS] {
        STATS.with(|c| std::array::from_fn(|k| std::array::from_fn(|i| c[k][i].replace(0))))
    }

    /// Guard for one call of kind `kind`: notes whether the same key was seen before, and the work a
    /// memo hit would have skipped.
    pub struct Guard {
        kind: usize,
        v0: u64,
        repeat: bool,
        outer_repeat: bool,
        top: bool,
    }

    fn start(kind: usize, key: u64) -> Guard {
        let repeat = !SEEN.with(|s| s.borrow_mut()[kind].insert(key));
        let top = DEPTH.with(|c| c[kind].replace(c[kind].get() + 1)) == 0;
        let outer_repeat = IN_REPEAT.with(|c| c[kind].replace(c[kind].get() || repeat));
        STATS.with(|c| {
            let c = &c[kind];
            c[0].set(c[0].get() + 1);
            if top {
                c[4].set(c[4].get() + 1);
            }
            if repeat && !outer_repeat {
                c[1].set(c[1].get() + 1);
            }
            if top && repeat {
                c[5].set(c[5].get() + 1);
            }
        });
        Guard { kind, v0: work(kind), repeat, outer_repeat, top }
    }

    impl Drop for Guard {
        fn drop(&mut self) {
            let visits = work(self.kind) - self.v0;
            let k = self.kind;
            DEPTH.with(|c| c[k].set(c[k].get() - 1));
            IN_REPEAT.with(|c| c[k].set(self.outer_repeat));
            STATS.with(|c| {
                let c = &c[k];
                if self.repeat && !self.outer_repeat {
                    c[2].set(c[2].get() + visits);
                }
                if self.top {
                    c[3].set(c[3].get() + visits);
                    if self.repeat {
                        c[6].set(c[6].get() + visits);
                    }
                }
            });
        }
    }

    pub fn inst_enter(e: &Expr, args: &[&Expr], d: u32) -> Guard {
        let mut h = std::collections::hash_map::DefaultHasher::new();
        id_of(e, false).hash(&mut h);
        for a in args {
            id_of(a, false).hash(&mut h);
        }
        d.hash(&mut h);
        start(0, h.finish())
    }

    pub fn shift_enter(e: &Expr, cutoff: u32, amount: i32) -> Guard {
        let mut h = std::collections::hash_map::DefaultHasher::new();
        id_of(e, false).hash(&mut h);
        (cutoff, amount).hash(&mut h);
        start(1, h.finish())
    }

    pub fn whnf_enter(e: &Expr) -> Guard {
        start(2, id_of(e, false))
    }

    pub fn conv_enter(x: &Expr, y: &Expr) -> Guard {
        let (a, b) = (id_of(x, false), id_of(y, false));
        let mut h = std::collections::hash_map::DefaultHasher::new();
        (a.min(b), a.max(b)).hash(&mut h);
        start(3, h.finish())
    }
}

#[cfg(feature = "record-defeq")]
pub use hc_probe::{take_built as take_hc_built, take_inst as take_hc_inst};

/// One more than the largest loose `Var` index in `e`, 0 when it's
/// closed, from its children's cached ranges. A child one binder deeper
/// (the second field of `Pi`/`Lam`/`W`/`Sigma`, `WRec`'s `children_ty`,
/// `Pair`'s `fam`) has one loose variable fewer out here. Saturating, so a
/// `Var(u32::MAX)` doesn't wrap to "closed"; the range is exact only below
/// `u32::MAX` (`Var(u32::MAX - 1)` and `Var(u32::MAX)` both give
/// `u32::MAX`, which no real term reaches).
pub fn loose_of(e: &Expr) -> u32 {
    let l = |c: &Rc<Expr>| c.loose();
    let u = |c: &Rc<Expr>| c.loose().saturating_sub(1);
    match e {
        Expr::Var(k) => k.saturating_add(1),
        Expr::Sort(_) | Expr::Const(_) | Expr::Free(_) => 0,
        Expr::Pi(a, b) | Expr::Lam(a, b) | Expr::W(a, b) | Expr::Sigma(a, b) => l(a).max(u(b)),
        Expr::App(a, b) | Expr::Sup(a, b) => l(a).max(l(b)),
        Expr::Id(a, b, c) | Expr::SigRec { motive: a, step: b, target: c } => l(a).max(l(b)).max(l(c)),
        Expr::Pair(fam, a, b) => u(fam).max(l(a)).max(l(b)),
        Expr::Refl(a) => l(a),
        Expr::J { motive, base, a, b, p } => l(motive).max(l(base)).max(l(a)).max(l(b)).max(l(p)),
        Expr::WRec { motive, children_ty, step, target } => l(motive).max(u(children_ty)).max(l(step)).max(l(target)),
    }
}

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

// --- stack growth ----------------------------------------------------------
//
// Every traversal in this module recurses over `Expr` structure, and
// `whnf`/`nf` also recurse once per reduction step, so native stack use
// grows with both a term's depth and its reduction length. Measured
// before this existed: a debug build on a 1 MB thread (the Windows main
// thread) overflowed at depth ~90, a release build at ~450-570
// (`RELATED_WORK.md` 31). Rather than hand-convert `infer`/`check` into
// an explicit continuation machine -- hundreds of new lines inside the
// trusted kernel, no longer reading like the typing rules they implement
// -- each recursive entry point runs through `grow`, which spills onto a
// fresh heap-allocated stack segment when the current one runs low. The
// approach and constants are rustc's own `ensure_sufficient_stack`; the
// per-call check is this module's own, because stacker's measured too
// slow to make at every node (see `FLOOR`).

/// Headroom below which `grow` switches to a new segment: enough for the
/// deepest chain of un-wrapped frames between two wrapped calls.
const RED_ZONE: usize = 100 * 1024;
/// Size of each new segment `grow` allocates.
const STACK_PER_RECURSION: usize = 1024 * 1024;
/// Size of the one segment a large `check_in` runs on. On Windows stacker builds a fiber per
/// segment and frees it on return, so a deep recursion that straddles a segment boundary pays that
/// cost at every crossing (65k+ times at n=512, a third of the CPU in page faults, doc section 76).
/// Starting the check on a segment big enough that it never reaches the end avoids it; reserving it
/// costs nothing until touched, and a deeper recursion still chains further segments.
const CHECK_SEGMENT: usize = 64 * 1024 * 1024;

thread_local! {
    /// The lowest stack address the current segment can reach with
    /// [`RED_ZONE`] still to spare; `usize::MAX` -- "unknown", which
    /// every check fails -- until [`grow_slow`] first learns it on this
    /// thread. Tracked here rather than asking stacker each
    /// time: `stacker::remaining_stack` measured 8.9 ns a call on Windows
    /// (a lazily-initialized thread-local plus a non-inlined assembly
    /// call), and at one check per `shift`/`==`/`Drop` node that nearly
    /// doubled every proof benchmark. This check is a local's address
    /// against a const thread-local, ~1 ns.
    static FLOOR: std::cell::Cell<usize> = const { std::cell::Cell::new(usize::MAX) };
}

/// An address inside the current frame -- close enough to the stack
/// pointer, with [`RED_ZONE`] of slack.
#[inline(always)]
fn stack_addr() -> usize {
    let here = 0u8;
    std::hint::black_box(&here) as *const u8 as usize
}

/// Whether at least [`RED_ZONE`] bytes of the current segment remain.
#[inline(always)]
fn stack_ok() -> bool {
    stack_addr() > FLOOR.with(|f| f.get())
}

/// Runs `f`, first moving onto a fresh stack segment if fewer than
/// [`RED_ZONE`] bytes remain. Wraps the body of every recursive function
/// in this module -- and `PartialEq` and `Debug` for `Expr`; `Drop` uses
/// [`stack_ok`] directly -- so their depth is bounded by heap, not native
/// stack.
#[inline(always)]
pub(crate) fn grow<R>(f: impl FnOnce() -> R) -> R {
    if stack_ok() { f() } else { grow_slow(f) }
}

/// [`grow`]'s slow path: the first check on a thread (`FLOOR` unknown),
/// or a segment genuinely running low. Keeps `FLOOR` describing whichever
/// segment is current: set on entry to a new one, restored on the way
/// out -- by a guard, so an unwinding panic restores it too.
///
/// Outside any segment of ours, `FLOOR` unknown means this is the thread's
/// own stack, learned once and kept. Where stacker cannot measure that
/// stack, `FLOOR` stays unknown and every call grows a fresh segment:
/// slow, but never unprotected.
#[cold]
#[inline(never)]
fn grow_slow<R>(f: impl FnOnce() -> R) -> R {
    fn floor_here() -> Option<usize> {
        stacker::remaining_stack().map(|left| stack_addr().saturating_sub(left) + RED_ZONE)
    }
    if FLOOR.with(|f| f.get()) == usize::MAX
        && let Some(floor) = floor_here()
    {
        FLOOR.with(|f| f.set(floor));
        if stack_ok() {
            return f();
        }
    }
    on_segment(STACK_PER_RECURSION, f)
}

thread_local! {
    static SEGMENT_SWITCHES: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// How many times this thread has moved onto a new stack segment (by `grow` or a large `check_in`).
/// A segment is a fiber on Windows, so a recursion that crosses a boundary over and over is costly
/// (doc section 76): tests read this to catch a return of that.
pub fn segment_switches() -> u64 {
    SEGMENT_SWITCHES.with(|c| c.get())
}

/// Runs `f` on a new stack segment of `size` bytes, with `FLOOR` describing it meanwhile.
fn on_segment<R>(size: usize, f: impl FnOnce() -> R) -> R {
    SEGMENT_SWITCHES.with(|c| c.set(c.get() + 1));
    fn floor_here() -> Option<usize> {
        stacker::remaining_stack().map(|left| stack_addr().saturating_sub(left) + RED_ZONE)
    }
    struct Restore(usize);
    impl Drop for Restore {
        fn drop(&mut self) {
            FLOOR.with(|f| f.set(self.0));
        }
    }
    stacker::grow(size, || {
        let _restore = Restore(FLOOR.with(|f| f.replace(floor_here().unwrap_or(usize::MAX))));
        f()
    })
}

/// Recursive fields are `Rc`, not `Box`: `Expr` is built and re-threaded
/// through deeply nested proof terms (the Ev-witness builder's
/// per-call-site composition, ...) almost entirely by `.clone()`,
/// and a `Box`-tree clone is a full deep copy -- cost that scales with the
/// *entire* accumulated proof term, not with what actually changed. With
/// `Rc`, `#[derive(Clone)]` on `Expr` clones each field by bumping a
/// refcount, so cloning any `Expr` (regardless of how large the subtree it
/// roots is) is O(1) and its children are genuinely shared, not copied. This
/// is not full hash-consing (two independently-built-but-equal subtrees
/// still get distinct allocations -- there's no intern table), but it
/// removes the actual cost this crate was paying: repeated deep copies of
/// one proof term as it's threaded through several composition steps.
#[derive(Clone)]
pub enum Expr {
    /// De Bruijn index; `Var(0)` is the innermost binder.
    Var(u32),
    /// `Type_i`.
    Sort(u32),
    /// A postulate: entry `l` of the global environment (`Globals`),
    /// numbered from the first, so neither a binder nor a later global
    /// renumbers it. Typed by `globals[l]`, which must be closed.
    Const(u32),
    /// A builder scope's parameter, by a level no other parameter reuses.
    /// Never typed: `infer` and `check` reject any term, expected type or
    /// context entry with one in it, so a parameter that escapes its
    /// scope fails the check instead of acting as an axiom.
    Free(u32),
    /// `Pi(A, B)`: `B` is checked one binder deeper than `A` (i.e. `B` may
    /// mention the newly-bound variable of type `A` as `Var(0)`).
    Pi(Rc<Expr>, Rc<Expr>),
    /// `Lam(A, body)`: `A` is the domain annotation; `body` one binder deeper.
    Lam(Rc<Expr>, Rc<Expr>),
    App(Rc<Expr>, Rc<Expr>),
    /// `Id(A, a, b)`: the type of proofs that `a` and `b` (both `: A`) are equal.
    Id(Rc<Expr>, Rc<Expr>, Rc<Expr>),
    /// `Refl(a) : Id(A, a, a)`, the only primitive way to construct an equality.
    Refl(Rc<Expr>),
    /// Eliminator for `Id`. `motive` is `C : Pi x y : A. Id(A,x,y) -> Sort(k)`,
    /// `base` is `c : Pi x : A. C x x (refl x)`, `p : Id(A, a, b)`.
    /// Result type: `C a b p`. Reduces to `base a` when `p` reduces to a `Refl`.
    J {
        motive: Rc<Expr>,
        base: Rc<Expr>,
        a: Rc<Expr>,
        b: Rc<Expr>,
        p: Rc<Expr>,
    },
    /// `W(A, B)`: `B` one binder deeper than `A`, i.e. `B` is the family
    /// `B(x)` for `x : A` giving the arity/shape of the children at tag `x`.
    W(Rc<Expr>, Rc<Expr>),
    /// `Sup(a, f) : W(A,B)` where `a : A` and `f : B(a) -> W(A,B)`.
    Sup(Rc<Expr>, Rc<Expr>),
    /// Eliminator (recursor) for `W`. `motive : W(A,B) -> Sort(k)`,
    /// `step : Pi a:A. Pi f:(B a -> W). (Pi y:B a. motive (f y)) -> motive (sup a f)`.
    /// Reduces on a `Sup` target by recursing into every child.
    ///
    /// `children_ty` is `B` itself, in the *same* representation `W(A,B)`'s
    /// own second field already uses (written one binder deeper than `A`,
    /// i.e. `B(x)` with the ambient `x:A` as `Var(0)`) -- carried here,
    /// redundantly with `target`'s own real type `W(A,B)`, purely so
    /// `whnf_impl`'s own automatic reduction (which has no typing context
    /// at all, by design) can give its induction-hypothesis closure an
    /// honest domain (`subst_top(children_ty, a)`, i.e. `B(a)`) instead of
    /// an inert placeholder. `infer` independently re-derives `B` from
    /// `target`'s own real inferred type and checks it against this field
    /// via `def_eq` -- a term built with a *wrong* `children_ty` (whether
    /// by mistake or by a hostile caller) is rejected outright, never
    /// silently trusted, so this redundancy can't become a soundness hole.
    WRec {
        motive: Rc<Expr>,
        children_ty: Rc<Expr>,
        step: Rc<Expr>,
        target: Rc<Expr>,
    },
    /// `Sigma(A, B)`: `B` one binder deeper than `A`, i.e. `B` is the
    /// family `B(x)` for `x : A` -- the type of dependent pairs `(a, b)`
    /// with `a : A` and `b : B(a)`. See this module's own top-level docs
    /// for why this is a genuinely separate primitive, not derivable from
    /// `W` here.
    Sigma(Rc<Expr>, Rc<Expr>),
    /// `Pair(fam, a, b) : Sigma(A, B)` where `a : A`, `b : B(a)`. `fam` is
    /// `B` itself, in the *same* representation `Sigma`'s own second field
    /// already uses (one binder deeper than the ambient context) --
    /// carried explicitly because, unlike `Sup`'s own second argument
    /// (whose `Pi`-type already reveals the whole `W(A,B)` it targets), a
    /// pair's own two components alone don't determine which family `B`
    /// was intended (many different families agree at one concrete `a`)
    /// -- the same reason `Lam` carries its own domain annotation.
    Pair(Rc<Expr>, Rc<Expr>, Rc<Expr>),
    /// Eliminator (recursor) for `Sigma`. `motive : Sigma(A,B) -> Sort(k)`,
    /// `step : Pi a:A. Pi b:B(a). motive (pair(fam,a,b))`. Reduces on a
    /// `Pair` target to `step a b`. Unlike `WRec`, needs no extra
    /// `children_ty`-style redundant field: a pair isn't recursive, so
    /// there's no induction-hypothesis closure to give an honest domain to
    /// -- `target`'s own real type alone is enough context for both
    /// `infer` and `whnf_impl`.
    SigRec {
        motive: Rc<Expr>,
        step: Rc<Expr>,
        target: Rc<Expr>,
    },
}

/// Structural equality, written out rather than derived so it recurses
/// through [`grow`] -- `def_eq` compares two large terms with it.
/// Same semantics as the derive: fields compared in declaration order,
/// and `Rc`'s own `==` still short-circuits on pointer identity (it does
/// so for any `T: Eq`).
impl PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        grow(|| same_shape(self, other, |p, q| Rc::ptr_eq(p, q) || (!(p.canonical() && q.canonical()) && **p == **q)))
    }
}

/// Whether `x` and `y` have the same outermost constructor (and index, for
/// `Var`/`Sort`/`Const`/`Free`) and `c` holds of each pair of children, in
/// field order, stopping at the first that fails. Syntactic equality and
/// `conv_whnf` are both this with a different `c`.
pub(crate) fn same_shape(x: &Expr, y: &Expr, mut c: impl FnMut(&Rc<Expr>, &Rc<Expr>) -> bool) -> bool {
    use Expr::*;
    match (x, y) {
        (Var(i), Var(j)) | (Sort(i), Sort(j)) | (Const(i), Const(j)) | (Free(i), Free(j)) => i == j,
        (Refl(a), Refl(b)) => c(a, b),
        (Pi(a1, b1), Pi(a2, b2))
        | (Lam(a1, b1), Lam(a2, b2))
        | (App(a1, b1), App(a2, b2))
        | (W(a1, b1), W(a2, b2))
        | (Sup(a1, b1), Sup(a2, b2))
        | (Sigma(a1, b1), Sigma(a2, b2)) => c(a1, a2) && c(b1, b2),
        (Id(a1, b1, c1), Id(a2, b2, c2)) | (Pair(a1, b1, c1), Pair(a2, b2, c2)) => c(a1, a2) && c(b1, b2) && c(c1, c2),
        (
            J { motive: m1, base: s1, a: a1, b: b1, p: p1 },
            J { motive: m2, base: s2, a: a2, b: b2, p: p2 },
        ) => c(m1, m2) && c(s1, s2) && c(a1, a2) && c(b1, b2) && c(p1, p2),
        (
            WRec { motive: m1, children_ty: c1, step: s1, target: t1 },
            WRec { motive: m2, children_ty: c2, step: s2, target: t2 },
        ) => c(m1, m2) && c(c1, c2) && c(s1, s2) && c(t1, t2),
        (SigRec { motive: m1, step: s1, target: t1 }, SigRec { motive: m2, step: s2, target: t2 }) => {
            c(m1, m2) && c(s1, s2) && c(t1, t2)
        }
        _ => false,
    }
}

impl Eq for Expr {}

thread_local! {
    /// What `Drop for Expr` swaps into a child slot it is about to free,
    /// so the child can be dropped inside `grow` rather than by the
    /// compiler-generated glue afterwards. Shared, so a swap is a refcount
    /// bump, not an allocation.
    static LEAF: Rc<Expr> = Rc::new(Expr::Sort(0));
}

/// Keeps dropping an `Expr` stack-safe. The compiler-generated drop glue
/// is recursive, and it runs wherever a term is discarded -- `whnf` throws
/// away a full intermediate term at every beta step -- so on whatever
/// stack segment is current, with only [`RED_ZONE`] guaranteed. Unguarded,
/// a 1,000-deep term reliably overflowed there.
///
/// The glue calls this at every level before recursing into that level's
/// fields, so a cheap [`stack_ok`] check is all most drops pay. Only when
/// the stack runs low does it move the children it would free
/// (`strong_count == 1`; a shared one just loses a reference, which
/// cannot recurse) out of their slots and drop them on a fresh segment.
/// During thread teardown, once `LEAF` is gone, this falls back to the
/// plain recursive glue.
impl Drop for Expr {
    fn drop(&mut self) {
        if stack_ok() {
            return;
        }
        let free = |c: &mut Rc<Expr>| {
            if Rc::strong_count(c) == 1
                && let Ok(leaf) = LEAF.try_with(Rc::clone)
            {
                drop(std::mem::replace(c, leaf));
            }
        };
        grow_slow(|| match self {
            Expr::Var(_) | Expr::Sort(_) | Expr::Const(_) | Expr::Free(_) => {}
            Expr::Refl(a) => free(a),
            Expr::Pi(a, b) | Expr::Lam(a, b) | Expr::App(a, b) | Expr::W(a, b) | Expr::Sup(a, b) | Expr::Sigma(a, b) => {
                free(a);
                free(b);
            }
            Expr::Id(a, b, c) | Expr::Pair(a, b, c) => {
                free(a);
                free(b);
                free(c);
            }
            Expr::J { motive, base, a, b, p } => {
                for c in [motive, base, a, b, p] {
                    free(c);
                }
            }
            Expr::WRec { motive, children_ty, step, target } => {
                for c in [motive, children_ty, step, target] {
                    free(c);
                }
            }
            Expr::SigRec { motive, step, target } => {
                for c in [motive, step, target] {
                    free(c);
                }
            }
        })
    }
}

/// `x` printed with `{:?}`, cut off after about 400 characters. A term is a DAG but prints as a tree,
/// so the full text of an error's terms can be exponentially large in the DAG's size (the rejection
/// of a false statement at n=12 spent 99% of its 11 s, and 2.4 GB, in formatting the message;
/// doc section 82). The writer fails once it is full, which stops the printer's recursion.
pub(crate) fn brief<T: fmt::Debug + ?Sized>(x: &T) -> String {
    const LIMIT: usize = 400;
    struct Limited(String);
    impl fmt::Write for Limited {
        fn write_str(&mut self, s: &str) -> fmt::Result {
            let room = LIMIT.saturating_sub(self.0.len());
            if s.len() > room {
                let mut cut = room;
                while !s.is_char_boundary(cut) {
                    cut -= 1;
                }
                self.0.push_str(&s[..cut]);
                return Err(fmt::Error);
            }
            self.0.push_str(s);
            Ok(())
        }
    }
    let mut out = Limited(String::new());
    if fmt::Write::write_fmt(&mut out, format_args!("{x:?}")).is_err() {
        out.0.push_str(" ...");
    }
    out.0
}

impl fmt::Debug for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        grow(|| match self {
            Expr::Var(k) => write!(f, "#{k}"),
            Expr::Sort(i) => write!(f, "Type{i}"),
            Expr::Const(l) => write!(f, "@{l}"),
            Expr::Free(l) => write!(f, "${l}"),
            Expr::Pi(a, b) => write!(f, "(Pi {a:?}. {b:?})"),
            Expr::Lam(a, b) => write!(f, "(\\{a:?}. {b:?})"),
            Expr::App(g, a) => write!(f, "({g:?} {a:?})"),
            Expr::Id(a, x, y) => write!(f, "(Id {a:?} {x:?} {y:?})"),
            Expr::Refl(a) => write!(f, "(refl {a:?})"),
            Expr::J { a, b, p, .. } => write!(f, "(J .. {a:?} {b:?} {p:?})"),
            Expr::W(a, b) => write!(f, "(W {a:?}. {b:?})"),
            Expr::Sup(a, g) => write!(f, "(sup {a:?} {g:?})"),
            Expr::WRec { target, .. } => write!(f, "(wrec .. {target:?})"),
            Expr::Sigma(a, b) => write!(f, "(Sigma {a:?}. {b:?})"),
            Expr::Pair(fam, a, b) => write!(f, "(pair {fam:?} {a:?} {b:?})"),
            Expr::SigRec { target, .. } => write!(f, "(sigrec .. {target:?})"),
        })
    }
}

// --- convenience constructors -------------------------------------------

pub fn var(k: u32) -> Expr {
    Expr::Var(k)
}
pub fn sort(i: u32) -> Expr {
    Expr::Sort(i)
}
/// While one is alive, terms built with this module's constructors (`app`, `lam`, `pi`, ...) and
/// the nodes `shift`/`instantiate` make are interned: structurally equal children are one node, so
/// a proof that repeats itself is a small DAG, and the checks run inside it (`check_in`, `infer_in`,
/// `def_eq`) find the terms already canonical. Hold one across building a proof and checking it.
/// Tables and memos live until the outermost one drops; without the `hashcons` feature it does
/// nothing. Per thread.
///
/// Worth it for large proofs and a loss for small ones: it halves the check and, at n=512, saves
/// half the time and memory of the whole build-and-check, but building inside it costs more per
/// node, so a proof that checks in well under a millisecond (the gcd proofs) is about 20% slower
/// overall (doc sections 69 and 71). `check_in` already interns large inputs by itself; this scope
/// is for proofs big enough that the builder's own sharing matters.
#[must_use]
pub struct InternScope(#[allow(dead_code)] hc::Scope);

impl InternScope {
    pub fn enter() -> InternScope {
        let s = hc::Scope::enter();
        hc::activate();
        InternScope(s)
    }
}

/// The constructors below make each child through `hc::intern_new`: inside an [`InternScope`] equal
/// children are one node, outside it is `Rc::new`.
pub fn pi(a: Expr, b: Expr) -> Expr {
    Expr::Pi(hc::intern_new(a), hc::intern_new(b))
}
pub fn lam(a: Expr, body: Expr) -> Expr {
    Expr::Lam(hc::intern_new(a), hc::intern_new(body))
}
pub fn app(f: Expr, a: Expr) -> Expr {
    Expr::App(hc::intern_new(f), hc::intern_new(a))
}
pub fn app2(f: Expr, a: Expr, b: Expr) -> Expr {
    app(app(f, a), b)
}
pub fn app3(f: Expr, a: Expr, b: Expr, c: Expr) -> Expr {
    app(app2(f, a, b), c)
}
pub fn id(a: Expr, x: Expr, y: Expr) -> Expr {
    Expr::Id(hc::intern_new(a), hc::intern_new(x), hc::intern_new(y))
}
pub fn refl(a: Expr) -> Expr {
    Expr::Refl(hc::intern_new(a))
}
pub fn jelim(motive: Expr, base: Expr, a: Expr, b: Expr, p: Expr) -> Expr {
    Expr::J {
        motive: hc::intern_new(motive),
        base: hc::intern_new(base),
        a: hc::intern_new(a),
        b: hc::intern_new(b),
        p: hc::intern_new(p),
    }
}
pub fn wty(a: Expr, b: Expr) -> Expr {
    Expr::W(hc::intern_new(a), hc::intern_new(b))
}
pub fn sup(a: Expr, f: Expr) -> Expr {
    Expr::Sup(hc::intern_new(a), hc::intern_new(f))
}
pub fn wrec(motive: Expr, children_ty: Expr, step: Expr, target: Expr) -> Expr {
    Expr::WRec {
        motive: hc::intern_new(motive),
        children_ty: hc::intern_new(children_ty),
        step: hc::intern_new(step),
        target: hc::intern_new(target),
    }
}
pub fn sigma(a: Expr, b: Expr) -> Expr {
    Expr::Sigma(hc::intern_new(a), hc::intern_new(b))
}
pub fn pair(fam: Expr, a: Expr, b: Expr) -> Expr {
    Expr::Pair(hc::intern_new(fam), hc::intern_new(a), hc::intern_new(b))
}
pub fn sigrec(motive: Expr, step: Expr, target: Expr) -> Expr {
    Expr::SigRec {
        motive: hc::intern_new(motive),
        step: hc::intern_new(step),
        target: hc::intern_new(target),
    }
}
/// A non-dependent function type `a -> b`.
pub fn arrow(a: Expr, b: Expr) -> Expr {
    pi(a, shift(&b, 0, 1))
}

// --- shifting & substitution (standard de Bruijn machinery) -------------

/// Add `amount` to every free variable at or above `cutoff`. Exposed
/// (beyond this module's own substitution machinery) for moving a term
/// under a new binder, e.g. the `cong` motives in `proof.rs`.
pub fn shift(e: &Expr, cutoff: u32, amount: i32) -> Expr {
    // Adding 0 changes no index, and a term whose loose variables all sit
    // below `cutoff` has none to change: either way `e` comes back as is.
    if amount == 0 || loose_of(e) <= cutoff {
        return e.clone();
    }
    shift_unchecked(e, cutoff, amount)
}

/// `shift` for an `e` already known to have a loose variable at or above
/// `cutoff` (and `amount != 0`).
fn shift_unchecked(e: &Expr, cutoff: u32, amount: i32) -> Expr {
    shift_via(e, cutoff, amount, &|x, c| shift_child(x, c, amount))
}

/// `shift_unchecked` with the shifting of each child done by `go`, which gets the child and the
/// cutoff for it.
fn shift_via(e: &Expr, cutoff: u32, amount: i32, go: &impl Fn(&Rc<Expr>, u32) -> Rc<Expr>) -> Expr {
    #[cfg(feature = "record-defeq")]
    let _hc_guard = hc_probe::shift_enter(e, cutoff, amount);
    walk_count(1);
    grow(|| match e {
        Expr::Var(k) => {
            if *k >= cutoff {
                Expr::Var((*k as i32 + amount) as u32)
            } else {
                Expr::Var(*k)
            }
        }
        Expr::Sort(i) => Expr::Sort(*i),
        Expr::Const(l) => Expr::Const(*l),
        Expr::Free(l) => Expr::Free(*l),
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
        Expr::Sigma(..) | Expr::Pair(..) | Expr::SigRec { .. } => shift_sigma_family(e, cutoff, go),
    })
}

/// `shift` of one child: the same `Rc` when it has nothing to shift.
fn shift_child(x: &Rc<Expr>, cutoff: u32, amount: i32) -> Rc<Expr> {
    if x.loose() <= cutoff {
        return x.clone();
    }
    if let Some(r) = hc::shift_get(x, cutoff, amount) {
        return r;
    }
    let e = shift_unchecked(x, cutoff, amount);
    // The largest loose variable sat at or above `cutoff`, so it moves by
    // exactly `amount`; `Free` levels don't change. (Saturated ranges
    // are recomputed.)
    let r = match x.loose() {
        u32::MAX => hc::intern(e, None),
        l => hc::intern(e, Some(((l as i64 + amount as i64) as u32, x.free()))),
    };
    hc::shift_put(x, cutoff, amount, &r);
    r
}

/// `shift`'s own `Sigma`/`Pair`/`SigRec` cases, out of line -- see
/// `infer_sigma`'s docs for why these extractions exist and why they
/// are kept.
#[inline(never)]
fn shift_sigma_family(e: &Expr, cutoff: u32, go: &impl Fn(&Rc<Expr>, u32) -> Rc<Expr>) -> Expr {
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

/// A source node and its copy.
type RcPair = (Rc<Expr>, Rc<Expr>);
/// (node address, cutoff, amount).
type ShiftKey = (usize, u32, i32);

/// Shifted copies already built, by (node, cutoff, amount), for builders that shift the same large
/// terms many times (`cong_n`): each node is then shifted once per (cutoff, amount) and the copies are
/// shared. Keeps the source nodes alive so a pointer is not reused for another node.
#[derive(Default)]
pub struct ShiftMemo(std::cell::RefCell<PtrMap<ShiftKey, RcPair>>);

/// [`shift`] through `memo`.
pub fn shift_memo(e: &Expr, cutoff: u32, amount: i32, memo: &ShiftMemo) -> Expr {
    if amount == 0 || loose_of(e) <= cutoff {
        return e.clone();
    }
    shift_via(e, cutoff, amount, &|x, c| shift_memo_child(x, c, amount, memo))
}

fn shift_memo_child(x: &Rc<Expr>, cutoff: u32, amount: i32, memo: &ShiftMemo) -> Rc<Expr> {
    if x.loose() <= cutoff {
        return x.clone();
    }
    let key = (Rc::as_ptr(x) as usize, cutoff, amount);
    if let Some((_, r)) = memo.0.borrow().get(&key) {
        return r.clone();
    }
    let r = hc::intern_new(shift_memo(x, cutoff, amount, memo));
    memo.0.borrow_mut().insert(key, (x.clone(), r.clone()));
    r
}

/// The hash-consing prototype (`hashcons` feature, bit-vector design doc section 60). While a
/// [`hc::Scope`] is open, `instantiate_n` and `shift_child` intern the nodes they build and
/// memoise their results; the table and memos are dropped with the outermost scope. A node is
/// interned under an exact key (constructor, leaf value, child pointers), so two nodes merge only
/// if structurally equal; ones built elsewhere simply stay distinct. With the feature off every
/// function here is a no-op that makes the callers behave as before.
#[cfg(feature = "hashcons")]
mod hc {
    use super::*;
    use std::cell::{Cell, RefCell};

    #[derive(PartialEq, Eq)]
    struct NodeKey {
        tag: u8,
        leaf: u32,
        kids: [usize; 5],
    }

    /// Folds the fields into six words (the derived impl also hashes the array's length and the tag
    /// on its own: eight mixing steps per lookup).
    impl std::hash::Hash for NodeKey {
        fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
            h.write_u64(((self.tag as u64) << 32) | self.leaf as u64);
            for k in self.kids {
                h.write_usize(k);
            }
        }
    }

    #[derive(Default)]
    struct Table {
        nodes: PtrMap<NodeKey, Rc<Expr>>,
        /// (source node, argument-set id, depth) -> (the source, kept alive; its instantiation).
        inst: PtrMap<(usize, u64, u32), RcPair>,
        shifts: PtrMap<ShiftKey, RcPair>,
        /// (node, depth, argument count) -> (the node, kept alive; whether it has a loose `Var` in
        /// `[depth, depth + count)`).
        uses: PtrMap<(usize, u32, u32), (Rc<Expr>, bool)>,
        /// Argument sets of two or more nodes, by their node pointers.
        arg_sets: HashMap<Vec<usize>, u64>,
    }

    /// Non-trivial `instantiate_n` calls in a scope before the table switches on: a small check
    /// would only pay for the table.
    #[cfg(test)]
    const WARM_UP: u32 = 0;
    #[cfg(not(test))]
    const WARM_UP: u32 = 3000;

    thread_local! {
        static TABLE: RefCell<Table> = RefCell::new(Table::default());
        static DEPTH: Cell<u32> = const { Cell::new(0) };
        static CALLS: Cell<u32> = const { Cell::new(0) };
        /// 0 until the table is on in this scope, then the scope's generation (never 0, never reused).
        static GENERATION: Cell<u32> = const { Cell::new(0) };
        static NEXT_GENERATION: Cell<u32> = const { Cell::new(1) };
    }

    pub struct Scope;

    impl Scope {
        pub fn enter() -> Scope {
            DEPTH.with(|d| d.set(d.get() + 1));
            Scope
        }
    }

    /// Switches the table on now (inside a scope), instead of after `WARM_UP` calls.
    pub fn activate() {
        if !active() {
            let g = NEXT_GENERATION.with(|g| g.replace(g.get() + 1));
            GENERATION.with(|c| c.set(g));
        }
    }

    pub fn intern_new(e: Expr) -> Rc<Expr> {
        intern(e, None)
    }

    impl Drop for Scope {
        fn drop(&mut self) {
            if DEPTH.with(|d| {
                d.set(d.get() - 1);
                d.get() == 0
            }) {
                GENERATION.with(|g| g.set(0));
                CALLS.with(|c| c.set(0));
                let old = TABLE.with(|t| std::mem::take(&mut *t.borrow_mut()));
                drop(old);
            }
        }
    }

    #[inline(always)]
    pub fn generation() -> u32 {
        GENERATION.with(|g| g.get())
    }

    #[inline(always)]
    fn active() -> bool {
        generation() != 0
    }

    /// Calls `f` on each child, in a fixed order per constructor.
    #[inline(always)]
    fn for_kids<'a>(e: &'a Expr, mut f: impl FnMut(&'a Rc<Expr>)) {
        match e {
            Expr::Var(_) | Expr::Sort(_) | Expr::Const(_) | Expr::Free(_) => {}
            Expr::Pi(a, b) | Expr::Lam(a, b) | Expr::App(a, b) | Expr::W(a, b) | Expr::Sup(a, b) | Expr::Sigma(a, b) => {
                f(a);
                f(b);
            }
            Expr::Refl(a) => f(a),
            Expr::Id(a, b, c) | Expr::Pair(a, b, c) | Expr::SigRec { motive: a, step: b, target: c } => {
                f(a);
                f(b);
                f(c);
            }
            Expr::J { motive, base, a, b, p } => {
                f(motive);
                f(base);
                f(a);
                f(b);
                f(p);
            }
            Expr::WRec { motive, children_ty, step, target } => {
                f(motive);
                f(children_ty);
                f(step);
                f(target);
            }
        }
    }

    /// The table's node for `e` (built with `ranges` when it is new and they are known), or a fresh
    /// one while the table is off.
    pub fn intern(e: Expr, ranges: Option<(u32, u32)>) -> Rc<Expr> {
        intern_as(e, |e| match ranges {
            Some((l, f)) => Rc::with_ranges(e, l, f),
            None => Rc::new(e),
        })
    }

    /// `intern`, with `build` making the node when the table has none for `e` (and while it is off).
    fn intern_as(e: Expr, build: impl FnOnce(Expr) -> Rc<Expr>) -> Rc<Expr> {
        let generation = generation();
        if generation == 0 {
            return build(e);
        }
        let (tag, leaf) = match &e {
            Expr::Var(k) => (0, *k),
            Expr::Sort(k) => (1, *k),
            Expr::Const(k) => (2, *k),
            Expr::Free(k) => (3, *k),
            Expr::Pi(..) => (4, 0),
            Expr::Lam(..) => (5, 0),
            Expr::App(..) => (6, 0),
            Expr::Id(..) => (7, 0),
            Expr::Refl(..) => (8, 0),
            Expr::J { .. } => (9, 0),
            Expr::W(..) => (10, 0),
            Expr::Sup(..) => (11, 0),
            Expr::WRec { .. } => (12, 0),
            Expr::Sigma(..) => (13, 0),
            Expr::Pair(..) => (14, 0),
            Expr::SigRec { .. } => (15, 0),
        };
        let mut kids = [0usize; 5];
        let mut i = 0;
        let mut canonical = true;
        for_kids(&e, |p| {
            kids[i] = Rc::as_ptr(p) as usize;
            i += 1;
            canonical &= p.canonical();
        });
        TABLE.with(|t| match t.borrow_mut().nodes.entry(NodeKey { tag, leaf, kids }) {
            hashbrown::hash_map::Entry::Occupied(o) => o.get().clone(),
            hashbrown::hash_map::Entry::Vacant(v) => {
                let n = build(e);
                if canonical {
                    n.0.generation.set(generation);
                }
                v.insert(n.clone());
                n
            }
        })
    }

    /// Terms larger than this many nodes (counted once per allocation) are interned on entry to a
    /// scope; smaller ones are left to the lazy switch-on. Unit tests intern every input.
    const LARGE: usize = if cfg!(test) { 0 } else { 3000 };

    /// Whether the terms reachable from `roots` have more than `limit` distinct nodes.
    fn exceeds(roots: &[&Expr], limit: usize) -> bool {
        let mut seen: PtrSet<usize> = PtrSet::default();
        let mut stack: Vec<&Expr> = roots.to_vec();
        while let Some(e) = stack.pop() {
            let mut kids: Vec<&Rc<Expr>> = Vec::new();
            for_kids(e, |p| kids.push(p));
            for p in kids {
                if seen.insert(Rc::as_ptr(p) as usize) {
                    if seen.len() > limit {
                        return true;
                    }
                    stack.push(p);
                }
            }
        }
        limit == 0 && !roots.is_empty()
    }

    /// `e` with each child replaced by `f` of it.
    fn map_kids(e: &Expr, f: &mut impl FnMut(&Rc<Expr>) -> Rc<Expr>) -> Expr {
        match e {
            Expr::Var(k) => Expr::Var(*k),
            Expr::Sort(k) => Expr::Sort(*k),
            Expr::Const(k) => Expr::Const(*k),
            Expr::Free(k) => Expr::Free(*k),
            Expr::Pi(a, b) => Expr::Pi(f(a), f(b)),
            Expr::Lam(a, b) => Expr::Lam(f(a), f(b)),
            Expr::App(a, b) => Expr::App(f(a), f(b)),
            Expr::W(a, b) => Expr::W(f(a), f(b)),
            Expr::Sup(a, b) => Expr::Sup(f(a), f(b)),
            Expr::Sigma(a, b) => Expr::Sigma(f(a), f(b)),
            Expr::Refl(a) => Expr::Refl(f(a)),
            Expr::Id(a, b, c) => Expr::Id(f(a), f(b), f(c)),
            Expr::Pair(a, b, c) => Expr::Pair(f(a), f(b), f(c)),
            Expr::SigRec { motive, step, target } => Expr::SigRec { motive: f(motive), step: f(step), target: f(target) },
            Expr::J { motive, base, a, b, p } => Expr::J { motive: f(motive), base: f(base), a: f(a), b: f(b), p: f(p) },
            Expr::WRec { motive, children_ty, step, target } => {
                Expr::WRec { motive: f(motive), children_ty: f(children_ty), step: f(step), target: f(target) }
            }
        }
    }

    fn canon(rc: &Rc<Expr>, memo: &mut HashMap<usize, Rc<Expr>>) -> Rc<Expr> {
        if rc.canonical() {
            return rc.clone();
        }
        let key = Rc::as_ptr(rc) as usize;
        if let Some(r) = memo.get(&key) {
            return r.clone();
        }
        let e = grow(|| map_kids(rc, &mut |c| canon(c, memo)));
        // Children all unchanged (leaves, or nodes whose children were already the table's): put this
        // node itself in the table instead of allocating its twin.
        let r = if same_shape(&e, rc, Rc::ptr_eq) {
            intern_as(e, |_| rc.clone())
        } else {
            intern(e, Some((rc.loose(), rc.free())))
        };
        memo.insert(key, r.clone());
        r
    }

    /// Whether `check_in`'s term and claim are large (the same bound that makes `canonical_inputs`
    /// intern them), so that it runs them on one big stack segment (`on_segment`).
    pub fn large(e: &Expr, expected: &Expr) -> bool {
        exceeds(&[e, expected], LARGE)
    }

    /// `check_in`'s term and claim, with every node under them interned when they are large, so the
    /// comparisons against types the checker builds (which are interned) meet canonical nodes on
    /// both sides. Small inputs are returned as they are.
    pub fn canonical_inputs(e: &Expr, expected: &Expr) -> (Expr, Expr) {
        if !active() {
            if DEPTH.with(|d| d.get()) == 0 || !exceeds(&[e, expected], LARGE) {
                return (e.clone(), expected.clone());
            }
            let g = NEXT_GENERATION.with(|g| g.replace(g.get() + 1));
            GENERATION.with(|c| c.set(g));
        }
        let mut memo = HashMap::new();
        let a = map_kids(e, &mut |c| canon(c, &mut memo));
        let b = map_kids(expected, &mut |c| canon(c, &mut memo));
        (a, b)
    }

    /// Whether `x` mentions a loose `Var` in `[d, d + m)`, i.e. whether instantiating `m` arguments
    /// at depth `d` can put any of them in. When it cannot, the result is `x` shifted down by `m`
    /// above `d + m`, whatever the arguments are. Memoised per (node, depth, count): at n=256 99% of
    /// the memo entries keyed by argument list were for such nodes (doc section 64).
    pub fn uses(x: &Rc<Expr>, d: u32, m: u32) -> bool {
        if x.loose() <= d {
            return false;
        }
        if let Expr::Var(k) = &**x {
            return *k < d + m;
        }
        let key = (Rc::as_ptr(x) as usize, d, m);
        if let Some(r) = TABLE.with(|t| t.borrow().uses.get(&key).map(|(_, r)| *r)) {
            return r;
        }
        let r = grow(|| {
            let mut found = false;
            let mut i = 0;
            for_kids(x, |c| {
                // Index of the child among its parent's, and whether that child sits under a binder.
                let under = match &**x {
                    Expr::Pi(..) | Expr::Lam(..) | Expr::W(..) | Expr::Sigma(..) => i == 1,
                    Expr::WRec { .. } => i == 1,
                    Expr::Pair(..) => i == 0,
                    _ => false,
                };
                i += 1;
                found = found || uses(c, d + under as u32, m);
            });
            found
        });
        TABLE.with(|t| t.borrow_mut().uses.insert(key, (x.clone(), r)));
        r
    }

    /// An id for the argument list: the interned node's address for one argument (even), an
    /// odd table id for several; 0 while the table is off (which it leaves after `WARM_UP` calls).
    pub fn args_id(args: &[&Expr]) -> u64 {
        if !active() {
            if DEPTH.with(|d| d.get()) == 0 {
                return 0;
            }
            let n = CALLS.with(|c| {
                c.set(c.get() + 1);
                c.get()
            });
            #[allow(clippy::absurd_extreme_comparisons)] // `WARM_UP` is 0 under test
            if n < WARM_UP {
                return 0;
            }
            let g = NEXT_GENERATION.with(|g| g.replace(g.get() + 1));
            GENERATION.with(|c| c.set(g));
        }
        let ptrs: Vec<usize> = args.iter().map(|a| Rc::as_ptr(&intern((*a).clone(), None)) as usize).collect();
        if let [p] = ptrs[..] {
            return p as u64;
        }
        TABLE.with(|t| {
            let mut t = t.borrow_mut();
            let next = 2 * t.arg_sets.len() as u64 + 1;
            *t.arg_sets.entry(ptrs).or_insert(next)
        })
    }

    pub fn inst_get(x: &Rc<Expr>, aid: u64, d: u32) -> Option<Rc<Expr>> {
        if aid == 0 {
            return None;
        }
        TABLE.with(|t| t.borrow().inst.get(&(Rc::as_ptr(x) as usize, aid, d)).map(|(_, r)| r.clone()))
    }

    pub fn inst_put(x: &Rc<Expr>, aid: u64, d: u32, r: &Rc<Expr>) {
        if aid != 0 {
            TABLE.with(|t| t.borrow_mut().inst.insert((Rc::as_ptr(x) as usize, aid, d), (x.clone(), r.clone())));
        }
    }

    pub fn shift_get(x: &Rc<Expr>, cutoff: u32, amount: i32) -> Option<Rc<Expr>> {
        if !active() {
            return None;
        }
        TABLE.with(|t| t.borrow().shifts.get(&(Rc::as_ptr(x) as usize, cutoff, amount)).map(|(_, r)| r.clone()))
    }

    pub fn shift_put(x: &Rc<Expr>, cutoff: u32, amount: i32, r: &Rc<Expr>) {
        if active() {
            TABLE.with(|t| t.borrow_mut().shifts.insert((Rc::as_ptr(x) as usize, cutoff, amount), (x.clone(), r.clone())));
        }
    }
}

#[cfg(not(feature = "hashcons"))]
mod hc {
    use super::*;

    pub struct Scope;

    impl Scope {
        #[inline(always)]
        pub fn enter() -> Scope {
            Scope
        }
    }

    #[inline(always)]
    pub fn activate() {}

    #[inline(always)]
    pub fn intern_new(e: Expr) -> Rc<Expr> {
        Rc::new(e)
    }

    #[inline(always)]
    pub fn intern(e: Expr, ranges: Option<(u32, u32)>) -> Rc<Expr> {
        match ranges {
            Some((l, f)) => Rc::with_ranges(e, l, f),
            None => Rc::new(e),
        }
    }
    #[inline(always)]
    pub fn large(_: &Expr, _: &Expr) -> bool {
        false
    }
    #[inline(always)]
    pub fn canonical_inputs(e: &Expr, expected: &Expr) -> (Expr, Expr) {
        (e.clone(), expected.clone())
    }
    #[inline(always)]
    pub fn uses(_: &Rc<Expr>, _: u32, _: u32) -> bool {
        true
    }
    #[inline(always)]
    pub fn args_id(_: &[&Expr]) -> u64 {
        0
    }
    #[inline(always)]
    pub fn inst_get(_: &Rc<Expr>, _: u64, _: u32) -> Option<Rc<Expr>> {
        None
    }
    #[inline(always)]
    pub fn inst_put(_: &Rc<Expr>, _: u64, _: u32, _: &Rc<Expr>) {}
    #[inline(always)]
    pub fn shift_get(_: &Rc<Expr>, _: u32, _: i32) -> Option<Rc<Expr>> {
        None
    }
    #[inline(always)]
    pub fn shift_put(_: &Rc<Expr>, _: u32, _: i32, _: &Rc<Expr>) {}
}

/// Beta-substitution: replace `Var(0)` in `body` (which lives one binder
/// deeper) with `s`, then discharge that binder. `s` is walked only where
/// `body` uses it, so not at all when `body` doesn't mention `Var(0)`:
/// `infer`'s `App` rule substitutes every argument into its function's
/// codomain, usually `Int`, and shifting the argument there cost a walk of
/// it per application (`RELATED_WORK.md` §50, §58).
fn subst_top(body: &Expr, s: &Expr) -> Expr {
    instantiate(body, s, 0)
}

/// `subst_top`'s substitution in one pass: under `d` binders of `e`,
/// `Var(d)` becomes `s` shifted past them, and `e`'s own free variables
/// above it drop by one for the discharged binder. Equal to substituting
/// `shift(s, 0, 1)` and then shifting the result by -1, but `s` is shifted
/// only where it's used, not at every binder crossed and again in the
/// result (`RELATED_WORK.md` §52).
///
/// A subterm with no loose variable at or above its depth is kept by
/// pointer.
fn instantiate(e: &Expr, s: &Expr, d: u32) -> Expr {
    instantiate_n(e, &[s], d)
}

/// `instantiate` for `args.len()` binders at once: `e` lives under that many binders, `args` are in
/// application order (so the last one is `Var(0)`), and the result is `e` with all of them
/// discharged. Equal to calling `subst_top` once per argument, outermost first, without building the
/// intermediate terms: each argument is shifted past the `d` binders it ends up under, and `e`'s own
/// free variables above the discharged ones drop by `args.len()`.
fn instantiate_n(e: &Expr, args: &[&Expr], d: u32) -> Expr {
    if loose_of(e) <= d {
        return e.clone();
    }
    inst_rec(e, args, hc::args_id(args), d)
}

/// `instantiate_n`'s recursion, with the argument list's id for the `hashcons` memo (0: none).
fn inst_rec(e: &Expr, args: &[&Expr], aid: u64, d: u32) -> Expr {
    #[cfg(feature = "record-defeq")]
    let _hc_guard = hc_probe::inst_enter(e, args, d);
    walk_count(0);
    let m = args.len() as u32;
    let go = |x: &Rc<Expr>, d: u32| {
        if x.loose() <= d {
            return x.clone();
        }
        if aid != 0 && x.loose() != u32::MAX && !hc::uses(x, d, m) {
            return shift_child(x, d + m, -(m as i32));
        }
        if let Some(r) = hc::inst_get(x, aid, d) {
            return r;
        }
        let r = if aid == 0 { Rc::new(inst_rec(x, args, aid, d)) } else { hc::intern(inst_rec(x, args, aid, d), None) };
        hc::inst_put(x, aid, d, &r);
        r
    };
    grow(|| match e {
        Expr::Var(k) => {
            if *k >= d + m {
                Expr::Var(*k - m)
            } else if *k >= d {
                let arg = args[(m - 1 - (*k - d)) as usize];
                // Probe slots: 5 uses, 6 at depth 0, 7 deeper with a closed argument, 8 deeper with
                // loose variables, 9 `shift` visits those last uses cost.
                walk_count(5);
                if d == 0 {
                    walk_count(6);
                } else if loose_of(arg) == 0 {
                    walk_count(7);
                } else {
                    walk_count(8);
                }
                #[cfg(feature = "record-defeq")]
                let v0 = WALKS.with(|w| w[1].get());
                let r = shift(arg, 0, d as i32);
                #[cfg(feature = "record-defeq")]
                if d > 0 && loose_of(arg) > 0 {
                    // Slots 10/11: uses whose argument mentions a binder `conv` opened (internal) or
                    // only the checker's context; 12/13 the shift visits each class cost.
                    let k = INTERNAL.with(|c| c.get());
                    let internal = (0..k).any(|i| is_var_free(arg, i));
                    let cost = WALKS.with(|w| w[1].get()) - v0;
                    // Slots 15/16: distinct (argument, depth) pairs within one `def_eq` and the shift
                    // visits they cost, i.e. what a per-query shift memo would still pay.
                    let fresh = SEEN.with(|m| m.borrow_mut().insert((arg as *const Expr, d)));
                    WALKS.with(|w| {
                        if fresh {
                            w[15].set(w[15].get() + 1);
                            w[16].set(w[16].get() + cost);
                        }
                        w[9].set(w[9].get() + cost);
                        let (n, c) = if internal { (10, 12) } else { (11, 13) };
                        w[n].set(w[n].get() + 1);
                        w[c].set(w[c].get() + cost);
                    });
                }
                r
            } else {
                Expr::Var(*k)
            }
        }
        Expr::Sort(i) => Expr::Sort(*i),
        Expr::Const(l) => Expr::Const(*l),
        Expr::Free(l) => Expr::Free(*l),
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

#[cfg(feature = "record-defeq")]
fn instantiate_memo(e: &Expr, args: &[&Expr], d: u32, memo: &std::cell::RefCell<HashMap<(*const Expr, u32), Rc<Expr>>>) -> Expr {
    if loose_of(e) <= d {
        return e.clone();
    }
    walk_count(0);
    let m = args.len() as u32;
    let go = |x: &Rc<Expr>, d: u32| {
        if x.loose() <= d {
            return x.clone();
        }
        let key = (Rc::as_ptr(x), d);
        if let Some(r) = memo.borrow().get(&key) {
            return r.clone();
        }
        let r = Rc::new(instantiate_memo(x, args, d, memo));
        memo.borrow_mut().insert(key, r.clone());
        r
    };
    grow(|| match e {
        Expr::Var(k) => {
            if *k >= d + m {
                Expr::Var(*k - m)
            } else if *k >= d {
                shift(args[(m - 1 - (*k - d)) as usize], 0, d as i32)
            } else {
                Expr::Var(*k)
            }
        }
        Expr::Sort(i) => Expr::Sort(*i),
        Expr::Const(l) => Expr::Const(*l),
        Expr::Free(l) => Expr::Free(*l),
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

/// Whether `Var(idx)` occurs free in `e`, tracking binder depth through
/// every variant exactly as `shift`/`subst` do (one more binder crosses
/// under `Pi`/`Lam`/`W`'s second field/`WRec`'s `children_ty`/`Sigma`'s
/// second field/`Pair`'s `fam`, none elsewhere). Used by `Sup`'s typing
/// rule (see its own doc and the `infer` arm below) to *enforce*, not
/// merely assume, the documented requirement that a `Sup`'s codomain not
/// actually depend on `f`'s own bound argument: without this check,
/// `subst_top(cod, a)` is only ever validated at the one concrete `a`
/// this particular `Sup` term happens to use, silently trusting -- with
/// nothing to back it up -- that every other point of `f`'s domain
/// agrees on the same `W(A,B)`.
///
/// A subterm whose cached range shows no variable at or above idx isn't
/// walked.
fn is_var_free(e: &Expr, idx: u32) -> bool {
    if loose_of(e) <= idx {
        return false;
    }
    grow(|| match e {
        Expr::Var(k) => *k == idx,
        Expr::Sort(_) | Expr::Const(_) | Expr::Free(_) => false,
        Expr::Pi(a, b) => is_var_free(a, idx) || is_var_free(b, idx + 1),
        Expr::Lam(a, b) => is_var_free(a, idx) || is_var_free(b, idx + 1),
        Expr::App(f, a) => is_var_free(f, idx) || is_var_free(a, idx),
        Expr::Id(a, x, y) => is_var_free(a, idx) || is_var_free(x, idx) || is_var_free(y, idx),
        Expr::Refl(a) => is_var_free(a, idx),
        Expr::J { motive, base, a, b, p } => {
            is_var_free(motive, idx) || is_var_free(base, idx) || is_var_free(a, idx) || is_var_free(b, idx) || is_var_free(p, idx)
        }
        Expr::W(a, b) => is_var_free(a, idx) || is_var_free(b, idx + 1),
        Expr::Sup(a, f) => is_var_free(a, idx) || is_var_free(f, idx),
        Expr::WRec { motive, children_ty, step, target } => {
            is_var_free(motive, idx) || is_var_free(children_ty, idx + 1) || is_var_free(step, idx) || is_var_free(target, idx)
        }
        Expr::Sigma(a, b) => is_var_free(a, idx) || is_var_free(b, idx + 1),
        Expr::Pair(fam, a, b) => is_var_free(fam, idx + 1) || is_var_free(a, idx) || is_var_free(b, idx),
        Expr::SigRec { motive, step, target } => is_var_free(motive, idx) || is_var_free(step, idx) || is_var_free(target, idx),
    })
}

/// `infer`'s own `Sup` arm's error-message formatting, out of line and
/// `#[cold]` -- an error path, kept off `infer`'s hot frame (see
/// `infer_sigma`).
#[cold]
#[inline(never)]
fn sup_codomain_depends_on_own_argument(cod_nf: &Expr) -> String {
    format!("sup: children function's codomain must not depend on its own argument: {}", brief(cod_nf))
}

/// The error for a `Free` reaching the type checker, out of line and
/// `#[cold]` (see `infer_sigma`).
#[cold]
#[inline(never)]
fn free_escaped(l: u32) -> String {
    format!("free parameter ${l} escaped its scope")
}

// --- reduction ------------------------------------------------------------
//
// `whnf`/`nf` are memoized within one top-level call (not across calls --
// see `ReductionCache`'s own docs for why, and for the cross-call sharing
// this deliberately leaves on the table). This is always sound regardless
// of typing context, since reduction never consults one -- unlike a
// hypothetical cache for `infer`/`check` themselves, which would need to
// be keyed on more than just `Expr` identity to stay correct (the same
// subterm can mean different things under different contexts), memoizing
// pure reduction has no such caveat.

/// Caches `whnf`/`nf` results for one top-level call, keyed by the `Rc`
/// pointer identity of the subterm being reduced (see [`PtrKey`]). Two
/// *equal but independently-allocated* subterms are still cache-distinct
/// (this is sharing, not hash-consing) -- but a subterm that's genuinely
/// the same `Rc` allocation, reached from several places while reducing one
/// larger term (exactly what happens once a proof term embeds the same
/// subterm or `cong_n` argument in multiple positions), is
/// normalized once and reused everywhere else it's referenced, instead of
/// being re-walked -- and, for `whnf` specifically, potentially
/// re-beta-reduced, which is where repeated-substitution cost actually
/// lives -- from scratch at every occurrence.
#[derive(Default)]
struct ReductionCache {
    whnf: PtrMap<PtrKey, Rc<Expr>>,
    nf: PtrMap<PtrKey, Expr>,
    /// Pairs `def_eq` found syntactically unequal; see [`eq_noting`].
    unequal: PtrSet<(PtrKey, PtrKey)>,
}

/// Hashes the integers a [`PtrKey`] key is made of (a pointer, a context id) by multiply and
/// rotate, with no per-map random seed: every `def_eq` call builds a `ReductionCache`, most of
/// them for a comparison that ends at `==` without inserting anything, and seeding three hashers
/// for each showed as 4% of a whole check (bit-vector design doc §47). The
/// keys are the checker's own pointers, not attacker-chosen input, so there is nothing for a
/// random seed to defend.
#[derive(Default, Clone, Copy)]
struct PtrHasher(u64);
impl std::hash::Hasher for PtrHasher {
    fn finish(&self) -> u64 {
        self.0.rotate_left(26)
    }
    fn write(&mut self, bytes: &[u8]) {
        for b in bytes {
            self.write_u64(*b as u64);
        }
    }
    fn write_u64(&mut self, x: u64) {
        self.0 = (self.0.rotate_left(5) ^ x).wrapping_mul(0x517c_c1b7_2722_0a95);
    }
    fn write_u32(&mut self, x: u32) {
        self.write_u64(x as u64);
    }
    fn write_usize(&mut self, x: usize) {
        self.write_u64(x as u64);
    }
}
type PtrMap<K, V> = HashMap<K, V, std::hash::BuildHasherDefault<PtrHasher>>;
type PtrSet<K> = HashSet<K, std::hash::BuildHasherDefault<PtrHasher>>;

/// `infer`'s memo for one public `infer` or `check` call (`RELATED_WORK.md`
/// §63). A context is named by an id: 0 is the caller's, and entering a
/// binder whose type is the `Rc` `a` from context `cid` gives the id
/// interned for `(cid, a)`. Equal ids then mean the same sequence of binder
/// types, which, with the node, is all `infer`'s answer depends on within
/// one call -- it also depends on `g`, but that's sound because a cache
/// lives only for the one `infer_in`/`check_in` call that made it, and `g`
/// is fixed for that whole call. Keys hold their `Rc`s (`PtrKey`), so no
/// address is reused within the call.
#[derive(Default)]
struct InferCache {
    types: PtrMap<(PtrKey, u32), Expr>,
    contexts: PtrMap<(u32, PtrKey), u32>,
    next: u32,
    /// For each context id, (parent id, binder type pointer, that type's loose range); a binder with
    /// no type of the term (`fresh`) has loose range `u32::MAX`.
    info: Vec<(u32, usize, u32)>,
    /// Interned windows of binder types, outermost first: (window id of the outer part, pointer of
    /// the next binder type inward) to the window's id. 0 is the empty window.
    windows: PtrMap<(u32, usize), u32>,
    /// Probe: (node pointer, signature of the bindings it can depend on) seen so far.
    #[cfg(feature = "record-defeq")]
    relaxed: std::collections::HashSet<(usize, u64)>,
}

impl InferCache {
    /// The id of context `cid` extended by a binder of type `a`.
    fn enter(&mut self, cid: u32, a: &Rc<Expr>) -> u32 {
        walk_count(21);
        let next = &mut self.next;
        let info = &mut self.info;
        *self.contexts.entry((cid, PtrKey(a.clone()))).or_insert_with(|| {
            *next += 1;
            if info.len() <= *next as usize {
                info.resize(*next as usize + 1, (0, 0, 0));
            }
            info[*next as usize] = (cid, Rc::as_ptr(a) as usize, a.loose());
            *next
        })
    }

    /// An id no other context has: for a binder type that isn't an `Rc`
    /// of the term, like a `Pair`'s inferred first component.
    fn fresh(&mut self) -> u32 {
        self.next += 1;
        if self.info.len() <= self.next as usize {
            self.info.resize(self.next as usize + 1, (0, 0, 0));
        }
        self.info[self.next as usize] = (0, 0, u32::MAX);
        self.next
    }

    /// The id `infer_rc` keys its memo by for node `e` in context `cid`: the interned window of
    /// the innermost binder types `e` can depend on, instead of the whole context. `e`'s loose range
    /// says how many binders it mentions; each of those binders' types may mention outer binders in
    /// turn, so the window grows to cover them (a type with loose range `m` at position `p`, counted
    /// from the innermost, reaches binder `p + m`). Inside that window nothing else is consulted:
    /// `infer` looks up only variables of `e`, and a lookup's answer is that binder's type shifted,
    /// whose own variables are in the window by construction. So two contexts with the same window
    /// give `e` the same answer, in the same variable numbering (indices count from the innermost
    /// binder either way). Window ids have the top bit set, so they never meet a whole-context id.
    /// Falls back to `cid` when the window would pass a binder the term doesn't name (`fresh`), run
    /// past the call's own binders into the caller's context, or exceed `MAX_WINDOW`.
    fn memo_context(&mut self, cid: u32, e: &Expr) -> u32 {
        const WINDOW_BIT: u32 = 1 << 31;
        const MAX_WINDOW: usize = 8;
        let mut need = loose_of(e) as usize;
        if need == 0 {
            return WINDOW_BIT;
        }
        let mut ptrs = [0usize; MAX_WINDOW];
        let mut c = cid;
        let mut p = 0;
        while p < need {
            if c == 0 || p >= MAX_WINDOW {
                return cid;
            }
            let (parent, ptr, loose) = self.info[c as usize];
            if loose == u32::MAX {
                return cid;
            }
            ptrs[p] = ptr;
            if loose > 0 {
                need = need.max(p + 1 + loose as usize);
            }
            c = parent;
            p += 1;
        }
        let mut wid = 0;
        for &ptr in ptrs[..need].iter().rev() {
            let next = self.windows.len() as u32 + 1;
            wid = *self.windows.entry((wid, ptr)).or_insert(next);
        }
        WINDOW_BIT | wid
    }

    /// Probe: a signature of the innermost bindings `e` can depend on in context `cid` (the loose
    /// range of `e`, closed over the loose ranges of those bindings' own types), and how many that
    /// is.
    #[cfg(feature = "record-defeq")]
    fn relevant_signature(&self, cid: u32, e: &Expr) -> (u64, u32) {
        let mut chain: Vec<(usize, u32)> = Vec::new();
        let mut c = cid;
        while c != 0 {
            let (parent, ptr, loose) = self.info[c as usize];
            chain.push((ptr, loose));
            c = parent;
        }
        let mut need = loose_of(e) as usize;
        let mut p = 0;
        while p < need && p < chain.len() {
            let m = chain[p].1;
            if m == u32::MAX {
                need = chain.len();
            } else {
                need = need.max(p + 1 + m as usize);
            }
            p += 1;
        }
        let take = need.min(chain.len());
        let mut h: u64 = 0xcbf2_9ce4_8422_2325;
        for &(ptr, _) in &chain[..take] {
            h = (h ^ ptr as u64).wrapping_mul(0x100_0000_01b3);
        }
        h ^= (need > chain.len()) as u64;
        (h, take as u32)
    }
}

/// Wraps an `Rc<Expr>` for use as a `HashMap` key by *pointer* identity
/// (`Rc::ptr_eq`/`Rc::as_ptr`), not `Expr`'s own structural `PartialEq`/
/// `Hash` (which aren't even derived for `Rc` fields the way you'd get "two
/// equal trees hash equal" -- pointer identity is deliberately what we
/// want here: a cache hit should mean "the literal same allocation was
/// already reduced," not "an equal one was"). Holds the `Rc` itself, not
/// just its address, so the entry keeps that allocation alive for as long
/// as it's in the cache -- without that, a freed node's address could be
/// reused by an unrelated later allocation within the same top-level call,
/// turning a cache lookup into a false hit against the wrong `Expr`.
struct PtrKey(Rc<Expr>);
impl PartialEq for PtrKey {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}
impl Eq for PtrKey {}
impl std::hash::Hash for PtrKey {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        (Rc::as_ptr(&self.0) as usize).hash(state);
    }
}

/// Weak head normal form: reduce only the outermost redex chain.
pub fn whnf(e: &Expr) -> Expr {
    whnf_impl(e, &mut ReductionCache::default())
}

fn whnf_impl(e: &Expr, cache: &mut ReductionCache) -> Expr {
    whnf_step(e, cache).unwrap_or_else(|| e.clone())
}

/// `whnf_step` for an application spine `h a1 ... ak` (`k >= 2`) whose head reduces to a lambda:
/// peel as many directly nested lambdas as there are arguments and substitute all of them in one
/// `instantiate_n` pass, instead of one `subst_top` per argument, each rebuilding the body the next
/// one rebuilds again. Arguments left over are applied to the result. `None` when the head is not a
/// lambda, so the caller's one-argument path runs unchanged (and keeps a stuck spine's per-prefix
/// cache entries).
fn beta_spine(e: &Expr, cache: &mut ReductionCache) -> Option<Expr> {
    let mut args: Vec<&Rc<Expr>> = Vec::new();
    let mut head = e;
    while let Expr::App(g, b) = head {
        args.push(b);
        head = g;
    }
    args.reverse();
    let wh = whnf_rc(&Rc::new(head.clone()), cache);
    let Expr::Lam(_, first) = &*wh else { return None };
    let mut body: &Expr = first;
    let mut taken = 1;
    while taken < args.len()
        && let Expr::Lam(_, inner) = body
    {
        body = inner;
        taken += 1;
    }
    #[cfg(feature = "record-defeq")]
    BETAS.with(|c| c.set(c.get() + taken as u64));
    let subst: Vec<&Expr> = args[..taken].iter().map(|a| &***a).collect();
    let mut r = instantiate_n(body, &subst, 0);
    for a in &args[taken..] {
        r = Expr::App(Rc::new(r), (*a).clone());
    }
    Some(whnf_impl(&r, cache))
}

/// `whnf`, or `None` when `e` is already in weak head normal form. A stuck
/// term keeps its allocations: its arguments' and also its stuck head's or
/// target's. `ReductionCache` is keyed by pointer, so a copy misses it,
/// and each level of a stuck spine then reduced the whole spine below it
/// again (`RELATED_WORK.md` §48, §59).
fn whnf_step(e: &Expr, cache: &mut ReductionCache) -> Option<Expr> {
    #[cfg(feature = "record-defeq")]
    let _hc_guard = hc_probe::whnf_enter(e);
    grow(|| match e {
        Expr::App(f, a) => {
            if matches!(&**f, Expr::App(..))
                && let Some(r) = beta_spine(e, cache)
            {
                return Some(r);
            }
            let wf = whnf_rc(f, cache);
            match &*wf {
                Expr::Lam(_, body) => {
                    #[cfg(feature = "record-defeq")]
                    BETAS.with(|c| c.set(c.get() + 1));
                    let r = subst_top(body, a);
                    Some(whnf_impl(&r, cache))
                }
                _ => (!Rc::ptr_eq(&wf, f)).then(|| Expr::App(wf, a.clone())),
            }
        }
        Expr::J {
            motive,
            base,
            a,
            b,
            p,
        } => {
            let wp = whnf_rc(p, cache);
            match &*wp {
                Expr::Refl(_) => Some(whnf_impl(&Expr::App(base.clone(), a.clone()), cache)),
                _ => (!Rc::ptr_eq(&wp, p)).then(|| Expr::J {
                    motive: motive.clone(),
                    base: base.clone(),
                    a: a.clone(),
                    b: b.clone(),
                    p: wp,
                }),
            }
        }
        Expr::WRec {
            motive,
            children_ty,
            step,
            target,
        } => {
            let wt = whnf_rc(target, cache);
            match &*wt {
                Expr::Sup(a, f) => {
                    // step a f (\y:B(a). wrec(motive, children_ty, step, f y))
                    // -- `subst_top(children_ty, a)` gives the induction-
                    // hypothesis closure its *honest* domain (`B(a)`, the same
                    // `Sup`'s own typing rule requires of `f`'s domain), not
                    // an inert placeholder -- see `Expr::WRec`'s own doc for
                    // why this field exists at all.
                    let rec_step = lam(
                        subst_top(children_ty, a),
                        wrec(
                            shift(motive, 0, 1),
                            // `children_ty` is already "one binder deeper" than
                            // `motive`/`step`/`target` (`W`'s own convention for
                            // its second field) -- inserting the new `y` binder
                            // below that existing one needs `cutoff + 1`, the
                            // same bump `Expr::W`'s own `shift`/`subst` arms use
                            // for their own second field.
                            shift(children_ty, 1, 1),
                            shift(step, 0, 1),
                            app(shift(f, 0, 1), var(0)),
                        ),
                    );
                    Some(whnf_impl(
                        &Expr::App(Rc::new(Expr::App(Rc::new(Expr::App(step.clone(), a.clone())), f.clone())), Rc::new(rec_step)),
                        cache,
                    ))
                }
                _ => (!Rc::ptr_eq(&wt, target)).then(|| Expr::WRec {
                    motive: motive.clone(),
                    children_ty: children_ty.clone(),
                    step: step.clone(),
                    target: wt,
                }),
            }
        }
        Expr::SigRec { motive, step, target } => whnf_sigrec(motive, step, target, cache),
        _ => None,
    })
}

/// `whnf_step`'s own `SigRec` case, out of line -- see `infer_sigma`.
#[inline(never)]
fn whnf_sigrec(motive: &Rc<Expr>, step: &Rc<Expr>, target: &Rc<Expr>, cache: &mut ReductionCache) -> Option<Expr> {
    let wt = whnf_rc(target, cache);
    match &*wt {
        Expr::Pair(_, a, b) => Some(whnf_impl(&Expr::App(Rc::new(Expr::App(step.clone(), a.clone())), b.clone()), cache)),
        _ => (!Rc::ptr_eq(&wt, target)).then(|| Expr::SigRec {
            motive: motive.clone(),
            step: step.clone(),
            target: wt,
        }),
    }
}

/// `whnf`, cached, for a child already held as `Rc<Expr>` (a struct field)
/// -- exactly the position where the same subterm recurs many times within
/// one top-level call once a proof term shares structure. Returns `e`
/// itself when it is already in weak head normal form, so reducing a
/// result again, as `nf` and `def_eq` do with a stuck head, keeps its
/// pointer and hits the cache from then on.
fn whnf_rc(e: &Rc<Expr>, cache: &mut ReductionCache) -> Rc<Expr> {
    let key = PtrKey(e.clone());
    if let Some(hit) = cache.whnf.get(&key) {
        return hit.clone();
    }
    let result = whnf_step(e, cache).map_or_else(|| e.clone(), Rc::new);
    cache.whnf.insert(key, result.clone());
    result
}

/// Full normal form: `whnf`, then recurse structurally into subterms.
fn nf(e: &Expr) -> Expr {
    nf_impl(e, &mut ReductionCache::default())
}

fn nf_impl(e: &Expr, cache: &mut ReductionCache) -> Expr {
    nf_whnf(&whnf_impl(e, cache), cache)
}

/// `nf` of a term already in weak head normal form: its constructor over
/// the `nf` of each child.
fn nf_whnf(w: &Expr, cache: &mut ReductionCache) -> Expr {
    walk_count(4);
    grow(|| match w {
        Expr::Var(k) => Expr::Var(*k),
        Expr::Sort(i) => Expr::Sort(*i),
        Expr::Const(l) => Expr::Const(*l),
        Expr::Free(l) => Expr::Free(*l),
        Expr::Pi(a, b) => pi(nf_rc(a, cache), nf_rc(b, cache)),
        Expr::Lam(a, b) => lam(nf_rc(a, cache), nf_rc(b, cache)),
        Expr::App(f, a) => app(nf_rc(f, cache), nf_rc(a, cache)),
        Expr::Id(a, x, y) => id(nf_rc(a, cache), nf_rc(x, cache), nf_rc(y, cache)),
        Expr::Refl(a) => refl(nf_rc(a, cache)),
        Expr::J {
            motive,
            base,
            a,
            b,
            p,
        } => jelim(nf_rc(motive, cache), nf_rc(base, cache), nf_rc(a, cache), nf_rc(b, cache), nf_rc(p, cache)),
        Expr::W(a, b) => wty(nf_rc(a, cache), nf_rc(b, cache)),
        Expr::Sup(a, f) => sup(nf_rc(a, cache), nf_rc(f, cache)),
        Expr::WRec {
            motive,
            children_ty,
            step,
            target,
        } => wrec(nf_rc(motive, cache), nf_rc(children_ty, cache), nf_rc(step, cache), nf_rc(target, cache)),
        other @ (Expr::Sigma(..) | Expr::Pair(..) | Expr::SigRec { .. }) => nf_sigma_family(other, cache),
    })
}

/// `nf_impl`'s own `Sigma`/`Pair`/`SigRec` cases, out of line -- see
/// `shift_sigma_family`'s own docs for why.
#[inline(never)]
fn nf_sigma_family(e: &Expr, cache: &mut ReductionCache) -> Expr {
    match e {
        Expr::Sigma(a, b) => sigma(nf_rc(a, cache), nf_rc(b, cache)),
        Expr::Pair(fam, a, b) => pair(nf_rc(fam, cache), nf_rc(a, cache), nf_rc(b, cache)),
        Expr::SigRec { motive, step, target } => sigrec(nf_rc(motive, cache), nf_rc(step, cache), nf_rc(target, cache)),
        _ => unreachable!("nf_sigma_family called on a non-Sigma-family Expr"),
    }
}

fn nf_rc(e: &Rc<Expr>, cache: &mut ReductionCache) -> Expr {
    let key = PtrKey(e.clone());
    if let Some(hit) = cache.nf.get(&key) {
        return hit.clone();
    }
    let w = whnf_rc(e, cache);
    let result = nf_whnf(&w, cache);
    cache.nf.insert(key, result.clone());
    result
}

/// `nf(a) == nf(b)`, decided without computing either normal form, and
/// sharing one [`ReductionCache`] across both sides -- worthwhile whenever
/// `a`/`b` reference overlapping subterms, which two sides of a proof
/// obligation very often do (the same postulates, the same sub-witnesses).
pub fn def_eq(a: &Expr, b: &Expr) -> bool {
    let _hc = hc::Scope::enter();
    #[cfg(feature = "record-defeq")]
    let _g = site(3);
    #[cfg(feature = "record-defeq")]
    SEEN.with(|m| m.borrow_mut().clear());
    conv(a, b, &mut ReductionCache::default())
}

/// `def_eq`'s comparison. Syntactically equal sides are equal without
/// reducing, since `nf` is a function; most calls from `infer` are
/// (`RELATED_WORK.md` §56), and `==` stops at the first difference
/// otherwise. Else `nf(e)` is `whnf(e)`'s outermost constructor over the
/// `nf` of each child, so the normal forms are equal exactly when the two
/// weak head normal forms have the same constructor and pairwise equal
/// children's normal forms. Recursing on that reduces only where the
/// sides differ (`RELATED_WORK.md` §57).
fn conv(a: &Expr, b: &Expr, cache: &mut ReductionCache) -> bool {
    if std::ptr::eq(a, b) || eq_noting(a, b, &mut cache.unequal) {
        return true;
    }
    conv_whnf(&whnf_impl(a, cache), &whnf_impl(b, cache), cache)
}

/// `conv` for children held as `Rc<Expr>`, so `whnf` is cached. A pair
/// an earlier `==` found unequal skips `==`.
fn conv_rc(a: &Rc<Expr>, b: &Rc<Expr>, cache: &mut ReductionCache) -> bool {
    if Rc::ptr_eq(a, b) {
        return true;
    }
    let noted = cache.unequal.contains(&(PtrKey(a.clone()), PtrKey(b.clone())));
    if !noted && eq_noting(a, b, &mut cache.unequal) {
        return true;
    }
    conv_whnf(&whnf_rc(a, cache), &whnf_rc(b, cache), cache)
}

/// Compares two weak head normal forms: same constructor, then `conv` on
/// each pair of children, in the order `nf_impl` visits them.
fn conv_whnf(x: &Expr, y: &Expr, cache: &mut ReductionCache) -> bool {
    #[cfg(feature = "record-defeq")]
    let _hc_guard = hc_probe::conv_enter(x, y);
    walk_count(3);
    #[cfg(feature = "record-defeq")]
    {
        // Probe: track how many binders `conv` has opened (by comparing bodies without
        // instantiating them), so a loose variable in a substituted argument can be told apart as
        // internal or a reference to the checker's context.
        let mut idx = 0;
        let under = match x {
            Expr::Pi(..) | Expr::Lam(..) | Expr::W(..) | Expr::Sigma(..) => 1,
            Expr::Pair(..) | Expr::WRec { .. } => 1,
            _ => usize::MAX,
        };
        let x_pair = matches!(x, Expr::Pair(..));
        return grow(|| {
            same_shape(x, y, |p, q| {
                let opens = if x_pair { idx == 0 } else { idx == under };
                idx += 1;
                if opens {
                    walk_count(14);
                    INTERNAL.with(|c| c.set(c.get() + 1));
                }
                let r = conv_rc(p, q, cache);
                if opens {
                    INTERNAL.with(|c| c.set(c.get() - 1));
                }
                r
            })
        });
    }
    #[cfg(not(feature = "record-defeq"))]
    grow(|| same_shape(x, y, |p, q| conv_rc(p, q, cache)))
}

/// `a == b`, noting in `unequal` each pair of children found unequal on
/// the way. `conv` recurses into exactly those pairs next, and without the
/// note each would repeat the walk below it: quadratic on a chain that
/// differs only at the bottom (`RELATED_WORK.md` §61).
fn eq_noting(a: &Expr, b: &Expr, unequal: &mut PtrSet<(PtrKey, PtrKey)>) -> bool {
    walk_count(2);
    grow(|| {
        same_shape(a, b, |p, q| {
            Rc::ptr_eq(p, q) || (!(p.canonical() && q.canonical()) && eq_noting(p, q, unequal)) || {
                unequal.insert((PtrKey(p.clone()), PtrKey(q.clone())));
                false
            }
        })
    })
}

pub fn normalize(e: &Expr) -> Expr {
    nf(e)
}

// --- typechecking -----------------------------------------------------

/// The typing context `infer`/`check` thread through every recursive call,
/// growing by one entry per binder entered (`Pi`/`Lam`/`Sigma`/`Pair`) and
/// shrinking back via `truncate` on the way out. A plain `Vec<Expr>` would
/// make each of those binder-entry sites pay an O(current length) clone --
/// negligible for a shallow context, but this kernel's own deeply-recursive
/// callers (`eval_dyn`'s per-instance proof search in particular) can
/// legitimately build up nontrivial context depth, turning that into
/// O(depth^2) total work across one recursive descent. `im::Vector` gives
/// the same by-value, append/truncate-at-the-end API `Ctx`'s callers
/// already use, but backed by structural sharing: `.clone()` and
/// `.push_back()` are both O(log n) (amortized ~O(1) in practice) instead
/// of O(n), so this cost disappears without changing any call site's own
/// control flow.
pub type Ctx = im::Vector<Expr>;

/// The global environment: constant `l`'s type is `globals[l]`, closed, so
/// no binder or later global changes what it means. Kept apart from
/// [`Ctx`], the kernel's own binders, so a `Const` can never resolve to
/// one: with a single vector, `(λx:A. Const(L)) a` would reduce to a
/// `Const(L)` that no longer refers to anything.
///
/// Trusted like `Ctx`: nothing checks that an entry is a type, and a
/// constant is an axiom.
pub type Globals = im::Vector<Expr>;

/// The checker's working context: the caller's `base` plus the binders
/// entered since, in a plain `Vec` pushed and truncated in place. Cloning
/// and pushing an `im::Vector` at every binder copies a shared tail
/// (about 15% of samples on the bit-vector lemma); `base` is cloned once
/// per top-level call.
struct CtxScope {
    base: Ctx,
    local: Vec<Expr>,
}

impl CtxScope {
    fn new(base: &Ctx) -> CtxScope {
        CtxScope { base: base.clone(), local: Vec::new() }
    }
}

fn ctx_lookup(ctx: &CtxScope, k: u32) -> Result<Expr, String> {
    let k_usize = k as usize;
    let len = ctx.base.len() + ctx.local.len();
    if k_usize >= len {
        return Err(format!("unbound variable #{k}"));
    }
    let idx = len - 1 - k_usize;
    let ty = if idx < ctx.base.len() { &ctx.base[idx] } else { &ctx.local[idx - ctx.base.len()] };
    if free_of(ty) > 0 {
        return Err(free_escaped(free_of(ty) - 1));
    }
    // `ctx[idx]` was checked when the context had length `idx` (that many
    // entries existed before it was pushed); reinterpreting it at the
    // current length requires shifting by `k + 1`, not `k` — e.g. for
    // `Var(0)` itself (k=0), its stored type was written one binder
    // shallower than "now", so it still needs a shift of 1.
    #[cfg(feature = "record-defeq")]
    let _g = site(1);
    #[cfg(feature = "record-defeq")]
    {
        // Probe slot 17: `shift` visits spent in this lookup.
        let v0 = WALKS.with(|w| w[1].get());
        let r = shift(ty, 0, k as i32 + 1);
        WALKS.with(|w| w[17].set(w[17].get() + w[1].get() - v0));
        return Ok(r);
    }
    #[cfg(not(feature = "record-defeq"))]
    Ok(shift(ty, 0, k as i32 + 1))
}

/// Constant `l`'s type: `globals[l]` as is, since a closed type has no
/// variable to shift. An error when `l` is past the environment, or when
/// the type isn't closed.
fn const_type(g: &Globals, l: u32) -> Result<Expr, String> {
    match g.get(l as usize) {
        Some(ty) if loose_of(ty) == 0 && free_of(ty) == 0 => Ok(ty.clone()),
        Some(ty) => Err(format!("constant @{l}'s type isn't closed: {}", brief(ty))),
        None => Err(format!("unknown constant @{l}")),
    }
}

fn expect_sort(e: &Expr) -> Result<u32, String> {
    match whnf(e) {
        Expr::Sort(i) => Ok(i),
        other => Err(format!("expected a Sort, got {}", brief(&other))),
    }
}

fn expect_pi(e: &Expr) -> Result<(Expr, Expr), String> {
    match whnf(e) {
        Expr::Pi(ref a, ref b) => Ok(((**a).clone(), (**b).clone())),
        other => Err(format!("expected a Pi type, got {}", brief(&other))),
    }
}

fn expect_w(e: &Expr) -> Result<(Expr, Expr), String> {
    match whnf(e) {
        Expr::W(ref a, ref b) => Ok(((**a).clone(), (**b).clone())),
        other => Err(format!("expected a W type, got {}", brief(&other))),
    }
}

fn expect_sigma(e: &Expr) -> Result<(Expr, Expr), String> {
    match whnf(e) {
        Expr::Sigma(ref a, ref b) => Ok(((**a).clone(), (**b).clone())),
        other => Err(format!("expected a Sigma type, got {}", brief(&other))),
    }
}

/// `infer`'s own `Sigma`/`Pair`/`SigRec` cases, out of line, so these
/// arms' locals don't sit in `infer`'s frame on every *other* shape.
///
/// This, and every other `#[inline(never)]` extraction in this module,
/// was once load-bearing: `eval_dyn`'s per-instance proof search ran
/// close to a native-stack budget tuned in a debug test thread, and
/// inlining these arms back into `infer` measurably shrank its margin
/// and overflowed a deep-recursion test. Every traversal here, and
/// `eval_dyn`, now runs through [`grow`] (`RELATED_WORK.md` 31, 32), so
/// frame size only decides how soon a deep walk moves to a new stack
/// segment. They are kept because smaller hot frames cost nothing, not
/// because anything depends on them.
#[inline(never)]
fn infer_sigma(g: &Globals, ic: &mut InferCache, ctx: &mut CtxScope, cid: u32, a: &Rc<Expr>, b: &Rc<Expr>) -> Result<Expr, String> {
    let i = expect_sort(&infer_rc(g, ic, ctx, cid, a)?)?;
    let depth = ctx.local.len();
    ctx.local.push((**a).clone());
    let cid2 = ic.enter(cid, a);
    let j = infer_rc(g, ic, ctx, cid2, b);
    ctx.local.truncate(depth);
    let j = expect_sort(&j?)?;
    Ok(Expr::Sort(i.max(j)))
}

#[inline(never)]
fn infer_pair(g: &Globals, ic: &mut InferCache, ctx: &mut CtxScope, cid: u32, fam: &Rc<Expr>, a: &Rc<Expr>, b: &Rc<Expr>) -> Result<Expr, String> {
    let ta = infer_rc(g, ic, ctx, cid, a)?;
    let depth = ctx.local.len();
    ctx.local.push(ta.clone());
    let cid2 = ic.fresh();
    let tf = infer_rc(g, ic, ctx, cid2, fam);
    ctx.local.truncate(depth);
    expect_sort(&tf?)?;
    let expected_b_ty = subst_top(fam, a);
    check_rc(g, ic, ctx, cid, b, &expected_b_ty)?;
    Ok(sigma(ta, (**fam).clone()))
}

#[inline(never)]
fn infer_sigrec(g: &Globals, ic: &mut InferCache, ctx: &mut CtxScope, cid: u32, motive: &Rc<Expr>, step: &Rc<Expr>, target: &Rc<Expr>) -> Result<Expr, String> {
    let (sa, sb) = expect_sigma(&infer_rc(g, ic, ctx, cid, target)?)?;
    infer_rc(g, ic, ctx, cid, motive)?; // sanity: motive must itself be well-typed

    // step : Pi a:A. Pi b:B(a). motive (pair(B,a,b))
    // `sb` already assumes exactly one binder (`Sigma`'s own convention)
    // -- b's own domain under binder `a` (depth1) is `sb` unchanged, the
    // same way `WRec`'s own `f_dom_d1` reuses `wb` unchanged.
    let b_dom_d1 = sb.clone();
    // under binders a(Var1), b(Var0) -- depth2:
    let motive_d2 = shift(motive, 0, 2);
    // `sb`'s own bound tag (Var0) must stay untouched (`Pair`'s own `fam`
    // field needs a *fresh* tag binder of its own, one level below
    // wherever the `Pair` itself sits) -- only whatever `sb` references
    // *above* that (the 2 extra binders `a`/`b` now sitting between it
    // and the ambient context) shifts, cutoff 1.
    let fam_d2 = shift(&sb, 1, 2);
    let concl_d2 = app(motive_d2, pair(fam_d2, var(1), var(0)));
    let expected_step_ty = pi(sa.clone(), pi(b_dom_d1, concl_d2));
    check_rc(g, ic, ctx, cid, step, &expected_step_ty)?;

    Ok(app((**motive).clone(), (**target).clone()))
}

/// `infer`'s own `WRec` mismatch error, out of line and `#[cold]` so its
/// own locals (two `nf` calls, a `format!`) stay off `infer`'s hot frame
/// (see `infer_sigma`).
#[cold]
#[inline(never)]
fn wrec_children_ty_mismatch(children_ty: &Expr, wb: &Expr) -> String {
    format!("wrec: children_ty doesn't match target's own real children-type: {} vs {}", brief(&nf(children_ty)), brief(&nf(wb)))
}

/// `infer`'s own `Sup` arm, out of line: `ta`/`dom`/`cod`/`w_candidate`/
/// `wa`/`wb` would otherwise sit in `infer`'s frame on every call (see
/// `infer_sigma`).
#[inline(never)]
fn infer_sup(g: &Globals, ic: &mut InferCache, ctx: &mut CtxScope, cid: u32, a: &Rc<Expr>, f: &Rc<Expr>) -> Result<Expr, String> {
    let ta = infer_rc(g, ic, ctx, cid, a)?;
    let (dom, cod) = expect_pi(&infer_rc(g, ic, ctx, cid, f)?)?;
    // `cod` is written one binder deeper than `f`'s own domain binder; a
    // `Sup`'s codomain must not actually depend on it -- enforced here
    // (not just documented), by an occurs-check on `cod`'s own normal
    // form, since `subst_top` just below would otherwise only ever be
    // validated at this one concrete `a`, silently trusting every other
    // point of `f`'s domain agrees.
    let cod_nf = nf(&cod);
    if is_var_free(&cod_nf, 0) {
        return Err(sup_codomain_depends_on_own_argument(&cod_nf));
    }
    let w_candidate = subst_top(&cod, a);
    let (wa, wb) = expect_w(&w_candidate)?;
    if !def_eq(&wa, &ta) {
        return Err(format!("sup: element type mismatch: {} vs {}", brief(&wa), brief(&ta)));
    }
    let expected_dom = subst_top(&wb, a);
    if !def_eq(&dom, &expected_dom) {
        return Err(format!(
            "sup: children-function domain mismatch: {} vs {}",
            brief(&dom),
            brief(&expected_dom)
        ));
    }
    Ok(wty(wa, wb))
}

/// `e`'s type, with constants typed by `globals` and variables by `ctx`.
/// A `Free` anywhere in `e` is an error; so is one in a `ctx` entry, when
/// `e` uses it.
///
/// Checked here, not only at the leaf: `infer` hands some children to
/// `check_rc` (an `App`'s argument, `Id`'s sides, `J`'s fields), whose
/// `Lam` rule against a `Pi` compares the domain by `def_eq` and never
/// infers it, and `WRec`'s `children_ty` is only compared, so a `Free`
/// under a redex in any of them would reduce away unseen. `free_of` is
/// O(1).
pub fn infer_in(globals: &Globals, ctx: &Ctx, e: &Expr) -> Result<Expr, String> {
    if free_of(e) > 0 {
        return Err(free_escaped(free_of(e) - 1));
    }
    let _hc = hc::Scope::enter();
    infer_node(globals, &mut InferCache::default(), &mut CtxScope::new(ctx), 0, &Rc::new(e.clone()))
}

/// [`infer_in`] with no globals.
pub fn infer(ctx: &Ctx, e: &Expr) -> Result<Expr, String> {
    infer_in(&Globals::new(), ctx, e)
}

/// `infer` on a child. A node referenced from more than one place is
/// memoised by pointer and context id, so a shared subterm is inferred
/// once per context rather than once per occurrence (`RELATED_WORK.md`
/// §63). A node referenced once can only be reached twice through a shared
/// ancestor, which is memoised instead, so skipping it keeps the walk
/// linear in the DAG and costs unshared terms no hashing. Only successes
/// are stored: an error ends the whole check.
fn infer_rc(g: &Globals, ic: &mut InferCache, ctx: &mut CtxScope, cid: u32, e: &Rc<Expr>) -> Result<Expr, String> {
    // Probe slots 18 single-reference calls, 19 memo hits, 20 memo misses (inserts), 21 binder
    // entries (`InferCache::enter`).
    if Rc::strong_count(e) == 1 {
        walk_count(18);
        return infer_node(g, ic, ctx, cid, e);
    }
    // Keyed by the window of binders the node can depend on, not the whole context, so one
    // inference serves every binder stack that agrees on that window (bit-vector design doc §50:
    // 96 to 99.5% of the whole-context misses were such repeats).
    let key = (PtrKey(e.clone()), ic.memo_context(cid, e));
    #[cfg(feature = "record-defeq")]
    {
        // Probe slots 22 relaxed-key lookups, 23 strict misses a relaxed key would have hit, 24 sum
        // of window sizes.
        let (sig, take) = ic.relevant_signature(cid, e);
        walk_count(22);
        WALKS.with(|w| w[24].set(w[24].get() + take as u64));
        let seen = !ic.relaxed.insert((Rc::as_ptr(e) as usize, sig));
        if seen && !ic.types.contains_key(&key) {
            walk_count(23);
            if loose_of(e) == 0 {
                walk_count(25);
            }
        }
    }
    if let Some(ty) = ic.types.get(&key) {
        walk_count(19);
        return Ok(ty.clone());
    }
    walk_count(20);
    let ty = infer_node(g, ic, ctx, cid, e)?;
    ic.types.insert(key, ty.clone());
    Ok(ty)
}

fn infer_node(g: &Globals, ic: &mut InferCache, ctx: &mut CtxScope, cid: u32, e: &Rc<Expr>) -> Result<Expr, String> {
    grow(|| match &**e {
        Expr::Var(k) => ctx_lookup(ctx, *k),
        Expr::Sort(i) => i.checked_add(1).map(Expr::Sort).ok_or_else(|| format!("universe overflow: no successor sort above Type{i}")),
        Expr::Const(l) => const_type(g, *l),
        Expr::Free(l) => Err(free_escaped(*l)),
        Expr::Pi(a, b) => {
            let i = expect_sort(&infer_rc(g, ic, ctx, cid, a)?)?;
            let depth = ctx.local.len();
            ctx.local.push((**a).clone());
            let cid2 = ic.enter(cid, a);
            let j = infer_rc(g, ic, ctx, cid2, b);
    ctx.local.truncate(depth);
    let j = expect_sort(&j?)?;
            Ok(Expr::Sort(i.max(j)))
        }
        Expr::Lam(a, body) => {
            expect_sort(&infer_rc(g, ic, ctx, cid, a)?)?;
            let depth = ctx.local.len();
            ctx.local.push((**a).clone());
            let cid2 = ic.enter(cid, a);
            let tbody = infer_rc(g, ic, ctx, cid2, body);
            ctx.local.truncate(depth);
            let tbody = tbody?;
            Ok(pi((**a).clone(), tbody))
        }
        Expr::App(f, a) => {
            let (dom, cod) = expect_pi(&infer_rc(g, ic, ctx, cid, f)?)?;
            check_rc(g, ic, ctx, cid, a, &dom)?;
            #[cfg(feature = "record-defeq")]
            let _g = site(2);
            Ok(subst_top(&cod, a))
        }
        Expr::Id(a, x, y) => {
            let i = expect_sort(&infer_rc(g, ic, ctx, cid, a)?)?;
            check_rc(g, ic, ctx, cid, x, a)?;
            check_rc(g, ic, ctx, cid, y, a)?;
            Ok(Expr::Sort(i))
        }
        Expr::Refl(a) => {
            let ta = infer_rc(g, ic, ctx, cid, a)?;
            Ok(id(ta, (**a).clone(), (**a).clone()))
        }
        Expr::J {
            motive,
            base,
            a,
            b,
            p,
        } => {
            let ta = infer_rc(g, ic, ctx, cid, a)?;
            check_rc(g, ic, ctx, cid, b, &ta)?;
            check_rc(g, ic, ctx, cid, p, &id(ta.clone(), (**a).clone(), (**b).clone()))?;
            infer_rc(g, ic, ctx, cid, motive)?; // sanity: motive must itself be well-typed
            let expected_base_ty = pi(
                ta.clone(),
                app3(
                    shift(motive, 0, 1),
                    var(0),
                    var(0),
                    refl(var(0)),
                ),
            );
            check_rc(g, ic, ctx, cid, base, &expected_base_ty)?;
            Ok(app3(
                (**motive).clone(),
                (**a).clone(),
                (**b).clone(),
                (**p).clone(),
            ))
        }
        Expr::W(a, b) => {
            let i = expect_sort(&infer_rc(g, ic, ctx, cid, a)?)?;
            let depth = ctx.local.len();
            ctx.local.push((**a).clone());
            let cid2 = ic.enter(cid, a);
            let j = infer_rc(g, ic, ctx, cid2, b);
    ctx.local.truncate(depth);
    let j = expect_sort(&j?)?;
            Ok(Expr::Sort(i.max(j)))
        }
        Expr::Sup(a, f) => infer_sup(g, ic, ctx, cid, a, f),
        Expr::WRec {
            motive,
            children_ty,
            step,
            target,
        } => {
            let (wa, wb) = expect_w(&infer_rc(g, ic, ctx, cid, target)?)?;
            // Soundness gate for `whnf_impl`'s own use of `children_ty`
            // (see `Expr::WRec`'s own doc): `target`'s *real* children-type
            // family, independently re-derived here from its own inferred
            // type, must match the field a `WRec` term carries exactly --
            // otherwise a term built with a wrong `children_ty` would
            // reduce its own induction-hypothesis closure to a domain that
            // lies about what's actually being recursed into, letting an
            // otherwise-untyped step function's body get away with
            // anything at that domain.
            if !def_eq(children_ty, &wb) {
                return Err(wrec_children_ty_mismatch(children_ty, &wb));
            }
            infer_rc(g, ic, ctx, cid, motive)?;
            let w_ty0 = wty(wa.clone(), wb.clone());

            // f : B(a) -> W(A,B), formed under binder `a` (depth 1).
            let f_dom_d1 = wb.clone(); // wb already assumes exactly one binder
            let f_ty_d1 = pi(f_dom_d1, shift(&w_ty0, 0, 2));

            // under binders a (Var1), f (Var0) — depth 2:
            // ih_ty : Pi y : B(a). motive (f y)      [formed at depth2, body at depth3]
            let ih_dom_d2 = shift(&wb, 0, 1); // B(a) reindexed for depth-2 frame
            let motive_d3 = shift(motive, 0, 3);
            let f_at_d3 = var(1); // f, seen from depth3 (a=2,f=1,y=0)
            let y_at_d3 = var(0);
            let ih_body_d3 = app(motive_d3, app(f_at_d3, y_at_d3));
            let ih_ty_d2 = pi(ih_dom_d2, ih_body_d3);

            // concl_ty : motive (sup a f), at depth2 (a=1, f=0)
            let motive_d2 = shift(motive, 0, 2);
            let concl_ty_d2 = app(motive_d2, sup(var(1), var(0)));

            let arrow_ty_d2 = pi(ih_ty_d2, shift(&concl_ty_d2, 0, 1));

            let expected_step_ty = pi(wa.clone(), pi(f_ty_d1, arrow_ty_d2));
            check_rc(g, ic, ctx, cid, step, &expected_step_ty)?;

            Ok(app((**motive).clone(), (**target).clone()))
        }
        Expr::Sigma(a, b) => infer_sigma(g, ic, ctx, cid, a, b),
        Expr::Pair(fam, a, b) => infer_pair(g, ic, ctx, cid, fam, a, b),
        Expr::SigRec { motive, step, target } => infer_sigrec(g, ic, ctx, cid, motive, step, target),
    })
}

/// Checks `e` against `expected`.
///
/// Safe at any depth: every traversal it reaches runs through [`grow`],
/// so an expression is bounded by heap, not native stack. That is also
/// why there is no depth guard here or in [`typecheck`] any more -- the
/// one that used to exist (`MAX_CHECK_DEPTH`, `RELATED_WORK.md` 30) was
/// purely a stack-survival bound. How long a deep check takes is the
/// caller's to bound; `proof.rs`'s step budgets do that.
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
    // The claim must be a type before anything is checked against it, as
    // in Lean's `check_constant_val` and Coq's `infer_definition`
    // (RELATED_WORK §67): the rules below compare `expected` by `def_eq`
    // and never infer it, so a malformed claim would otherwise be proved.
    // One cache for both, so a claim's subterms the proof shares hit it.
    let _hc = hc::Scope::enter();
    let large = hc::large(e, expected);
    let (e, expected) = hc::canonical_inputs(e, expected);
    let body = || {
        let mut ic = InferCache::default();
        let mut scope = CtxScope::new(ctx);
        expect_sort(&infer_rc(globals, &mut ic, &mut scope, 0, &hc::intern(expected.clone(), None))?)?;
        check_rc(globals, &mut ic, &mut scope, 0, &hc::intern(e, None), &expected)
    };
    if large { on_segment(CHECK_SEGMENT, body) } else { body() }
}

/// [`check_in`] with no globals.
pub fn check(ctx: &Ctx, e: &Expr, expected: &Expr) -> Result<(), String> {
    check_in(&Globals::new(), ctx, e, expected)
}

#[cfg(feature = "record-defeq")]
thread_local! {
    static DEFEQ_LOG: std::cell::RefCell<Vec<(Expr, Expr, u32)>> = const { std::cell::RefCell::new(Vec::new()) };
}

#[cfg(feature = "record-defeq")]
thread_local! {
    static BETAS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

// Node visits by `[instantiate, shift, eq_noting, conv_whnf, nf_whnf]` since the last
// `take_walk_counts`, to see which traversals pay by tree node. Compiled out by default.
#[cfg(feature = "record-defeq")]
thread_local! {
    static WALKS: [std::cell::Cell<u64>; 26] = const { [const { std::cell::Cell::new(0) }; 26] };
}
#[cfg(feature = "record-defeq")]
thread_local! {
    static SEEN: std::cell::RefCell<HashSet<(*const Expr, u32)>> = std::cell::RefCell::new(HashSet::new());
}
#[cfg(feature = "record-defeq")]
thread_local! {
    static INTERNAL: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
}
// Probe: `[instantiate, shift, eq]` visits by call site (0 other, 1 `ctx_lookup`, 2 `App` rule's
// `subst_top`, 3 `def_eq`).
#[cfg(feature = "record-defeq")]
thread_local! {
    static SITE: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static SITES: [[std::cell::Cell<u64>; 3]; 4] = const { [const { [const { std::cell::Cell::new(0) }; 3] }; 4] };
}
#[cfg(feature = "record-defeq")]
struct SiteGuard(usize);
#[cfg(feature = "record-defeq")]
impl Drop for SiteGuard {
    fn drop(&mut self) {
        SITE.with(|c| c.set(self.0));
    }
}
#[cfg(feature = "record-defeq")]
fn site(i: usize) -> SiteGuard {
    SiteGuard(SITE.with(|c| c.replace(i)))
}
/// (nodes counted once per allocation, nodes counted once per occurrence) in `e`.
pub fn term_sizes(e: &Expr) -> (usize, u128) {
    fn go(e: &Expr, seen: &mut HashMap<*const Expr, u128>) -> u128 {
        let mut n = 1u128;
        same_shape(e, e, |p, _| {
            let k = Rc::as_ptr(p);
            n += match seen.get(&k) {
                Some(&t) => t,
                None => {
                    let t = go(p, seen);
                    seen.insert(k, t);
                    t
                }
            };
            true
        });
        n
    }
    let mut seen = HashMap::new();
    let tree = go(e, &mut seen);
    (seen.len() + 1, tree)
}
#[cfg(feature = "record-defeq")]
pub fn take_site_counts() -> [[u64; 3]; 4] {
    SITES.with(|s| std::array::from_fn(|i| std::array::from_fn(|j| s[i][j].replace(0))))
}
#[cfg(feature = "record-defeq")]
#[inline(always)]
fn walk_count(i: usize) {
    WALKS.with(|w| w[i].set(w[i].get() + 1));
    if i < 3 {
        let site = SITE.with(|c| c.get());
        SITES.with(|s| s[site][i].set(s[site][i].get() + 1));
    }
}
#[cfg(not(feature = "record-defeq"))]
#[inline(always)]
fn walk_count(_: usize) {}
#[cfg(feature = "record-defeq")]
pub fn take_walk_counts() -> [u64; 26] {
    WALKS.with(|w| std::array::from_fn(|i| w[i].replace(0)))
}

/// Probe for option C: `e` with each of its first `depth` free variables replaced by a distinct
/// `Free`, so a comparison afterwards works on closed terms.
#[cfg(feature = "record-defeq")]
pub fn rename_context_to_frees(e: &Expr, depth: u32) -> Expr {
    let frees: Vec<Expr> = (0..depth).map(Expr::Free).collect();
    let refs: Vec<&Expr> = frees.iter().collect();
    instantiate_n(e, &refs, 0)
}

/// `rename_context_to_frees` for a pair of sides sharing one pointer-keyed memo, so a node reached
/// twice is renamed once.
#[cfg(feature = "record-defeq")]
pub fn rename_pair_memo(a: &Expr, b: &Expr, depth: u32) -> (Expr, Expr) {
    let frees: Vec<Expr> = (0..depth).map(Expr::Free).collect();
    let refs: Vec<&Expr> = frees.iter().collect();
    let memo = std::cell::RefCell::new(HashMap::new());
    (instantiate_memo(a, &refs, 0, &memo), instantiate_memo(b, &refs, 0, &memo))
}

/// Beta steps `whnf_step` took since the last call.
#[cfg(feature = "record-defeq")]
pub fn take_beta_count() -> u64 {
    BETAS.with(|c| c.replace(0))
}

/// Drains the `(inferred, expected, context depth)` triples `check_rc` compared since the last call.
#[cfg(feature = "record-defeq")]
pub fn take_defeq_log() -> Vec<(Expr, Expr, u32)> {
    DEFEQ_LOG.with(|l| std::mem::take(&mut *l.borrow_mut()))
}

fn check_rc(g: &Globals, ic: &mut InferCache, ctx: &mut CtxScope, cid: u32, e: &Rc<Expr>, expected: &Expr) -> Result<(), String> {
    grow(|| {
        if let Expr::Lam(a, body) = &**e
            && let Expr::Pi(ref dom, ref cod) = whnf(expected)
        {
            // As `infer`'s `Lam` rule does: `def_eq` alone would accept an
            // ill-typed annotation that reduces to `dom`.
            expect_sort(&infer_rc(g, ic, ctx, cid, a)?)?;
            if !def_eq(a, dom) {
                return Err(format!("lambda domain mismatch: {} vs {}", brief(a), brief(dom)));
            }
            let depth = ctx.local.len();
            ctx.local.push((**a).clone());
            let cid2 = ic.enter(cid, a);
            let r = check_rc(g, ic, ctx, cid2, body, cod);
            ctx.local.truncate(depth);
            return r;
        }
        let inferred = infer_rc(g, ic, ctx, cid, e)?;
        #[cfg(feature = "record-defeq")]
        DEFEQ_LOG.with(|l| l.borrow_mut().push((inferred.clone(), expected.clone(), (ctx.base.len() + ctx.local.len()) as u32)));
        if def_eq(&inferred, expected) {
            Ok(())
        } else {
            Err(format!(
                "type mismatch: inferred {}, expected {}",
                brief(&nf(&inferred)),
                brief(&nf(expected))
            ))
        }
    })
}

/// Typecheck a closed term and return its normalized type.
pub fn typecheck(e: &Expr) -> Result<Expr, String> {
    infer(&Ctx::new(), e).map(|t| nf(&t))
}

mod postulates;
pub use postulates::*;

#[cfg(test)]
mod tests;
