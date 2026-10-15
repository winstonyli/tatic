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
//! built from these five, not a further primitive. See the tests in `kernel/tests.rs`
//! for worked examples, including a proof that uses `J` (symmetry
//! of `Id`), a `WRec`-defined function whose defining equation holds by
//! `refl` alone (i.e. genuinely *computes*, which is the whole point of
//! choosing `W` over an impredicative/Church encoding), and a `SigRec`
//! projection that computes the same way.
//!
//! Besides those formers a term has `Var` (de Bruijn index), `Free` (a level, for builder parameters) and `Const`
//! (a postulate or definition in `Globals`).
//!
//! This is the trusted core: the proof pipeline (`proof`, `jit`) builds terms and has this module check them; nothing
//! else decides equality or typing. Layout: this file holds `Node`/`Expr`, `shift`/`instantiate`, the hash-consing
//! layer (`hc`), `whnf`/`def_eq`/`normalize` and `infer`/`check`. Child modules: `postulates` (builders over `Globals`,
//! not read by the checker) and `tests`. The closure-based `kernel_lazy::def_eq` is an untrusted second evaluator used
//! to test `def_eq` differentially.

use hashbrown::{HashMap, HashSet};
use std::fmt;

// --- nodes -----------------------------------------------------------------
//
// A term is a handle (`Expr`) to its outermost node, and the node holds its children as handles, so every subterm is
// a node and a term is a DAG. Each node caches its loose-variable and free-level ranges, computed from its children
// when it is built: `shift`, `instantiate` and `is_var_free` read them to skip the subterms they would leave
// unchanged, and keep those as they are (`RELATED_WORK.md` §64).

/// A term's outermost constructor over children of type `C`. `Node<Expr>` is what [`Expr::node`] hands out.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Node<C> {
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
    Pi(C, C),
    /// `Lam(A, body)`: `A` is the domain annotation; `body` one binder deeper.
    Lam(C, C),
    App(C, C),
    /// `Id(A, a, b)`: the type of proofs that `a` and `b` (both `: A`) are equal.
    Id(C, C, C),
    /// `Refl(a) : Id(A, a, a)`, the only primitive way to construct an equality.
    Refl(C),
    /// Eliminator for `Id`. `motive` is `C : Pi x y : A. Id(A,x,y) -> Sort(k)`,
    /// `base` is `c : Pi x : A. C x x (refl x)`, `p : Id(A, a, b)`.
    /// Result type: `C a b p`. Reduces to `base a` when `p` reduces to a `Refl`.
    J { motive: C, base: C, a: C, b: C, p: C },
    /// `W(A, B)`: `B` one binder deeper than `A`, i.e. `B` is the family
    /// `B(x)` for `x : A` giving the arity/shape of the children at tag `x`.
    W(C, C),
    /// `Sup(a, f) : W(A,B)` where `a : A` and `f : B(a) -> W(A,B)`.
    Sup(C, C),
    /// Eliminator (recursor) for `W`. `motive : W(A,B) -> Sort(k)`,
    /// `step : Pi a:A. Pi f:(B a -> W). (Pi y:B a. motive (f y)) -> motive (sup a f)`.
    /// Reduces on a `Sup` target by recursing into every child.
    ///
    /// `children_ty` is `B` itself, in the *same* representation `W(A,B)`'s
    /// own second field already uses (written one binder deeper than `A`,
    /// i.e. `B(x)` with the ambient `x:A` as `Var(0)`) -- carried here,
    /// redundantly with `target`'s own real type `W(A,B)`, purely so
    /// `whnf_in`'s own automatic reduction (which has no typing context
    /// at all, by design) can give its induction-hypothesis closure an
    /// honest domain (`subst_top(children_ty, a)`, i.e. `B(a)`) instead of
    /// an inert placeholder. `infer` independently re-derives `B` from
    /// `target`'s own real inferred type and checks it against this field
    /// via `def_eq` -- a term built with a *wrong* `children_ty` (whether
    /// by mistake or by a hostile caller) is rejected outright, never
    /// silently trusted, so this redundancy can't become a soundness hole.
    WRec { motive: C, children_ty: C, step: C, target: C },
    /// `Sigma(A, B)`: `B` one binder deeper than `A`, i.e. `B` is the
    /// family `B(x)` for `x : A` -- the type of dependent pairs `(a, b)`
    /// with `a : A` and `b : B(a)`. See this module's own top-level docs
    /// for why this is a genuinely separate primitive, not derivable from
    /// `W` here.
    Sigma(C, C),
    /// `Pair(fam, a, b) : Sigma(A, B)` where `a : A`, `b : B(a)`. `fam` is
    /// `B` itself, in the *same* representation `Sigma`'s own second field
    /// already uses (one binder deeper than the ambient context) --
    /// carried explicitly because, unlike `Sup`'s own second argument
    /// (whose `Pi`-type already reveals the whole `W(A,B)` it targets), a
    /// pair's own two components alone don't determine which family `B`
    /// was intended (many different families agree at one concrete `a`)
    /// -- the same reason `Lam` carries its own domain annotation.
    Pair(C, C, C),
    /// Eliminator (recursor) for `Sigma`. `motive : Sigma(A,B) -> Sort(k)`,
    /// `step : Pi a:A. Pi b:B(a). motive (pair(fam,a,b))`. Reduces on a
    /// `Pair` target to `step a b`. Unlike `WRec`, needs no extra
    /// `children_ty`-style redundant field: a pair isn't recursive, so
    /// there's no induction-hypothesis closure to give an honest domain to
    /// -- `target`'s own real type alone is enough context for both
    /// `infer` and `whnf_in`.
    SigRec { motive: C, step: C, target: C },
}

impl<C> Node<C> {
    /// Calls `f` on each child in field order, with whether the child sits under a binder of this node (the second
    /// field of `Pi`/`Lam`/`W`/`Sigma`, `WRec`'s `children_ty`, `Pair`'s `fam`).
    #[inline(always)]
    pub fn for_kids<'a>(&'a self, mut f: impl FnMut(&'a C, bool)) {
        use Node::*;
        match self {
            Var(_) | Sort(_) | Const(_) | Free(_) => {}
            Refl(a) => f(a, false),
            Pi(a, b) | Lam(a, b) | W(a, b) | Sigma(a, b) => {
                f(a, false);
                f(b, true);
            }
            App(a, b) | Sup(a, b) => {
                f(a, false);
                f(b, false);
            }
            Id(a, b, c) | SigRec { motive: a, step: b, target: c } => {
                f(a, false);
                f(b, false);
                f(c, false);
            }
            Pair(fam, a, b) => {
                f(fam, true);
                f(a, false);
                f(b, false);
            }
            J { motive, base, a, b, p } => {
                for c in [motive, base, a, b, p] {
                    f(c, false);
                }
            }
            WRec { motive, children_ty, step, target } => {
                f(motive, false);
                f(children_ty, true);
                f(step, false);
                f(target, false);
            }
        }
    }

    /// The same constructor with each child replaced by `f(child, under_binder)`, called in field order.
    #[inline(always)]
    pub fn map_kids<D>(self, mut f: impl FnMut(C, bool) -> D) -> Node<D> {
        use Node::*;
        match self {
            Var(k) => Var(k),
            Sort(k) => Sort(k),
            Const(k) => Const(k),
            Free(k) => Free(k),
            Pi(a, b) => Pi(f(a, false), f(b, true)),
            Lam(a, b) => Lam(f(a, false), f(b, true)),
            App(a, b) => App(f(a, false), f(b, false)),
            Id(a, b, c) => Id(f(a, false), f(b, false), f(c, false)),
            Refl(a) => Refl(f(a, false)),
            J { motive, base, a, b, p } => J { motive: f(motive, false), base: f(base, false), a: f(a, false), b: f(b, false), p: f(p, false) },
            W(a, b) => W(f(a, false), f(b, true)),
            Sup(a, b) => Sup(f(a, false), f(b, false)),
            WRec { motive, children_ty, step, target } => {
                WRec { motive: f(motive, false), children_ty: f(children_ty, true), step: f(step, false), target: f(target, false) }
            }
            Sigma(a, b) => Sigma(f(a, false), f(b, true)),
            Pair(fam, a, b) => Pair(f(fam, true), f(a, false), f(b, false)),
            SigRec { motive, step, target } => SigRec { motive: f(motive, false), step: f(step, false), target: f(target, false) },
        }
    }

    /// The constructor's tag and leaf value, as the node tables key them.
    pub fn tag_leaf(&self) -> (u8, u32) {
        use Node::*;
        match self {
            Var(k) => (0, *k),
            Sort(k) => (1, *k),
            Const(k) => (2, *k),
            Free(k) => (3, *k),
            Pi(..) => (4, 0),
            Lam(..) => (5, 0),
            App(..) => (6, 0),
            Id(..) => (7, 0),
            Refl(..) => (8, 0),
            J { .. } => (9, 0),
            W(..) => (10, 0),
            Sup(..) => (11, 0),
            WRec { .. } => (12, 0),
            Sigma(..) => (13, 0),
            Pair(..) => (14, 0),
            SigRec { .. } => (15, 0),
        }
    }

    /// Whether `self` and `other` have the same outermost constructor (and index, for `Var`/`Sort`/`Const`/`Free`)
    /// and `c` holds of each pair of children, in field order, stopping at the first that fails. Syntactic equality
    /// and `conv_whnf` are both this with a different `c`.
    pub fn same_shape(&self, other: &Node<C>, mut c: impl FnMut(&C, &C) -> bool) -> bool {
        if self.tag_leaf() != other.tag_leaf() {
            return false;
        }
        let mut kids: [Option<&C>; 5] = [None; 5];
        let mut i = 0;
        other.for_kids(|k, _| {
            kids[i] = Some(k);
            i += 1;
        });
        let (mut ok, mut j) = (true, 0);
        self.for_kids(|k, _| {
            ok = ok && c(k, kids[j].unwrap());
            j += 1;
        });
        ok
    }

    /// One more than the largest loose `Var` index and one more than the largest `Free` level, from the children's
    /// (`loose`, `free`): a binder child has one loose variable fewer out here, and a binder doesn't change `free` (a
    /// `Free` is a level, not an index). Saturating, so `Var(u32::MAX)` doesn't wrap to "closed" (the range is exact
    /// only below `u32::MAX`, which no real term reaches).
    pub fn ranges(&self, loose: impl Fn(&C) -> u32, free: impl Fn(&C) -> u32) -> (u32, u32) {
        match self {
            Node::Var(k) => (k.saturating_add(1), 0),
            Node::Free(l) => (0, l.saturating_add(1)),
            _ => {
                let (mut l, mut f) = (0, 0);
                self.for_kids(|c, under| {
                    l = l.max(if under { loose(c).saturating_sub(1) } else { loose(c) });
                    f = f.max(free(c));
                });
                (l, f)
            }
        }
    }
}

/// A term: a handle to its outermost node. Cloning is a refcount bump, not a copy: a term is built and re-threaded
/// through deeply nested proof terms (the Ev-witness builder's per-call-site composition, ...) almost entirely by
/// `.clone()`, so cloning any term, however large, is O(1) and its children are shared. The id arena (spec
/// docs/superpowers/specs/2026-10-14-id-arena-spec.md) replaces the `Rc` with an id behind the same API.
#[derive(Clone)]
pub struct Expr(std::rc::Rc<Header>);

struct Header {
    loose: u32,
    free: u32,
    /// The `hc` table generation this node is canonical in (0: not).
    generation: std::cell::Cell<u32>,
    /// The last [`hc::uses`] answer for this node, packed by [`Spaces::uses_slot`] (0: none). A fact about the node
    /// alone, like `loose` and `free`, so it never goes stale.
    uses: std::cell::Cell<u32>,
    /// Nodes built over this one, saturating at 2 ([`Spaces::shared`]).
    parents: std::cell::Cell<u8>,
    node: Node<Expr>,
}

impl Expr {
    /// A new node over `n`, outside any table ([`hc::intern`] decides whether to share one instead).
    fn build(n: Node<Expr>) -> Expr {
        #[cfg(feature = "record-defeq")]
        BUILT.with(|b| b[1].set(b[1].get() + 1));
        let (loose, free) = n.ranges(|c| c.0.loose, |c| c.0.free);
        n.for_kids(|c, _| c.0.parents.set(c.0.parents.get().saturating_add(1).min(2)));
        Expr(std::rc::Rc::new(Header {
            loose,
            free,
            generation: std::cell::Cell::new(0),
            uses: std::cell::Cell::new(0),
            parents: std::cell::Cell::new(0),
            node: n,
        }))
    }

    /// Whether this node and everything under it came from the current `hc` table, so that two canonical nodes are
    /// structurally equal exactly when they are the same node. False outside a scope.
    #[inline(always)]
    pub(crate) fn canonical(&self) -> bool {
        let g = self.0.generation.get();
        g != 0 && g == hc::generation()
    }

    /// The outermost constructor, over the children.
    pub fn node(&self) -> Node<Expr> {
        with_spaces(|s| s.node(self))
    }

    /// One more than the largest loose `Var` index, 0 when closed (saturating at `u32::MAX`).
    pub fn loose(&self) -> u32 {
        with_spaces(|s| s.loose(self))
    }

    /// One more than the largest `Free` level, 0 when there is none (saturating).
    pub fn free(&self) -> u32 {
        with_spaces(|s| s.free(self))
    }

    /// Whether two or more nodes are built over this one (the memos' "worth remembering" test).
    pub fn shared(&self) -> bool {
        with_spaces(|s| s.shared(self))
    }
}

/// The node `n`, interned while a scope's table is on.
pub fn mk(n: Node<Expr>) -> Expr {
    with_spaces(|s| s.mk(n))
}

/// An id for `e`'s node: two handles have the same key exactly when they name the same node. For tests, and for maps
/// that live only while a root keeps the nodes they key alive (`bin::write`, `term_sizes`, `kernel_lazy`).
pub fn node_key(e: &Expr) -> u64 {
    std::rc::Rc::as_ptr(&e.0) as u64
}

/// The kernel's view of term storage. A stub over `Rc` nodes until the id arena gives it state; internals take it as
/// `s` so the arena changes only this type.
pub(crate) struct Spaces;

/// Runs `f` with this thread's spaces.
#[inline(always)]
pub(crate) fn with_spaces<R>(f: impl FnOnce(&Spaces) -> R) -> R {
    f(&Spaces)
}

/// A map key naming a node. It holds the node, so no address is reused while the map lives.
pub(crate) type Key = PtrKey;
/// An argument list's id in the instantiation memo ([`hc::args_id`]).
pub(crate) type Aid = u64;

impl Spaces {
    #[inline(always)]
    pub(crate) fn node(&self, e: &Expr) -> Node<Expr> {
        e.0.node.clone()
    }

    #[inline(always)]
    pub(crate) fn mk(&self, n: Node<Expr>) -> Expr {
        hc::intern(n)
    }

    #[inline(always)]
    pub(crate) fn loose(&self, e: &Expr) -> u32 {
        e.0.loose
    }

    #[inline(always)]
    pub(crate) fn free(&self, e: &Expr) -> u32 {
        e.0.free
    }

    #[inline(always)]
    pub(crate) fn shared(&self, e: &Expr) -> bool {
        e.0.parents.get() > 1
    }

    #[inline(always)]
    pub(crate) fn same(&self, a: &Expr, b: &Expr) -> bool {
        std::rc::Rc::ptr_eq(&a.0, &b.0)
    }

    #[inline(always)]
    pub(crate) fn key(&self, e: &Expr) -> Key {
        PtrKey(e.clone())
    }

    #[inline(always)]
    #[allow(clippy::wrong_self_convention)] // reads through `self` once nodes live in the arena
    pub(crate) fn from_key(&self, k: &Key) -> Expr {
        k.0.clone()
    }

    /// The node's remembered `uses(e, d, m)`, if the slot holds that query. The slot packs a set bit, `d` and `m` in 15
    /// bits each, and the answer; queries that don't fit are never stored.
    #[inline(always)]
    pub(crate) fn uses_slot(&self, e: &Expr, d: u32, m: u32) -> Option<bool> {
        let s = e.0.uses.get();
        (d < 1 << 15 && m < 1 << 15 && s >> 1 == (1 << 30 | d << 15 | m)).then_some(s & 1 == 1)
    }

    #[inline(always)]
    pub(crate) fn set_uses_slot(&self, e: &Expr, d: u32, m: u32, r: bool) {
        if d < 1 << 15 && m < 1 << 15 {
            e.0.uses.set((1 << 30 | d << 15 | m) << 1 | r as u32);
        }
    }
}

#[cfg(feature = "record-defeq")]
thread_local! {
    /// `mk` calls and new nodes since the last [`take_built`].
    static BUILT: [std::cell::Cell<u64>; 2] = const { [std::cell::Cell::new(0), std::cell::Cell::new(0)] };
}

/// Probe: the number of `mk` calls and of new nodes built since the last call, on this thread.
#[cfg(feature = "record-defeq")]
pub fn take_built() -> (u64, u64) {
    BUILT.with(|b| (b[0].replace(0), b[1].replace(0)))
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
/// in this module -- and `PartialEq` and `Debug` for `Expr`; `Drop` for `Header` uses
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

/// Structural equality, written out rather than derived so it recurses through [`grow`] -- `def_eq` compares two
/// large terms with it. The same node is equal without a walk, and two canonical nodes are equal only when they are
/// the same node.
impl PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        std::rc::Rc::ptr_eq(&self.0, &other.0)
            || (!(self.canonical() && other.canonical()) && grow(|| self.0.node.same_shape(&other.0.node, |p, q| p == q)))
    }
}

impl Eq for Expr {}

/// Keeps dropping a term stack-safe. The compiler-generated drop glue is recursive, and it runs wherever a term is
/// discarded -- `whnf` throws away a full intermediate term at every beta step -- so on whatever stack segment is
/// current, with only [`RED_ZONE`] guaranteed. Unguarded, a 1,000-deep term reliably overflowed there.
///
/// The glue calls this at every node before recursing into its children, so a cheap [`stack_ok`] check is all most
/// drops pay. Only when the stack runs low does it move the node out (leaving a leaf) and drop its children on a fresh
/// segment. A shared child just loses a reference, which cannot recurse.
impl Drop for Header {
    fn drop(&mut self) {
        if stack_ok() {
            return;
        }
        let n = std::mem::replace(&mut self.node, Node::Sort(0));
        grow_slow(|| drop(n))
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

/// `brief(&nf(e))`, normalizing only what gets printed: each node is reduced to whnf as the printer
/// reaches it, and `brief`'s limit stops the printer, so a type mismatch between two large normal
/// forms costs the first `LIMIT` characters of each, not both whole normal forms (doc section
/// "The NEG control's wall was the error message").
pub(crate) fn brief_nf(e: &Expr) -> String {
    struct Nf<'a>(Expr, &'a std::cell::RefCell<ReductionCache>);
    impl fmt::Debug for Nf<'_> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let w = with_spaces(|s| whnf_in(s, &self.0, &mut self.1.borrow_mut()));
            write_expr(&w.node(), f, &|c, f| fmt::Debug::fmt(&Nf(c.clone(), self.1), f))
        }
    }
    brief(&Nf(e.clone(), &std::cell::RefCell::new(ReductionCache::default())))
}

/// A child printed by the function it carries (`write_expr`).
struct Child<'a, F>(&'a Expr, &'a F);
impl<F: Fn(&Expr, &mut fmt::Formatter<'_>) -> fmt::Result> fmt::Debug for Child<'_, F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (self.1)(self.0, f)
    }
}

/// The node `n`, with each child printed by `child`.
fn write_expr<F: Fn(&Expr, &mut fmt::Formatter<'_>) -> fmt::Result>(n: &Node<Expr>, f: &mut fmt::Formatter<'_>, child: &F) -> fmt::Result {
    let c = |x| Child(x, child);
    grow(|| match n {
        Node::Var(k) => write!(f, "#{k}"),
        Node::Sort(i) => write!(f, "Type{i}"),
        Node::Const(l) => write!(f, "@{l}"),
        Node::Free(l) => write!(f, "${l}"),
        Node::Pi(a, b) => write!(f, "(Pi {:?}. {:?})", c(a), c(b)),
        Node::Lam(a, b) => write!(f, "(\\{:?}. {:?})", c(a), c(b)),
        Node::App(g, a) => write!(f, "({:?} {:?})", c(g), c(a)),
        Node::Id(a, x, y) => write!(f, "(Id {:?} {:?} {:?})", c(a), c(x), c(y)),
        Node::Refl(a) => write!(f, "(refl {:?})", c(a)),
        Node::J { a, b, p, .. } => write!(f, "(J .. {:?} {:?} {:?})", c(a), c(b), c(p)),
        Node::W(a, b) => write!(f, "(W {:?}. {:?})", c(a), c(b)),
        Node::Sup(a, g) => write!(f, "(sup {:?} {:?})", c(a), c(g)),
        Node::WRec { target, .. } => write!(f, "(wrec .. {:?})", c(target)),
        Node::Sigma(a, b) => write!(f, "(Sigma {:?}. {:?})", c(a), c(b)),
        Node::Pair(fam, a, b) => write!(f, "(pair {:?} {:?} {:?})", c(fam), c(a), c(b)),
        Node::SigRec { target, .. } => write!(f, "(sigrec .. {:?})", c(target)),
    })
}

impl fmt::Debug for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_expr(&self.0.node, f, &|c, f| fmt::Debug::fmt(c, f))
    }
}

// --- convenience constructors -------------------------------------------
//
// Each builds its node through `mk`: inside [`scoped`] structurally equal nodes are one node, outside it each call
// makes a new one.

pub fn var(k: u32) -> Expr {
    mk(Node::Var(k))
}
pub fn sort(i: u32) -> Expr {
    mk(Node::Sort(i))
}
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

/// `e` as a term that outlives the open scope. A move today; the id arena copies it out of the region.
pub fn persist(e: Expr) -> PExpr {
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

/// The current interning generation: 0 while the table is off, else a number never reused. A term kept across a change
/// of generation stays correct but is no longer canonical (it loses the pointer-equality fast path), so a cache of built
/// terms that wants to stay canonical keys on this.
pub fn intern_generation() -> u32 {
    hc::generation()
}

pub fn pi(a: Expr, b: Expr) -> Expr {
    mk(Node::Pi(a, b))
}
pub fn lam(a: Expr, body: Expr) -> Expr {
    mk(Node::Lam(a, body))
}
pub fn app(f: Expr, a: Expr) -> Expr {
    mk(Node::App(f, a))
}
pub fn app2(f: Expr, a: Expr, b: Expr) -> Expr {
    app(app(f, a), b)
}
pub fn app3(f: Expr, a: Expr, b: Expr, c: Expr) -> Expr {
    app(app2(f, a, b), c)
}
pub fn id(a: Expr, x: Expr, y: Expr) -> Expr {
    mk(Node::Id(a, x, y))
}
pub fn refl(a: Expr) -> Expr {
    mk(Node::Refl(a))
}
pub fn jelim(motive: Expr, base: Expr, a: Expr, b: Expr, p: Expr) -> Expr {
    mk(Node::J { motive, base, a, b, p })
}
pub fn wty(a: Expr, b: Expr) -> Expr {
    mk(Node::W(a, b))
}
pub fn sup(a: Expr, f: Expr) -> Expr {
    mk(Node::Sup(a, f))
}
pub fn wrec(motive: Expr, children_ty: Expr, step: Expr, target: Expr) -> Expr {
    mk(Node::WRec { motive, children_ty, step, target })
}
pub fn sigma(a: Expr, b: Expr) -> Expr {
    mk(Node::Sigma(a, b))
}
pub fn pair(fam: Expr, a: Expr, b: Expr) -> Expr {
    mk(Node::Pair(fam, a, b))
}
pub fn sigrec(motive: Expr, step: Expr, target: Expr) -> Expr {
    mk(Node::SigRec { motive, step, target })
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
    with_spaces(|s| shift_in(s, e, cutoff, amount))
}

/// [`shift`] inside the kernel.
fn shift_in(s: &Spaces, e: &Expr, cutoff: u32, amount: i32) -> Expr {
    // Adding 0 changes no index, and a term whose loose variables all sit
    // below `cutoff` has none to change: either way `e` comes back as is.
    if amount == 0 || s.loose(e) <= cutoff {
        return e.clone();
    }
    shift_unchecked(s, e, cutoff, amount)
}

/// `shift` for an `e` already known to have a loose variable at or above
/// `cutoff` (and `amount != 0`).
fn shift_unchecked(s: &Spaces, e: &Expr, cutoff: u32, amount: i32) -> Expr {
    walk_count(1);
    grow(|| match s.node(e) {
        Node::Var(k) if k >= cutoff => var((k as i32 + amount) as u32),
        Node::Var(_) | Node::Sort(_) | Node::Const(_) | Node::Free(_) => e.clone(),
        n => s.mk(n.map_kids(|x, under| shift_child(s, &x, cutoff + under as u32, amount))),
    })
}

/// `shift` of one child: the child itself when it has nothing to shift, else memoised while the table is on.
fn shift_child(s: &Spaces, x: &Expr, cutoff: u32, amount: i32) -> Expr {
    if s.loose(x) <= cutoff {
        return x.clone();
    }
    if let Some(r) = hc::shift_get(x, cutoff, amount) {
        return r;
    }
    let r = shift_unchecked(s, x, cutoff, amount);
    hc::shift_put(x, cutoff, amount, &r);
    r
}

/// (node address, cutoff, amount).
type ShiftKey = (usize, u32, i32);

/// The hash-consing layer (bit-vector design doc sections 60 and 62). While a
/// [`hc::Scope`] is open, `mk` interns the nodes it builds and `instantiate_n` and `shift_child`
/// memoise their results; the table and memos are dropped with the outermost scope. A node is
/// interned under an exact key (constructor, leaf value, child nodes), so two nodes merge only
/// if structurally equal; ones built elsewhere simply stay distinct. While the table is off every
/// function here is a no-op that makes the callers behave as without it.
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

    struct Table {
        /// Interned nodes with their key's hash, found by comparing the candidate node's own key: 16
        /// bytes an entry instead of a stored 48-byte key (doc section "Where the node table's time goes").
        nodes: hashbrown::HashTable<(u64, Expr)>,
        /// (source node, argument-set id, depth) -> its instantiation.
        inst: PtrMap<(usize, Aid, u32), Expr>,
        shifts: PtrMap<ShiftKey, Expr>,
        /// Node -> its weak head normal form. `whnf` reads no context, so its answer holds for the
        /// whole scope, across `def_eq` calls (doc section "Why the table lookups stay").
        whnf: PtrMap<usize, Expr>,
        /// (closed node, depth) -> its head normal form to that depth; see `hnf_rc`.
        hnf: PtrMap<(usize, u32), Expr>,
        /// Argument sets of two or more nodes, by their node addresses.
        arg_sets: PtrMap<Vec<usize>, u64>,
        /// (node, depth) -> bounds `(lo, hi)` on its lowest loose variable from that depth, which
        /// [`uses`] narrows: every `uses(x, d, m)` with `m <= lo` is false and with `m > hi` true.
        bounds: PtrMap<(usize, u32), (u32, u32)>,
        /// The memos' non-canonical source nodes, kept alive to the scope's end (canonical ones live
        /// in `nodes`), so no other node takes the address a memo key holds.
        keep: Vec<Expr>,
    }

    impl Table {
        /// Empty, and `const` so the thread-local needs no lazy initialization on each access.
        const fn new() -> Table {
            const H: std::hash::BuildHasherDefault<PtrHasher> = std::hash::BuildHasherDefault::new();
            Table {
                nodes: hashbrown::HashTable::new(),
                inst: PtrMap::with_hasher(H),
                shifts: PtrMap::with_hasher(H),
                whnf: PtrMap::with_hasher(H),
                hnf: PtrMap::with_hasher(H),
                arg_sets: PtrMap::with_hasher(H),
                bounds: PtrMap::with_hasher(H),
                keep: Vec::new(),
            }
        }
    }

    /// A node's address, as the memos key it.
    #[inline(always)]
    fn addr(x: &Expr) -> usize {
        node_key(x) as usize
    }

    /// Keeps a memo's source node alive while the table holds its address.
    fn pin(t: &mut Table, x: &Expr) {
        if !x.canonical() {
            t.keep.push(x.clone());
        }
    }

    /// Non-trivial `instantiate_n` calls in a scope before the table switches on: a small check
    /// would only pay for the table.
    #[cfg(test)]
    const WARM_UP: u32 = 0;
    #[cfg(not(test))]
    const WARM_UP: u32 = 3000;

    thread_local! {
        static TABLE: RefCell<Table> = const { RefCell::new(Table::new()) };
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

    /// Switches the table on now (inside a scope), instead of after `WARM_UP` calls.
    pub fn activate() {
        if !active() {
            let g = NEXT_GENERATION.with(|g| g.replace(g.get() + 1));
            GENERATION.with(|c| c.set(g));
        }
    }

    impl Drop for Scope {
        fn drop(&mut self) {
            if DEPTH.with(|d| {
                d.set(d.get() - 1);
                d.get() == 0
            }) {
                GENERATION.with(|g| g.set(0));
                CALLS.with(|c| c.set(0));
                let old = TABLE.with(|t| std::mem::replace(&mut *t.borrow_mut(), Table::new()));
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

    /// The table's node for `n`, or a fresh one while the table is off.
    pub fn intern(n: Node<Expr>) -> Expr {
        #[cfg(feature = "record-defeq")]
        BUILT.with(|b| b[0].set(b[0].get() + 1));
        intern_as(n, Expr::build)
    }

    /// `intern`, with `build` making the node when the table has none for `n` (and while it is off).
    fn intern_as(n: Node<Expr>, build: impl FnOnce(Node<Expr>) -> Expr) -> Expr {
        let generation = generation();
        if generation == 0 {
            return build(n);
        }
        let key = key_of(&n);
        let h = {
            use std::hash::{Hash, Hasher};
            let mut s = PtrHasher::default();
            key.hash(&mut s);
            s.finish()
        };
        // The lookup borrows only the key; `n` moves once, into `build`, on a miss.
        let hit = TABLE.with(|t| t.borrow().nodes.find(h, |(g, m)| *g == h && key_of(&m.0.node) == key).map(|(_, m)| m.clone()));
        if let Some(m) = hit {
            return m;
        }
        let mut canonical = true;
        n.for_kids(|p, _| canonical &= p.canonical());
        let m = build(n);
        if canonical {
            m.0.generation.set(generation);
        }
        TABLE.with(|t| {
            t.borrow_mut().nodes.insert_unique(h, (h, m.clone()), |(g, _)| *g);
        });
        m
    }

    /// The table's key for `n`: constructor, leaf value, child nodes.
    fn key_of(n: &Node<Expr>) -> NodeKey {
        let (tag, leaf) = n.tag_leaf();
        let mut kids = [0usize; 5];
        let mut i = 0;
        n.for_kids(|p, _| {
            kids[i] = addr(p);
            i += 1;
        });
        NodeKey { tag, leaf, kids }
    }

    /// Terms larger than this many nodes (counted once per node below the roots) are interned on
    /// entry to a scope; smaller ones are left to the lazy switch-on. Unit tests intern every input.
    const LARGE: usize = if cfg!(test) { 0 } else { 3000 };

    /// Whether the terms reachable from `roots` have more than `limit` distinct nodes below them.
    fn exceeds(s: &Spaces, roots: &[&Expr], limit: usize) -> bool {
        let mut seen: PtrSet<usize> = PtrSet::default();
        let mut stack: Vec<Expr> = roots.iter().map(|&e| e.clone()).collect();
        while let Some(e) = stack.pop() {
            let mut over = false;
            s.node(&e).for_kids(|p, _| {
                if !over && seen.insert(addr(p)) {
                    over = seen.len() > limit;
                    stack.push(p.clone());
                }
            });
            if over {
                return true;
            }
        }
        limit == 0 && !roots.is_empty()
    }

    fn canon(s: &Spaces, x: &Expr, memo: &mut HashMap<usize, Expr>) -> Expr {
        if x.canonical() {
            return x.clone();
        }
        let key = addr(x);
        if let Some(r) = memo.get(&key) {
            return r.clone();
        }
        let n = grow(|| s.node(x).map_kids(|c, _| canon(s, &c, memo)));
        // Children all unchanged (leaves, or nodes whose children were already the table's): put this
        // node itself in the table instead of allocating its twin.
        let r = if n.same_shape(&x.0.node, |p, q| s.same(p, q)) { intern_as(n, |_| x.clone()) } else { intern(n) };
        memo.insert(key, r.clone());
        r
    }

    /// Whether `check_in`'s term and claim are large (the same bound that makes `canonical_inputs`
    /// intern them), so that it runs them on one big stack segment (`on_segment`).
    pub fn large(s: &Spaces, e: &Expr, expected: &Expr) -> bool {
        exceeds(s, &[e, expected], LARGE)
    }

    /// `check_in`'s term and claim, with every node in them interned when they are large, so the
    /// comparisons against types the checker builds (which are interned) meet canonical nodes on
    /// both sides. Small inputs are returned as they are.
    pub fn canonical_inputs(s: &Spaces, e: &Expr, expected: &Expr) -> (Expr, Expr) {
        if !active() {
            if DEPTH.with(|d| d.get()) == 0 || !exceeds(s, &[e, expected], LARGE) {
                return (e.clone(), expected.clone());
            }
            let g = NEXT_GENERATION.with(|g| g.replace(g.get() + 1));
            GENERATION.with(|c| c.set(g));
        }
        let mut memo = HashMap::new();
        let a = canon(s, e, &mut memo);
        let b = canon(s, expected, &mut memo);
        (a, b)
    }

    /// Whether `x` mentions a loose `Var` in `[d, d + m)`, i.e. whether instantiating `m` arguments
    /// at depth `d` can put any of them in. When it cannot, the result is `x` shifted down by `m`
    /// above `d + m`, whatever the arguments are. The node's header remembers its last answer
    /// ([`Spaces::uses_slot`]). Its misses go to the table's `bounds` on the node's lowest loose
    /// variable from `d`, which one (node, depth) entry answers for every `m` outside them; a walk
    /// that still stops at its first hit narrows them (doc section "The slot in front of bounds").
    /// Only while the table is on.
    pub fn uses(s: &Spaces, x: &Expr, d: u32, m: u32) -> bool {
        let loose = s.loose(x);
        if loose <= d {
            return false;
        }
        let n = s.node(x);
        if let Node::Var(k) = n {
            return k < d + m;
        }
        if let Some(r) = s.uses_slot(x, d, m) {
            return r;
        }
        // `lo <= the lowest loose variable from d <= hi`. `loose` bounds it from above unless it
        // saturated.
        let key = (addr(x), d);
        let (lo, hi) = TABLE
            .with(|t| t.borrow().bounds.get(&key).copied())
            .unwrap_or((0, if loose == u32::MAX { u32::MAX } else { loose - 1 - d }));
        let r = if hi < m {
            true
        } else if lo >= m {
            false
        } else {
            let r = grow(|| {
                let mut found = false;
                n.for_kids(|c, under| found = found || uses(s, c, d + under as u32, m));
                found
            });
            let b = if r { (lo, m - 1) } else { (m, hi) };
            TABLE.with(|t| {
                let mut t = t.borrow_mut();
                pin(&mut t, x);
                t.bounds.insert(key, b);
            });
            r
        };
        s.set_uses_slot(x, d, m, r);
        r
    }

    /// The smallest loose `Var` index of `x` seen from `d` binders inside it, i.e. among `x`'s loose
    /// variables `k >= d`, the least `k - d`; `u32::MAX` when there is none. Memoised in `memo` by
    /// (node, `d`).
    pub(super) fn lowest_loose(s: &Spaces, x: &Expr, d: u32, memo: &mut PtrMap<(Key, u32), u32>) -> u32 {
        if s.loose(x) <= d {
            return u32::MAX;
        }
        let n = s.node(x);
        if let Node::Var(k) = n {
            return k - d;
        }
        let key = (s.key(x), d);
        if let Some(&r) = memo.get(&key) {
            return r;
        }
        let r = grow(|| {
            let mut low = u32::MAX;
            n.for_kids(|c, under| low = low.min(lowest_loose(s, c, d + under as u32, memo)));
            low
        });
        memo.insert(key, r);
        r
    }

    /// An id for the argument list: the interned node's address for one argument (even), an
    /// odd table id for several; `None` while the table is off (which it leaves after `WARM_UP`
    /// calls). A canonical argument is its own interned node, so only the others are looked up.
    pub fn args_id(s: &Spaces, args: &[&Expr]) -> Option<Aid> {
        if !active() {
            if DEPTH.with(|d| d.get()) == 0 {
                return None;
            }
            let n = CALLS.with(|c| {
                c.set(c.get() + 1);
                c.get()
            });
            #[allow(clippy::absurd_extreme_comparisons)] // `WARM_UP` is 0 under test
            if n < WARM_UP {
                return None;
            }
            let g = NEXT_GENERATION.with(|g| g.replace(g.get() + 1));
            GENERATION.with(|c| c.set(g));
        }
        let id = |a: &&Expr| if a.canonical() { addr(a) } else { addr(&intern(s.node(a))) };
        if let [a] = args {
            return Some(id(a) as Aid);
        }
        // The ids go in a stack buffer when they fit; the set is only allocated for a new list.
        let mut buf = [0usize; 8];
        let heap: Vec<usize>;
        let ptrs: &[usize] = if args.len() <= buf.len() {
            buf.iter_mut().zip(args).for_each(|(s, a)| *s = id(a));
            &buf[..args.len()]
        } else {
            heap = args.iter().map(id).collect();
            &heap
        };
        Some(TABLE.with(|t| {
            let mut t = t.borrow_mut();
            if let Some(&n) = t.arg_sets.get(ptrs) {
                return n;
            }
            let next = 2 * t.arg_sets.len() as u64 + 1;
            t.arg_sets.insert(ptrs.to_vec(), next);
            next
        }))
    }

    fn height_at_most(s: &Spaces, x: &Expr, h: u32) -> bool {
        let mut ok = true;
        s.node(x).for_kids(|c, _| ok = ok && h > 0 && height_at_most(s, c, h - 1));
        ok
    }

    /// Whether `x` is too small for the instantiation memo to pay: at most two levels above its
    /// leaves. Rebuilding such a node is a few node-table probes; its memo entry cost a probe and an
    /// insert for a 36% hit rate (one level), and the cutoff at two beat one, three and four (doc
    /// section "Small nodes skip the instantiation memo").
    pub fn low(s: &Spaces, x: &Expr) -> bool {
        height_at_most(s, x, 2)
    }

    pub fn inst_get(x: &Expr, aid: Option<Aid>, d: u32) -> Option<Expr> {
        let aid = aid?;
        TABLE.with(|t| t.borrow().inst.get(&(addr(x), aid, d)).cloned())
    }

    pub fn inst_put(x: &Expr, aid: Option<Aid>, d: u32, r: &Expr) {
        if let Some(aid) = aid {
            TABLE.with(|t| {
                let mut t = t.borrow_mut();
                pin(&mut t, x);
                t.inst.insert((addr(x), aid, d), r.clone());
            });
        }
    }

    /// `x`'s weak head normal form if the scope has one; `None` also while the table is off.
    pub fn whnf_get(x: &Expr) -> Option<Expr> {
        TABLE.with(|t| t.borrow().whnf.get(&addr(x)).cloned())
    }

    pub fn whnf_put(x: &Expr, r: &Expr) {
        TABLE.with(|t| {
            let mut t = t.borrow_mut();
            pin(&mut t, x);
            t.whnf.insert(addr(x), r.clone());
        });
    }

    pub fn hnf_get(x: &Expr, d: u32) -> Option<Expr> {
        TABLE.with(|t| t.borrow().hnf.get(&(addr(x), d)).cloned())
    }

    pub fn hnf_put(x: &Expr, d: u32, r: &Expr) {
        TABLE.with(|t| {
            let mut t = t.borrow_mut();
            pin(&mut t, x);
            t.hnf.insert((addr(x), d), r.clone());
        });
    }

    pub fn shift_get(x: &Expr, cutoff: u32, amount: i32) -> Option<Expr> {
        if !active() {
            return None;
        }
        TABLE.with(|t| t.borrow().shifts.get(&(addr(x), cutoff, amount)).cloned())
    }

    pub fn shift_put(x: &Expr, cutoff: u32, amount: i32, r: &Expr) {
        if active() {
            TABLE.with(|t| {
                let mut t = t.borrow_mut();
                pin(&mut t, x);
                t.shifts.insert((addr(x), cutoff, amount), r.clone());
            });
        }
    }
}

/// Beta-substitution: replace `Var(0)` in `body` (which lives one binder
/// deeper) with `a`, then discharge that binder. `a` is walked only where
/// `body` uses it, so not at all when `body` doesn't mention `Var(0)`:
/// `infer`'s `App` rule substitutes every argument into its function's
/// codomain, usually `Int`, and shifting the argument there cost a walk of
/// it per application (`RELATED_WORK.md` §50, §58).
fn subst_top(s: &Spaces, body: &Expr, a: &Expr) -> Expr {
    instantiate(s, body, a, 0)
}

/// `subst_top`'s substitution in one pass: under `d` binders of `e`,
/// `Var(d)` becomes `a` shifted past them, and `e`'s own free variables
/// above it drop by one for the discharged binder. Equal to substituting
/// `shift(a, 0, 1)` and then shifting the result by -1, but `a` is shifted
/// only where it's used, not at every binder crossed and again in the
/// result (`RELATED_WORK.md` §52).
///
/// A subterm with no loose variable at or above its depth is kept as it is.
fn instantiate(s: &Spaces, e: &Expr, a: &Expr, d: u32) -> Expr {
    instantiate_n(s, e, &[a], d)
}

/// `instantiate` for `args.len()` binders at once: `e` lives under that many binders, `args` are in
/// application order (so the last one is `Var(0)`), and the result is `e` with all of them
/// discharged. Equal to calling `subst_top` once per argument, outermost first, without building the
/// intermediate terms: each argument is shifted past the `d` binders it ends up under, and `e`'s own
/// free variables above the discharged ones drop by `args.len()`.
fn instantiate_n(s: &Spaces, e: &Expr, args: &[&Expr], d: u32) -> Expr {
    if s.loose(e) <= d {
        return e.clone();
    }
    inst_rec(s, e, args, hc::args_id(s, args), d)
}

/// `instantiate_n`'s recursion, with the argument list's id for the hash-consing memo (`None`: none).
fn inst_rec(s: &Spaces, e: &Expr, args: &[&Expr], aid: Option<Aid>, d: u32) -> Expr {
    walk_count(0);
    let m = args.len() as u32;
    let go = |x: Expr, under: bool| {
        let d = d + under as u32;
        if s.loose(&x) <= d {
            return x;
        }
        if aid.is_some() && s.loose(&x) != u32::MAX && !hc::uses(s, &x, d, m) {
            return shift_child(s, &x, d + m, -(m as i32));
        }
        let memo = !hc::low(s, &x);
        if memo && let Some(r) = hc::inst_get(&x, aid, d) {
            return r;
        }
        let r = inst_rec(s, &x, args, aid, d);
        if memo {
            hc::inst_put(&x, aid, d, &r);
        }
        r
    };
    grow(|| match s.node(e) {
        Node::Var(k) if k >= d + m => var(k - m),
        Node::Var(k) if k >= d => {
            let arg = args[(m - 1 - (k - d)) as usize];
            // Probe slots: 5 uses, 6 at depth 0, 7 deeper with a closed argument, 8 deeper with
            // loose variables, 9 `shift` visits those last uses cost.
            walk_count(5);
            if d == 0 {
                walk_count(6);
            } else if s.loose(arg) == 0 {
                walk_count(7);
            } else {
                walk_count(8);
            }
            #[cfg(feature = "record-defeq")]
            let v0 = WALKS.with(|w| w[1].get());
            let r = shift_in(s, arg, 0, d as i32);
            #[cfg(feature = "record-defeq")]
            if d > 0 && s.loose(arg) > 0 {
                // Slots 10/11: uses whose argument mentions a binder `conv` opened (internal) or
                // only the checker's context; 12/13 the shift visits each class cost.
                let k = INTERNAL.with(|c| c.get());
                let internal = (0..k).any(|i| is_var_free(s, arg, i));
                let cost = WALKS.with(|w| w[1].get()) - v0;
                // Slots 15/16: distinct (argument, depth) pairs within one `def_eq` and the shift
                // visits they cost, i.e. what a per-query shift memo would still pay.
                let fresh = SEEN.with(|m| m.borrow_mut().insert((node_key(arg), d)));
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
        }
        Node::Var(_) | Node::Sort(_) | Node::Const(_) | Node::Free(_) => e.clone(),
        n => s.mk(n.map_kids(&go)),
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
fn is_var_free(s: &Spaces, e: &Expr, idx: u32) -> bool {
    if s.loose(e) <= idx {
        return false;
    }
    grow(|| match s.node(e) {
        Node::Var(k) => k == idx,
        n => {
            let mut f = false;
            n.for_kids(|c, under| f = f || is_var_free(s, c, idx + under as u32));
            f
        }
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
// be keyed on more than just node identity to stay correct (the same
// subterm can mean different things under different contexts), memoizing
// pure reduction has no such caveat.

/// Caches `whnf`/`nf` results for one top-level call, keyed by the node
/// identity of the subterm being reduced (see [`PtrKey`]). Two
/// *equal but independently-built* subterms are still cache-distinct
/// outside a scope's table -- but a subterm that's genuinely
/// the same node, reached from several places while reducing one
/// larger term (exactly what happens once a proof term embeds the same
/// subterm or `cong_n` argument in multiple positions), is
/// normalized once and reused everywhere else it's referenced, instead of
/// being re-walked -- and, for `whnf` specifically, potentially
/// re-beta-reduced, which is where repeated-substitution cost actually
/// lives -- from scratch at every occurrence.
#[derive(Default)]
struct ReductionCache {
    whnf: PtrMap<Key, Expr>,
    nf: PtrMap<Key, Expr>,
    hnf: PtrMap<(Key, u32), Expr>,
    /// Pairs `def_eq` found syntactically unequal; see [`eq_noting`].
    unequal: PtrSet<(Key, Key)>,
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
/// binder whose type is the node `a` from context `cid` gives the id
/// interned for `(cid, a)`. Equal ids then mean the same sequence of binder
/// types, which, with the node, is all `infer`'s answer depends on within
/// one call -- it also depends on `g`, but that's sound because a cache
/// lives only for the one `infer_in`/`check_in` call that made it, and `g`
/// is fixed for that whole call. Keys hold their nodes (`Key`), so no
/// address is reused within the call.
#[derive(Default)]
struct InferCache {
    types: PtrMap<(Key, (u32, u32)), Key>,
    contexts: PtrMap<(u32, Key), u32>,
    next: u32,
    /// For each context id, (parent id, binder type, that type's loose range); a binder with no type of
    /// the term (`fresh`) has no type recorded and loose range `u32::MAX`.
    info: Vec<(u32, Option<Key>, u32)>,
    /// Interned windows of binder types, outermost first: (window id of the outer part, the next binder
    /// type inward) to the window's id. 0 is the empty window.
    windows: PtrMap<(u32, Key), u32>,
    /// (context id, binders needed) to its window, `None` for a fallback; see [`InferCache::window`].
    window_of: PtrMap<(u32, u32), Option<u32>>,
    /// Scratch for [`InferCache::window`]'s walk.
    path: Vec<(u32, u32)>,
    /// [`hc::lowest_loose`]'s memo.
    lows: PtrMap<(Key, u32), u32>,
    /// (context id, lowest loose variable, loose range) to [`InferCache::memo_context`]'s answer.
    context_of: PtrMap<(u32, u32, u32), (u32, u32)>,
    /// Probe: (node key, signature of the bindings it can depend on) seen so far.
    #[cfg(feature = "record-defeq")]
    relaxed: std::collections::HashSet<(u64, u64)>,
}

impl InferCache {
    /// The id of context `cid` extended by a binder of type `a`.
    fn enter(&mut self, s: &Spaces, cid: u32, a: &Expr) -> u32 {
        walk_count(21);
        let next = &mut self.next;
        let info = &mut self.info;
        *self.contexts.entry((cid, s.key(a))).or_insert_with(|| {
            *next += 1;
            if info.len() <= *next as usize {
                info.resize(*next as usize + 1, (0, None, 0));
            }
            info[*next as usize] = (cid, Some(s.key(a)), s.loose(a));
            *next
        })
    }

    /// An id no other context has: for a binder type that isn't a node
    /// of the term, like a `Pair`'s inferred first component.
    fn fresh(&mut self) -> u32 {
        self.next += 1;
        if self.info.len() <= self.next as usize {
            self.info.resize(self.next as usize + 1, (0, None, 0));
        }
        self.info[self.next as usize] = (0, None, u32::MAX);
        self.next
    }

    /// What `infer_rc` keys its memo by for node `e` in context `cid`, besides `e`: `(lo, window)`,
    /// the interned window of the binder types `e` can depend on, instead of the whole context.
    /// `lo` is `e`'s lowest loose variable: the `lo` innermost binders are never looked up, so
    /// contexts that differ only there share the entry (a `J` motive's own binders around a shared
    /// term, as in `trans_proof`). Nor is the numbering affected: the answer mentions only binders
    /// from `lo` out, at the same positions. From there, `e`'s loose range
    /// says how many binders it mentions; each of those binders' types may mention outer binders in
    /// turn, so the window grows to cover them (a type with loose range `m` at position `p`, counted
    /// from the innermost, reaches binder `p + m`). Inside that window nothing else is consulted:
    /// `infer` looks up only variables of `e`, and a lookup's answer is that binder's type shifted,
    /// whose own variables are in the window by construction. So two contexts with the same window
    /// give `e` the same answer, in the same variable numbering (indices count from the innermost
    /// binder either way). Window ids have the top bit set, so they never meet a whole-context id (whose
    /// `lo` is 0).
    /// Falls back to `cid` when the window would pass a binder the term doesn't name (`fresh`), or
    /// run past the call's own binders into the caller's context.
    fn memo_context(&mut self, s: &Spaces, cid: u32, e: &Expr) -> (u32, u32) {
        const WINDOW_BIT: u32 = 1 << 31;
        let need = s.loose(e);
        if need == 0 {
            return (0, WINDOW_BIT);
        }
        let lo = hc::lowest_loose(s, e, 0, &mut self.lows);
        if let Some(&r) = self.context_of.get(&(cid, lo, need)) {
            return r;
        }
        // The `lo` innermost binders, which `e` never names, are skipped; a skipped `fresh` binder
        // has no parent recorded, so the walk falls back there as it does inside a window.
        let mut c = Some(cid);
        for _ in 0..lo {
            c = c.filter(|&c| c != 0 && self.info[c as usize].2 != u32::MAX).map(|c| self.info[c as usize].0);
        }
        let r = c.and_then(|c| self.window(c, need - lo)).map_or((0, cid), |w| (lo, WINDOW_BIT | w));
        self.context_of.insert((cid, lo, need), r);
        r
    }

    /// The interned window of the innermost `need` binders of context `cid`, grown over their
    /// types' loose ranges, or `None` for a fallback. The window of `(c, k)` is the window of
    /// `(parent, max(k - 1, loose of c's type))` extended inward by `c`'s binder type, so each
    /// `(c, k)` is computed once (`window_of`) and a lookup costs one probe, however deep the window.
    fn window(&mut self, cid: u32, need: u32) -> Option<u32> {
        let mut path = std::mem::take(&mut self.path);
        path.clear();
        let (mut c, mut k) = (cid, need);
        let mut w = loop {
            if k == 0 {
                break Some(0);
            }
            if let Some(&w) = self.window_of.get(&(c, k)) {
                break w;
            }
            if c == 0 {
                break None;
            }
            let (parent, loose) = (self.info[c as usize].0, self.info[c as usize].2);
            if loose == u32::MAX {
                break None;
            }
            path.push((c, k));
            (c, k) = (parent, (k - 1).max(loose));
        };
        for &(c, k) in path.iter().rev() {
            if let Some(outer) = w {
                let next = self.windows.len() as u32 + 1;
                let ty = self.info[c as usize].1.clone().expect("a window binder has a type");
                w = Some(*self.windows.entry((outer, ty)).or_insert(next));
            }
            self.window_of.insert((c, k), w);
        }
        self.path = path;
        w
    }

    /// Probe: a signature of the innermost bindings `e` can depend on in context `cid` (the loose
    /// range of `e`, closed over the loose ranges of those bindings' own types), and how many that
    /// is.
    #[cfg(feature = "record-defeq")]
    fn relevant_signature(&self, cid: u32, e: &Expr) -> (u64, u32) {
        let mut chain: Vec<(u64, u32)> = Vec::new();
        let mut c = cid;
        while c != 0 {
            let (parent, ty, loose) = &self.info[c as usize];
            chain.push((ty.as_ref().map_or(0, |k| node_key(&k.0)), *loose));
            c = *parent;
        }
        let mut need = e.loose() as usize;
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
            h = (h ^ ptr).wrapping_mul(0x100_0000_01b3);
        }
        h ^= (need > chain.len()) as u64;
        (h, take as u32)
    }
}

/// Wraps a node for use as a `HashMap` key by *node* identity (`node_key`),
/// not `Expr`'s own structural `PartialEq` -- pointer identity is
/// deliberately what we want here: a cache hit should mean "the literal
/// same node was already reduced," not "an equal one was". Holds the node
/// itself, not just its address, so the entry keeps that node alive for as
/// long as it's in the cache -- without that, a freed node's address could
/// be reused by an unrelated later node within the same top-level call,
/// turning a cache lookup into a false hit against the wrong term.
#[derive(Clone)]
pub(crate) struct PtrKey(Expr);
impl PartialEq for PtrKey {
    fn eq(&self, other: &Self) -> bool {
        std::rc::Rc::ptr_eq(&self.0.0, &other.0.0)
    }
}
impl Eq for PtrKey {}
impl std::hash::Hash for PtrKey {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        (node_key(&self.0) as usize).hash(state);
    }
}

/// Weak head normal form: reduce only the outermost redex chain.
pub fn whnf(e: &Expr) -> Expr {
    with_spaces(|s| whnf_in(s, e, &mut ReductionCache::default()))
}

/// `whnf_step` for an application spine `h a1 ... ak` (`k >= 2`) whose head reduces to a lambda:
/// peel as many directly nested lambdas as there are arguments and substitute all of them in one
/// `instantiate_n` pass, instead of one `subst_top` per argument, each rebuilding the body the next
/// one rebuilds again. Arguments left over are applied to the result. `None` when the head is not a
/// lambda, so the caller's one-argument path runs unchanged (and keeps a stuck spine's per-prefix
/// cache entries).
fn beta_spine(s: &Spaces, e: &Expr, cache: &mut ReductionCache) -> Option<Expr> {
    // The head is reduced as the node the spine holds, so its cache entry is shared by every level
    // of the spine; the arguments are collected only once it is a lambda.
    let Node::App(f, _) = s.node(e) else { return None };
    let mut head = f;
    let mut k = 1;
    while let Node::App(g, _) = s.node(&head) {
        head = g;
        k += 1;
    }
    let wh = whnf_in(s, &head, cache);
    let Node::Lam(_, first) = s.node(&wh) else { return None };
    let mut args: Vec<Expr> = Vec::with_capacity(k);
    let mut spine = e.clone();
    while let Node::App(g, b) = s.node(&spine) {
        args.push(b);
        spine = g;
    }
    args.reverse();
    let mut body = first;
    let mut taken = 1;
    while taken < args.len()
        && let Node::Lam(_, inner) = s.node(&body)
    {
        body = inner;
        taken += 1;
    }
    #[cfg(feature = "record-defeq")]
    BETAS.with(|c| c.set(c.get() + taken as u64));
    let used: Vec<&Expr> = args[..taken].iter().collect();
    let mut r = instantiate_n(s, &body, &used, 0);
    for a in &args[taken..] {
        r = app(r, a.clone());
    }
    Some(whnf_in(s, &r, cache))
}

/// `whnf_step` for a spine `P a1 ... ad` whose longest proper prefix `P` with no loose variable
/// reduces to a lambda: `P`'s head normal form to depth `d` (`hnf_rc`) is instantiated with the
/// arguments. A closed function value used at several places with different arguments -- a Church
/// boolean `xor_ a b` applied to each use's own continuations -- is then reduced once, not once per
/// use, since the memo is keyed by `P`, not by the whole application. `None` when there is no such
/// prefix or it does not reduce to a lambda.
fn closed_prefix_spine(s: &Spaces, e: &Expr, cache: &mut ReductionCache) -> Option<Expr> {
    let mut args: Vec<Expr> = Vec::new();
    let mut spine = e.clone();
    let p = loop {
        let Node::App(g, b) = s.node(&spine) else { return None };
        args.push(b);
        if s.loose(&g) == 0 {
            break g;
        }
        spine = g;
    };
    args.reverse();
    let mut body = hnf_rc(s, &p, args.len() as u32, cache);
    let mut taken = 0;
    while taken < args.len()
        && let Node::Lam(_, inner) = s.node(&body)
    {
        body = inner;
        taken += 1;
    }
    if taken == 0 {
        return None;
    }
    #[cfg(feature = "record-defeq")]
    BETAS.with(|c| c.set(c.get() + taken as u64));
    let used: Vec<&Expr> = args[..taken].iter().collect();
    let mut r = instantiate_n(s, &body, &used, 0);
    for a in &args[taken..] {
        r = app(r, a.clone());
    }
    Some(whnf_in(s, &r, cache))
}

/// Head normal form of `p` to depth `d`: its whnf, and while that is a lambda (at most `d` deep),
/// the body's whnf under it. Applying the result to `d` arguments and reducing does no more work
/// than reducing `p a1 ... ad` would (head reduction commutes with substitution), and the work done
/// here is shared by every application of `p`. Memoised by `(p, d)`: in the scope's table while it
/// is on, else in `cache`. An application recurses on its function at depth `d + 1`, so the memo
/// also covers each shorter prefix of a spine.
fn hnf_rc(s: &Spaces, p: &Expr, d: u32, cache: &mut ReductionCache) -> Expr {
    let table = hc::generation() != 0;
    if table {
        if let Some(hit) = hc::hnf_get(p, d) {
            return hit;
        }
    } else if let Some(hit) = cache.hnf.get(&(s.key(p), d)) {
        return hit.clone();
    }
    let r = match s.node(p) {
        Node::App(f, a) => {
            let hf = hnf_rc(s, &f, d + 1, cache);
            match s.node(&hf) {
                Node::Lam(_, body) => {
                    let x = subst_top(s, &body, &a);
                    let w = whnf_step(s, &x, cache).unwrap_or(x);
                    under_lams(s, w, d, cache)
                }
                // `hf` is `f`'s whnf and not a lambda, so `hf a` is stuck.
                _ if s.same(&hf, &f) => p.clone(),
                _ => app(hf, a),
            }
        }
        _ => under_lams(s, whnf_in(s, p, cache), d, cache),
    };
    if table {
        hc::hnf_put(p, d, &r);
    } else {
        cache.hnf.insert((s.key(p), d), r.clone());
    }
    r
}

/// `w` (in whnf) with the bodies of its first `d` nested lambdas reduced to whnf in turn.
fn under_lams(s: &Spaces, w: Expr, d: u32, cache: &mut ReductionCache) -> Expr {
    let Node::Lam(a, b) = s.node(&w) else { return w };
    if d == 0 {
        return w;
    }
    let wb = whnf_step(s, &b, cache).unwrap_or_else(|| b.clone());
    let nb = under_lams(s, wb, d - 1, cache);
    if s.same(&nb, &b) { w } else { lam(a, nb) }
}

/// `whnf`, or `None` when `e` is already in weak head normal form. A stuck
/// term keeps its nodes: its arguments' and also its stuck head's or
/// target's. `ReductionCache` is keyed by node, so a copy misses it,
/// and each level of a stuck spine then reduced the whole spine below it
/// again (`RELATED_WORK.md` §48, §59).
fn whnf_step(s: &Spaces, e: &Expr, cache: &mut ReductionCache) -> Option<Expr> {
    grow(|| match s.node(e) {
        Node::App(f, a) => {
            if let Some(r) = closed_prefix_spine(s, e, cache) {
                return Some(r);
            }
            if matches!(s.node(&f), Node::App(..))
                && let Some(r) = beta_spine(s, e, cache)
            {
                return Some(r);
            }
            let wf = whnf_in(s, &f, cache);
            match s.node(&wf) {
                Node::Lam(_, body) => {
                    #[cfg(feature = "record-defeq")]
                    BETAS.with(|c| c.set(c.get() + 1));
                    let r = subst_top(s, &body, &a);
                    Some(whnf_in(s, &r, cache))
                }
                _ => (!s.same(&wf, &f)).then(|| app(wf, a)),
            }
        }
        Node::J { motive, base, a, b, p } => {
            let wp = whnf_in(s, &p, cache);
            match s.node(&wp) {
                Node::Refl(_) => Some(whnf_in(s, &app(base, a), cache)),
                _ => (!s.same(&wp, &p)).then(|| jelim(motive, base, a, b, wp)),
            }
        }
        Node::WRec { motive, children_ty, step, target } => {
            let wt = whnf_in(s, &target, cache);
            match s.node(&wt) {
                Node::Sup(a, f) => {
                    // step a f (\y:B(a). wrec(motive, children_ty, step, f y))
                    // -- `subst_top(children_ty, a)` gives the induction-
                    // hypothesis closure its *honest* domain (`B(a)`, the same
                    // `Sup`'s own typing rule requires of `f`'s domain), not
                    // an inert placeholder -- see `Node::WRec`'s own doc for
                    // why this field exists at all.
                    let rec_step = lam(
                        subst_top(s, &children_ty, &a),
                        wrec(
                            shift_in(s, &motive, 0, 1),
                            // `children_ty` is already "one binder deeper" than
                            // `motive`/`step`/`target` (`W`'s own convention for
                            // its second field) -- inserting the new `y` binder
                            // below that existing one needs `cutoff + 1`, the
                            // same bump `Node::W`'s own `shift`/`subst` arms use
                            // for their own second field.
                            shift_in(s, &children_ty, 1, 1),
                            shift_in(s, &step, 0, 1),
                            app(shift_in(s, &f, 0, 1), var(0)),
                        ),
                    );
                    Some(whnf_in(s, &app(app(app(step, a), f), rec_step), cache))
                }
                _ => (!s.same(&wt, &target)).then(|| wrec(motive, children_ty, step, wt)),
            }
        }
        Node::SigRec { motive, step, target } => whnf_sigrec(s, motive, step, target, cache),
        _ => None,
    })
}

/// `whnf_step`'s own `SigRec` case, out of line -- see `infer_sigma`.
#[inline(never)]
fn whnf_sigrec(s: &Spaces, motive: Expr, step: Expr, target: Expr, cache: &mut ReductionCache) -> Option<Expr> {
    let wt = whnf_in(s, &target, cache);
    match s.node(&wt) {
        Node::Pair(_, a, b) => Some(whnf_in(s, &app(app(step, a), b), cache)),
        _ => (!s.same(&wt, &target)).then(|| sigrec(motive, step, wt)),
    }
}

/// `whnf`, cached -- the same subterm recurs many times within one top-level call once a proof term
/// shares structure. Returns `e` itself when it is already in weak head normal form, so reducing a
/// result again, as `nf` and `def_eq` do with a stuck head, keeps its node and hits the cache from
/// then on.
fn whnf_in(s: &Spaces, e: &Expr, cache: &mut ReductionCache) -> Expr {
    // While the table is on, its memo serves the whole scope; `cache.whnf` only this call.
    if hc::generation() != 0 {
        if let Some(hit) = hc::whnf_get(e) {
            return hit;
        }
        let result = whnf_step(s, e, cache).unwrap_or_else(|| e.clone());
        hc::whnf_put(e, &result);
        return result;
    }
    let key = s.key(e);
    if let Some(hit) = cache.whnf.get(&key) {
        return hit.clone();
    }
    let result = whnf_step(s, e, cache).unwrap_or_else(|| e.clone());
    cache.whnf.insert(key, result.clone());
    result
}

/// Full normal form: `whnf`, then recurse structurally into subterms, cached per node.
fn nf_in(s: &Spaces, e: &Expr, cache: &mut ReductionCache) -> Expr {
    let key = s.key(e);
    if let Some(hit) = cache.nf.get(&key) {
        return hit.clone();
    }
    let w = whnf_in(s, e, cache);
    let result = nf_whnf(s, &w, cache);
    cache.nf.insert(key, result.clone());
    result
}

/// `nf` of a term already in weak head normal form: its constructor over
/// the `nf` of each child.
fn nf_whnf(s: &Spaces, w: &Expr, cache: &mut ReductionCache) -> Expr {
    walk_count(4);
    grow(|| match s.node(w) {
        Node::Var(_) | Node::Sort(_) | Node::Const(_) | Node::Free(_) => w.clone(),
        n => s.mk(n.map_kids(|c, _| nf_in(s, &c, cache))),
    })
}

/// `nf(a) == nf(b)`, decided without computing either normal form, and
/// sharing one [`ReductionCache`] across both sides -- worthwhile whenever
/// `a`/`b` reference overlapping subterms, which two sides of a proof
/// obligation very often do (the same postulates, the same sub-witnesses).
pub fn def_eq(a: &Expr, b: &Expr) -> bool {
    hc::scoped(false, || with_spaces(|s| def_eq_in(s, a, b)))
}

/// [`def_eq`] inside the kernel.
fn def_eq_in(s: &Spaces, a: &Expr, b: &Expr) -> bool {
    #[cfg(feature = "record-defeq")]
    let _g = site(3);
    #[cfg(feature = "record-defeq")]
    SEEN.with(|m| m.borrow_mut().clear());
    conv(s, a, b, &mut ReductionCache::default())
}

/// `def_eq`'s comparison. Syntactically equal sides are equal without
/// reducing, since `nf` is a function; most calls from `infer` are
/// (`RELATED_WORK.md` §56), and `==` stops at the first difference
/// otherwise. Else `nf(e)` is `whnf(e)`'s outermost constructor over the
/// `nf` of each child, so the normal forms are equal exactly when the two
/// weak head normal forms have the same constructor and pairwise equal
/// children's normal forms. Recursing on that reduces only where the
/// sides differ (`RELATED_WORK.md` §57). A pair an earlier `==` found
/// unequal skips `==`.
fn conv(s: &Spaces, a: &Expr, b: &Expr, cache: &mut ReductionCache) -> bool {
    if s.same(a, b) {
        return true;
    }
    let noted = cache.unequal.contains(&(s.key(a), s.key(b)));
    if !noted && eq_noting(s, a, b, &mut cache.unequal) {
        return true;
    }
    conv_whnf(s, &whnf_in(s, a, cache), &whnf_in(s, b, cache), cache)
}

/// Compares two weak head normal forms: same constructor, then `conv` on
/// each pair of children, in the order `nf_in` visits them.
fn conv_whnf(s: &Spaces, x: &Expr, y: &Expr, cache: &mut ReductionCache) -> bool {
    walk_count(3);
    let (nx, ny) = (s.node(x), s.node(y));
    #[cfg(feature = "record-defeq")]
    {
        // Probe: track how many binders `conv` has opened (by comparing bodies without
        // instantiating them), so a loose variable in a substituted argument can be told apart as
        // internal or a reference to the checker's context.
        let mut idx = 0;
        let under = match nx {
            Node::Pi(..) | Node::Lam(..) | Node::W(..) | Node::Sigma(..) => 1,
            Node::Pair(..) | Node::WRec { .. } => 1,
            _ => usize::MAX,
        };
        let x_pair = matches!(nx, Node::Pair(..));
        return grow(|| {
            nx.same_shape(&ny, |p, q| {
                let opens = if x_pair { idx == 0 } else { idx == under };
                idx += 1;
                if opens {
                    walk_count(14);
                    INTERNAL.with(|c| c.set(c.get() + 1));
                }
                let r = conv(s, p, q, cache);
                if opens {
                    INTERNAL.with(|c| c.set(c.get() - 1));
                }
                r
            })
        });
    }
    #[cfg(not(feature = "record-defeq"))]
    grow(|| nx.same_shape(&ny, |p, q| conv(s, p, q, cache)))
}

/// `a == b`, noting in `unequal` each pair of children found unequal on
/// the way. `conv` recurses into exactly those pairs next, and without the
/// note each would repeat the walk below it: quadratic on a chain that
/// differs only at the bottom (`RELATED_WORK.md` §61).
fn eq_noting(s: &Spaces, a: &Expr, b: &Expr, unequal: &mut PtrSet<(Key, Key)>) -> bool {
    walk_count(2);
    grow(|| {
        s.node(a).same_shape(&s.node(b), |p, q| {
            s.same(p, q) || (!(p.canonical() && q.canonical()) && eq_noting(s, p, q, unequal)) || {
                unequal.insert((s.key(p), s.key(q)));
                false
            }
        })
    })
}

pub fn normalize(e: &Expr) -> Expr {
    with_spaces(|s| nf_in(s, e, &mut ReductionCache::default()))
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
pub type Globals = im::Vector<PExpr>;

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

fn ctx_lookup(s: &Spaces, ctx: &CtxScope, k: u32) -> Result<Expr, String> {
    let k_usize = k as usize;
    let len = ctx.base.len() + ctx.local.len();
    if k_usize >= len {
        return Err(format!("unbound variable #{k}"));
    }
    let idx = len - 1 - k_usize;
    let ty = if idx < ctx.base.len() { &ctx.base[idx] } else { &ctx.local[idx - ctx.base.len()] };
    if s.free(ty) > 0 {
        return Err(free_escaped(s.free(ty) - 1));
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
        let r = shift_in(s, ty, 0, k as i32 + 1);
        WALKS.with(|w| w[17].set(w[17].get() + w[1].get() - v0));
        return Ok(r);
    }
    #[cfg(not(feature = "record-defeq"))]
    Ok(shift_in(s, ty, 0, k as i32 + 1))
}

/// Constant `l`'s type: `globals[l]` as is, since a closed type has no
/// variable to shift. An error when `l` is past the environment, or when
/// the type isn't closed.
fn const_type(s: &Spaces, g: &Globals, l: u32) -> Result<Expr, String> {
    match g.get(l as usize).map(PExpr::get) {
        Some(ty) if s.loose(&ty) == 0 && s.free(&ty) == 0 => Ok(ty),
        Some(ty) => Err(format!("constant @{l}'s type isn't closed: {}", brief(&ty))),
        None => Err(format!("unknown constant @{l}")),
    }
}

/// `e`'s weak head normal form, reduced with a cache of its own.
fn whnf_fresh(s: &Spaces, e: &Expr) -> Expr {
    whnf_in(s, e, &mut ReductionCache::default())
}

fn expect_sort(s: &Spaces, e: &Expr) -> Result<u32, String> {
    let w = whnf_fresh(s, e);
    match s.node(&w) {
        Node::Sort(i) => Ok(i),
        _ => Err(format!("expected a Sort, got {}", brief(&w))),
    }
}

fn expect_pi(s: &Spaces, e: &Expr) -> Result<(Expr, Expr), String> {
    let w = whnf_fresh(s, e);
    match s.node(&w) {
        Node::Pi(a, b) => Ok((a, b)),
        _ => Err(format!("expected a Pi type, got {}", brief(&w))),
    }
}

fn expect_w(s: &Spaces, e: &Expr) -> Result<(Expr, Expr), String> {
    let w = whnf_fresh(s, e);
    match s.node(&w) {
        Node::W(a, b) => Ok((a, b)),
        _ => Err(format!("expected a W type, got {}", brief(&w))),
    }
}

fn expect_sigma(s: &Spaces, e: &Expr) -> Result<(Expr, Expr), String> {
    let w = whnf_fresh(s, e);
    match s.node(&w) {
        Node::Sigma(a, b) => Ok((a, b)),
        _ => Err(format!("expected a Sigma type, got {}", brief(&w))),
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
fn infer_sigma(s: &Spaces, g: &Globals, ic: &mut InferCache, ctx: &mut CtxScope, cid: u32, a: &Expr, b: &Expr) -> Result<Expr, String> {
    let i = expect_sort(s, &infer_rc(s, g, ic, ctx, cid, a)?)?;
    let depth = ctx.local.len();
    ctx.local.push(a.clone());
    let cid2 = ic.enter(s, cid, a);
    let j = infer_rc(s, g, ic, ctx, cid2, b);
    ctx.local.truncate(depth);
    let j = expect_sort(s, &j?)?;
    Ok(sort(i.max(j)))
}

#[inline(never)]
#[allow(clippy::too_many_arguments)]
fn infer_pair(s: &Spaces, g: &Globals, ic: &mut InferCache, ctx: &mut CtxScope, cid: u32, fam: &Expr, a: &Expr, b: &Expr) -> Result<Expr, String> {
    let ta = infer_rc(s, g, ic, ctx, cid, a)?;
    let depth = ctx.local.len();
    ctx.local.push(ta.clone());
    let cid2 = ic.fresh();
    let tf = infer_rc(s, g, ic, ctx, cid2, fam);
    ctx.local.truncate(depth);
    expect_sort(s, &tf?)?;
    let expected_b_ty = subst_top(s, fam, a);
    check_rc(s, g, ic, ctx, cid, b, &expected_b_ty)?;
    Ok(sigma(ta, fam.clone()))
}

#[inline(never)]
#[allow(clippy::too_many_arguments)]
fn infer_sigrec(s: &Spaces, g: &Globals, ic: &mut InferCache, ctx: &mut CtxScope, cid: u32, motive: &Expr, step: &Expr, target: &Expr) -> Result<Expr, String> {
    let (sa, sb) = expect_sigma(s, &infer_rc(s, g, ic, ctx, cid, target)?)?;
    infer_rc(s, g, ic, ctx, cid, motive)?; // sanity: motive must itself be well-typed

    // step : Pi a:A. Pi b:B(a). motive (pair(B,a,b))
    // `sb` already assumes exactly one binder (`Sigma`'s own convention)
    // -- b's own domain under binder `a` (depth1) is `sb` unchanged, the
    // same way `WRec`'s own `f_dom_d1` reuses `wb` unchanged.
    let b_dom_d1 = sb.clone();
    // under binders a(Var1), b(Var0) -- depth2:
    let motive_d2 = shift_in(s, motive, 0, 2);
    // `sb`'s own bound tag (Var0) must stay untouched (`Pair`'s own `fam`
    // field needs a *fresh* tag binder of its own, one level below
    // wherever the `Pair` itself sits) -- only whatever `sb` references
    // *above* that (the 2 extra binders `a`/`b` now sitting between it
    // and the ambient context) shifts, cutoff 1.
    let fam_d2 = shift_in(s, &sb, 1, 2);
    let concl_d2 = app(motive_d2, pair(fam_d2, var(1), var(0)));
    let expected_step_ty = pi(sa.clone(), pi(b_dom_d1, concl_d2));
    check_rc(s, g, ic, ctx, cid, step, &expected_step_ty)?;

    Ok(app(motive.clone(), target.clone()))
}

/// `infer`'s own `WRec` mismatch error, out of line and `#[cold]` so its
/// own locals (two `nf` calls, a `format!`) stay off `infer`'s hot frame
/// (see `infer_sigma`).
#[cold]
#[inline(never)]
fn wrec_children_ty_mismatch(children_ty: &Expr, wb: &Expr) -> String {
    format!("wrec: children_ty doesn't match target's own real children-type: {} vs {}", brief_nf(children_ty), brief_nf(wb))
}

/// `infer`'s own `Sup` arm, out of line: `ta`/`dom`/`cod`/`w_candidate`/
/// `wa`/`wb` would otherwise sit in `infer`'s frame on every call (see
/// `infer_sigma`).
#[inline(never)]
fn infer_sup(s: &Spaces, g: &Globals, ic: &mut InferCache, ctx: &mut CtxScope, cid: u32, a: &Expr, f: &Expr) -> Result<Expr, String> {
    let ta = infer_rc(s, g, ic, ctx, cid, a)?;
    let (dom, cod) = expect_pi(s, &infer_rc(s, g, ic, ctx, cid, f)?)?;
    // `cod` is written one binder deeper than `f`'s own domain binder; a
    // `Sup`'s codomain must not actually depend on it -- enforced here
    // (not just documented), by an occurs-check on `cod`'s own normal
    // form, since `subst_top` just below would otherwise only ever be
    // validated at this one concrete `a`, silently trusting every other
    // point of `f`'s domain agrees.
    let cod_nf = nf_in(s, &cod, &mut ReductionCache::default());
    if is_var_free(s, &cod_nf, 0) {
        return Err(sup_codomain_depends_on_own_argument(&cod_nf));
    }
    let w_candidate = subst_top(s, &cod, a);
    let (wa, wb) = expect_w(s, &w_candidate)?;
    if !def_eq_in(s, &wa, &ta) {
        return Err(format!("sup: element type mismatch: {} vs {}", brief(&wa), brief(&ta)));
    }
    let expected_dom = subst_top(s, &wb, a);
    if !def_eq_in(s, &dom, &expected_dom) {
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
/// under a redex in any of them would reduce away unseen. `free` is
/// O(1).
pub fn infer_in(globals: &Globals, ctx: &Ctx, e: &Expr) -> Result<Expr, String> {
    if e.free() > 0 {
        return Err(free_escaped(e.free() - 1));
    }
    hc::scoped(false, || with_spaces(|s| infer_node(s, globals, &mut InferCache::default(), &mut CtxScope::new(ctx), 0, e)))
}

/// [`infer_in`] with no globals.
pub fn infer(ctx: &Ctx, e: &Expr) -> Result<Expr, String> {
    infer_in(&Globals::new(), ctx, e)
}

/// `infer` on a child. A node with two or more parents is memoised by
/// node and context id, so a shared subterm is inferred once per context
/// rather than once per occurrence (`RELATED_WORK.md` §63). A node with one
/// parent can only be reached twice through a shared ancestor, which is
/// memoised instead, so skipping it keeps the walk linear in the DAG and
/// costs unshared terms no hashing. Only successes are stored: an error
/// ends the whole check.
fn infer_rc(s: &Spaces, g: &Globals, ic: &mut InferCache, ctx: &mut CtxScope, cid: u32, e: &Expr) -> Result<Expr, String> {
    // Probe slots 18 unshared calls, 19 memo hits, 20 memo misses (inserts), 21 binder entries
    // (`InferCache::enter`).
    if !s.shared(e) {
        walk_count(18);
        return infer_node(s, g, ic, ctx, cid, e);
    }
    // Keyed by the window of binders the node can depend on, not the whole context, so one
    // inference serves every binder stack that agrees on that window (bit-vector design doc §50:
    // 96 to 99.5% of the whole-context misses were such repeats).
    let key = (s.key(e), ic.memo_context(s, cid, e));
    #[cfg(feature = "record-defeq")]
    {
        // Probe slots 22 relaxed-key lookups, 23 strict misses a relaxed key would have hit, 24 sum
        // of window sizes.
        let (sig, take) = ic.relevant_signature(cid, e);
        walk_count(22);
        WALKS.with(|w| w[24].set(w[24].get() + take as u64));
        let seen = !ic.relaxed.insert((node_key(e), sig));
        if seen && !ic.types.contains_key(&key) {
            walk_count(23);
            if s.loose(e) == 0 {
                walk_count(25);
            }
        }
    }
    if let Some(ty) = ic.types.get(&key) {
        walk_count(19);
        return Ok(s.from_key(ty));
    }
    walk_count(20);
    let ty = infer_node(s, g, ic, ctx, cid, e)?;
    ic.types.insert(key, s.key(&ty));
    Ok(ty)
}

fn infer_node(s: &Spaces, g: &Globals, ic: &mut InferCache, ctx: &mut CtxScope, cid: u32, e: &Expr) -> Result<Expr, String> {
    grow(|| match s.node(e) {
        Node::Var(k) => ctx_lookup(s, ctx, k),
        Node::Sort(i) => i.checked_add(1).map(sort).ok_or_else(|| format!("universe overflow: no successor sort above Type{i}")),
        Node::Const(l) => const_type(s, g, l),
        Node::Free(l) => Err(free_escaped(l)),
        Node::Pi(a, b) => {
            let i = expect_sort(s, &infer_rc(s, g, ic, ctx, cid, &a)?)?;
            let depth = ctx.local.len();
            ctx.local.push(a.clone());
            let cid2 = ic.enter(s, cid, &a);
            let j = infer_rc(s, g, ic, ctx, cid2, &b);
            ctx.local.truncate(depth);
            let j = expect_sort(s, &j?)?;
            Ok(sort(i.max(j)))
        }
        Node::Lam(a, body) => {
            expect_sort(s, &infer_rc(s, g, ic, ctx, cid, &a)?)?;
            let depth = ctx.local.len();
            ctx.local.push(a.clone());
            let cid2 = ic.enter(s, cid, &a);
            let tbody = infer_rc(s, g, ic, ctx, cid2, &body);
            ctx.local.truncate(depth);
            let tbody = tbody?;
            Ok(pi(a, tbody))
        }
        Node::App(..) => {
            // The whole spine `h a1 ... ak` at once, as `beta_spine` does for reduction: each domain
            // is instantiated with the arguments before it and the last codomain once with all of
            // them, instead of one `subst_top` per argument, each copying the rest of the telescope.
            // A codomain that is not syntactically a Pi takes the pending arguments first, then whnf.
            let mut args = vec![];
            let mut head = e.clone();
            while let Node::App(f, a) = s.node(&head) {
                args.push(a);
                head = f;
            }
            args.reverse();
            let mut ty = infer_rc(s, g, ic, ctx, cid, &head)?;
            let mut pending: Vec<&Expr> = vec![];
            for a in &args {
                if !matches!(s.node(&ty), Node::Pi(..)) && !pending.is_empty() {
                    ty = instantiate_n(s, &ty, &pending, 0);
                    pending.clear();
                }
                let (dom, cod) = expect_pi(s, &ty)?;
                let dom = if pending.is_empty() { dom } else { instantiate_n(s, &dom, &pending, 0) };
                check_rc(s, g, ic, ctx, cid, a, &dom)?;
                pending.push(a);
                ty = cod;
            }
            #[cfg(feature = "record-defeq")]
            let _g = site(2);
            Ok(instantiate_n(s, &ty, &pending, 0))
        }
        Node::Id(a, x, y) => {
            let i = expect_sort(s, &infer_rc(s, g, ic, ctx, cid, &a)?)?;
            check_rc(s, g, ic, ctx, cid, &x, &a)?;
            check_rc(s, g, ic, ctx, cid, &y, &a)?;
            Ok(sort(i))
        }
        Node::Refl(a) => {
            let ta = infer_rc(s, g, ic, ctx, cid, &a)?;
            Ok(id(ta, a.clone(), a))
        }
        Node::J { motive, base, a, b, p } => {
            let ta = infer_rc(s, g, ic, ctx, cid, &a)?;
            check_rc(s, g, ic, ctx, cid, &b, &ta)?;
            check_rc(s, g, ic, ctx, cid, &p, &id(ta.clone(), a.clone(), b.clone()))?;
            infer_rc(s, g, ic, ctx, cid, &motive)?; // sanity: motive must itself be well-typed
            let expected_base_ty = pi(ta.clone(), app3(shift_in(s, &motive, 0, 1), var(0), var(0), refl(var(0))));
            check_rc(s, g, ic, ctx, cid, &base, &expected_base_ty)?;
            Ok(app3(motive, a, b, p))
        }
        Node::W(a, b) => {
            let i = expect_sort(s, &infer_rc(s, g, ic, ctx, cid, &a)?)?;
            let depth = ctx.local.len();
            ctx.local.push(a.clone());
            let cid2 = ic.enter(s, cid, &a);
            let j = infer_rc(s, g, ic, ctx, cid2, &b);
            ctx.local.truncate(depth);
            let j = expect_sort(s, &j?)?;
            Ok(sort(i.max(j)))
        }
        Node::Sup(a, f) => infer_sup(s, g, ic, ctx, cid, &a, &f),
        Node::WRec { motive, children_ty, step, target } => {
            let (wa, wb) = expect_w(s, &infer_rc(s, g, ic, ctx, cid, &target)?)?;
            // Soundness gate for `whnf_in`'s own use of `children_ty`
            // (see `Node::WRec`'s own doc): `target`'s *real* children-type
            // family, independently re-derived here from its own inferred
            // type, must match the field a `WRec` term carries exactly --
            // otherwise a term built with a wrong `children_ty` would
            // reduce its own induction-hypothesis closure to a domain that
            // lies about what's actually being recursed into, letting an
            // otherwise-untyped step function's body get away with
            // anything at that domain.
            if !def_eq_in(s, &children_ty, &wb) {
                return Err(wrec_children_ty_mismatch(&children_ty, &wb));
            }
            infer_rc(s, g, ic, ctx, cid, &motive)?;
            let w_ty0 = wty(wa.clone(), wb.clone());

            // f : B(a) -> W(A,B), formed under binder `a` (depth 1).
            let f_dom_d1 = wb.clone(); // wb already assumes exactly one binder
            let f_ty_d1 = pi(f_dom_d1, shift_in(s, &w_ty0, 0, 2));

            // under binders a (Var1), f (Var0) — depth 2:
            // ih_ty : Pi y : B(a). motive (f y)      [formed at depth2, body at depth3]
            let ih_dom_d2 = shift_in(s, &wb, 0, 1); // B(a) reindexed for depth-2 frame
            let motive_d3 = shift_in(s, &motive, 0, 3);
            let f_at_d3 = var(1); // f, seen from depth3 (a=2,f=1,y=0)
            let y_at_d3 = var(0);
            let ih_body_d3 = app(motive_d3, app(f_at_d3, y_at_d3));
            let ih_ty_d2 = pi(ih_dom_d2, ih_body_d3);

            // concl_ty : motive (sup a f), at depth2 (a=1, f=0)
            let motive_d2 = shift_in(s, &motive, 0, 2);
            let concl_ty_d2 = app(motive_d2, sup(var(1), var(0)));

            let arrow_ty_d2 = pi(ih_ty_d2, shift_in(s, &concl_ty_d2, 0, 1));

            let expected_step_ty = pi(wa.clone(), pi(f_ty_d1, arrow_ty_d2));
            check_rc(s, g, ic, ctx, cid, &step, &expected_step_ty)?;

            Ok(app(motive, target))
        }
        Node::Sigma(a, b) => infer_sigma(s, g, ic, ctx, cid, &a, &b),
        Node::Pair(fam, a, b) => infer_pair(s, g, ic, ctx, cid, &fam, &a, &b),
        Node::SigRec { motive, step, target } => infer_sigrec(s, g, ic, ctx, cid, &motive, &step, &target),
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
    // them would reduce away unseen. `free` is O(1).
    for t in [e, expected] {
        if t.free() > 0 {
            return Err(free_escaped(t.free() - 1));
        }
    }
    // The claim must be a type before anything is checked against it, as
    // in Lean's `check_constant_val` and Coq's `infer_definition`
    // (RELATED_WORK §67): the rules below compare `expected` by `def_eq`
    // and never infer it, so a malformed claim would otherwise be proved.
    // One cache for both, so a claim's subterms the proof shares hit it.
    hc::scoped(false, || {
        with_spaces(|s| {
            let large = hc::large(s, e, expected);
            let (e, expected) = hc::canonical_inputs(s, e, expected);
            let body = || {
                let mut ic = InferCache::default();
                let mut scope = CtxScope::new(ctx);
                expect_sort(s, &infer_rc(s, globals, &mut ic, &mut scope, 0, &expected)?)?;
                check_rc(s, globals, &mut ic, &mut scope, 0, &e, &expected)
            };
            if large { on_segment(CHECK_SEGMENT, body) } else { body() }
        })
    })
}

/// [`check_in`] with no globals.
pub fn check(ctx: &Ctx, e: &Expr, expected: &Expr) -> Result<(), String> {
    check_in(&Globals::new(), ctx, e, expected)
}

#[cfg(feature = "record-defeq")]
thread_local! {
    /// `check_rc`'s comparisons, persisted so their readers can use them after the check's region closes.
    static DEFEQ_LOG: std::cell::RefCell<Vec<(PExpr, PExpr, u32)>> = const { std::cell::RefCell::new(Vec::new()) };
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
    static SEEN: std::cell::RefCell<HashSet<(u64, u32)>> = std::cell::RefCell::new(HashSet::new());
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
/// (distinct nodes, nodes counted once per occurrence) in `e`.
pub fn term_sizes(e: &Expr) -> (usize, u128) {
    fn go(e: &Expr, seen: &mut HashMap<u64, u128>) -> u128 {
        let mut n = 1u128;
        e.0.node.for_kids(|p, _| {
            let k = node_key(p);
            n += match seen.get(&k) {
                Some(&t) => t,
                None => {
                    let t = grow(|| go(p, seen));
                    seen.insert(k, t);
                    t
                }
            };
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

/// Beta steps `whnf_step` took since the last call.
#[cfg(feature = "record-defeq")]
pub fn take_beta_count() -> u64 {
    BETAS.with(|c| c.replace(0))
}

/// Drains the `(inferred, expected, context depth)` triples `check_rc` compared since the last call.
#[cfg(feature = "record-defeq")]
pub fn take_defeq_log() -> Vec<(Expr, Expr, u32)> {
    DEFEQ_LOG.with(|l| std::mem::take(&mut *l.borrow_mut())).into_iter().map(|(a, b, d)| (a.get(), b.get(), d)).collect()
}

fn check_rc(s: &Spaces, g: &Globals, ic: &mut InferCache, ctx: &mut CtxScope, cid: u32, e: &Expr, expected: &Expr) -> Result<(), String> {
    grow(|| {
        if let Node::Lam(a, body) = s.node(e)
            && let Node::Pi(dom, cod) = s.node(&whnf_fresh(s, expected))
        {
            // As `infer`'s `Lam` rule does: `def_eq` alone would accept an
            // ill-typed annotation that reduces to `dom`.
            expect_sort(s, &infer_rc(s, g, ic, ctx, cid, &a)?)?;
            if !def_eq_in(s, &a, &dom) {
                return Err(format!("lambda domain mismatch: {} vs {}", brief(&a), brief(&dom)));
            }
            let depth = ctx.local.len();
            ctx.local.push(a.clone());
            let cid2 = ic.enter(s, cid, &a);
            let r = check_rc(s, g, ic, ctx, cid2, &body, &cod);
            ctx.local.truncate(depth);
            return r;
        }
        let inferred = infer_rc(s, g, ic, ctx, cid, e)?;
        #[cfg(feature = "record-defeq")]
        DEFEQ_LOG.with(|l| l.borrow_mut().push((persist(inferred.clone()), persist(expected.clone()), (ctx.base.len() + ctx.local.len()) as u32)));
        if def_eq_in(s, &inferred, expected) {
            Ok(())
        } else {
            Err(format!(
                "type mismatch: inferred {}, expected {}",
                brief_nf(&inferred),
                brief_nf(expected)
            ))
        }
    })
}

/// Typecheck a closed term and return its normalized type.
pub fn typecheck(e: &Expr) -> Result<Expr, String> {
    infer(&Ctx::new(), e).map(|t| normalize(&t))
}

mod postulates;
pub use postulates::*;

pub mod bin;

#[cfg(test)]
mod tests;

