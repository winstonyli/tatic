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
//! not read by the checker) and `tests`.

use hashbrown::HashMap;
use std::fmt;
use spaces::{IdMap, IdSet, Ref, Spaces, LIST_BIT};

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

/// A term: a node id in this thread's spaces (`spaces.rs`) and the region generation it was made in. `Copy`, 8 bytes,
/// neither `Send` nor `Sync`. A handle from a region that has closed is dead: reading it panics ("dead handle"), and
/// `Debug` prints `<dead handle>`. Persist what must outlive the region ([`persist`], or return it from [`scoped`]).
#[derive(Clone, Copy)]
pub struct Expr {
    r: Ref,
    epoch: u32,
    _thread: std::marker::PhantomData<*const ()>,
}

impl Expr {
    #[inline(always)]
    fn at(r: Ref, epoch: u32) -> Expr {
        Expr { r, epoch, _thread: std::marker::PhantomData }
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

/// The node `n`: the one node with that structure, in the open region or the persistent space.
pub fn mk(n: Node<Expr>) -> Expr {
    with_spaces(|s| s.mk(n))
}

/// An id for `e`'s node: two handles have the same key exactly when they name the same node, which, the spaces being
/// hash-consed, is when they are structurally equal. Valid while the region it was taken in is open.
pub fn node_key(e: &Expr) -> u64 {
    with_spaces(|s| s.key(e) as u64)
}

thread_local! {
    static SPACES: Spaces = const { Spaces::new() };
}

/// Runs `f` with this thread's spaces.
#[inline(always)]
pub(crate) fn with_spaces<R>(f: impl FnOnce(&Spaces) -> R) -> R {
    SPACES.with(f)
}

/// A map key naming a node: its resolved `Ref`'s bits.
pub(crate) type Key = u32;
/// An argument list's id in the instantiation memo ([`hc::args_id`]).
pub(crate) type Aid = u32;

/// The kernel's handle-level reads and builds (`spaces.rs` works on `Ref`s).
impl Spaces {
    #[inline(always)]
    fn res(&self, e: &Expr) -> Ref {
        self.resolve(e.r, e.epoch)
    }

    #[inline(always)]
    pub(crate) fn node(&self, e: &Expr) -> Node<Expr> {
        let g = self.epoch();
        self.node_at(self.res(e)).map_kids(|r, _| Expr::at(r, g))
    }

    pub(crate) fn mk(&self, n: Node<Expr>) -> Expr {
        let r = self.build(n.map_kids(|c, _| self.res(&c)));
        Expr::at(r, self.epoch())
    }

    #[inline(always)]
    pub(crate) fn loose(&self, e: &Expr) -> u32 {
        self.loose_at(self.res(e))
    }

    #[inline(always)]
    pub(crate) fn free(&self, e: &Expr) -> u32 {
        self.free_at(self.res(e))
    }

    #[inline(always)]
    pub(crate) fn shared(&self, e: &Expr) -> bool {
        self.parents_at(self.res(e)) > 1
    }

    /// The height of `e` as a tree (a leaf 0), saturating at 255.
    #[inline(always)]
    pub(crate) fn height(&self, e: &Expr) -> u8 {
        self.height_at(self.res(e))
    }

    #[inline(always)]
    pub(crate) fn same(&self, a: &Expr, b: &Expr) -> bool {
        self.res(a) == self.res(b)
    }

    #[inline(always)]
    pub(crate) fn key(&self, e: &Expr) -> Key {
        self.res(e).0
    }

    #[inline(always)]
    pub(crate) fn expr_of(&self, k: &Key) -> Expr {
        Expr::at(Ref(*k), self.epoch())
    }

    /// The node's remembered `uses(e, d, m)`, if the slot holds that query. The slot packs a set bit, `d` and `m` in 15
    /// bits each, and the answer; queries that don't fit are never stored.
    #[inline(always)]
    pub(crate) fn uses_slot(&self, e: &Expr, d: u32, m: u32) -> Option<bool> {
        let s = self.uses_at(self.res(e));
        (d < 1 << 15 && m < 1 << 15 && s >> 1 == (1 << 30 | d << 15 | m)).then_some(s & 1 == 1)
    }

    #[inline(always)]
    pub(crate) fn set_uses_slot(&self, e: &Expr, d: u32, m: u32, r: bool) {
        if d < 1 << 15 && m < 1 << 15 {
            self.set_uses_at(self.res(e), (1 << 30 | d << 15 | m) << 1 | r as u32);
        }
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
/// in this module, and `Debug` for `Expr` -- so their depth is bounded by
/// heap, not native stack.
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

/// Structural equality. The spaces are hash-consed, so two terms are equal exactly when their handles name the same
/// node: one comparison, no walk.
impl PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        with_spaces(|s| s.same(self, other))
    }
}

impl Eq for Expr {}

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
    struct Nf(Expr);
    impl fmt::Debug for Nf {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let w = with_spaces(|s| whnf_in(s, &self.0));
            write_expr(&w.node(), f, &|c, f| fmt::Debug::fmt(&Nf(*c), f))
        }
    }
    brief(&Nf(*e))
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
        match with_spaces(|s| s.live(self.r, self.epoch).then(|| s.node(self))) {
            None => write!(f, "<dead handle>"),
            Some(n) => write_expr(&n, f, &|c, f| fmt::Debug::fmt(c, f)),
        }
    }
}

// --- convenience constructors -------------------------------------------
//
// Each builds its node through `mk`, so structurally equal terms are one node: in the open region, or in the persistent
// space while none is open.

pub fn var(k: u32) -> Expr {
    mk(Node::Var(k))
}
pub fn sort(i: u32) -> Expr {
    mk(Node::Sort(i))
}
/// A term kept past the region it was built in: what long-lived stores hold. Made only by [`persist`]. A persistent
/// node id, valid after the region closes (spec `docs/superpowers/specs/2026-10-14-id-arena-spec.md`, "PExpr"); its
/// `Eq` and `Hash` are that id's, so they are structural and stable. It lends no `&Expr`: [`PExpr::get`] hands out
/// the term.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct PExpr(Ref, std::marker::PhantomData<*const ()>);

impl PExpr {
    /// The term, for building and checking.
    pub fn get(&self) -> Expr {
        with_spaces(|s| Expr::at(self.0, s.epoch()))
    }
}

impl From<PExpr> for Expr {
    fn from(p: PExpr) -> Expr {
        p.get()
    }
}

impl fmt::Debug for PExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.get(), f)
    }
}

/// `e` as a term that outlives the open region: the region nodes it reaches are copied out to the persistent space
/// (once per region). The identity on a persistent term.
pub fn persist(e: Expr) -> PExpr {
    with_spaces(|s| PExpr(s.persist(s.res(&e)), std::marker::PhantomData))
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

/// Runs `f` in the open region, or in a new one. Terms built meanwhile live in the region, which the call that opened
/// it frees in bulk when it returns, after passing `f`'s result through [`Escape`] (which persists the terms in it). A
/// handle kept past that otherwise is dead. The region's memos (`whnf`, instantiation, ...) live as long, so build a
/// proof and check it in one call. A panic closes the region too, without escaping. Per thread.
pub fn scoped<R: Escape>(f: impl FnOnce() -> R) -> R {
    struct Close;
    impl Drop for Close {
        fn drop(&mut self) {
            with_spaces(|s| s.close());
        }
    }
    if !with_spaces(|s| s.open()) {
        return f();
    }
    let close = Close;
    let r = f().escape();
    drop(close);
    r
}

/// The open region's generation: 0 while none is open, else a number never reused. A cache of built terms keys on it,
/// since its region terms die when the generation changes.
pub fn intern_generation() -> u32 {
    with_spaces(|s| s.epoch())
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
        return *e;
    }
    shift_unchecked(s, e, cutoff, amount)
}

/// `shift` for an `e` already known to have a loose variable at or above
/// `cutoff` (and `amount != 0`).
fn shift_unchecked(s: &Spaces, e: &Expr, cutoff: u32, amount: i32) -> Expr {
    grow(|| match s.node(e) {
        Node::Var(k) if k >= cutoff => var((k as i32 + amount) as u32),
        Node::Var(_) | Node::Sort(_) | Node::Const(_) | Node::Free(_) => *e,
        n => s.mk(n.map_kids(|x, under| shift_child(s, &x, cutoff + under as u32, amount))),
    })
}

/// `shift` of one child: the child itself when it has nothing to shift, else memoised if shared (see [`hc`]).
fn shift_child(s: &Spaces, x: &Expr, cutoff: u32, amount: i32) -> Expr {
    if s.loose(x) <= cutoff {
        return *x;
    }
    if !s.shared(x) {
        return shift_unchecked(s, x, cutoff, amount);
    }
    if let Some(r) = hc::shift_get(s, x, cutoff, amount) {
        return r;
    }
    let r = shift_unchecked(s, x, cutoff, amount);
    hc::shift_put(s, x, cutoff, amount, &r);
    r
}

/// The memos over the hash-consed spaces (bit-vector design doc sections 60 and 62): `instantiate_n`, `shift_child`,
/// `whnf`, head normal forms and `nf`, keyed by node (`Spaces::key`) and kept in `Spaces::memos` until the region
/// closes. A node is one term, so a memo entry serves every place the term occurs.
///
/// A walk's memo (`inst`, `shifts`, `InferCache`'s `lows` and `types`, `abstract_frees_in`'s) stores only shared nodes
/// (`Spaces::shared`, two or more parents). An unshared node is reached only through its one parent, so a repeated walk
/// stops at the parent's entry first: its own entry would almost never be read (77% of `inst`'s entries took 14 of
/// 148,047 hits in rule 33's check at n=64; doc section "Why `inst` has many entries per node"). `whnf`, `hnf` and
/// `nf` serve calls on any term, not one walk, and `uses`' `bounds` is asked again per `m`, so they keep every node.
mod hc {
    use super::*;

    /// Terms larger than this many nodes (counted once per node below the roots) are checked on one big stack segment
    /// (`check_in`). Unit tests take that path for every input.
    const LARGE: usize = if cfg!(test) { 0 } else { 3000 };

    /// Whether the terms reachable from `roots` have more than `limit` distinct nodes below them.
    fn exceeds(s: &Spaces, roots: &[&Expr], limit: usize) -> bool {
        // The walk stops once `seen` holds `limit + 1` keys, so it never grows past this.
        let mut seen: IdSet<Key> = IdSet::with_capacity_and_hasher(limit + 1, Default::default());
        let mut stack: Vec<Expr> = roots.iter().map(|&e| *e).collect();
        while let Some(e) = stack.pop() {
            let mut over = false;
            s.node(&e).for_kids(|p, _| {
                if !over && seen.insert(s.key(p)) {
                    over = seen.len() > limit;
                    stack.push(*p);
                }
            });
            if over {
                return true;
            }
        }
        limit == 0 && !roots.is_empty()
    }

    /// Whether `check_in`'s term and claim are large, so that it runs them on one big stack segment (`on_segment`).
    pub fn large(s: &Spaces, e: &Expr, expected: &Expr) -> bool {
        exceeds(s, &[e, expected], LARGE)
    }

    /// Whether `x` mentions a loose `Var` in `[d, d + m)`, i.e. whether instantiating `m` arguments
    /// at depth `d` can put any of them in. When it cannot, the result is `x` shifted down by `m`
    /// above `d + m`, whatever the arguments are. The node remembers its last answer
    /// ([`Spaces::uses_slot`]). Its misses go to the memos' `bounds` on the node's lowest loose
    /// variable from `d`, which one (node, depth) entry answers for every `m` outside them; a walk
    /// that still stops at its first hit narrows them (doc section "The slot in front of bounds").
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
        let key = (s.key(x), d);
        let (lo, hi) = s
            .memos
            .borrow()
            .bounds
            .get(&key)
            .copied()
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
            s.memos.borrow_mut().bounds.insert(key, b);
            r
        };
        s.set_uses_slot(x, d, m, r);
        r
    }

    /// The smallest loose `Var` index of `x` seen from `d` binders inside it, i.e. among `x`'s loose
    /// variables `k >= d`, the least `k - d`; `u32::MAX` when there is none. Memoised in `memo` by
    /// (node, `d`) for shared nodes (see [`hc`](self)); its one caller, `memo_context`, asks only of
    /// shared ones. A shared node's answer from 0, `l`, also answers every `d <= l` as `l - d`, so
    /// a node reached at many depths, like a shared term under a growing stack of binders it
    /// doesn't use, is walked once rather than once per depth; only depths past `l` get entries
    /// of their own.
    pub(super) fn lowest_loose(s: &Spaces, x: &Expr, d: u32, memo: &mut IdMap<(Key, u32), u32>) -> u32 {
        if s.loose(x) <= d {
            return u32::MAX;
        }
        let n = s.node(x);
        if let Node::Var(k) = n {
            return k - d;
        }
        let shared = s.shared(x);
        if shared && d > 0 {
            let l = lowest_loose(s, x, 0, memo);
            if l >= d {
                return l - d;
            }
        }
        let key = (s.key(x), d);
        if shared && let Some(&r) = memo.get(&key) {
            return r;
        }
        let r = grow(|| {
            let mut low = u32::MAX;
            n.for_kids(|c, under| low = low.min(lowest_loose(s, c, d + under as u32, memo)));
            low
        });
        if shared {
            memo.insert(key, r);
        }
        r
    }

    /// An id for the argument list: the node's key for one argument (`LIST_BIT` clear), `LIST_BIT | n` for the `n`-th
    /// list of several.
    pub fn args_id(s: &Spaces, args: &[&Expr]) -> Aid {
        if let [a] = args {
            return s.key(a);
        }
        // The keys go in a stack buffer when they fit; the set is only allocated for a new list.
        let mut buf = [0u32; 8];
        let heap: Vec<u32>;
        let keys: &[u32] = if args.len() <= buf.len() {
            buf.iter_mut().zip(args).for_each(|(k, a)| *k = s.key(a));
            &buf[..args.len()]
        } else {
            heap = args.iter().map(|a| s.key(a)).collect();
            &heap
        };
        let mut m = s.memos.borrow_mut();
        if let Some(&n) = m.arg_sets.get(keys) {
            return n;
        }
        let n = m.arg_sets.len() as u32;
        assert!(n < LIST_BIT, "argument lists ran out of ids");
        m.arg_sets.insert(keys.to_vec(), LIST_BIT | n);
        LIST_BIT | n
    }

    /// Whether `x` is too small for the instantiation memo to pay: at most two levels above its
    /// leaves. Rebuilding such a node is a few node-table probes; its memo entry cost a probe and an
    /// insert for a 36% hit rate (one level), and the cutoff at two beat one, three and four (doc
    /// section "Small nodes skip the instantiation memo").
    pub fn low(s: &Spaces, x: &Expr) -> bool {
        s.height(x) <= 2
    }

    pub fn inst_get(s: &Spaces, x: &Expr, aid: Aid, d: u32) -> Option<Expr> {
        s.memos.borrow().inst.get(&(s.key(x), aid, d)).map(|r| s.expr_of(r))
    }

    pub fn inst_put(s: &Spaces, x: &Expr, aid: Aid, d: u32, r: &Expr) {
        s.memos.borrow_mut().inst.insert((s.key(x), aid, d), s.key(r));
    }

    /// `x`'s weak head normal form, if the memos have it. `whnf` reads no context, so an answer holds for the whole
    /// region, across `def_eq` calls (doc section "Why the table lookups stay").
    pub fn whnf_get(s: &Spaces, x: &Expr) -> Option<Expr> {
        s.memos.borrow().whnf.get(&s.key(x)).map(|r| s.expr_of(r))
    }

    pub fn whnf_put(s: &Spaces, x: &Expr, r: &Expr) {
        s.memos.borrow_mut().whnf.insert(s.key(x), s.key(r));
    }

    pub fn nf_get(s: &Spaces, x: &Expr) -> Option<Expr> {
        s.memos.borrow().nf.get(&s.key(x)).map(|r| s.expr_of(r))
    }

    pub fn nf_put(s: &Spaces, x: &Expr, r: &Expr) {
        s.memos.borrow_mut().nf.insert(s.key(x), s.key(r));
    }

    /// Closed node -> its head normal form; see `hnf_rc`.
    pub fn hnf_get(s: &Spaces, x: &Expr) -> Option<Expr> {
        s.memos.borrow().hnf.get(&s.key(x)).map(|r| s.expr_of(r))
    }

    pub fn hnf_put(s: &Spaces, x: &Expr, r: &Expr) {
        s.memos.borrow_mut().hnf.insert(s.key(x), s.key(r));
    }

    /// Application -> its spine's head and closed prefix; see `spine`.
    pub fn spine_get(s: &Spaces, x: &Expr) -> Option<(Expr, Option<Expr>)> {
        s.memos.borrow().spine.get(&s.key(x)).map(|&(h, p)| (s.expr_of(&h), p.map(|p| s.expr_of(&p))))
    }

    pub fn spine_put(s: &Spaces, x: &Expr, (h, p): (Expr, Option<Expr>)) {
        s.memos.borrow_mut().spine.insert(s.key(x), (s.key(&h), p.map(|p| s.key(&p))));
    }

    pub fn shift_get(s: &Spaces, x: &Expr, cutoff: u32, amount: i32) -> Option<Expr> {
        s.memos.borrow().shifts.get(&(s.key(x), cutoff, amount)).map(|r| s.expr_of(r))
    }

    pub fn shift_put(s: &Spaces, x: &Expr, cutoff: u32, amount: i32, r: &Expr) {
        s.memos.borrow_mut().shifts.insert((s.key(x), cutoff, amount), s.key(r));
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
        return *e;
    }
    inst_rec(s, e, args, hc::args_id(s, args), d)
}

/// `instantiate_n`'s recursion, with the argument list's id for the hash-consing memo.
fn inst_rec(s: &Spaces, e: &Expr, args: &[&Expr], aid: Aid, d: u32) -> Expr {
    let m = args.len() as u32;
    let go = |x: Expr, under: bool| {
        let d = d + under as u32;
        if s.loose(&x) <= d {
            return x;
        }
        if s.loose(&x) != u32::MAX && !hc::uses(s, &x, d, m) {
            return shift_child(s, &x, d + m, -(m as i32));
        }
        let memo = s.shared(&x) && !hc::low(s, &x);
        if memo && let Some(r) = hc::inst_get(s, &x, aid, d) {
            return r;
        }
        let r = inst_rec(s, &x, args, aid, d);
        if memo {
            hc::inst_put(s, &x, aid, d, &r);
        }
        r
    };
    grow(|| match s.node(e) {
        Node::Var(k) if k >= d + m => var(k - m),
        Node::Var(k) if k >= d => shift_in(s, args[(m - 1 - (k - d)) as usize], 0, d as i32),
        Node::Var(_) | Node::Sort(_) | Node::Const(_) | Node::Free(_) => *e,
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
// `whnf`/`nf` are memoized by node for the whole region (`hc`'s memos). This
// is sound regardless of typing context, since reduction never consults one
// -- unlike a cache for `infer`/`check` themselves, which must be keyed on
// more than the node (the same subterm can mean different things under
// different contexts; see `InferCache`).

/// A context id's innermost binder, for [`InferCache`]. A binder with no type of the term (`fresh`)
/// has no type recorded and loose range `u32::MAX`; it and the caller's context 0 have `run` 0.
#[derive(Clone, Copy, Default)]
struct CtxBinder {
    parent: u32,
    ty: Option<Key>,
    /// The type's loose range.
    loose: u32,
    /// How many binders with a type of the term this context ends with, itself included.
    run: u32,
    /// An ancestor at most `run` binders out (itself when `run` is 0), from which
    /// [`InferCache::skip`] climbs a run in O(log) steps: Myers' skew-binary jump pointers.
    jump: u32,
}

/// `infer`'s memo for one public `infer` or `check` call (`RELATED_WORK.md`
/// §63). A context is named by an id: 0 is the caller's, and entering a
/// binder whose type is the node `a` from context `cid` gives the id
/// interned for `(cid, a)`. Equal ids then mean the same sequence of binder
/// types, which, with the node, is all `infer`'s answer depends on within
/// one call -- it also depends on `g` and the caller's context, but that's
/// sound because the cache is empty when a call starts and emptied when it
/// ends ([`with_infer_cache`]), and both are fixed for that whole call. Keys
/// are node ids, valid for the region the call runs in.
#[derive(Default)]
struct InferCache {
    types: IdMap<(Key, (u32, u32)), Key>,
    contexts: IdMap<(u32, Key), u32>,
    next: u32,
    /// For each context id, its innermost binder.
    info: Vec<CtxBinder>,
    /// Interned windows of binder types, outermost first: (window id of the outer part, the next binder
    /// type inward) to the window's id. 0 is the empty window.
    windows: IdMap<(u32, Key), u32>,
    /// (context id, binders needed) to its window, `None` for a fallback; see [`InferCache::window`].
    window_of: IdMap<(u32, u32), Option<u32>>,
    /// Scratch for [`InferCache::window`]'s walk.
    path: Vec<(u32, u32)>,
    /// [`hc::lowest_loose`]'s memo.
    lows: IdMap<(Key, u32), u32>,
    /// (context id, lowest loose variable, loose range) to [`InferCache::memo_context`]'s answer.
    context_of: IdMap<(u32, u32, u32), (u32, u32)>,
}

thread_local! {
    static INFER_CACHE: std::cell::Cell<InferCache> = std::cell::Cell::default();
}

/// Runs `f` with this thread's [`InferCache`], emptied afterwards ([`InferCache::reset`]). A nested call, or one
/// after a panic, finds the slot empty and starts from a new cache.
fn with_infer_cache<R>(f: impl FnOnce(&mut InferCache) -> R) -> R {
    let mut ic = INFER_CACHE.take();
    let r = f(&mut ic);
    ic.reset();
    INFER_CACHE.set(ic);
    r
}

impl InferCache {
    /// The id of context `cid` extended by a binder of type `a`.
    fn enter(&mut self, s: &Spaces, cid: u32, a: &Expr) -> u32 {
        let next = &mut self.next;
        let info = &mut self.info;
        *self.contexts.entry((cid, s.key(a))).or_insert_with(|| {
            *next += 1;
            if info.len() <= *next as usize {
                info.resize(*next as usize + 1, CtxBinder::default());
            }
            // Jump twice as far as the parent when the parent's jump and its jump's jump span equal
            // lengths, else to the parent: every climb then takes O(log run) steps.
            let p = info[cid as usize];
            let (j, jj) = (info[p.jump as usize], info[info[p.jump as usize].jump as usize]);
            let jump = if p.run > 0 && p.run - j.run == j.run - jj.run { j.jump } else { cid };
            info[*next as usize] = CtxBinder { parent: cid, ty: Some(s.key(a)), loose: s.loose(a), run: p.run + 1, jump };
            *next
        })
    }

    /// The context `lo` binders out from `cid`, or `None` when one of those binders has no type of
    /// the term (or is the caller's).
    fn skip(&self, cid: u32, lo: u32) -> Option<u32> {
        // Context 0 has no entry until a binder is entered.
        let run = |c: u32| self.info.get(c as usize).map_or(0, |b| b.run);
        let target = run(cid).checked_sub(lo)?;
        let mut c = cid;
        while run(c) > target {
            let b = self.info[c as usize];
            c = if run(b.jump) >= target { b.jump } else { b.parent };
        }
        Some(c)
    }

    /// Empties the cache for the next call, keeping its capacity: a sweep makes thousands of calls, and growing
    /// each one's maps from empty was most of `Checker::infer`'s 0.9% under `reserve_rehash` (`docs/tier-cycle.md`,
    /// "where the growth comes from"). Clearing costs time in the capacity, so a map grown past `KEEP` is let go.
    fn reset(&mut self) {
        const KEEP: usize = 1 << 14;
        fn empty_map<K, V>(m: &mut IdMap<K, V>) {
            if m.capacity() > KEEP {
                *m = IdMap::default();
            } else {
                m.clear();
            }
        }
        fn empty_vec<T>(v: &mut Vec<T>) {
            if v.capacity() > KEEP {
                *v = Vec::new();
            } else {
                v.clear();
            }
        }
        // Every field by name, so a field added later fails to compile here until it is emptied too.
        let InferCache {
            types,
            contexts,
            next,
            info,
            windows,
            window_of,
            path,
            lows,
            context_of,
        } = self;
        empty_map(types);
        empty_map(contexts);
        empty_map(windows);
        empty_map(window_of);
        empty_map(lows);
        empty_map(context_of);
        empty_vec(info);
        empty_vec(path);
        *next = 0;
    }

    /// An id no other context has: for a binder type that isn't a node
    /// of the term, like a `Pair`'s inferred first component.
    fn fresh(&mut self) -> u32 {
        self.next += 1;
        if self.info.len() <= self.next as usize {
            self.info.resize(self.next as usize + 1, CtxBinder::default());
        }
        self.info[self.next as usize] = CtxBinder { parent: 0, ty: None, loose: u32::MAX, run: 0, jump: self.next };
        self.next
    }

    /// What `Checker::infer` keys its memo by for node `e` in context `cid`, besides `e`: `(lo, window)`,
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
        // The `lo` innermost binders, which `e` never names, are skipped; skipping a `fresh` binder
        // falls back as passing one inside a window does.
        let r = self.skip(cid, lo).and_then(|c| self.window(c, need - lo)).map_or((0, cid), |w| (lo, WINDOW_BIT | w));
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
            let CtxBinder { parent, loose, .. } = self.info[c as usize];
            if loose == u32::MAX {
                break None;
            }
            path.push((c, k));
            (c, k) = (parent, (k - 1).max(loose));
        };
        for &(c, k) in path.iter().rev() {
            if let Some(outer) = w {
                let next = self.windows.len() as u32 + 1;
                let ty = self.info[c as usize].ty.expect("a window binder has a type");
                w = Some(*self.windows.entry((outer, ty)).or_insert(next));
            }
            self.window_of.insert((c, k), w);
        }
        self.path = path;
        w
    }
}

/// Weak head normal form: reduce only the outermost redex chain.
pub fn whnf(e: &Expr) -> Expr {
    scoped(|| with_spaces(|s| whnf_in(s, e)))
}

/// For an application `e`, its spine's head and its longest proper prefix with no loose variable
/// (`None` for none); `(e, None)` for anything else. Memoised for every application of two or more
/// arguments on the way down, so the levels of a stuck spine, each asking for its own, walk the
/// spine once in all, not once each: that made `nf` and `def_eq` quadratic in a stuck spine's
/// length (`RELATED_WORK.md` §79). One argument is answered directly.
fn spine(s: &Spaces, e: &Expr) -> (Expr, Option<Expr>) {
    let Node::App(f, _) = s.node(e) else { return (*e, None) };
    let closed = (s.loose(&f) == 0).then_some(f);
    if !matches!(s.node(&f), Node::App(..)) {
        return (f, closed);
    }
    if let Some(hit) = hc::spine_get(s, e) {
        return hit;
    }
    let (head, below) = grow(|| spine(s, &f));
    let info = (head, closed.or(below));
    hc::spine_put(s, e, info);
    info
}

/// `whnf_step` for an application spine `h a1 ... ak` (`k >= 2`) whose head reduces to a lambda:
/// peel as many directly nested lambdas as there are arguments and substitute all of them in one
/// `instantiate_n` pass, instead of one `subst_top` per argument, each rebuilding the body the next
/// one rebuilds again. Arguments left over are applied to the result. `None` when the head is not a
/// lambda, so the caller's one-argument path runs unchanged (and keeps a stuck spine's per-prefix
/// cache entries). `head` is the spine's, from [`spine`].
fn beta_spine(s: &Spaces, e: &Expr, head: &Expr) -> Option<Expr> {
    // The head is reduced as the node the spine holds, so its cache entry is shared by every level
    // of the spine; the arguments are collected only once it is a lambda.
    let wh = whnf_in(s, head);
    let Node::Lam(_, first) = s.node(&wh) else { return None };
    let mut args: Vec<Expr> = Vec::new();
    let mut spine = *e;
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
    let used: Vec<&Expr> = args[..taken].iter().collect();
    let mut r = instantiate_n(s, &body, &used, 0);
    for a in &args[taken..] {
        r = app(r, *a);
    }
    Some(whnf_in(s, &r))
}

/// `whnf_step` for a spine `P a1 ... ad` whose longest proper prefix `P` with no loose variable
/// reduces to a lambda: `P`'s head normal form (`hnf_rc`) is instantiated with the arguments. A closed function value used at several places with different arguments -- a Church
/// boolean `xor_ a b` applied to each use's own continuations -- is then reduced once, not once per
/// use, since the memo is keyed by `P`, not by the whole application. `None` when there is no such
/// prefix (`p`, from [`spine`]) or it does not reduce to a lambda; the arguments are collected only
/// once it does.
fn closed_prefix_spine(s: &Spaces, e: &Expr, p: &Expr) -> Option<Expr> {
    let mut body = hnf_rc(s, p);
    if !matches!(s.node(&body), Node::Lam(..)) {
        return None;
    }
    let mut args: Vec<Expr> = Vec::new();
    let mut rest = *e;
    while let Node::App(g, b) = s.node(&rest) {
        args.push(b);
        if s.same(&g, p) {
            break;
        }
        rest = g;
    }
    args.reverse();
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
    let used: Vec<&Expr> = args[..taken].iter().collect();
    let mut r = instantiate_n(s, &body, &used, 0);
    for a in &args[taken..] {
        r = app(r, *a);
    }
    Some(whnf_in(s, &r))
}

/// Head normal form of `p`: its whnf, and while that is a lambda, the body's whnf under it. The
/// work is shared by every application of `p`, memoised by `p`; an application recurses on its
/// function, so the memo also covers each shorter prefix of a spine. It goes under every lambda,
/// not only those the spine's arguments fill: a Church boolean selects under its own `\C t f`, so a
/// table of `mux` gates applied to its first arguments drops the branches they rule out, and each
/// longer prefix holds only its sub-diagram (docs/tier-cycle.md, "Full head normal form").
fn hnf_rc(s: &Spaces, p: &Expr) -> Expr {
    if let Some(hit) = hc::hnf_get(s, p) {
        return hit;
    }
    let r = match s.node(p) {
        Node::App(f, a) => {
            let hf = hnf_rc(s, &f);
            match s.node(&hf) {
                Node::Lam(_, body) => {
                    let x = subst_top(s, &body, &a);
                    let w = whnf_step(s, &x).unwrap_or(x);
                    under_lams(s, w)
                }
                // `hf` is `f`'s head normal form and not a lambda, so `hf a` is stuck.
                _ if s.same(&hf, &f) => *p,
                _ => app(hf, a),
            }
        }
        _ => under_lams(s, whnf_in(s, p)),
    };
    hc::hnf_put(s, p, &r);
    r
}

/// `w` (in whnf) with the body of each nested lambda reduced to whnf in turn.
fn under_lams(s: &Spaces, w: Expr) -> Expr {
    let Node::Lam(a, b) = s.node(&w) else { return w };
    let wb = whnf_step(s, &b).unwrap_or(b);
    let nb = under_lams(s, wb);
    if s.same(&nb, &b) { w } else { lam(a, nb) }
}

/// `whnf`, or `None` when `e` is already in weak head normal form. A stuck
/// term keeps its nodes: its arguments' and also its stuck head's or
/// target's. The memos are keyed by node, and before terms were hash-consed
/// a copy missed them, so each level of a stuck spine reduced the whole
/// spine below it again (`RELATED_WORK.md` §48, §59).
fn whnf_step(s: &Spaces, e: &Expr) -> Option<Expr> {
    grow(|| match s.node(e) {
        Node::App(f, a) => {
            // `e`'s spine facts from `f`'s, asked for only as needed: `f` itself is the common
            // closed prefix, and the head is wanted only once that shortcut fails.
            let closed = if s.loose(&f) == 0 { Some(f) } else { spine(s, &f).1 };
            if let Some(p) = closed
                && let Some(r) = closed_prefix_spine(s, e, &p)
            {
                return Some(r);
            }
            if matches!(s.node(&f), Node::App(..))
                && let Some(r) = beta_spine(s, e, &spine(s, &f).0)
            {
                return Some(r);
            }
            let wf = whnf_in(s, &f);
            match s.node(&wf) {
                Node::Lam(_, body) => {
                    let r = subst_top(s, &body, &a);
                    Some(whnf_in(s, &r))
                }
                _ => (!s.same(&wf, &f)).then(|| app(wf, a)),
            }
        }
        Node::J { motive, base, a, b, p } => {
            let wp = whnf_in(s, &p);
            match s.node(&wp) {
                Node::Refl(_) => Some(whnf_in(s, &app(base, a))),
                _ => (!s.same(&wp, &p)).then(|| jelim(motive, base, a, b, wp)),
            }
        }
        Node::WRec { motive, children_ty, step, target } => {
            let wt = whnf_in(s, &target);
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
                    Some(whnf_in(s, &app(app(app(step, a), f), rec_step)))
                }
                _ => (!s.same(&wt, &target)).then(|| wrec(motive, children_ty, step, wt)),
            }
        }
        Node::SigRec { motive, step, target } => whnf_sigrec(s, motive, step, target),
        _ => None,
    })
}

/// `whnf_step`'s own `SigRec` case, out of line -- see `infer_sigma`.
#[inline(never)]
fn whnf_sigrec(s: &Spaces, motive: Expr, step: Expr, target: Expr) -> Option<Expr> {
    let wt = whnf_in(s, &target);
    match s.node(&wt) {
        Node::Pair(_, a, b) => Some(whnf_in(s, &app(app(step, a), b))),
        _ => (!s.same(&wt, &target)).then(|| sigrec(motive, step, wt)),
    }
}

/// `whnf`, cached -- the same subterm recurs many times within one top-level call once a proof term
/// shares structure. Returns `e` itself when it is already in weak head normal form, so reducing a
/// result again, as `nf` and `def_eq` do with a stuck head, keeps its node and hits the cache from
/// then on.
fn whnf_in(s: &Spaces, e: &Expr) -> Expr {
    if let Some(hit) = hc::whnf_get(s, e) {
        return hit;
    }
    let result = whnf_step(s, e).unwrap_or(*e);
    hc::whnf_put(s, e, &result);
    result
}

/// Full normal form: `whnf`, then recurse structurally into subterms, cached per node.
fn nf_in(s: &Spaces, e: &Expr) -> Expr {
    if let Some(hit) = hc::nf_get(s, e) {
        return hit;
    }
    let w = whnf_in(s, e);
    let result = nf_whnf(s, &w);
    hc::nf_put(s, e, &result);
    result
}

/// `nf` of a term already in weak head normal form: its constructor over
/// the `nf` of each child.
fn nf_whnf(s: &Spaces, w: &Expr) -> Expr {
    grow(|| match s.node(w) {
        Node::Var(_) | Node::Sort(_) | Node::Const(_) | Node::Free(_) => *w,
        n => s.mk(n.map_kids(|c, _| nf_in(s, &c))),
    })
}

/// `nf(a) == nf(b)`, decided without computing either normal form, and
/// sharing the region's memos across both sides -- worthwhile whenever
/// `a`/`b` reference overlapping subterms, which two sides of a proof
/// obligation very often do (the same postulates, the same sub-witnesses).
pub fn def_eq(a: &Expr, b: &Expr) -> bool {
    scoped(|| with_spaces(|s| def_eq_in(s, a, b)))
}

/// [`def_eq`] inside the kernel.
fn def_eq_in(s: &Spaces, a: &Expr, b: &Expr) -> bool {
    EQUAL.with(|m| m.borrow_mut().clear());
    conv(s, a, b)
}

thread_local! {
    /// The pairs one `def_eq` call has shown equal, as `key(a) << 32 | key(b)`.
    static EQUAL: std::cell::RefCell<hashbrown::HashSet<u64>> = std::cell::RefCell::new(hashbrown::HashSet::new());
}

/// `def_eq`'s comparison. Syntactically equal sides are equal without
/// reducing, since `nf` is a function; most calls from `infer` are
/// (`RELATED_WORK.md` §56), and with the spaces hash-consed that test is
/// one id comparison. Else `nf(e)` is `whnf(e)`'s outermost constructor
/// over the `nf` of each child, so the normal forms are equal exactly when
/// the two weak head normal forms have the same constructor and pairwise
/// equal children's normal forms. Recursing on that reduces only where the
/// sides differ (`RELATED_WORK.md` §57).
///
/// A pair already shown equal in this call is answered from `EQUAL`. Without
/// it the walk is a tree walk over shared nodes: two equal but distinct
/// subterms under a case tree that shares its tail (a borrow chain applied to
/// continuations) were compared once per path, 2^n times for n bits
/// (docs/tier-cycle.md, "The countdown invariant is exponential"). Unequal
/// pairs need no entry: the first one ends the call.
fn conv(s: &Spaces, a: &Expr, b: &Expr) -> bool {
    if s.same(a, b) {
        return true;
    }
    let pair = (s.key(a) as u64) << 32 | s.key(b) as u64;
    if EQUAL.with(|m| m.borrow().contains(&pair)) {
        return true;
    }
    let equal = conv_whnf(s, &whnf_in(s, a), &whnf_in(s, b));
    if equal {
        EQUAL.with(|m| m.borrow_mut().insert(pair));
    }
    equal
}

/// Compares two weak head normal forms: same constructor, then `conv` on
/// each pair of children, in the order `nf_in` visits them.
fn conv_whnf(s: &Spaces, x: &Expr, y: &Expr) -> bool {
    let (nx, ny) = (s.node(x), s.node(y));
    grow(|| nx.same_shape(&ny, |p, q| conv(s, p, q)))
}

pub fn normalize(e: &Expr) -> Expr {
    scoped(|| with_spaces(|s| nf_in(s, e)))
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


fn expect_sort(s: &Spaces, e: &Expr) -> Result<u32, String> {
    let w = whnf_in(s, e);
    match s.node(&w) {
        Node::Sort(i) => Ok(i),
        _ => Err(format!("expected a Sort, got {}", brief(&w))),
    }
}

fn expect_pi(s: &Spaces, e: &Expr) -> Result<(Expr, Expr), String> {
    let w = whnf_in(s, e);
    match s.node(&w) {
        Node::Pi(a, b) => Ok((a, b)),
        _ => Err(format!("expected a Pi type, got {}", brief(&w))),
    }
}

fn expect_w(s: &Spaces, e: &Expr) -> Result<(Expr, Expr), String> {
    let w = whnf_in(s, e);
    match s.node(&w) {
        Node::W(a, b) => Ok((a, b)),
        _ => Err(format!("expected a W type, got {}", brief(&w))),
    }
}

fn expect_sigma(s: &Spaces, e: &Expr) -> Result<(Expr, Expr), String> {
    let w = whnf_in(s, e);
    match s.node(&w) {
        Node::Sigma(a, b) => Ok((a, b)),
        _ => Err(format!("expected a Sigma type, got {}", brief(&w))),
    }
}

/// One type check in progress: the spaces and globals it reads, the inference memo, and the context entered so far with
/// its id (`InferCache::enter`).
struct Checker<'c> {
    s: &'c Spaces,
    g: &'c Globals,
    ic: &'c mut InferCache,
    ctx: CtxScope,
    cid: u32,
}

impl Checker<'_> {
    /// Runs `f` under one more binder, of type `a` and context id `cid`, restoring the context afterwards (on error too).
    fn under<R>(&mut self, a: Expr, cid: u32, f: impl FnOnce(&mut Self) -> R) -> R {
        let (depth, outer) = (self.ctx.local.len(), self.cid);
        self.ctx.local.push(a);
        self.cid = cid;
        let r = f(self);
        self.ctx.local.truncate(depth);
        self.cid = outer;
        r
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
    fn infer_sigma(&mut self, a: &Expr, b: &Expr) -> Result<Expr, String> {
        let s = self.s;
        let i = expect_sort(s, &self.infer(a)?)?;
        let cid2 = self.ic.enter(s, self.cid, a);
        let j = self.under(*a, cid2, |c| c.infer(b));
        let j = expect_sort(s, &j?)?;
        Ok(sort(i.max(j)))
    }

    #[inline(never)]
    fn infer_pair(&mut self, fam: &Expr, a: &Expr, b: &Expr) -> Result<Expr, String> {
        let s = self.s;
        let ta = self.infer(a)?;
        let cid2 = self.ic.fresh();
        let tf = self.under(ta, cid2, |c| c.infer(fam));
        expect_sort(s, &tf?)?;
        let expected_b_ty = subst_top(s, fam, a);
        self.check(b, &expected_b_ty)?;
        Ok(sigma(ta, *fam))
    }

    #[inline(never)]
    fn infer_sigrec(&mut self, motive: &Expr, step: &Expr, target: &Expr) -> Result<Expr, String> {
        let s = self.s;
        let (sa, sb) = expect_sigma(s, &self.infer(target)?)?;
        self.infer(motive)?; // sanity: motive must itself be well-typed

        // step : Pi a:A. Pi b:B(a). motive (pair(B,a,b))
        // `sb` already assumes exactly one binder (`Sigma`'s own convention)
        // -- b's own domain under binder `a` (depth1) is `sb` unchanged, the
        // same way `WRec`'s own `f_dom_d1` reuses `wb` unchanged.
        let b_dom_d1 = sb;
        // under binders a(Var1), b(Var0) -- depth2:
        let motive_d2 = shift_in(s, motive, 0, 2);
        // `sb`'s own bound tag (Var0) must stay untouched (`Pair`'s own `fam`
        // field needs a *fresh* tag binder of its own, one level below
        // wherever the `Pair` itself sits) -- only whatever `sb` references
        // *above* that (the 2 extra binders `a`/`b` now sitting between it
        // and the ambient context) shifts, cutoff 1.
        let fam_d2 = shift_in(s, &sb, 1, 2);
        let concl_d2 = app(motive_d2, pair(fam_d2, var(1), var(0)));
        let expected_step_ty = pi(sa, pi(b_dom_d1, concl_d2));
        self.check(step, &expected_step_ty)?;

        Ok(app(*motive, *target))
    }

    /// `infer`'s own `Sup` arm, out of line: `ta`/`dom`/`cod`/`w_candidate`/
    /// `wa`/`wb` would otherwise sit in `infer`'s frame on every call (see
    /// `infer_sigma`).
    #[inline(never)]
    fn infer_sup(&mut self, a: &Expr, f: &Expr) -> Result<Expr, String> {
        let s = self.s;
        let ta = self.infer(a)?;
        let (dom, cod) = expect_pi(s, &self.infer(f)?)?;
        // `cod` is written one binder deeper than `f`'s own domain binder; a
        // `Sup`'s codomain must not actually depend on it -- enforced here
        // (not just documented), by an occurs-check on `cod`'s own normal
        // form, since `subst_top` just below would otherwise only ever be
        // validated at this one concrete `a`, silently trusting every other
        // point of `f`'s domain agrees.
        let cod_nf = nf_in(s, &cod);
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

    /// `infer` on a child. A node with two or more parents is memoised by
    /// node and context id, so a shared subterm is inferred once per context
    /// rather than once per occurrence (`RELATED_WORK.md` §63). A node with one
    /// parent can only be reached twice through a shared ancestor, which is
    /// memoised instead, so skipping it keeps the walk linear in the DAG and
    /// costs unshared terms no hashing. Only successes are stored: an error
    /// ends the whole check.
    fn infer(&mut self, e: &Expr) -> Result<Expr, String> {
        let s = self.s;
        if !s.shared(e) {
            return self.infer_node(e);
        }
        // Keyed by the window of binders the node can depend on, not the whole context, so one
        // inference serves every binder stack that agrees on that window (bit-vector design doc §50:
        // 96 to 99.5% of the whole-context misses were such repeats).
        let key = (s.key(e), self.ic.memo_context(s, self.cid, e));
        if let Some(ty) = self.ic.types.get(&key) {
            return Ok(s.expr_of(ty));
        }
        let ty = self.infer_node(e)?;
        self.ic.types.insert(key, s.key(&ty));
        Ok(ty)
    }

    fn infer_node(&mut self, e: &Expr) -> Result<Expr, String> {
        let s = self.s;
        grow(|| match s.node(e) {
            Node::Var(k) => ctx_lookup(s, &self.ctx, k),
            Node::Sort(i) => i.checked_add(1).map(sort).ok_or_else(|| format!("universe overflow: no successor sort above Type{i}")),
            Node::Const(l) => const_type(s, self.g, l),
            Node::Free(l) => Err(free_escaped(l)),
            Node::Pi(a, b) => {
                let i = expect_sort(s, &self.infer(&a)?)?;
                let cid2 = self.ic.enter(s, self.cid, &a);
                let j = self.under(a, cid2, |c| c.infer(&b));
                let j = expect_sort(s, &j?)?;
                Ok(sort(i.max(j)))
            }
            Node::Lam(a, body) => {
                expect_sort(s, &self.infer(&a)?)?;
                let cid2 = self.ic.enter(s, self.cid, &a);
                let tbody = self.under(a, cid2, |c| c.infer(&body));
                let tbody = tbody?;
                Ok(pi(a, tbody))
            }
            Node::App(..) => {
                // The whole spine `h a1 ... ak` at once, as `beta_spine` does for reduction: each domain
                // is instantiated with the arguments before it and the last codomain once with all of
                // them, instead of one `subst_top` per argument, each copying the rest of the telescope.
                // A codomain that is not syntactically a Pi takes the pending arguments first, then whnf.
                let mut args = vec![];
                let mut head = *e;
                while let Node::App(f, a) = s.node(&head) {
                    args.push(a);
                    head = f;
                }
                args.reverse();
                let mut ty = self.infer(&head)?;
                let mut pending: Vec<&Expr> = vec![];
                for a in &args {
                    if !matches!(s.node(&ty), Node::Pi(..)) && !pending.is_empty() {
                        ty = instantiate_n(s, &ty, &pending, 0);
                        pending.clear();
                    }
                    let (dom, cod) = expect_pi(s, &ty)?;
                    let dom = if pending.is_empty() { dom } else { instantiate_n(s, &dom, &pending, 0) };
                    self.check(a, &dom)?;
                    pending.push(a);
                    ty = cod;
                }
                Ok(instantiate_n(s, &ty, &pending, 0))
            }
            Node::Id(a, x, y) => {
                let i = expect_sort(s, &self.infer(&a)?)?;
                self.check(&x, &a)?;
                self.check(&y, &a)?;
                Ok(sort(i))
            }
            Node::Refl(a) => {
                let ta = self.infer(&a)?;
                Ok(id(ta, a, a))
            }
            Node::J { motive, base, a, b, p } => {
                let ta = self.infer(&a)?;
                self.check(&b, &ta)?;
                self.check(&p, &id(ta, a, b))?;
                self.infer(&motive)?; // sanity: motive must itself be well-typed
                let expected_base_ty = pi(ta, app3(shift_in(s, &motive, 0, 1), var(0), var(0), refl(var(0))));
                self.check(&base, &expected_base_ty)?;
                Ok(app3(motive, a, b, p))
            }
            Node::W(a, b) => {
                let i = expect_sort(s, &self.infer(&a)?)?;
                let cid2 = self.ic.enter(s, self.cid, &a);
                let j = self.under(a, cid2, |c| c.infer(&b));
                let j = expect_sort(s, &j?)?;
                Ok(sort(i.max(j)))
            }
            Node::Sup(a, f) => self.infer_sup(&a, &f),
            Node::WRec { motive, children_ty, step, target } => {
                let (wa, wb) = expect_w(s, &self.infer(&target)?)?;
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
                self.infer(&motive)?;
                let w_ty0 = wty(wa, wb);

                // f : B(a) -> W(A,B), formed under binder `a` (depth 1).
                let f_dom_d1 = wb; // wb already assumes exactly one binder
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

                let expected_step_ty = pi(wa, pi(f_ty_d1, arrow_ty_d2));
                self.check(&step, &expected_step_ty)?;

                Ok(app(motive, target))
            }
            Node::Sigma(a, b) => self.infer_sigma(&a, &b),
            Node::Pair(fam, a, b) => self.infer_pair(&fam, &a, &b),
            Node::SigRec { motive, step, target } => self.infer_sigrec(&motive, &step, &target),
        })
    }

    fn check(&mut self, e: &Expr, expected: &Expr) -> Result<(), String> {
        let s = self.s;
        grow(|| {
            if let Node::Lam(a, body) = s.node(e)
                && let Node::Pi(dom, cod) = s.node(&whnf_in(s, expected))
            {
                // As `infer`'s `Lam` rule does: `def_eq` alone would accept an
                // ill-typed annotation that reduces to `dom`.
                expect_sort(s, &self.infer(&a)?)?;
                if !def_eq_in(s, &a, &dom) {
                    return Err(format!("lambda domain mismatch: {} vs {}", brief(&a), brief(&dom)));
                }
                let cid2 = self.ic.enter(s, self.cid, &a);
                return self.under(a, cid2, |c| c.check(&body, &cod));
            }
            let inferred = self.infer(e)?;
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
}




/// `infer`'s own `WRec` mismatch error, out of line and `#[cold]` so its
/// own locals (two `nf` calls, a `format!`) stay off `infer`'s hot frame
/// (see `infer_sigma`).
#[cold]
#[inline(never)]
fn wrec_children_ty_mismatch(children_ty: &Expr, wb: &Expr) -> String {
    format!("wrec: children_ty doesn't match target's own real children-type: {} vs {}", brief_nf(children_ty), brief_nf(wb))
}


/// `e`'s type, with constants typed by `globals` and variables by `ctx`.
/// A `Free` anywhere in `e` is an error; so is one in a `ctx` entry, when
/// `e` uses it.
///
/// Checked here, not only at the leaf: `infer` hands some children to
/// `Checker::check` (an `App`'s argument, `Id`'s sides, `J`'s fields), whose
/// `Lam` rule against a `Pi` compares the domain by `def_eq` and never
/// infers it, and `WRec`'s `children_ty` is only compared, so a `Free`
/// under a redex in any of them would reduce away unseen. `free` is
/// O(1).
pub fn infer_in(globals: &Globals, ctx: &Ctx, e: &Expr) -> Result<Expr, String> {
    if e.free() > 0 {
        return Err(free_escaped(e.free() - 1));
    }
    scoped(|| with_spaces(|s| with_infer_cache(|ic| Checker { s, g: globals, ic, ctx: CtxScope::new(ctx), cid: 0 }.infer_node(e))))
}

/// [`infer_in`] with no globals.
pub fn infer(ctx: &Ctx, e: &Expr) -> Result<Expr, String> {
    infer_in(&Globals::new(), ctx, e)
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
    scoped(|| {
        with_spaces(|s| {
            let large = hc::large(s, e, expected);
            let body = || {
                with_infer_cache(|ic| {
                    let mut c = Checker { s, g: globals, ic, ctx: CtxScope::new(ctx), cid: 0 };
                    expect_sort(s, &c.infer(expected)?)?;
                    c.check(e, expected)
                })
            };
            if large { on_segment(CHECK_SEGMENT, body) } else { body() }
        })
    })
}

/// [`check_in`] with no globals.
pub fn check(ctx: &Ctx, e: &Expr, expected: &Expr) -> Result<(), String> {
    check_in(&Globals::new(), ctx, e, expected)
}

/// (distinct nodes, nodes counted once per occurrence) in `e`.
pub fn term_sizes(e: &Expr) -> (usize, u128) {
    fn go(e: &Expr, seen: &mut HashMap<u64, u128>) -> u128 {
        let mut n = 1u128;
        e.node().for_kids(|p, _| {
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


/// Typecheck a closed term and return its normalized type.
pub fn typecheck(e: &Expr) -> Result<Expr, String> {
    scoped(|| infer(&Ctx::new(), e).map(|t| with_spaces(|s| nf_in(s, &t))))
}

mod spaces;
mod postulates;
pub use postulates::*;

pub mod bin;

#[cfg(test)]
mod tests;

