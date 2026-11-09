use super::*;

// --- nodes -----------------------------------------------------------------
//
// A term is a handle (`Expr`) to its outermost node, and the node holds its children as handles, so every subterm is
// a node and a term is a DAG. Each node caches its loose-variable and free-level ranges, computed from its children
// when it is built: `shift`, `instantiate` and `is_var_free` read them to skip the subterms they would leave
// unchanged, and keep those as they are (`docs/related-work/` §64).

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
    pub(super) r: Ref,
    pub(super) epoch: u32,
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

/// This thread's kernel work so far: calls to the recursive workers (`shift`, `instantiate`, `whnf` step, `nf`, `conv`,
/// and `infer` on a type-cache miss), counted in every build. Deterministic for a given input and memo state, so
/// differences of it measure work where a clock measures load; a thread reports only its own.
pub fn work() -> u64 {
    with_spaces(|s| s.work())
}

/// A map key naming a node: its resolved `Ref`'s bits.
pub(crate) type Key = u32;

/// The bounds slot's limits (`Spaces::bounds_slot`): depths below `DEPTH_CAP` are stored; a bound is stored up to `BOUND_CAP`.
const DEPTH_CAP: u32 = 1 << 15;
const BOUND_CAP: u64 = (1 << 24) - 1;

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

    /// The node's remembered bounds `(lo, hi)` on its lowest loose variable from depth `d` (`hc::uses`), if the slot
    /// holds depth `d`. The slot is one word: bit 63 set, `d` in 15 bits, `lo` and `hi` in 24 bits each. It only ever
    /// loosens a bound: a `lo` past the cap is stored as the cap (a lower bound may go down), a `hi` past it as the cap
    /// too, which reads back as `u32::MAX` (unbounded); a `d` that doesn't fit is never stored.
    #[inline(always)]
    pub(crate) fn bounds_slot(&self, e: &Expr, d: u32) -> Option<(u32, u32)> {
        let s = self.bounds_at(self.res(e));
        (d < DEPTH_CAP && s >> 63 == 1 && (s >> 48) & (DEPTH_CAP as u64 - 1) == d as u64).then(|| {
            let hi = (s & BOUND_CAP) as u32;
            (((s >> 24) & BOUND_CAP) as u32, if hi as u64 == BOUND_CAP { u32::MAX } else { hi })
        })
    }

    #[inline(always)]
    pub(crate) fn set_bounds_slot(&self, e: &Expr, d: u32, lo: u32, hi: u32) {
        if d < DEPTH_CAP {
            let (lo, hi) = ((lo as u64).min(BOUND_CAP), (hi as u64).min(BOUND_CAP));
            self.set_bounds_at(self.res(e), 1 << 63 | (d as u64) << 48 | lo << 24 | hi);
        }
    }
}

/// Structural equality. The spaces are hash-consed, so two terms are equal exactly when their handles name the same
/// node: one comparison, no walk.
impl PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        with_spaces(|s| s.same(self, other))
    }
}

impl Eq for Expr {}

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

