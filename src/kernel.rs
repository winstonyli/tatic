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
use std::rc::Rc;

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
    struct Restore(usize);
    impl Drop for Restore {
        fn drop(&mut self) {
            FLOOR.with(|f| f.set(self.0));
        }
    }
    if FLOOR.with(|f| f.get()) == usize::MAX
        && let Some(floor) = floor_here()
    {
        FLOOR.with(|f| f.set(floor));
        if stack_ok() {
            return f();
        }
    }
    stacker::grow(STACK_PER_RECURSION, || {
        let _restore = Restore(FLOOR.with(|f| f.replace(floor_here().unwrap_or(usize::MAX))));
        f()
    })
}

/// Recursive fields are `Rc`, not `Box`: `Expr` is built and re-threaded
/// through deeply nested proof terms (`proof.rs`'s `Anchored`, the Ev-witness
/// builder's per-call-site composition, ...) almost entirely by `.clone()`,
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
        grow(|| same_shape(self, other, |p, q| p == q))
    }
}

/// Whether `x` and `y` have the same outermost constructor (and index, for
/// `Var`/`Sort`) and `c` holds of each pair of children, in field order,
/// stopping at the first that fails. Syntactic equality and `conv_whnf`
/// are both this with a different `c`.
fn same_shape(x: &Expr, y: &Expr, mut c: impl FnMut(&Rc<Expr>, &Rc<Expr>) -> bool) -> bool {
    use Expr::*;
    match (x, y) {
        (Var(i), Var(j)) | (Sort(i), Sort(j)) => i == j,
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
            Expr::Var(_) | Expr::Sort(_) => {}
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

impl fmt::Debug for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        grow(|| match self {
            Expr::Var(k) => write!(f, "#{k}"),
            Expr::Sort(i) => write!(f, "Type{i}"),
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
pub fn pi(a: Expr, b: Expr) -> Expr {
    Expr::Pi(Rc::new(a), Rc::new(b))
}
pub fn lam(a: Expr, body: Expr) -> Expr {
    Expr::Lam(Rc::new(a), Rc::new(body))
}
pub fn app(f: Expr, a: Expr) -> Expr {
    Expr::App(Rc::new(f), Rc::new(a))
}
pub fn app2(f: Expr, a: Expr, b: Expr) -> Expr {
    app(app(f, a), b)
}
pub fn app3(f: Expr, a: Expr, b: Expr, c: Expr) -> Expr {
    app(app2(f, a, b), c)
}
pub fn id(a: Expr, x: Expr, y: Expr) -> Expr {
    Expr::Id(Rc::new(a), Rc::new(x), Rc::new(y))
}
pub fn refl(a: Expr) -> Expr {
    Expr::Refl(Rc::new(a))
}
pub fn jelim(motive: Expr, base: Expr, a: Expr, b: Expr, p: Expr) -> Expr {
    Expr::J {
        motive: Rc::new(motive),
        base: Rc::new(base),
        a: Rc::new(a),
        b: Rc::new(b),
        p: Rc::new(p),
    }
}
pub fn wty(a: Expr, b: Expr) -> Expr {
    Expr::W(Rc::new(a), Rc::new(b))
}
pub fn sup(a: Expr, f: Expr) -> Expr {
    Expr::Sup(Rc::new(a), Rc::new(f))
}
pub fn wrec(motive: Expr, children_ty: Expr, step: Expr, target: Expr) -> Expr {
    Expr::WRec {
        motive: Rc::new(motive),
        children_ty: Rc::new(children_ty),
        step: Rc::new(step),
        target: Rc::new(target),
    }
}
pub fn sigma(a: Expr, b: Expr) -> Expr {
    Expr::Sigma(Rc::new(a), Rc::new(b))
}
pub fn pair(fam: Expr, a: Expr, b: Expr) -> Expr {
    Expr::Pair(Rc::new(fam), Rc::new(a), Rc::new(b))
}
pub fn sigrec(motive: Expr, step: Expr, target: Expr) -> Expr {
    Expr::SigRec {
        motive: Rc::new(motive),
        step: Rc::new(step),
        target: Rc::new(target),
    }
}
/// A non-dependent function type `a -> b`.
pub fn arrow(a: Expr, b: Expr) -> Expr {
    pi(a, shift(&b, 0, 1))
}

// --- shifting & substitution (standard de Bruijn machinery) -------------

/// Add `amount` to every free variable at or above `cutoff`. Exposed
/// (beyond this module's own substitution machinery) for reindexing a
/// term built at one ambient context depth for reuse at a deeper one --
/// see `proof.rs`'s `Anchored`.
pub fn shift(e: &Expr, cutoff: u32, amount: i32) -> Expr {
    // Adding 0 changes no index, so this is provably the identity on `e`
    // regardless of its content -- skip the full recursive rebuild.
    if amount == 0 {
        return e.clone();
    }
    grow(|| match e {
        Expr::Var(k) => {
            if *k >= cutoff {
                Expr::Var((*k as i32 + amount) as u32)
            } else {
                Expr::Var(*k)
            }
        }
        Expr::Sort(i) => Expr::Sort(*i),
        Expr::Pi(a, b) => pi(shift(a, cutoff, amount), shift(b, cutoff + 1, amount)),
        Expr::Lam(a, b) => lam(shift(a, cutoff, amount), shift(b, cutoff + 1, amount)),
        Expr::App(f, a) => app(shift(f, cutoff, amount), shift(a, cutoff, amount)),
        Expr::Id(a, x, y) => id(
            shift(a, cutoff, amount),
            shift(x, cutoff, amount),
            shift(y, cutoff, amount),
        ),
        Expr::Refl(a) => refl(shift(a, cutoff, amount)),
        Expr::J {
            motive,
            base,
            a,
            b,
            p,
        } => jelim(
            shift(motive, cutoff, amount),
            shift(base, cutoff, amount),
            shift(a, cutoff, amount),
            shift(b, cutoff, amount),
            shift(p, cutoff, amount),
        ),
        Expr::W(a, b) => wty(shift(a, cutoff, amount), shift(b, cutoff + 1, amount)),
        Expr::Sup(a, f) => sup(shift(a, cutoff, amount), shift(f, cutoff, amount)),
        Expr::WRec {
            motive,
            children_ty,
            step,
            target,
        } => wrec(
            shift(motive, cutoff, amount),
            shift(children_ty, cutoff + 1, amount),
            shift(step, cutoff, amount),
            shift(target, cutoff, amount),
        ),
        Expr::Sigma(..) | Expr::Pair(..) | Expr::SigRec { .. } => shift_sigma_family(e, cutoff, amount),
    })
}

/// `shift`'s own `Sigma`/`Pair`/`SigRec` cases, out of line -- see
/// `infer_sigma`'s docs for why these extractions exist and why they
/// are kept.
#[inline(never)]
fn shift_sigma_family(e: &Expr, cutoff: u32, amount: i32) -> Expr {
    match e {
        Expr::Sigma(a, b) => sigma(shift(a, cutoff, amount), shift(b, cutoff + 1, amount)),
        Expr::Pair(fam, a, b) => pair(
            shift(fam, cutoff + 1, amount),
            shift(a, cutoff, amount),
            shift(b, cutoff, amount),
        ),
        Expr::SigRec { motive, step, target } => sigrec(
            shift(motive, cutoff, amount),
            shift(step, cutoff, amount),
            shift(target, cutoff, amount),
        ),
        _ => unreachable!("shift_sigma_family called on a non-Sigma-family Expr"),
    }
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
fn instantiate(e: &Expr, s: &Expr, d: u32) -> Expr {
    let go = |x: &Rc<Expr>, d: u32| instantiate(x, s, d);
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
fn is_var_free(e: &Expr, idx: u32) -> bool {
    grow(|| match e {
        Expr::Var(k) => *k == idx,
        Expr::Sort(_) => false,
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
    format!("sup: children function's codomain must not depend on its own argument: {cod_nf:?}")
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
/// `Anchored` value or `cong_n` argument in multiple positions), is
/// normalized once and reused everywhere else it's referenced, instead of
/// being re-walked -- and, for `whnf` specifically, potentially
/// re-beta-reduced, which is where repeated-substitution cost actually
/// lives -- from scratch at every occurrence.
#[derive(Default)]
struct ReductionCache {
    whnf: HashMap<PtrKey, Rc<Expr>>,
    nf: HashMap<PtrKey, Expr>,
    /// Pairs `def_eq` found syntactically unequal; see [`eq_noting`].
    unequal: HashSet<(PtrKey, PtrKey)>,
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

/// `whnf`, or `None` when `e` is already in weak head normal form. A stuck
/// term keeps its allocations: its arguments' and also its stuck head's or
/// target's. `ReductionCache` is keyed by pointer, so a copy misses it,
/// and each level of a stuck spine then reduced the whole spine below it
/// again (`RELATED_WORK.md` §48, §59).
fn whnf_step(e: &Expr, cache: &mut ReductionCache) -> Option<Expr> {
    grow(|| match e {
        Expr::App(f, a) => {
            let wf = whnf_rc(f, cache);
            match &*wf {
                Expr::Lam(_, body) => Some(whnf_impl(&subst_top(body, a), cache)),
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
    grow(|| match w {
        Expr::Var(k) => Expr::Var(*k),
        Expr::Sort(i) => Expr::Sort(*i),
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
    grow(|| same_shape(x, y, |p, q| conv_rc(p, q, cache)))
}

/// `a == b`, noting in `unequal` each pair of children found unequal on
/// the way. `conv` recurses into exactly those pairs next, and without the
/// note each would repeat the walk below it: quadratic on a chain that
/// differs only at the bottom (`RELATED_WORK.md` §61).
fn eq_noting(a: &Expr, b: &Expr, unequal: &mut HashSet<(PtrKey, PtrKey)>) -> bool {
    grow(|| {
        same_shape(a, b, |p, q| {
            Rc::ptr_eq(p, q) || eq_noting(p, q, unequal) || {
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

/// Wraps `ctx[base_len..]` (everything appended to `ctx` since it had
/// length `base_len`) as nested `Pi` binders around `body`, which must
/// have been built using `ctx` in full (i.e. that suffix as ambient
/// context, the way ordinary `Postulates`-based code already builds
/// terms). No reindexing is needed beyond what's already stored: `ctx[i]`
/// was written assuming exactly `i` prior bindings, which is exactly what
/// `Pi`'s own convention wants for the domain sitting at that same depth.
///
/// This turns "N more things were pushed onto the context, then this term
/// was built" into a single closed `Pi`-type valid in `ctx[..base_len]` --
/// the general tool for building a postulate's type when its type itself
/// needs to quantify over freshly-introduced variables (see `proof.rs`'s
/// `params_and_close`, built on top of this).
pub fn close_pi(base_len: usize, ctx: &Ctx, body: Expr) -> Expr {
    ctx.iter()
        .skip(base_len)
        .rev()
        .fold(body, |acc, dom| pi(dom.clone(), acc))
}

/// Like `close_pi`, but builds the corresponding *value* (`Lam` binders,
/// one per domain in `ctx[base_len..]`) instead of the type those binders
/// have -- for when the goal is a term of that `Pi`-type (e.g. a motive or
/// a proof to pass as an argument), not the type itself.
pub fn close_lam(base_len: usize, ctx: &Ctx, body: Expr) -> Expr {
    ctx.iter()
        .skip(base_len)
        .rev()
        .fold(body, |acc, dom| lam(dom.clone(), acc))
}

fn ctx_lookup(ctx: &Ctx, k: u32) -> Option<Expr> {
    let k_usize = k as usize;
    if k_usize >= ctx.len() {
        return None;
    }
    let idx = ctx.len() - 1 - k_usize;
    // `ctx[idx]` was checked when the context had length `idx` (that many
    // entries existed before it was pushed); reinterpreting it at the
    // current length requires shifting by `k + 1`, not `k` — e.g. for
    // `Var(0)` itself (k=0), its stored type was written one binder
    // shallower than "now", so it still needs a shift of 1.
    Some(shift(&ctx[idx], 0, k as i32 + 1))
}

fn expect_sort(e: &Expr) -> Result<u32, String> {
    match whnf(e) {
        Expr::Sort(i) => Ok(i),
        other => Err(format!("expected a Sort, got {other:?}")),
    }
}

fn expect_pi(e: &Expr) -> Result<(Expr, Expr), String> {
    match whnf(e) {
        Expr::Pi(ref a, ref b) => Ok(((**a).clone(), (**b).clone())),
        other => Err(format!("expected a Pi type, got {other:?}")),
    }
}

fn expect_w(e: &Expr) -> Result<(Expr, Expr), String> {
    match whnf(e) {
        Expr::W(ref a, ref b) => Ok(((**a).clone(), (**b).clone())),
        other => Err(format!("expected a W type, got {other:?}")),
    }
}

fn expect_sigma(e: &Expr) -> Result<(Expr, Expr), String> {
    match whnf(e) {
        Expr::Sigma(ref a, ref b) => Ok(((**a).clone(), (**b).clone())),
        other => Err(format!("expected a Sigma type, got {other:?}")),
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
fn infer_sigma(ctx: &Ctx, a: &Rc<Expr>, b: &Rc<Expr>) -> Result<Expr, String> {
    let i = expect_sort(&infer(ctx, a)?)?;
    let mut ctx2 = ctx.clone();
    ctx2.push_back((**a).clone());
    let j = expect_sort(&infer(&ctx2, b)?)?;
    Ok(Expr::Sort(i.max(j)))
}

#[inline(never)]
fn infer_pair(ctx: &Ctx, fam: &Rc<Expr>, a: &Rc<Expr>, b: &Rc<Expr>) -> Result<Expr, String> {
    let ta = infer(ctx, a)?;
    let mut ctx2 = ctx.clone();
    ctx2.push_back(ta.clone());
    expect_sort(&infer(&ctx2, fam)?)?;
    let expected_b_ty = subst_top(fam, a);
    check(ctx, b, &expected_b_ty)?;
    Ok(sigma(ta, (**fam).clone()))
}

#[inline(never)]
fn infer_sigrec(ctx: &Ctx, motive: &Rc<Expr>, step: &Rc<Expr>, target: &Rc<Expr>) -> Result<Expr, String> {
    let (sa, sb) = expect_sigma(&infer(ctx, target)?)?;
    infer(ctx, motive)?; // sanity: motive must itself be well-typed

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
    check(ctx, step, &expected_step_ty)?;

    Ok(app((**motive).clone(), (**target).clone()))
}

/// `infer`'s own `WRec` mismatch error, out of line and `#[cold]` so its
/// own locals (two `nf` calls, a `format!`) stay off `infer`'s hot frame
/// (see `infer_sigma`).
#[cold]
#[inline(never)]
fn wrec_children_ty_mismatch(children_ty: &Expr, wb: &Expr) -> String {
    format!("wrec: children_ty doesn't match target's own real children-type: {:?} vs {:?}", nf(children_ty), nf(wb))
}

/// `infer`'s own `Sup` arm, out of line: `ta`/`dom`/`cod`/`w_candidate`/
/// `wa`/`wb` would otherwise sit in `infer`'s frame on every call (see
/// `infer_sigma`).
#[inline(never)]
fn infer_sup(ctx: &Ctx, a: &Rc<Expr>, f: &Rc<Expr>) -> Result<Expr, String> {
    let ta = infer(ctx, a)?;
    let (dom, cod) = expect_pi(&infer(ctx, f)?)?;
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
        return Err(format!("sup: element type mismatch: {wa:?} vs {ta:?}"));
    }
    let expected_dom = subst_top(&wb, a);
    if !def_eq(&dom, &expected_dom) {
        return Err(format!(
            "sup: children-function domain mismatch: {dom:?} vs {expected_dom:?}"
        ));
    }
    Ok(wty(wa, wb))
}

pub fn infer(ctx: &Ctx, e: &Expr) -> Result<Expr, String> {
    grow(|| match e {
        Expr::Var(k) => ctx_lookup(ctx, *k).ok_or_else(|| format!("unbound variable #{k}")),
        Expr::Sort(i) => i.checked_add(1).map(Expr::Sort).ok_or_else(|| format!("universe overflow: no successor sort above Type{i}")),
        Expr::Pi(a, b) => {
            let i = expect_sort(&infer(ctx, a)?)?;
            let mut ctx2 = ctx.clone();
            ctx2.push_back((**a).clone());
            let j = expect_sort(&infer(&ctx2, b)?)?;
            Ok(Expr::Sort(i.max(j)))
        }
        Expr::Lam(a, body) => {
            expect_sort(&infer(ctx, a)?)?;
            let mut ctx2 = ctx.clone();
            ctx2.push_back((**a).clone());
            let tbody = infer(&ctx2, body)?;
            Ok(pi((**a).clone(), tbody))
        }
        Expr::App(f, a) => {
            let (dom, cod) = expect_pi(&infer(ctx, f)?)?;
            check(ctx, a, &dom)?;
            Ok(subst_top(&cod, a))
        }
        Expr::Id(a, x, y) => {
            let i = expect_sort(&infer(ctx, a)?)?;
            check(ctx, x, a)?;
            check(ctx, y, a)?;
            Ok(Expr::Sort(i))
        }
        Expr::Refl(a) => {
            let ta = infer(ctx, a)?;
            Ok(id(ta, (**a).clone(), (**a).clone()))
        }
        Expr::J {
            motive,
            base,
            a,
            b,
            p,
        } => {
            let ta = infer(ctx, a)?;
            check(ctx, b, &ta)?;
            check(ctx, p, &id(ta.clone(), (**a).clone(), (**b).clone()))?;
            infer(ctx, motive)?; // sanity: motive must itself be well-typed
            let expected_base_ty = pi(
                ta.clone(),
                app3(
                    shift(motive, 0, 1),
                    var(0),
                    var(0),
                    refl(var(0)),
                ),
            );
            check(ctx, base, &expected_base_ty)?;
            Ok(app3(
                (**motive).clone(),
                (**a).clone(),
                (**b).clone(),
                (**p).clone(),
            ))
        }
        Expr::W(a, b) => {
            let i = expect_sort(&infer(ctx, a)?)?;
            let mut ctx2 = ctx.clone();
            ctx2.push_back((**a).clone());
            let j = expect_sort(&infer(&ctx2, b)?)?;
            Ok(Expr::Sort(i.max(j)))
        }
        Expr::Sup(a, f) => infer_sup(ctx, a, f),
        Expr::WRec {
            motive,
            children_ty,
            step,
            target,
        } => {
            let (wa, wb) = expect_w(&infer(ctx, target)?)?;
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
            infer(ctx, motive)?;
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
            check(ctx, step, &expected_step_ty)?;

            Ok(app((**motive).clone(), (**target).clone()))
        }
        Expr::Sigma(a, b) => infer_sigma(ctx, a, b),
        Expr::Pair(fam, a, b) => infer_pair(ctx, fam, a, b),
        Expr::SigRec { motive, step, target } => infer_sigrec(ctx, motive, step, target),
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
pub fn check(ctx: &Ctx, e: &Expr, expected: &Expr) -> Result<(), String> {
    grow(|| {
        if let Expr::Lam(a, body) = e
            && let Expr::Pi(ref dom, ref cod) = whnf(expected)
        {
            if !def_eq(a, dom) {
                return Err(format!("lambda domain mismatch: {a:?} vs {dom:?}"));
            }
            let mut ctx2 = ctx.clone();
            ctx2.push_back((**a).clone());
            return check(&ctx2, body, cod);
        }
        let inferred = infer(ctx, e)?;
        if def_eq(&inferred, expected) {
            Ok(())
        } else {
            Err(format!(
                "type mismatch: inferred {:?}, expected {:?}",
                nf(&inferred),
                nf(expected)
            ))
        }
    })
}

/// Typecheck a closed term and return its normalized type.
pub fn typecheck(e: &Expr) -> Result<Expr, String> {
    infer(&Ctx::new(), e).map(|t| nf(&t))
}

/// Builds a context of *postulated* (assumed) constants: pushes a type and
/// returns a handle that can be resolved, at any later point while still
/// building on the same context, to the `Var` that correctly refers to it
/// (it self-adjusts for how many more postulates have been pushed since).
///
/// Used instead of trying to derive base types like Bool/Nat/Int from
/// nothing. That turns out to be a real dead end, not just tedium: any
/// "vacuous eliminator" for an empty/base case needs a witness-extractor
/// shaped like `Pi x : Sort(m). x`, but that type itself only exists at
/// `Sort(m+1)` — one universe *above* what it can extract into — so it can
/// never eliminate into its own level. Predicativity is correctly refusing
/// what would otherwise be a disguised `Type : Type`. Real kernels sidestep
/// this by taking a small base type as primitive (or, as here, postulated).
#[derive(Clone)]
pub struct Postulates {
    pub ctx: Ctx,
}
impl Postulates {
    pub fn new() -> Self {
        Postulates { ctx: Ctx::new() }
    }
    pub fn push(&mut self, ty: Expr) -> usize {
        let pos = self.ctx.len();
        self.ctx.push_back(ty);
        pos
    }
    pub fn get(&self, pos: usize) -> Expr {
        var((self.ctx.len() - 1 - pos) as u32)
    }
}
impl Default for Postulates {
    fn default() -> Self {
        Self::new()
    }
}

// --- reusable proof-term builders ---------------------------------------
//
// Generic lemmas, built once via `J`, for composing equality proofs.
// Not yet used by the straight-line proof in `proof.rs` (that fragment's
// correctness happens to hold by `refl` alone), but they're exactly the
// building blocks an inductive proof of the tail-call-to-loop compilation
// (a genuinely nontrivial equivalence) will need, so they belong here as
// kernel infrastructure rather than being reinvented ad hoc later.

/// `sym a_ty x y p : Id(A, y, x)`, given `p : Id(A, x, y)` -- propositional
/// symmetry of equality.
pub fn sym(a_ty: &Expr, x: &Expr, y: &Expr, p: Expr) -> Expr {
    // motive(x', y', _) := Id(A, y', x')
    let motive = lam(
        a_ty.clone(),
        lam(
            shift(a_ty, 0, 1),
            lam(
                id(shift(a_ty, 0, 2), var(1), var(0)),
                id(shift(a_ty, 0, 3), var(1), var(2)),
            ),
        ),
    );
    let base = lam(a_ty.clone(), refl(var(0)));
    jelim(motive, base, x.clone(), y.clone(), p)
}

/// `transport sort_k a_ty b_ty p x : b_ty`, given `p : Id(Sort(sort_k),
/// a_ty, b_ty)` and `x : a_ty` -- moves an element from one type to a
/// propositionally equal one (`a_ty`/`b_ty` themselves, as *elements* of
/// `Sort(sort_k)`), the standard operation `J` derives (sometimes called
/// `subst`). Built via `J`'s motive `\A B:Sort(k). \_:Id(Sort(k),A,B). A ->
/// B`, whose base case (`p` a `Refl`) is the identity function.
pub fn transport(sort_k: u32, a_ty: Expr, b_ty: Expr, p: Expr, x: Expr) -> Expr {
    let motive = lam(
        sort(sort_k),
        lam(
            sort(sort_k),
            lam(id(sort(sort_k), var(1), var(0)), arrow(var(2), var(1))),
        ),
    );
    let base = lam(sort(sort_k), lam(var(0), var(0)));
    app(jelim(motive, base, a_ty, b_ty, p), x)
}

/// `cong1 f a b p : Id(B, f a, f b)`, given `p : Id(A, a, b)` and `f : A ->
/// B`. Congruence for a unary function -- applying the same function to
/// equal arguments gives equal results, regardless of what `f` itself
/// computes. `b_ty` is `f`'s codomain, independent of `a_ty` (its domain);
/// callers where `f : A -> A` may pass the same `Expr` for both.
pub fn cong1(a_ty: &Expr, b_ty: &Expr, f: &Expr, a: Expr, b: Expr, p: Expr) -> Expr {
    // motive(a', b', _) := Id(B, f a', f b')
    let motive = lam(
        a_ty.clone(),
        lam(
            shift(a_ty, 0, 1),
            lam(
                id(shift(a_ty, 0, 2), var(1), var(0)),
                id(
                    shift(b_ty, 0, 3),
                    app(shift(f, 0, 3), var(2)),
                    app(shift(f, 0, 3), var(1)),
                ),
            ),
        ),
    );
    let base = lam(a_ty.clone(), refl(app(shift(f, 0, 1), var(0))));
    jelim(motive, base, a, b, p)
}

/// `trans a_ty x y z p1 p2 : Id(A, x, z)`, given `p1 : Id(A,x,y)` and
/// `p2 : Id(A,y,z)`. `a_ty`/`x` must be valid in the same context as
/// `p1`/`p2` (they are held fixed while eliminating on `p2`).
pub fn trans_proof(a_ty: &Expr, x: &Expr, y: &Expr, z: &Expr, p1: Expr, p2: Expr) -> Expr {
    // motive(y', z', _) := Id(A, x, y') -> Id(A, x, z')
    let motive = lam(
        a_ty.clone(),
        lam(
            shift(a_ty, 0, 1),
            lam(
                id(shift(a_ty, 0, 2), shift(x, 0, 2), var(1)),
                arrow(
                    id(shift(a_ty, 0, 3), shift(x, 0, 3), var(2)),
                    id(shift(a_ty, 0, 3), shift(x, 0, 3), var(1)),
                ),
            ),
        ),
    );
    let base = lam(
        a_ty.clone(),
        lam(id(shift(a_ty, 0, 1), shift(x, 0, 1), var(0)), var(0)),
    );
    app(jelim(motive, base, y.clone(), z.clone(), p2), p1)
}

/// `cong_n a_ty b_ty f xs ys ps : Id(B, f x_0 .. x_{n-1}, f y_0 .. y_{n-1})`,
/// given `ps[i] : Id(A, xs[i], ys[i])` for each `i` -- congruence for a
/// function of `n` arguments (all of type `A`, result type `B`), built by
/// rewriting one argument at a time (`cong1` on the partial application
/// with that argument's position held open as a fresh binder) and chaining
/// the `n` resulting steps with `trans_proof`. `n == 1` reduces to `cong1`
/// itself (up to an eta-expansion `cong1` doesn't need); `n == 0` is `refl`.
pub fn cong_n(a_ty: &Expr, b_ty: &Expr, f: &Expr, xs: &[Expr], ys: &[Expr], ps: Vec<Expr>) -> Expr {
    assert_eq!(xs.len(), ys.len());
    assert_eq!(xs.len(), ps.len());
    let apply = |args: &[Expr]| -> Expr { args.iter().cloned().fold(f.clone(), app) };
    let lhs_all = apply(xs);
    if xs.is_empty() {
        return refl(lhs_all);
    }

    let mut cur_args: Vec<Expr> = xs.to_vec();
    let mut acc: Option<(Expr, Expr)> = None; // (running proof, its right-hand value)
    for i in 0..xs.len() {
        // g := \z. f cur_args[0] .. cur_args[i-1] z cur_args[i+1] ..,
        // built fresh under one new binder, so every other (already-fixed)
        // argument needs reindexing by the binder `g` itself introduces.
        let g_body = cur_args.iter().enumerate().fold(shift(f, 0, 1), |acc, (j, a)| {
            app(acc, if j == i { var(0) } else { shift(a, 0, 1) })
        });
        let g = lam(a_ty.clone(), g_body);
        // `g` is `f` with every position but `i` already filled in -- a
        // *full* application under one open binder, not a curried partial
        // one, so its codomain is `f`'s own full result type `b_ty`
        // regardless of `i`.
        let step = cong1(a_ty, b_ty, &g, cur_args[i].clone(), ys[i].clone(), ps[i].clone());
        cur_args[i] = ys[i].clone();
        let after = apply(&cur_args);
        acc = Some(match acc {
            None => (step, after),
            Some((prev, mid)) => (trans_proof(b_ty, &lhs_all, &mid, &after, prev, step), after),
        });
    }
    acc.unwrap().0
}

/// `Pi C:(Bool->Sort0). Pi ct:C(true). Pi cf:C(false). <body_d3>`, where
/// `body_d3` must already be built assuming exactly this three-binder
/// depth (`C=Var2, ct=Var1, cf=Var0`) relative to `bool_ref`/`true_ref`/
/// `false_ref`'s own (shared) ambient depth -- the shared shape
/// `bool_rec`'s own type and both its computation-rule axioms all need,
/// differing only in what comes after the three binders.
fn wrap_c_ct_cf(bool_ref: &Expr, true_ref: &Expr, false_ref: &Expr, body_d3: Expr) -> Expr {
    let c_ty = arrow(bool_ref.clone(), sort(0));
    let true_d1 = shift(true_ref, 0, 1);
    let false_d2 = shift(false_ref, 0, 2);
    let pi_cf = pi(app(var(1), false_d2), body_d3);
    let pi_ct = pi(app(var(0), true_d1), pi_cf);
    pi(c_ty, pi_ct)
}

/// A real, computing `Nat` built from this kernel's own existing four
/// primitives alone (`Pi`/`Lam`/`Id`/`W`, plus `Postulates` for the base
/// types a predicative kernel can't derive from nothing) -- the reusable
/// form of `tests::nat_via_w_is_a_genuinely_computing_inductive_type`'s
/// own construction. See that test's doc comment for the full
/// derivation, including the induction-hypothesis-closure typing gap
/// `WRec`'s own `children_ty` field (see `Expr::WRec`'s own doc) closes.
/// `proof.rs`'s own `Ev`/`ev_rec` methodology -- postulate the
/// recursor's existence *and* separately postulate each leaf's own
/// computation rule as an explicit axiom, never relying on any
/// underlying automatic reduction -- remains the right shape for an
/// *indexed* family like `Ev(params, v)` regardless of that fix, since
/// this `Nat`'s own plain structural recursor doesn't eliminate for an
/// indexed family either way. Reusing this construction elsewhere
/// therefore saves inventing a *new* postulated base type per use site,
/// not that per-leaf axiom discipline itself.
///
/// Exposes postulate *positions*, not resolved `Expr`s: every accessor
/// below recomputes its result fresh from `p: &Postulates` at call time,
/// the same discipline `Postulates::get` itself follows (see its own
/// doc). This isn't just style -- it's what lets `nat_ty`/`zero`/`succ`
/// stay correct no matter how many further postulates get pushed onto
/// the same `Postulates` in between two calls, sidestepping by
/// construction the exact class of manual-reshifting bug the original,
/// self-contained test needed a hand-written `shift` to work around once
/// (a value built once, then reused unchanged after a later `p.push`,
/// silently ends up referencing the wrong postulate).
#[derive(Clone, Copy)]
pub struct NatPostulates {
    pub bool_pos: usize,
    pub true_pos: usize,
    pub false_pos: usize,
    pub unit_pos: usize,
    pub star_pos: usize,
    pub empty_pos: usize,
    pub empty_elim_pos: usize,
    pub child_ty_pos: usize,
    pub child_ty_true_eq_pos: usize,
    pub child_ty_false_eq_pos: usize,
    pub bool_rec_pos: usize,
    pub bool_rec_true_eq_pos: usize,
    pub bool_rec_false_eq_pos: usize,
}
impl NatPostulates {
    /// Pushes every postulate this construction needs onto `p`, in
    /// order. Call once per `Postulates`; every other method just
    /// resolves fresh against the positions stored here.
    pub fn new(p: &mut Postulates) -> Self {
        let bool_pos = p.push(sort(0));
        let true_pos = p.push(p.get(bool_pos));
        let false_pos = p.push(p.get(bool_pos));
        let unit_pos = p.push(sort(0));
        let star_pos = p.push(p.get(unit_pos));
        let empty_pos = p.push(sort(0));
        let empty_elim_pos = p.push(pi(sort(0), arrow(shift(&p.get(empty_pos), 0, 1), var(0))));
        let child_ty_pos = p.push(arrow(p.get(bool_pos), sort(0)));
        let child_ty_true_eq_pos = p.push(id(sort(0), app(p.get(child_ty_pos), p.get(true_pos)), p.get(unit_pos)));
        let child_ty_false_eq_pos = p.push(id(sort(0), app(p.get(child_ty_pos), p.get(false_pos)), p.get(empty_pos)));

        // bool_rec : Pi C:(Bool->Sort0). C(true) -> C(false) -> Pi b:Bool. C(b)
        let bool_rec_body_d3 = pi(shift(&p.get(bool_pos), 0, 3), app(var(3), var(0)));
        let bool_rec_ty = wrap_c_ct_cf(&p.get(bool_pos), &p.get(true_pos), &p.get(false_pos), bool_rec_body_d3);
        let bool_rec_pos = p.push(bool_rec_ty);

        // bool_rec_true_eq : Pi C ct cf. Id(C(true), bool_rec(C,ct,cf)(true), ct)
        let true_d3 = shift(&p.get(true_pos), 0, 3);
        let applied_d3 = app(app(app(shift(&p.get(bool_rec_pos), 0, 3), var(2)), var(1)), var(0));
        let true_eq_body_d3 = id(app(var(2), true_d3.clone()), app(applied_d3, true_d3), var(1));
        let bool_rec_true_eq_ty = wrap_c_ct_cf(&p.get(bool_pos), &p.get(true_pos), &p.get(false_pos), true_eq_body_d3);
        let bool_rec_true_eq_pos = p.push(bool_rec_true_eq_ty);

        // bool_rec_false_eq : Pi C ct cf. Id(C(false), bool_rec(C,ct,cf)(false), cf)
        let false_d3 = shift(&p.get(false_pos), 0, 3);
        let applied_d3b = app(app(app(shift(&p.get(bool_rec_pos), 0, 3), var(2)), var(1)), var(0));
        let false_eq_body_d3 = id(app(var(2), false_d3.clone()), app(applied_d3b, false_d3), var(0));
        let bool_rec_false_eq_ty = wrap_c_ct_cf(&p.get(bool_pos), &p.get(true_pos), &p.get(false_pos), false_eq_body_d3);
        let bool_rec_false_eq_pos = p.push(bool_rec_false_eq_ty);

        NatPostulates {
            bool_pos,
            true_pos,
            false_pos,
            unit_pos,
            star_pos,
            empty_pos,
            empty_elim_pos,
            child_ty_pos,
            child_ty_true_eq_pos,
            child_ty_false_eq_pos,
            bool_rec_pos,
            bool_rec_true_eq_pos,
            bool_rec_false_eq_pos,
        }
    }

    pub fn bool_ty(&self, p: &Postulates) -> Expr {
        p.get(self.bool_pos)
    }
    pub fn true_(&self, p: &Postulates) -> Expr {
        p.get(self.true_pos)
    }
    pub fn false_(&self, p: &Postulates) -> Expr {
        p.get(self.false_pos)
    }
    pub fn unit_ty(&self, p: &Postulates) -> Expr {
        p.get(self.unit_pos)
    }
    pub fn star(&self, p: &Postulates) -> Expr {
        p.get(self.star_pos)
    }
    pub fn empty_ty(&self, p: &Postulates) -> Expr {
        p.get(self.empty_pos)
    }
    /// `ChildTy(b)`.
    pub fn child_ty(&self, p: &Postulates, b: Expr) -> Expr {
        app(p.get(self.child_ty_pos), b)
    }
    /// The raw, uninstantiated `bool_rec : Pi C ct cf. Pi b:Bool. C(b)`.
    pub fn bool_rec(&self, p: &Postulates) -> Expr {
        p.get(self.bool_rec_pos)
    }
    /// The raw, uninstantiated `bool_rec_true_eq` computation-rule axiom.
    pub fn bool_rec_true_eq(&self, p: &Postulates) -> Expr {
        p.get(self.bool_rec_true_eq_pos)
    }
    /// The raw, uninstantiated `bool_rec_false_eq` computation-rule axiom.
    pub fn bool_rec_false_eq(&self, p: &Postulates) -> Expr {
        p.get(self.bool_rec_false_eq_pos)
    }

    /// `Nat := W(Bool, ChildTy) : Sort(0)`.
    pub fn nat_ty(&self, p: &Postulates) -> Expr {
        wty(p.get(self.bool_pos), app(shift(&p.get(self.child_ty_pos), 0, 1), var(0)))
    }

    /// `Zero : Nat`, transported from `empty_elim(Nat) : Empty -> Nat`
    /// along `child_ty_false_eq`.
    pub fn zero(&self, p: &Postulates) -> Expr {
        sup(p.get(self.false_pos), self.zero_child_fn(p))
    }

    /// `f_zero : ChildTy(false) -> Nat`, `Zero`'s own child function --
    /// exposed separately from `zero` because it's exactly the shape
    /// `WRec`'s own automatic reduction needs an induction-hypothesis
    /// closure to have (see `tests::nat_via_w_is_a_genuinely_computing_inductive_type`,
    /// which uses this to rebuild and typecheck that closure by hand).
    pub fn zero_child_fn(&self, p: &Postulates) -> Expr {
        let nat_ty = self.nat_ty(p);
        let f_empty_nat = app(p.get(self.empty_elim_pos), nat_ty.clone());
        let arrow_nat_fn = lam(sort(0), arrow(var(0), shift(&nat_ty, 0, 1)));
        let cong_false = cong1(
            &sort(0),
            &sort(0),
            &arrow_nat_fn,
            app(p.get(self.child_ty_pos), p.get(self.false_pos)),
            p.get(self.empty_pos),
            p.get(self.child_ty_false_eq_pos),
        );
        let sym_cong_false = sym(
            &sort(0),
            &arrow(app(p.get(self.child_ty_pos), p.get(self.false_pos)), nat_ty.clone()),
            &arrow(p.get(self.empty_pos), nat_ty.clone()),
            cong_false,
        );
        transport(
            0,
            arrow(p.get(self.empty_pos), nat_ty.clone()),
            arrow(app(p.get(self.child_ty_pos), p.get(self.false_pos)), nat_ty.clone()),
            sym_cong_false,
            f_empty_nat,
        )
    }

    /// `Succ(pred) : Nat`, given `pred : Nat` already valid in the
    /// caller's *current* context (e.g. `p.get` of a just-pushed
    /// postulate, or a local variable under whatever binders are
    /// ambient at the call site) -- transported from `(\_:Unit. pred) :
    /// Unit -> Nat` along `child_ty_true_eq`.
    pub fn succ(&self, p: &Postulates, pred: Expr) -> Expr {
        let nat_ty = self.nat_ty(p);
        let f_unit_nat = lam(p.get(self.unit_pos), shift(&pred, 0, 1));
        let arrow_nat_fn = lam(sort(0), arrow(var(0), shift(&nat_ty, 0, 1)));
        let cong_true = cong1(
            &sort(0),
            &sort(0),
            &arrow_nat_fn,
            app(p.get(self.child_ty_pos), p.get(self.true_pos)),
            p.get(self.unit_pos),
            p.get(self.child_ty_true_eq_pos),
        );
        let sym_cong_true = sym(
            &sort(0),
            &arrow(app(p.get(self.child_ty_pos), p.get(self.true_pos)), nat_ty.clone()),
            &arrow(p.get(self.unit_pos), nat_ty.clone()),
            cong_true,
        );
        let f_succ = transport(
            0,
            arrow(p.get(self.unit_pos), nat_ty.clone()),
            arrow(app(p.get(self.child_ty_pos), p.get(self.true_pos)), nat_ty.clone()),
            sym_cong_true,
            f_unit_nat,
        );
        sup(p.get(self.true_pos), f_succ)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Replace `Var(j)` with `s` throughout `e`: the reference `subst_top`
    /// is checked against, as `shift(&subst(body, 0, &shift(s, 0, 1)), 0, -1)`.
    fn subst(e: &Expr, j: u32, s: &Expr) -> Expr {
        grow(|| match e {
            Expr::Var(k) => {
                if *k == j {
                    s.clone()
                } else {
                    Expr::Var(*k)
                }
            }
            Expr::Sort(i) => Expr::Sort(*i),
            Expr::Pi(a, b) => pi(subst(a, j, s), subst(b, j + 1, &shift(s, 0, 1))),
            Expr::Lam(a, b) => lam(subst(a, j, s), subst(b, j + 1, &shift(s, 0, 1))),
            Expr::App(f, a) => app(subst(f, j, s), subst(a, j, s)),
            Expr::Id(a, x, y) => id(subst(a, j, s), subst(x, j, s), subst(y, j, s)),
            Expr::Refl(a) => refl(subst(a, j, s)),
            Expr::J {
                motive,
                base,
                a,
                b,
                p,
            } => jelim(
                subst(motive, j, s),
                subst(base, j, s),
                subst(a, j, s),
                subst(b, j, s),
                subst(p, j, s),
            ),
            Expr::W(a, b) => wty(subst(a, j, s), subst(b, j + 1, &shift(s, 0, 1))),
            Expr::Sup(a, f) => sup(subst(a, j, s), subst(f, j, s)),
            Expr::WRec {
                motive,
                children_ty,
                step,
                target,
            } => wrec(subst(motive, j, s), subst(children_ty, j + 1, &shift(s, 0, 1)), subst(step, j, s), subst(target, j, s)),
            Expr::Sigma(..) | Expr::Pair(..) | Expr::SigRec { .. } => subst_sigma_family(e, j, s),
        })
    }

    /// `subst`'s own `Sigma`/`Pair`/`SigRec` cases, out of line -- see
    /// `shift_sigma_family`'s own docs for why.
    #[inline(never)]
    fn subst_sigma_family(e: &Expr, j: u32, s: &Expr) -> Expr {
        match e {
            Expr::Sigma(a, b) => sigma(subst(a, j, s), subst(b, j + 1, &shift(s, 0, 1))),
            Expr::Pair(fam, a, b) => pair(subst(fam, j + 1, &shift(s, 0, 1)), subst(a, j, s), subst(b, j, s)),
            Expr::SigRec { motive, step, target } => sigrec(subst(motive, j, s), subst(step, j, s), subst(target, j, s)),
            _ => unreachable!("subst_sigma_family called on a non-Sigma-family Expr"),
        }
    }

    /// A random `Expr` of every variant, ill-typed as often as not, with
    /// indices small enough that `Var(0)` is often free and often not.
    fn random_expr(seed: &mut u64, fuel: u32) -> Expr {
        let mut next = || {
            *seed = seed.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = *seed;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            z ^ (z >> 31)
        };
        let pick = next();
        let k = (next() % 4) as u32;
        if fuel == 0 || pick % 4 == 0 {
            return if pick % 8 == 0 { sort(k % 2) } else { var(k) };
        }
        let mut sub = || random_expr(seed, fuel - 1);
        match (pick >> 3) % 13 {
            0 => pi(sub(), sub()),
            1 => lam(sub(), sub()),
            2 => app(sub(), sub()),
            3 => id(sub(), sub(), sub()),
            4 => refl(sub()),
            5 => jelim(sub(), sub(), sub(), sub(), sub()),
            6 => wty(sub(), sub()),
            7 => sup(sub(), sub()),
            8 => wrec(sub(), sub(), sub(), sub()),
            9 => sigma(sub(), sub()),
            10 => pair(sub(), sub(), sub()),
            11 => sigrec(sub(), sub(), sub()),
            _ => app(sub(), sub()),
        }
    }

    /// `subst_top`'s one pass (`RELATED_WORK.md` §53) must give exactly
    /// what substituting and then shifting gives, both when the body uses
    /// the variable and when it doesn't.
    #[test]
    fn subst_top_is_substituting_then_shifting() {
        let (mut seed, mut used, mut unused) = (1u64, 0, 0);
        for _ in 0..20_000 {
            let body = random_expr(&mut seed, 5);
            let s = random_expr(&mut seed, 3);
            let reference = shift(&subst(&body, 0, &shift(&s, 0, 1)), 0, -1);
            assert_eq!(subst_top(&body, &s), reference, "body {body:?}, s {s:?}");
            if is_var_free(&body, 0) { used += 1 } else { unused += 1 }
        }
        assert!(used > 2_000 && unused > 2_000, "used {used}, unused {unused}");
    }

    #[test]
    fn subst_top_leaves_an_unused_argument_alone() {
        // 21 distinct nodes, a million as a tree: copying it takes about a
        // second in a debug build, and the shortcut doesn't look at it.
        let mut s = var(0);
        for _ in 0..20 {
            s = app(s.clone(), s);
        }
        let body = pi(var(3), var(4));
        let t = std::time::Instant::now();
        assert_eq!(subst_top(&body, &s), pi(var(2), var(3)));
        assert!(t.elapsed() < std::time::Duration::from_millis(50), "took {:?}", t.elapsed());
    }

    /// Substituting under binders shifts the argument once, where it's used,
    /// not again at every binder crossed on the way (`RELATED_WORK.md` §52).
    /// Timed against one shift of the argument, so it holds on any machine.
    #[test]
    fn subst_top_shifts_a_used_argument_once() {
        let mut s = var(0);
        for _ in 0..14 {
            s = app(s.clone(), s);
        }
        let depth = 30;
        let mut body = var(depth);
        let mut expected = shift(&s, 0, depth as i32);
        let t = std::time::Instant::now();
        let one_shift = shift(&s, 0, depth as i32);
        let one_shift_time = t.elapsed();
        drop(one_shift);
        for _ in 0..depth {
            body = lam(sort(0), body);
            expected = lam(sort(0), expected);
        }
        let t = std::time::Instant::now();
        let got = subst_top(&body, &s);
        let took = t.elapsed();
        assert_eq!(got, expected);
        assert!(took < one_shift_time * 4 + std::time::Duration::from_millis(5), "took {took:?}, one shift {one_shift_time:?}");
    }

    /// `def_eq` answers syntactically equal sides without normalising
    /// them (`RELATED_WORK.md` §56). `d (d (... (d x)))` with
    /// `d = \x. x x` has a normal form of 2^n nodes, so normalising both
    /// sides and comparing takes about 0.3 s at n = 14.
    #[test]
    fn def_eq_answers_equal_sides_without_normalising() {
        let doubling = || {
            let mut t = var(0);
            for _ in 0..14 {
                t = app(lam(sort(0), app(var(0), var(0))), t);
            }
            t
        };
        let (a, b) = (doubling(), doubling());
        let t = std::time::Instant::now();
        assert!(def_eq(&a, &b));
        let took = t.elapsed();
        assert!(took < std::time::Duration::from_millis(5), "took {took:?}");
    }

    /// `def_eq` compares weak head normal forms and recurses into the
    /// children, so a part both sides share is never normalised
    /// (`RELATED_WORK.md` §57). Here the domains are equal copies of §56's
    /// doubling term and only the codomains need reducing.
    #[test]
    fn def_eq_normalises_only_where_the_sides_differ() {
        let doubling = || {
            let mut t = var(0);
            for _ in 0..14 {
                t = app(lam(sort(0), app(var(0), var(0))), t);
            }
            t
        };
        let a = pi(doubling(), app(lam(sort(1), var(0)), sort(0)));
        let b = pi(doubling(), sort(0));
        let t = std::time::Instant::now();
        assert!(def_eq(&a, &b));
        assert!(!def_eq(&a, &pi(doubling(), sort(1))));
        let took = t.elapsed();
        assert!(took < std::time::Duration::from_millis(5), "took {took:?}");
    }

    /// Wraps some of `e`'s subterms in a redex that reduces back to them,
    /// `(\_. x) Sort(0)` with `x` shifted under the new binder.
    fn with_redexes(e: &Expr, seed: &mut u64) -> Expr {
        *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        let wrap = (*seed >> 33).is_multiple_of(4);
        let mut go = |x: &Rc<Expr>| with_redexes(x, seed);
        let rebuilt = match e {
            Expr::Pi(a, b) => pi(go(a), go(b)),
            Expr::Lam(a, b) => lam(go(a), go(b)),
            Expr::App(f, a) => app(go(f), go(a)),
            Expr::Id(a, x, y) => id(go(a), go(x), go(y)),
            Expr::Sigma(a, b) => sigma(go(a), go(b)),
            Expr::Pair(fam, a, b) => pair(go(fam), go(a), go(b)),
            other => other.clone(),
        };
        if wrap { app(lam(sort(0), shift(&rebuilt, 0, 1)), sort(0)) } else { rebuilt }
    }

    /// `def_eq` decides exactly `nf(a) == nf(b)`: on random terms, some
    /// pairs unrelated and some the same term with different redexes
    /// inserted.
    #[test]
    fn def_eq_agrees_with_comparing_normal_forms() {
        let (mut seed, mut equal, mut unequal) = (7u64, 0, 0);
        for i in 0..20_000 {
            let a = random_expr(&mut seed, 4);
            let b = if i % 2 == 0 { a.clone() } else { random_expr(&mut seed, 4) };
            let (a, b) = (with_redexes(&a, &mut seed), with_redexes(&b, &mut seed));
            let reference = nf(&a) == nf(&b);
            assert_eq!(def_eq(&a, &b), reference, "a {a:?}, b {b:?}");
            if reference && a != b { equal += 1 } else if !reference { unequal += 1 }
        }
        assert!(equal > 2_000 && unequal > 2_000, "equal {equal}, unequal {unequal}");
    }

    /// The argument `Rc` of each application in `e`'s spine, outermost
    /// first.
    fn spine_args(e: &Expr) -> Vec<Rc<Expr>> {
        let mut out = Vec::new();
        let mut e = e;
        while let Expr::App(f, a) = e {
            out.push(a.clone());
            e = f;
        }
        out
    }

    /// `whnf` keeps the allocation of a stuck head or target, not only of
    /// the arguments: `ReductionCache` is keyed by pointer, so a copy
    /// misses it, and each level of a stuck spine then reduced the whole
    /// spine below it again (`RELATED_WORK.md` §59).
    #[test]
    fn whnf_keeps_the_stuck_part_it_was_given() {
        let stuck = Rc::new(app(app(var(0), var(1)), var(2)));
        let r = whnf(&Expr::App(stuck.clone(), Rc::new(var(3))));
        let Expr::App(got, _) = &r else { panic!("not an application") };
        assert!(Rc::ptr_eq(got, &stuck));

        let j = Expr::J {
            motive: Rc::new(var(0)),
            base: Rc::new(var(1)),
            a: Rc::new(var(2)),
            b: Rc::new(var(2)),
            p: stuck.clone(),
        };
        let r = whnf(&j);
        let Expr::J { p: got, .. } = &r else { panic!("not a J") };
        assert!(Rc::ptr_eq(got, &stuck));

        let w = Expr::WRec {
            motive: Rc::new(var(0)),
            children_ty: Rc::new(var(1)),
            step: Rc::new(var(2)),
            target: stuck.clone(),
        };
        let r = whnf(&w);
        let Expr::WRec { target: got, .. } = &r else { panic!("not a WRec") };
        assert!(Rc::ptr_eq(got, &stuck));

        let s = Expr::SigRec { motive: Rc::new(var(0)), step: Rc::new(var(1)), target: stuck.clone() };
        let r = whnf(&s);
        let Expr::SigRec { target: got, .. } = &r else { panic!("not a SigRec") };
        assert!(Rc::ptr_eq(got, &stuck));
    }

    /// `nf` and `def_eq` on stuck spines 2,000 applications deep, one of
    /// them with a redex for its head. Each took over 10 s in a debug build
    /// when every level re-reduced the spine below it (`RELATED_WORK.md`
    /// §59).
    #[test]
    fn nf_and_def_eq_are_linear_on_a_stuck_spine() {
        let spine = |head: Expr| {
            let mut t = head;
            for i in 0..2000 {
                t = app(t, var(i % 3));
            }
            t
        };
        let (a, b) = (spine(var(0)), spine(app(lam(sort(0), var(0)), var(1))));
        let t = std::time::Instant::now();
        assert_eq!(nf(&a), a);
        assert_eq!(nf(&b), spine(var(1)));
        assert!(!def_eq(&a, &b));
        let took = t.elapsed();
        assert!(took < std::time::Duration::from_millis(500), "took {took:?}");
    }

    /// `def_eq` on two right-nested chains `f (f (... x))`, 8,000 deep,
    /// that differ only at the bottom. `conv` tries `==` at every level,
    /// and each failing `==` walked down to the bottom again: 23 s in a
    /// debug build (`RELATED_WORK.md` §61).
    #[test]
    fn def_eq_is_linear_on_a_chain_that_differs_at_the_bottom() {
        let chain = |bottom: Expr| {
            let mut t = bottom;
            for _ in 0..8000 {
                t = app(var(0), t);
            }
            t
        };
        let (a, b) = (chain(var(1)), chain(var(2)));
        let t = std::time::Instant::now();
        assert!(!def_eq(&a, &b));
        let took = t.elapsed();
        assert!(took < std::time::Duration::from_millis(500), "took {took:?}");
    }

    /// `whnf` keeps each argument's allocation rather than copying it into
    /// a new `Rc`: `ReductionCache` is keyed by pointer, so a copy misses it,
    /// and `nf` then normalises the whole argument again at every
    /// application (`RELATED_WORK.md` §48).
    #[test]
    fn whnf_keeps_the_arguments_it_was_given() {
        let x = Rc::new(var(7));
        let y = Rc::new(var(8));
        let same = |got: &[Rc<Expr>], want: &[&Rc<Expr>]| {
            got.len() == want.len() && got.iter().zip(want).all(|(g, w)| Rc::ptr_eq(g, w))
        };

        // A stuck application.
        let stuck = Expr::App(Rc::new(app(var(0), var(1))), x.clone());
        assert!(same(&spine_args(&whnf(&stuck))[..1], &[&x]));

        // `J` on `refl` reduces to `base a`.
        let j = Expr::J {
            motive: Rc::new(var(0)),
            base: Rc::new(var(1)),
            a: x.clone(),
            b: x.clone(),
            p: Rc::new(refl(var(9))),
        };
        assert!(same(&spine_args(&whnf(&j)), &[&x]));

        // `SigRec` on a pair reduces to `step a b`.
        let s = Expr::SigRec {
            motive: Rc::new(var(0)),
            step: Rc::new(var(1)),
            target: Rc::new(Expr::Pair(Rc::new(var(2)), x.clone(), y.clone())),
        };
        assert!(same(&spine_args(&whnf(&s)), &[&y, &x]));

        // `WRec` on `sup a f` reduces to `step a f rec`.
        let w = Expr::WRec {
            motive: Rc::new(var(0)),
            children_ty: Rc::new(var(1)),
            step: Rc::new(var(2)),
            target: Rc::new(Expr::Sup(x.clone(), y.clone())),
        };
        assert!(same(&spine_args(&whnf(&w))[1..], &[&y, &x]));
    }

    /// Every recursive traversal `check` reaches -- `infer`, `whnf`
    /// (beta-reducing the whole chain), `def_eq`'s `conv` and `==`, and
    /// `Debug` in the error message -- must survive a term 1,000 levels
    /// deep on a 1 MB thread: the Windows main thread's size, where a debug
    /// build used to overflow at depth ~90 (`RELATED_WORK.md` 31). Goes
    /// through `check`, which has no depth guard, on purpose.
    #[test]
    fn check_survives_a_term_far_deeper_than_the_native_stack_allows() {
        const N: usize = 1_000;
        std::thread::Builder::new()
            .stack_size(1 << 20)
            .spawn(|| {
                let ctx = Ctx::new();

                // (\x:Type0. x) applied N-fold to Type0 -- infer + beta.
                let id_fn = lam(sort(1), var(0));
                let mut chain = sort(0);
                for _ in 0..N {
                    chain = app(id_fn.clone(), chain);
                }
                assert!(check(&ctx, &chain, &sort(1)).is_ok());

                // refl^N(Type0) against its own type, built independently,
                // so def_eq's `==` walks two distinct deep trees.
                let (mut e, mut ty) = (sort(0), sort(1));
                for _ in 0..N {
                    ty = id(ty, e.clone(), e.clone());
                    e = refl(e);
                }
                assert!(check(&ctx, &e, &ty).is_ok());
                let err = check(&ctx, &e, &sort(0)).unwrap_err();
                assert!(err.contains("type mismatch"), "unexpected error: {}", err.chars().take(80).collect::<String>());
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// A real, working `Nat` -- Zero/Succ and a genuinely computing
    /// structural recursor -- exercising `NatPostulates`, the reusable
    /// public API extracted from this same construction (see its own
    /// module-level doc for the full derivation: which base types get
    /// postulated and why, how `Zero`/`Succ` are transported into
    /// `ChildTy`, and the "generic recursion/induction principle" gap in
    /// `RELATED_WORK.md` §1/§3 this answers). This test is now a
    /// *consumer* of that API, not the construction itself -- every
    /// `check`/`assert_eq!` below is unchanged from this construction's
    /// original, self-contained form, confirming the extraction changed
    /// nothing observable.
    ///
    /// `bool_rec` (Bool's own postulated recursor, with its own two
    /// computation-rule axioms, also part of `NatPostulates`) is used
    /// below to build a genuinely per-case `is_zero : Nat -> Bool`
    /// dispatch -- demonstrating the identity recursor's own step (which
    /// ignores the tag entirely) isn't the only shape available.
    ///
    /// **A genuine scope boundary that was found here, then fixed at the
    /// `Expr::WRec` level** -- deeper than it first looked, and not a
    /// function-extensionality gap (an earlier misdiagnosis, corrected in
    /// an earlier commit: funext requires both sides to already be
    /// well-typed inhabitants of the same Pi-type before it can relate
    /// them, and one side here never was one at all). Proving a
    /// `bool_rec`-based step's own result concretely (e.g.
    /// `is_zero(Zero) = true`) needs more than one `cong1`/`trans_proof`
    /// step, since `bool_rec` is postulated and never auto-reduces on its
    /// own -- but building that step used to run into a second, deeper
    /// problem underneath: `WRec`'s own automatic reduction (`whnf_impl`)
    /// built its induction-hypothesis closure with an inert placeholder
    /// domain annotation (`sort(0)`) -- harmless for reduction itself
    /// (beta substitution never consults a `Lam`'s domain field), but
    /// that closure was *unconditionally ill-typed on its own* whenever
    /// the step function's `ih` parameter was genuinely used (not just
    /// discarded, the way the identity recursor's own step does),
    /// blocking it from appearing as a well-typed subterm in any
    /// hand-built propositional proof. Fixed now: `Expr::WRec` carries an
    /// explicit `children_ty` field (`B`, see its own doc) so
    /// `whnf_impl` can give that closure its *honest* domain
    /// (`subst_top(children_ty, a)`, i.e. `ChildTy(b)`) instead. The
    /// assertions below rebuild that exact closure by hand and confirm it
    /// now typechecks at its real domain -- flipped from this test's own
    /// original assertion that it was unconditionally rejected, which is
    /// why a deliberate revert of the fix (back to the `sort(0)`
    /// placeholder) is expected to make this test fail again immediately,
    /// not a sign the obstacle has returned.
    ///
    /// `proof.rs`'s own `Ev`/`ev_rec` methodology -- postulate the
    /// recursor's existence *and* separately postulate each leaf's own
    /// computation rule as an explicit axiom, never relying on any
    /// underlying automatic reduction -- remains the necessary shape for
    /// `Ev` regardless of this fix, not a historical accident of not
    /// having a `Nat` yet: `Ev(params, v)` is an *indexed* family
    /// (depends on `params`/`v`, unlike plain `Nat`), so a plain
    /// structural recursor over this `Nat` doesn't directly hand you
    /// `Ev`'s own induction principle either way, and reusing this `Nat`
    /// would still need the exact same per-leaf axiom discipline `Ev`
    /// already has -- what it would save is inventing a *new* postulated
    /// base type per strategy, not that per-leaf postulation itself. See
    /// `RELATED_WORK.md` §3 for the fuller accounting.
    #[test]
    fn nat_via_w_is_a_genuinely_computing_inductive_type() {
        let mut p = Postulates::new();
        let nat = NatPostulates::new(&mut p);

        let nat_ty = nat.nat_ty(&p);
        check(&p.ctx, &nat_ty, &sort(0)).expect("Nat := W(Bool, ChildTy) : Type0");

        let zero = nat.zero(&p);
        check(&p.ctx, &zero, &nat_ty).expect("Zero : Nat");

        // Succ(pred) needs an actual `pred : Nat` in scope -- push one as
        // a fresh postulate, then build Succ against it. Recomputing
        // `nat.nat_ty(&p)`/`nat.zero(&p)` fresh *after* this push (rather
        // than reshifting the snapshots above by hand) is exactly the
        // ergonomic win of `NatPostulates`'s own "always recompute, never
        // cache" design -- the original, self-contained version of this
        // construction needed a manual `shift` here to avoid silently
        // referencing the wrong postulate; this version doesn't.
        let pred_pos = p.push(nat.nat_ty(&p));
        let pred = p.get(pred_pos);
        let nat_ty_here = nat.nat_ty(&p);
        let succ_pred = nat.succ(&p, pred);
        check(&p.ctx, &succ_pred, &nat_ty_here).expect("Succ(pred) : Nat");

        // Sanity: the identity recursor (mirrors `w_recursor_computes_
        // definitionally`'s own "reconstruct the node unchanged, ignoring
        // ih" step, generalized from that test's constant-children-type W
        // to this Nat's own tag-dependent ChildTy) reduces `Zero`/
        // `Succ(pred)` back to themselves *definitionally* via `wrec`'s
        // own free Sup-reduction alone -- confirming this Nat really is a
        // genuine, computing W-type, not just a well-typed assemblage of
        // postulates.
        let zero_here = nat.zero(&p); // fresh at this (deeper, post-`pred_pos`) depth
        let wa_here = p.get(nat.bool_pos);
        let wb_here = app(shift(&p.get(nat.child_ty_pos), 0, 1), var(0));
        let motive_const = lam(nat_ty_here.clone(), shift(&nat_ty_here, 0, 1)); // \_:Nat. Nat

        let f_ty_d1 = pi(wb_here.clone(), shift(&nat_ty_here, 0, 2));
        let ih_dom_d2 = shift(&wb_here, 0, 1);
        let ih_body_d3 = app(shift(&motive_const, 0, 3), app(var(1), var(0)));
        let ih_ty_d2 = pi(ih_dom_d2, ih_body_d3);
        let step_id = lam(wa_here, lam(f_ty_d1, lam(ih_ty_d2, sup(var(2), var(1)))));

        let id_on_zero = wrec(motive_const.clone(), wb_here.clone(), step_id.clone(), zero_here.clone());
        check(&p.ctx, &id_on_zero, &nat_ty_here).expect("id-recursor applied to Zero should typecheck at Nat");
        assert_eq!(nf(&id_on_zero), nf(&zero_here), "the identity recursor should reduce Zero back to Zero");

        let id_on_succ = wrec(motive_const, wb_here.clone(), step_id, succ_pred.clone());
        check(&p.ctx, &id_on_succ, &nat_ty_here).expect("id-recursor applied to Succ(pred) should typecheck at Nat");
        assert_eq!(nf(&id_on_succ), nf(&succ_pred), "the identity recursor should reduce Succ(pred) back to Succ(pred)");

        // A genuinely per-case recursor: is_zero : Nat -> Bool, dispatching
        // on the tag via bool_rec (Bool's own postulated recursor) --
        // demonstrating the identity recursor's own step (which ignores
        // the tag entirely) isn't the only shape available. `bool_rec`
        // doesn't reduce automatically (a postulated recursor, same as
        // any other postulated axiom), so proving `is_zero(Zero) = true`
        // needs one explicit propositional step (`bool_rec_false_eq`)
        // rather than falling straight out of `nf`.
        let wb_here2 = app(shift(&p.get(nat.child_ty_pos), 0, 1), var(0));
        let f_ty_for_c_d1 = arrow(wb_here2.clone(), shift(&nat_ty_here, 0, 1));
        let ih_dom_d2 = shift(&wb_here2, 0, 1);
        let ih_ty_d2 = arrow(ih_dom_d2, shift(&p.get(nat.bool_pos), 0, 2));
        let c_body_d1 = pi(f_ty_for_c_d1, arrow(ih_ty_d2, shift(&p.get(nat.bool_pos), 0, 2)));
        let is_zero_motive_c = lam(p.get(nat.bool_pos), c_body_d1);

        let f_ty_true = arrow(app(p.get(nat.child_ty_pos), p.get(nat.true_pos)), nat_ty_here.clone());
        let ih_ty_true_d1 = arrow(shift(&app(p.get(nat.child_ty_pos), p.get(nat.true_pos)), 0, 1), shift(&p.get(nat.bool_pos), 0, 1));
        let case_true = lam(f_ty_true, lam(ih_ty_true_d1, shift(&p.get(nat.false_pos), 0, 2)));

        let f_ty_false = arrow(app(p.get(nat.child_ty_pos), p.get(nat.false_pos)), nat_ty_here.clone());
        let ih_ty_false_d1 = arrow(shift(&app(p.get(nat.child_ty_pos), p.get(nat.false_pos)), 0, 1), shift(&p.get(nat.bool_pos), 0, 1));
        let case_false = lam(f_ty_false, lam(ih_ty_false_d1, shift(&p.get(nat.true_pos), 0, 2)));

        let is_zero_step = app(app(app(nat.bool_rec(&p), is_zero_motive_c.clone()), case_true.clone()), case_false.clone());
        check(&p.ctx, &is_zero_step, &pi(p.get(nat.bool_pos), app(shift(&is_zero_motive_c, 0, 1), var(0))))
            .expect("is_zero_step : Pi b:Bool. C(b)");

        let is_zero_motive_const = lam(nat_ty_here.clone(), shift(&p.get(nat.bool_pos), 0, 1)); // \_:Nat. Bool
        let is_zero_on_zero = wrec(is_zero_motive_const.clone(), wb_here2.clone(), is_zero_step.clone(), zero_here.clone());
        check(&p.ctx, &is_zero_on_zero, &p.get(nat.bool_pos)).expect("is_zero(Zero) : Bool");

        // The obstacle this test used to demonstrate (see git history: an
        // "inert" placeholder domain, `sort(0)`, made `whnf_impl`'s own
        // induction-hypothesis closure unconditionally ill-typed standalone
        // whenever a step genuinely used it) is fixed now: `WRec` carries
        // its own `children_ty` field (`B` from the underlying `W(A,B)`,
        // `infer` cross-checks it against `target`'s own real type -- see
        // `Expr::WRec`'s own doc), and `whnf_impl` uses `subst_top
        // (children_ty, a)` -- `B(a)`, the true children type at tag `a` --
        // as the closure's own domain instead. This rebuilds *exactly* the
        // closure `whnf_impl` now builds internally when reducing
        // `is_zero_on_zero` one step (`is_zero_step` doesn't reduce further
        // on its own -- `bool_rec` is postulated, not a `Lam` -- so this is
        // where `whnf_impl`'s own reduction gets stuck, with this exact
        // closure embedded, unreduced, as `is_zero_step`'s own third
        // argument), confirming it's independently well-typed at its own
        // *honest* domain now, not just "harmless because reduction never
        // consults a `Lam`'s domain field" as before. `zero_child_fn`
        // (`f_zero : ChildTy(false) -> Nat`, `Zero`'s own child function)
        // recomputed fresh at this depth needs only the one extra shift for
        // `rec_step`'s own local binder, not a second one for the depth gap
        // since `pred_pos` was pushed -- the same "recompute, don't reshift
        // a snapshot" benefit as `zero_here` above.
        let f_zero_here = nat.zero_child_fn(&p);
        let honest_domain = subst_top(&wb_here2, &p.get(nat.false_pos));
        let rec_step = lam(
            honest_domain.clone(),
            wrec(shift(&is_zero_motive_const, 0, 1), shift(&wb_here2, 1, 1), shift(&is_zero_step, 0, 1), app(shift(&f_zero_here, 0, 1), var(0))),
        );
        let child_ty_false = app(p.get(nat.child_ty_pos), p.get(nat.false_pos));
        assert!(
            def_eq(&honest_domain, &child_ty_false),
            "subst_top(children_ty, false) should give exactly ChildTy(false), the real children type at the false tag"
        );
        let expected_domain = arrow(child_ty_false, p.get(nat.bool_pos));
        check(&p.ctx, &rec_step, &expected_domain)
            .expect("with children_ty threaded honestly through whnf_impl's own reduction rule, the induction-hypothesis closure now typechecks at its real domain, not just an inert placeholder");

        // Full end-to-end confirmation: `whnf(is_zero_on_zero)` (which
        // internally builds exactly `rec_step` above) itself still
        // typechecks at `Bool` -- the fix doesn't just make the isolated
        // closure well-typed, it keeps the *whole* one-step reduction
        // well-typed too, stuck-on-a-postulate tail and all.
        let stuck_one_step = whnf(&is_zero_on_zero);
        check(&p.ctx, &stuck_one_step, &p.get(nat.bool_pos)).expect("whnf(is_zero(Zero)) should still typecheck at Bool after the fix");
        assert_eq!(
            stuck_one_step,
            app(app(app(is_zero_step.clone(), p.get(nat.false_pos)), f_zero_here.clone()), rec_step.clone()),
            "whnf_impl's own stuck reduction should be exactly is_zero_step(false)(f_zero)(rec_step) -- \
             confirming the hand-rebuilt closure above is the *same* one whnf_impl actually produces, \
             not just an independently-typed lookalike"
        );

        // Genuinely finishing `is_zero(Zero) = true` propositionally, now
        // that the closure above is no longer unconditionally ill-typed:
        // `bool_rec_false_eq` (unaffected by the `children_ty` fix, since
        // `bool_rec` is postulated and never reduces on its own) relates
        // `is_zero_step(false)` to `case_false` at `C(false)`; one `cong1`
        // step lifts that (function-application congruence, holding
        // `f_zero_here`/`rec_step` fixed) to a `Bool`-typed equality
        // between the two ways of finishing the call, and `case_false`'s
        // own body ignores both its arguments and returns `true`
        // outright, so its own side reduces the rest of the way for free.
        let bool_ty = p.get(nat.bool_pos);
        let true_val = p.get(nat.true_pos);
        let false_val = p.get(nat.false_pos);
        let is_zero_step_at_false = app(is_zero_step.clone(), false_val.clone());
        let c_false_ty = app(is_zero_motive_c.clone(), false_val.clone());

        let bfe_inst = app(app(app(nat.bool_rec_false_eq(&p), is_zero_motive_c.clone()), case_true.clone()), case_false.clone());
        check(
            &p.ctx,
            &bfe_inst,
            &id(c_false_ty.clone(), is_zero_step_at_false.clone(), case_false.clone()),
        )
        .expect("bool_rec_false_eq instantiated at (is_zero_motive_c, case_true, case_false) should typecheck");

        // f_cong : C(false) -> Bool := \h. h(f_zero_here)(rec_step)
        let f_cong = lam(c_false_ty.clone(), app(app(var(0), shift(&f_zero_here, 0, 1)), shift(&rec_step, 0, 1)));
        let cong_step = cong1(&c_false_ty, &bool_ty, &f_cong, is_zero_step_at_false, case_false.clone(), bfe_inst);

        // `refl` bridges `is_zero_on_zero` to its own one-step reduction
        // (definitionally equal, `whnf` being one particular strategy for
        // reaching a shared normal form) -- `trans_proof` then chains that
        // with `cong_step` (whose own type, `Id(Bool, f_cong(is_zero_step
        // (false)), f_cong(case_false))`, is itself definitionally equal
        // to `Id(Bool, stuck_one_step, true)` once both sides beta-reduce,
        // `case_false`'s own body reducing all the way to `true`) to land
        // on the final result.
        let bridge = refl(is_zero_on_zero.clone());
        let final_proof = trans_proof(&bool_ty, &is_zero_on_zero, &stuck_one_step, &true_val, bridge, cong_step);
        check(&p.ctx, &final_proof, &id(bool_ty, is_zero_on_zero, true_val))
            .expect("is_zero(Zero) = true should now be provable propositionally");
    }

    #[test]
    fn a_tagged_selector_built_via_wrec_typechecks_a_pair_for_a_symbolic_tag() {
        // Prototype for RELATED_WORK.md sec 14's open question: can a
        // Sigma-tagged "either T1 or T2" encoding typecheck a Pair for a
        // SYMBOLIC (universally quantified) tag, not just a concrete one?
        // Hypothesis: build both the type selector (`fam`) and the paired
        // value as WRec applications sharing the same underlying "motive"
        // Lam -- WRec's own typing rule hands back `app(motive, target)`
        // as the type *by construction* (kernel.rs's own `infer`, `Expr::
        // WRec` case), so `def_eq` between the value's inferred type and
        // `fam`'s substituted form reduces to ordinary, unconditional
        // beta -- never needing the tag itself to reduce to a concrete Sup.
        let mut p = Postulates::new();
        let nat = NatPostulates::new(&mut p);

        // Push the tag as an abstract postulate up front -- genuinely
        // symbolic, not a concrete Sup value -- so everything built below
        // is naturally index-consistent with it already in scope.
        let a_pos = p.push(nat.nat_ty(&p));

        // sort_rec : Pi C:(Bool -> Sort1). C(true) -> C(false) -> Pi b:Bool. C(b)
        // -- bool_rec's own shape (`wrap_c_ct_cf`), but targeting Sort(1)
        // so C can select between *types*, not just Sort0 values (Nat
        // Postulates' own bool_rec hardcodes Sort(0) -- see this file's own
        // is_zero test and RELATED_WORK.md's universe-mismatch finding).
        fn wrap_c_ct_cf_sort1(bool_ref: &Expr, true_ref: &Expr, false_ref: &Expr, body_d3: Expr) -> Expr {
            let c_ty = arrow(bool_ref.clone(), sort(1));
            let true_d1 = shift(true_ref, 0, 1);
            let false_d2 = shift(false_ref, 0, 2);
            let pi_cf = pi(app(var(1), false_d2), body_d3);
            let pi_ct = pi(app(var(0), true_d1), pi_cf);
            pi(c_ty, pi_ct)
        }
        // Mirrors `infer`'s own `Expr::WRec` case exactly: returns
        // (per-tag body, one binder deep; full `Pi a:wa. ...`).
        fn wrec_step_type(wa: &Expr, wb: &Expr, w_ty0: &Expr, motive: &Expr) -> (Expr, Expr) {
            let f_dom_d1 = wb.clone();
            let f_ty_d1 = pi(f_dom_d1, shift(w_ty0, 0, 2));
            let ih_dom_d2 = shift(wb, 0, 1);
            let motive_d3 = shift(motive, 0, 3);
            let ih_body_d3 = app(motive_d3, app(var(1), var(0)));
            let ih_ty_d2 = pi(ih_dom_d2, ih_body_d3);
            let motive_d2 = shift(motive, 0, 2);
            let concl_ty_d2 = app(motive_d2, sup(var(1), var(0)));
            let arrow_ty_d2 = pi(ih_ty_d2, shift(&concl_ty_d2, 0, 1));
            let per_tag_body_d1 = pi(f_ty_d1, arrow_ty_d2);
            let full = pi(wa.clone(), per_tag_body_d1.clone());
            (per_tag_body_d1, full)
        }

        let sort_rec_body_d3 = pi(shift(&p.get(nat.bool_pos), 0, 3), app(var(3), var(0)));
        let sort_rec_ty = wrap_c_ct_cf_sort1(&p.get(nat.bool_pos), &p.get(nat.true_pos), &p.get(nat.false_pos), sort_rec_body_d3);
        let sort_rec_pos = p.push(sort_rec_ty);

        // sort_rec_true_eq : Pi C ct cf. Id(C(true), sort_rec(C,ct,cf)(true), ct)
        let true_d3 = shift(&p.get(nat.true_pos), 0, 3);
        let applied_d3 = app(app(app(shift(&p.get(sort_rec_pos), 0, 3), var(2)), var(1)), var(0));
        let true_eq_body_d3 = id(app(var(2), true_d3.clone()), app(applied_d3, true_d3), var(1));
        let sort_rec_true_eq_ty = wrap_c_ct_cf_sort1(&p.get(nat.bool_pos), &p.get(nat.true_pos), &p.get(nat.false_pos), true_eq_body_d3);
        let sort_rec_true_eq_pos = p.push(sort_rec_true_eq_ty);

        // sort_rec_false_eq : Pi C ct cf. Id(C(false), sort_rec(C,ct,cf)(false), cf)
        let false_d3 = shift(&p.get(nat.false_pos), 0, 3);
        let applied_d3b = app(app(app(shift(&p.get(sort_rec_pos), 0, 3), var(2)), var(1)), var(0));
        let false_eq_body_d3 = id(app(var(2), false_d3.clone()), app(applied_d3b, false_d3), var(0));
        let sort_rec_false_eq_ty = wrap_c_ct_cf_sort1(&p.get(nat.bool_pos), &p.get(nat.true_pos), &p.get(nat.false_pos), false_eq_body_d3);
        let sort_rec_false_eq_pos = p.push(sort_rec_false_eq_ty);

        // --- Fresh from here on: everything (a, sort_rec, its two
        // computation-rule axioms) is already in scope.
        let nat_ty = nat.nat_ty(&p);
        let bool_ty = nat.bool_ty(&p);
        let true_val = nat.true_(&p);
        let false_val = nat.false_(&p);
        let sort_rec = p.get(sort_rec_pos);
        let wb = app(shift(&p.get(nat.child_ty_pos), 0, 1), var(0)); // ChildTy(b), one binder (b)

        // type_motive : Nat -> Sort0, constant -- `fam`'s own overall type
        // doesn't need to vary per branch; what varies per branch is
        // `step`'s own *value*, selected via sort_rec below.
        let type_motive = lam(nat_ty.clone(), sort(0));
        check(&p.ctx, &type_motive, &arrow(nat_ty.clone(), sort(1))).expect("type_motive : Nat -> Sort1");

        let (type_per_tag_d1, type_expected_step_ty) = wrec_step_type(&bool_ty, &wb, &nat_ty, &type_motive);
        let type_motive_c = lam(bool_ty.clone(), type_per_tag_d1.clone());

        // Two genuinely distinct Sort0 types to select between -- stand-ins
        // for Clo_1/Clo_2.
        let clo1_ty = nat.unit_ty(&p);
        let clo2_ty = nat_ty.clone();

        let case_true_ty_expected = subst_top(&type_per_tag_d1, &true_val);
        let Expr::Pi(f_dom_true, rest_true) = &case_true_ty_expected else { panic!("expected Pi") };
        let Expr::Pi(ih_dom_true, _) = &**rest_true else { panic!("expected Pi") };
        let case_true_ty = lam((**f_dom_true).clone(), lam((**ih_dom_true).clone(), shift(&clo1_ty, 0, 2)));
        check(&p.ctx, &case_true_ty, &case_true_ty_expected).expect("case_true_ty : type_motive_c(true)");

        let case_false_ty_expected = subst_top(&type_per_tag_d1, &false_val);
        let Expr::Pi(f_dom_false, rest_false) = &case_false_ty_expected else { panic!("expected Pi") };
        let Expr::Pi(ih_dom_false, _) = &**rest_false else { panic!("expected Pi") };
        let case_false_ty = lam((**f_dom_false).clone(), lam((**ih_dom_false).clone(), shift(&clo2_ty, 0, 2)));
        check(&p.ctx, &case_false_ty, &case_false_ty_expected).expect("case_false_ty : type_motive_c(false)");

        let type_step = app(app(app(sort_rec.clone(), type_motive_c.clone()), case_true_ty.clone()), case_false_ty.clone());
        check(&p.ctx, &type_step, &type_expected_step_ty).expect("type_step : Pi b:Bool. type_motive_c(b)");

        // fam := wrec(type_motive, ChildTy(Var0), type_step, Var(0)) --
        // Sigma's own open family body, one binder under the tag.
        let fam = wrec(shift(&type_motive, 0, 1), shift(&wb, 1, 1), shift(&type_step, 0, 1), var(0));

        let sigma_ty = sigma(nat_ty.clone(), fam.clone());
        check(&p.ctx, &sigma_ty, &sort(0)).expect("Sigma(Nat, fam) : Sort0");

        // --- THE KEY CLAIM: Pair(fam, a, b) typechecks for a's tag being a
        // genuinely SYMBOLIC (universally quantified) postulate, not a
        // concrete Sup value -- unlike the earlier tagged-Sigma
        // investigation (RELATED_WORK.md sec 14), which needed `a` concrete.
        let a = p.get(a_pos);

        // value_motive := \x:Nat. fam -- literally reuses `fam` as the
        // Lam's own body, so `value_motive(a)` beta-reduces (unconditionally,
        // for ANY a, symbolic or not) to exactly `subst_top(fam, a)`.
        let value_motive = lam(nat_ty.clone(), fam.clone());
        check(&p.ctx, &value_motive, &arrow(nat_ty.clone(), sort(0))).expect("value_motive : Nat -> Sort0");

        let (value_per_tag_d1, value_expected_step_ty) = wrec_step_type(&bool_ty, &wb, &nat_ty, &value_motive);
        let value_motive_c = lam(bool_ty.clone(), value_per_tag_d1.clone());

        let value_case_true_expected = subst_top(&value_per_tag_d1, &true_val);
        let Expr::Pi(vf_dom_true, vrest_true) = &value_case_true_expected else { panic!("expected Pi") };
        let Expr::Pi(vih_dom_true, _) = &**vrest_true else { panic!("expected Pi") };

        let value_case_false_expected = subst_top(&value_per_tag_d1, &false_val);
        let Expr::Pi(vf_dom_false, vrest_false) = &value_case_false_expected else { panic!("expected Pi") };
        let Expr::Pi(vih_dom_false, _) = &**vrest_false else { panic!("expected Pi") };

        // Rebuild, under `case_*_val`'s own f/ih binders (depth 2), the
        // exact induction-hypothesis closure `whnf_impl`'s own WRec-Sup
        // rule auto-builds when reducing `value_motive(sup(tag,f))` --
        // mirroring `nat_via_w_is_a_genuinely_computing_inductive_type`'s
        // own hand-rebuild of `rec_step`, generalized to a bound `f`
        // instead of a closed one.
        fn rebuild_rec_step_d2(type_motive: &Expr, wb: &Expr, type_step: &Expr, tag: &Expr, f_ref: &Expr) -> Expr {
            let tm2 = shift(type_motive, 0, 2);
            let wb2 = shift(wb, 1, 2);
            let ts2 = shift(type_step, 0, 2);
            let tag2 = shift(tag, 0, 2);
            lam(
                subst_top(&wb2, &tag2),
                wrec(shift(&tm2, 0, 1), shift(&wb2, 1, 1), shift(&ts2, 0, 1), app(shift(f_ref, 0, 1), var(0))),
            )
        }

        // Bridges `type_step(tag)(f)(rec_step) = case_ty(f)(rec_step)`
        // propositionally via `sort_rec_{true,false}_eq` + one `cong1`
        // (the `f_cong` trick `is_zero`'s own proof above already uses),
        // then `transport`s a real, concrete witness across it.
        #[allow(clippy::too_many_arguments)]
        fn build_case_val(
            p: &Postulates,
            type_motive_c: &Expr,
            type_step: &Expr,
            case_ty: &Expr,
            eq_ref: &Expr,
            case_true_ty: &Expr,
            case_false_ty: &Expr,
            tag: &Expr,
            f_dom: &Expr,
            ih_dom: &Expr,
            rec_step: &Expr,
            witness_ty: &Expr,
            witness: &Expr,
        ) -> Expr {
            let f_ref = var(1);
            let tag2 = shift(tag, 0, 2);
            let type_step_at_tag = app(shift(type_step, 0, 2), tag2.clone());
            let target_ty = app(app(type_step_at_tag.clone(), f_ref.clone()), rec_step.clone());

            let c_at_tag = app(shift(type_motive_c, 0, 2), tag2.clone());
            let eq_inst = app(app(app(shift(eq_ref, 0, 2), shift(type_motive_c, 0, 2)), shift(case_true_ty, 0, 2)), shift(case_false_ty, 0, 2));
            let f_cong = lam(c_at_tag.clone(), app(app(var(0), shift(&f_ref, 0, 1)), shift(rec_step, 0, 1)));
            let cong_step = cong1(&c_at_tag, &sort(0), &f_cong, type_step_at_tag, shift(case_ty, 0, 2), eq_inst);

            // `witness`/`witness_ty` are given at *ambient* (outer-test)
            // depth -- everything else here is already shifted for this
            // function's own depth-2 (f, ih) scope, so these need the same
            // +2 shift for `sym`/`transport` to compare like-for-like.
            let witness_ty2 = shift(witness_ty, 0, 2);
            let witness2 = shift(witness, 0, 2);
            let bridge = sym(&sort(0), &target_ty, &witness_ty2, cong_step);
            let _ = p;
            lam(f_dom.clone(), lam(ih_dom.clone(), transport(0, witness_ty2, target_ty, bridge, witness2)))
        }

        let f_ref_true = var(1);
        let rec_step_true = rebuild_rec_step_d2(&type_motive, &wb, &type_step, &true_val, &f_ref_true);
        let star = nat.star(&p);
        let case_true_val = build_case_val(
            &p,
            &type_motive_c,
            &type_step,
            &case_true_ty,
            &p.get(sort_rec_true_eq_pos),
            &case_true_ty,
            &case_false_ty,
            &true_val,
            vf_dom_true,
            vih_dom_true,
            &rec_step_true,
            &clo1_ty,
            &star,
        );
        check(&p.ctx, &case_true_val, &value_case_true_expected).expect("case_true_val : value_motive_c(true)");

        let f_ref_false = var(1);
        let rec_step_false = rebuild_rec_step_d2(&type_motive, &wb, &type_step, &false_val, &f_ref_false);
        let zero_witness = nat.zero(&p);
        let case_false_val = build_case_val(
            &p,
            &type_motive_c,
            &type_step,
            &case_false_ty,
            &p.get(sort_rec_false_eq_pos),
            &case_true_ty,
            &case_false_ty,
            &false_val,
            vf_dom_false,
            vih_dom_false,
            &rec_step_false,
            &clo2_ty,
            &zero_witness,
        );
        check(&p.ctx, &case_false_val, &value_case_false_expected).expect("case_false_val : value_motive_c(false)");

        // `value_motive_c`'s own final codomain is `value_motive(sup(b,f))`
        // -- an *application*, itself Sort0-typed (unlike `type_motive_c`'s
        // literal `sort(0)` codomain, which is Sort1-typed as a value) --
        // so `value_motive_c : Bool -> Sort0` exactly matches the ordinary,
        // already-built `nat.bool_rec` (no new postulate needed here).
        let value_step = app(app(app(nat.bool_rec(&p), value_motive_c.clone()), case_true_val), case_false_val);
        check(&p.ctx, &value_step, &value_expected_step_ty).expect("value_step : Pi b:Bool. value_motive_c(b)");

        // b_val := wrec(value_motive, ChildTy(Var0), value_step, a) --
        // standalone, at the SAME (ambient) depth as `a` itself, no extra
        // binder (unlike `fam`, this isn't going *inside* anything).
        let b_val = wrec(value_motive.clone(), wb.clone(), value_step, a.clone());
        let expected_b_ty = subst_top(&fam, &a);
        check(&p.ctx, &b_val, &expected_b_ty).expect("b_val : subst_top(fam, a) -- the core claim, isolated");

        // Sanity: `a` is genuinely symbolic, not secretly concrete -- whnf
        // doesn't reduce a bare postulate reference to `Sup(..)`, and
        // `fam(a)` doesn't secretly normalize to some closed Sort0 type
        // either (both would make this whole exercise vacuous).
        assert_eq!(whnf(&a), a, "the tag must stay an unreduced postulate reference, not secretly a concrete Sup");
        assert!(
            !matches!(nf(&expected_b_ty), Expr::Sort(_) | Expr::W(..)),
            "fam(a) must stay stuck for symbolic a, not secretly collapse to a closed type: {:?}",
            nf(&expected_b_ty)
        );

        // --- THE ULTIMATE CLAIM: Pair(fam, a, b_val) typechecks as
        // Sigma(Nat, fam), for `a` a genuinely symbolic tag -- unlike the
        // earlier tagged-Sigma investigation (RELATED_WORK.md sec 14),
        // which needed `a` concrete before `Pair`'s own definitional-
        // equality check could ever succeed.
        let pr = pair(fam.clone(), a.clone(), b_val);
        let pr_ty = infer(&p.ctx, &pr).expect("Pair(fam, a, b_val) should typecheck for a SYMBOLIC tag");
        assert!(def_eq(&pr_ty, &sigma_ty), "Pair's own inferred type should be Sigma(Nat, fam): got {pr_ty:?}");
    }

    #[test]
    fn shift_by_zero_is_the_identity_including_through_binders() {
        // Exercises every variant, including ones whose subterms sit under
        // an extra binder (Pi/Lam/W bump `cutoff` for their second field) --
        // shift's `amount == 0` fast path returns `e.clone()` without
        // recursing at all, so this confirms that's equivalent to the full
        // structural recursion for a term where it'd actually matter if the
        // fast path skipped something it shouldn't.
        let e = pi(
            sort(0),
            jelim(
                lam(var(0), wty(var(1), sup(var(0), var(2)))),
                refl(var(0)),
                var(1),
                var(2),
                wrec(var(0), var(1), var(2), var(3)),
            ),
        );
        assert_eq!(shift(&e, 0, 0), e);
        assert_eq!(shift(&e, 3, 0), e);
    }

    #[test]
    fn universes_stratify() {
        assert_eq!(typecheck(&sort(0)).unwrap(), sort(1));
        assert_eq!(typecheck(&sort(5)).unwrap(), sort(6));
    }

    #[test]
    fn a_maximal_universe_level_is_a_clean_type_error_not_an_overflow_panic() {
        // Type_{u32::MAX} has no successor sort representable in this
        // encoding -- infer's own `i.checked_add(1)` reports that as an
        // ordinary Err, rather than panicking on the arithmetic overflow
        // `i + 1` would otherwise trigger (checked in debug builds, wrapping
        // silently to Type0 in release -- neither of which is the honest
        // "this term doesn't typecheck" answer every other rejection here
        // gives).
        assert!(typecheck(&sort(u32::MAX)).is_err());
    }

    #[test]
    fn identity_function_typechecks() {
        // \A:Type0. \x:A. x  :  Pi A:Type0. A -> A
        let f = lam(sort(0), lam(var(0), var(0)));
        let ty = typecheck(&f).unwrap();
        let expected = pi(sort(0), arrow(var(0), var(0)));
        assert!(def_eq(&ty, &expected), "got {ty:?}");
    }

    #[test]
    fn refl_typechecks_for_a_postulated_element() {
        let mut p = Postulates::new();
        let a_pos = p.push(sort(0)); // A : Type0
        let a0_pos = p.push(p.get(a_pos)); // a0 : A

        let a0 = p.get(a0_pos);
        let ty = infer(&p.ctx, &refl(a0.clone())).unwrap();
        assert!(def_eq(&ty, &id(p.get(a_pos), a0.clone(), a0)));
    }

    #[test]
    fn w_recursor_computes_definitionally() {
        // Postulate a base type A with a witness a0, a (tag-independent)
        // children-index type Bc, and a children function
        // f0 : Bc -> W(A, Bc). See `Postulates` docs above for why this is
        // postulated rather than derived.
        let mut p = Postulates::new();
        let a_pos = p.push(sort(0)); // A : Type0
        let a0_pos = p.push(p.get(a_pos)); // a0 : A
        let bc_pos = p.push(sort(0)); // Bc : Type0
        let w_ty_pre = wty(p.get(a_pos), shift(&p.get(bc_pos), 0, 1));
        let f0_pos = p.push(arrow(p.get(bc_pos), w_ty_pre)); // f0 : Bc -> W(A,Bc)

        // p.ctx now has 4 entries; re-fetch references at this depth.
        let a_ref = p.get(a_pos);
        let bc_ref = p.get(bc_pos);
        let w_ty = wty(a_ref.clone(), shift(&bc_ref, 0, 1));
        let target = sup(p.get(a0_pos), p.get(f0_pos));
        assert!(def_eq(&infer(&p.ctx, &target).unwrap(), &w_ty));

        // motive := \_ : W(A,Bc). W(A,Bc)   (constant motive)
        let motive = lam(w_ty.clone(), shift(&w_ty, 0, 1));

        // step := \a:A. \f:(Bc->W). \ih:(Pi y:Bc. motive (f y)). sup(a, f)
        // i.e. "reconstruct the node, ignoring the induction hypothesis" —
        // this makes `wrec(motive, step, _)` the identity on W, defined via
        // its own recursor rather than as a primitive.
        // Note: `pi`, not `arrow` -- `shift(&w_ty, 0, 2)` already lands the
        // codomain at the right depth (one deeper than this Pi's own
        // placement at depth1); wrapping it in `arrow` would shift it twice.
        let f_ty_d1 = pi(shift(&bc_ref, 0, 1), shift(&w_ty, 0, 2));
        let ih_ty_d2 = pi(
            shift(&bc_ref, 0, 2),
            app(shift(&motive, 0, 3), app(var(1), var(0))), // motive (f y)
        );
        let step = lam(a_ref, lam(f_ty_d1, lam(ih_ty_d2, sup(var(2), var(1)))));

        let reduced = wrec(motive, shift(&bc_ref, 0, 1), step, target.clone());
        check(&p.ctx, &reduced, &w_ty).expect("wrec application should typecheck");
        // The payoff of choosing W over an impredicative/Church encoding:
        // this holds by `refl` alone — the recursor genuinely *computes*,
        // it doesn't just make the equation provable with extra work.
        check(&p.ctx, &refl(target.clone()), &id(w_ty, reduced, target))
            .expect("wrec(motive, step, sup(a,f)) should reduce definitionally to sup(a,f)");
    }

    #[test]
    fn sup_rejects_a_children_function_whose_codomain_genuinely_depends_on_its_own_argument() {
        // `Sup(a, f)`'s own typing rule (see its doc) requires `f`'s
        // codomain to be a constant `W(A,B)`, independent of `f`'s own
        // bound argument -- otherwise `subst_top(cod, a)` is only ever
        // validated at this one concrete `a`, silently trusting every
        // other point of `f`'s domain agrees. Build a minimal witness
        // where that's structurally false: `g : D -> Type0` postulated
        // opaque (so its result genuinely varies per input, as far as the
        // kernel can tell -- no reduction could ever prove otherwise),
        // and `mk : Pi x:D. g(x)`, so `mk` itself has exactly the
        // offending shape `Pi x:D. cod` with `cod = g(x)` mentioning `x`.
        let mut p = Postulates::new();
        let a_pos = p.push(sort(0)); // A : Type0
        let a0_pos = p.push(p.get(a_pos)); // a0 : A
        let d_pos = p.push(sort(0)); // D : Type0
        let g_pos = p.push(arrow(p.get(d_pos), sort(0))); // g : D -> Type0
        let mk_ty = pi(p.get(d_pos), app(shift(&p.get(g_pos), 0, 1), var(0))); // Pi x:D. g(x)
        let mk_pos = p.push(mk_ty);

        let target = sup(p.get(a0_pos), p.get(mk_pos));
        let err = infer(&p.ctx, &target).expect_err("a dependent codomain must be rejected, not silently trusted");
        assert!(
            err.contains("must not depend"),
            "expected the dependent-codomain error, got: {err}"
        );
    }

    #[test]
    fn is_var_free_tracks_binder_depth_and_is_checked_against_normal_form_not_raw_syntax() {
        // `Sup`'s new occurs-check (above) runs `is_var_free` on `cod`'s
        // *normal form*, not its raw syntax, precisely so a codomain that
        // only syntactically mentions its own argument -- but beta-
        // reduces free of it -- is still accepted rather than wrongly
        // rejected. Exercise `is_var_free` itself directly, including
        // that specific reduces-away shape, rather than through the
        // fragile nested-W-type indexing a full `Sup` witness would need.
        assert!(is_var_free(&var(0), 0));
        assert!(!is_var_free(&var(1), 0));
        // `\_:Sort0. (outer Var(0))`, written under one more binder as
        // `Var(1)` -- does this Lam depend on the *outer* Var(0)? Yes.
        assert!(is_var_free(&lam(sort(0), var(1)), 0));
        // `\_:Sort0. Var(0)` (the lambda's *own* argument) -- does this
        // depend on something *outside* the lambda at outer-index 0? No.
        assert!(!is_var_free(&lam(sort(0), var(0)), 0));

        // `(\_:Sort0. Sort(1)) (Var 0)` mentions `Var(0)` syntactically as
        // the application's argument, but beta-reduces to plain
        // `Sort(1)`, genuinely independent of it.
        let redex = app(lam(sort(0), sort(1)), var(0));
        assert!(is_var_free(&redex, 0), "the raw syntax does mention Var(0)");
        assert!(!is_var_free(&nf(&redex), 0), "but it reduces away");
    }

    #[test]
    fn sigma_pairing_typechecks_and_projects_by_refl() {
        // A postulated type A, an element a0:A, a second type B, an
        // element b0:B -- a non-dependent pair Sigma(A, \_.B), the
        // simplest instance, isolating pairing/projection from
        // dependency itself (see
        // `sigma_family_genuinely_varies_with_the_tag` below for a case
        // that needs real dependency).
        let mut p = Postulates::new();
        let a_pos = p.push(sort(0));
        let a0_pos = p.push(p.get(a_pos));
        let b_pos = p.push(sort(0));
        let b0_pos = p.push(p.get(b_pos));

        let a_ref = p.get(a_pos);
        let a0_ref = p.get(a0_pos);
        let b_ref = p.get(b_pos);
        let b0_ref = p.get(b0_pos);

        let fam = shift(&b_ref, 0, 1); // \_:A. B, written one binder deeper
        let sig_ty = sigma(a_ref.clone(), fam.clone());
        let target = pair(fam.clone(), a0_ref.clone(), b0_ref.clone());
        check(&p.ctx, &target, &sig_ty).expect("pair(fam, a0, b0) : Sigma(A, fam)");

        // motive := \_:Sigma(A,fam). A  (constant motive)
        let motive = lam(sig_ty.clone(), shift(&a_ref, 0, 1));
        // step := \a:A. \b:B. a  -- i.e. "fst"
        let step = lam(a_ref.clone(), lam(fam, var(1)));
        let reduced = sigrec(motive, step, target.clone());
        check(&p.ctx, &reduced, &a_ref).expect("sigrec application should typecheck");
        // The same payoff `w_recursor_computes_definitionally` already
        // established for `W`: this holds by `refl` alone -- the
        // recursor genuinely *computes*, not just propositionally.
        check(&p.ctx, &refl(a0_ref.clone()), &id(a_ref, reduced, a0_ref))
            .expect("sigrec(motive, step, pair(fam,a0,b0)) should reduce definitionally to a0");
    }

    #[test]
    fn sigma_family_genuinely_varies_with_the_tag() {
        // A postulated type A and element a0:A; fam(x) := Id(A, x, a0),
        // a family that genuinely varies with the tag (not just carried
        // along unused, unlike the constant-family test above) --
        // Sigma(A,fam) is "an x together with a proof that x=a0".
        // pair(fam, a0, refl(a0)) should typecheck, needing
        // `subst_top(fam,a)`'s own substitution to correctly produce
        // `Id(A,a0,a0)` for `refl(a0)` to check against.
        let mut p = Postulates::new();
        let a_pos = p.push(sort(0));
        let a0_pos = p.push(p.get(a_pos));
        let a_ref = p.get(a_pos);
        let a0_ref = p.get(a0_pos);

        // fam := Id(A, Var(0), a0), one binder deeper than A (the tag x)
        let fam = id(shift(&a_ref, 0, 1), var(0), shift(&a0_ref, 0, 1));
        let sig_ty = sigma(a_ref, fam.clone());
        let target = pair(fam, a0_ref.clone(), refl(a0_ref));
        check(&p.ctx, &target, &sig_ty).expect("pair(fam, a0, refl(a0)) : Sigma(A, fam)");
    }

    #[test]
    fn pair_with_a_mismatched_second_component_is_rejected() {
        let mut p = Postulates::new();
        let a_pos = p.push(sort(0));
        let a0_pos = p.push(p.get(a_pos));
        let b_pos = p.push(sort(0));

        let a0_ref = p.get(a0_pos);
        let b_ref = p.get(b_pos);
        let fam = shift(&b_ref, 0, 1); // \_:A. B
        // second component should be B-typed, not A-typed
        let bad = pair(fam, a0_ref.clone(), a0_ref);
        assert!(infer(&p.ctx, &bad).is_err(), "pair's own second component must check against fam(a), not anything else");
    }

    /// The soundness gate `infer`'s own `WRec` case now needs (see
    /// `Expr::WRec`'s own doc): a term whose `children_ty` field doesn't
    /// match `target`'s own real children-type family must be rejected
    /// outright, not silently trusted. Without this check, `whnf_impl`
    /// would honestly (per its own, now-correct reduction rule) type an
    /// induction-hypothesis closure at whatever *wrong* domain a
    /// maliciously- or accidentally-constructed `children_ty` names --
    /// letting a step function's own body get away with treating that
    /// closure's argument as something it isn't.
    #[test]
    fn wrec_with_a_mismatched_children_ty_is_rejected() {
        let mut p = Postulates::new();
        let a_pos = p.push(sort(0)); // A : Type0
        let a0_pos = p.push(p.get(a_pos)); // a0 : A
        let bc_pos = p.push(sort(0)); // Bc : Type0
        let w_ty_pre = wty(p.get(a_pos), shift(&p.get(bc_pos), 0, 1));
        let f0_pos = p.push(arrow(p.get(bc_pos), w_ty_pre));

        let a_ref = p.get(a_pos);
        let bc_ref = p.get(bc_pos);
        let w_ty = wty(a_ref.clone(), shift(&bc_ref, 0, 1));
        let target = sup(p.get(a0_pos), p.get(f0_pos));
        let motive = lam(w_ty.clone(), shift(&w_ty, 0, 1));
        let f_ty_d1 = pi(shift(&bc_ref, 0, 1), shift(&w_ty, 0, 2));
        let ih_ty_d2 = pi(shift(&bc_ref, 0, 2), app(shift(&motive, 0, 3), app(var(1), var(0))));
        let step = lam(a_ref, lam(f_ty_d1, lam(ih_ty_d2, sup(var(2), var(1)))));

        // The real, matching children_ty (`shift(&bc_ref, 0, 1)`) is
        // exactly what `w_recursor_computes_definitionally` above uses,
        // and typechecks fine -- substituted here for a wrong one
        // (`Sort(0)`, `Bc`'s own type, one universe too high to even be
        // `def_eq` to `Bc` itself) that names the wrong children family.
        let wrong = wrec(motive, sort(0), step, target);
        assert!(
            infer(&p.ctx, &wrong).is_err(),
            "a WRec term whose children_ty doesn't match target's own real children-type should be rejected, not silently trusted"
        );
    }

    #[test]
    fn j_proves_symmetry_of_id() {
        // sym : Pi A:Type0. Pi x y:A. Id A x y -> Id A y x
        // sym = \A x y p. J(motive = \x y _. Id A y x, base = \x. refl x, x, y, p)
        //
        // Depths while building the body (A=d1,x=d2,y=d3,p=d4; at d4:
        // A=Var3, x=Var2, y=Var1, p=Var0).
        let motive = lam(
            var(3), // A, at d4 (motive's own binder x' sits at d4)
            lam(
                var(4), // A, at d5 (one more binder, y', intervened)
                lam(
                    id(var(5), var(1), var(0)), // Id A x' y', at d6
                    id(var(6), var(1), var(2)), // Id A y' x', at d7 (swapped)
                ),
            ),
        );
        let base = lam(var(3), refl(var(0))); // \x:A. refl x, at d4

        let sym = lam(
            sort(0),
            lam(
                var(0),
                lam(
                    shift(&var(0), 0, 1),
                    lam(
                        id(shift(&var(0), 0, 2), var(1), var(0)),
                        jelim(motive, base, var(2), var(1), var(0)),
                    ),
                ),
            ),
        );

        let ty = typecheck(&sym).unwrap();
        let expected = pi(
            sort(0),
            pi(
                var(0),
                pi(
                    shift(&var(0), 0, 1),
                    arrow(
                        id(shift(&var(0), 0, 2), var(1), var(0)),
                        id(shift(&var(0), 0, 2), var(0), var(1)),
                    ),
                ),
            ),
        );
        assert!(def_eq(&ty, &expected), "got {ty:?}\nexpected {expected:?}");

        // Sanity: sym A a a (refl a) reduces to refl a, for a postulated A/a.
        let mut p = Postulates::new();
        let a_pos = p.push(sort(0));
        let a0_pos = p.push(p.get(a_pos));
        let a_ty = p.get(a_pos);
        let a0 = p.get(a0_pos);
        let applied = app(
            app(app(app(sym.clone(), a_ty), a0.clone()), a0.clone()),
            refl(a0.clone()),
        );
        assert_eq!(nf(&applied), nf(&refl(a0)));
    }

    #[test]
    fn sym_typechecks_and_flips_the_equality() {
        let mut p = Postulates::new();
        let a_ty_pos = p.push(sort(0));
        let a_pos = p.push(p.get(a_ty_pos));
        let b_pos = p.push(p.get(a_ty_pos));
        let p1_pos = p.push(id(p.get(a_ty_pos), p.get(a_pos), p.get(b_pos)));

        let a_ty = p.get(a_ty_pos);
        let a = p.get(a_pos);
        let b = p.get(b_pos);
        let p1 = p.get(p1_pos);

        let flipped = sym(&a_ty, &a, &b, p1);
        check(&p.ctx, &flipped, &id(a_ty, b, a)).expect("sym(x,y,p) : Id(A, y, x)");
    }

    #[test]
    fn transport_moves_a_value_across_a_propositional_type_equality() {
        // Postulate two Sort(0)-level types A, B, a proof p : Id(Sort0,A,B),
        // and a : A -- transport(p, a) should typecheck at B.
        let mut p = Postulates::new();
        let a_ty_pos = p.push(sort(0));
        let b_ty_pos = p.push(sort(0));
        let p_pos = p.push(id(sort(0), p.get(a_ty_pos), p.get(b_ty_pos)));
        let a_pos = p.push(p.get(a_ty_pos));

        let a_ty = p.get(a_ty_pos);
        let b_ty = p.get(b_ty_pos);
        let proof = p.get(p_pos);
        let a = p.get(a_pos);

        let moved = transport(0, a_ty, b_ty.clone(), proof, a);
        check(&p.ctx, &moved, &b_ty).expect("transport(p,a) : B");
    }

    #[test]
    fn transport_along_refl_is_the_identity() {
        // p = refl A : Id(Sort0,A,A) -- transport should reduce to `a`
        // itself definitionally (the base case of J is the identity fn).
        let mut p = Postulates::new();
        let a_ty_pos = p.push(sort(0));
        let a_pos = p.push(p.get(a_ty_pos));

        let a_ty = p.get(a_ty_pos);
        let a = p.get(a_pos);

        let moved = transport(0, a_ty.clone(), a_ty.clone(), refl(a_ty.clone()), a.clone());
        assert_eq!(nf(&moved), nf(&a), "transport along refl should compute to the identity");
    }

    #[test]
    fn cong1_and_trans_typecheck_and_compose() {
        // Postulate A, a, b, c and proofs p1:Id(A,a,b), p2:Id(A,b,c), plus
        // a function f:A->A, then check cong1/trans against their expected
        // types and that they chain: trans(cong1(f,a,b,p1), cong1(f,b,c,p2))
        // : Id(A, f a, f c).
        let mut p = Postulates::new();
        let a_ty_pos = p.push(sort(0));
        let a_pos = p.push(p.get(a_ty_pos));
        let b_pos = p.push(p.get(a_ty_pos));
        let c_pos = p.push(p.get(a_ty_pos));
        let p1_pos = p.push(id(p.get(a_ty_pos), p.get(a_pos), p.get(b_pos)));
        let p2_pos = p.push(id(p.get(a_ty_pos), p.get(b_pos), p.get(c_pos)));
        let f_pos = p.push(arrow(p.get(a_ty_pos), p.get(a_ty_pos)));

        let a_ty = p.get(a_ty_pos);
        let a = p.get(a_pos);
        let b = p.get(b_pos);
        let c = p.get(c_pos);
        let p1 = p.get(p1_pos);
        let p2 = p.get(p2_pos);
        let f = p.get(f_pos);

        let c1 = cong1(&a_ty, &a_ty, &f, a.clone(), b.clone(), p1);
        check(&p.ctx, &c1, &id(a_ty.clone(), app(f.clone(), a.clone()), app(f.clone(), b.clone())))
            .expect("cong1(f,a,b,p1) : Id(A, f a, f b)");

        let c2 = cong1(&a_ty, &a_ty, &f, b.clone(), c.clone(), p2);
        check(&p.ctx, &c2, &id(a_ty.clone(), app(f.clone(), b.clone()), app(f.clone(), c.clone())))
            .expect("cong1(f,b,c,p2) : Id(A, f b, f c)");

        let chained = trans_proof(&a_ty, &app(f.clone(), a.clone()), &app(f.clone(), b.clone()), &app(f.clone(), c.clone()), c1, c2);
        check(&p.ctx, &chained, &id(a_ty, app(f.clone(), a), app(f, c)))
            .expect("trans(cong1(..p1), cong1(..p2)) : Id(A, f a, f c)");
    }

    #[test]
    fn cong1_with_a_different_codomain_than_domain_typechecks() {
        // f : A -> B (B distinct from A) -- every prior caller of cong1/
        // cong_n happened to have f's codomain equal its domain, so this
        // exercises the b_ty-distinct-from-a_ty case on its own for the
        // first time. cong1(f,a,b,p) : Id(B, f a, f b), not Id(A, ..).
        let mut p = Postulates::new();
        let a_ty_pos = p.push(sort(0));
        let b_ty_pos = p.push(sort(0));
        let a_pos = p.push(p.get(a_ty_pos));
        let b_pos = p.push(p.get(a_ty_pos));
        let f_pos = p.push(arrow(p.get(a_ty_pos), p.get(b_ty_pos)));
        let p1_pos = p.push(id(p.get(a_ty_pos), p.get(a_pos), p.get(b_pos)));

        let a_ty = p.get(a_ty_pos);
        let b_ty = p.get(b_ty_pos);
        let a = p.get(a_pos);
        let b = p.get(b_pos);
        let f = p.get(f_pos);
        let p1 = p.get(p1_pos);

        let c1 = cong1(&a_ty, &b_ty, &f, a.clone(), b.clone(), p1);
        check(&p.ctx, &c1, &id(b_ty, app(f.clone(), a), app(f, b))).expect("cong1(f,a,b,p1) : Id(B, f a, f b)");
    }

    #[test]
    fn cong_n_with_a_different_codomain_than_domain_typechecks() {
        // Same distinction one level up: g : A -> A -> B.
        let mut p = Postulates::new();
        let a_ty_pos = p.push(sort(0));
        let b_ty_pos = p.push(sort(0));
        let g_pos = p.push(arrow(p.get(a_ty_pos), arrow(p.get(a_ty_pos), p.get(b_ty_pos))));
        let x0_pos = p.push(p.get(a_ty_pos));
        let y0_pos = p.push(p.get(a_ty_pos));
        let x1_pos = p.push(p.get(a_ty_pos));
        let y1_pos = p.push(p.get(a_ty_pos));
        let p0_pos = p.push(id(p.get(a_ty_pos), p.get(x0_pos), p.get(y0_pos)));
        let p1_pos = p.push(id(p.get(a_ty_pos), p.get(x1_pos), p.get(y1_pos)));

        let a_ty = p.get(a_ty_pos);
        let b_ty = p.get(b_ty_pos);
        let g = p.get(g_pos);
        let x0 = p.get(x0_pos);
        let y0 = p.get(y0_pos);
        let x1 = p.get(x1_pos);
        let y1 = p.get(y1_pos);
        let p0 = p.get(p0_pos);
        let p1 = p.get(p1_pos);

        let proof = cong_n(&a_ty, &b_ty, &g, &[x0.clone(), x1.clone()], &[y0.clone(), y1.clone()], vec![p0, p1]);
        let expected = id(b_ty, app(app(g.clone(), x0), x1), app(app(g, y0), y1));
        check(&p.ctx, &proof, &expected).expect("cong_n(g,[x0,x1],[y0,y1],[p0,p1]) : Id(B, g x0 x1, g y0 y1)");
    }

    #[test]
    fn cong_n_typechecks_for_a_binary_function() {
        // Postulate A, a binary g:A->A->A, x0,y0,x1,y1:A and proofs
        // p0:Id(A,x0,y0), p1:Id(A,x1,y1); check cong_n(g,[x0,x1],[y0,y1],[p0,p1])
        // : Id(A, g x0 x1, g y0 y1) -- the n=2 case `proof.rs`'s non-tail-
        // recursion congruence step needs (e.g. for `f(n-1) + f(n-2)`).
        let mut p = Postulates::new();
        let a_ty_pos = p.push(sort(0));
        let g_pos = p.push(arrow(p.get(a_ty_pos), arrow(p.get(a_ty_pos), p.get(a_ty_pos))));
        let x0_pos = p.push(p.get(a_ty_pos));
        let y0_pos = p.push(p.get(a_ty_pos));
        let x1_pos = p.push(p.get(a_ty_pos));
        let y1_pos = p.push(p.get(a_ty_pos));
        let p0_pos = p.push(id(p.get(a_ty_pos), p.get(x0_pos), p.get(y0_pos)));
        let p1_pos = p.push(id(p.get(a_ty_pos), p.get(x1_pos), p.get(y1_pos)));

        let a_ty = p.get(a_ty_pos);
        let g = p.get(g_pos);
        let x0 = p.get(x0_pos);
        let y0 = p.get(y0_pos);
        let x1 = p.get(x1_pos);
        let y1 = p.get(y1_pos);
        let p0 = p.get(p0_pos);
        let p1 = p.get(p1_pos);

        let proof = cong_n(&a_ty, &a_ty, &g, &[x0.clone(), x1.clone()], &[y0.clone(), y1.clone()], vec![p0, p1]);
        let expected = id(a_ty, app(app(g.clone(), x0), x1), app(app(g, y0), y1));
        check(&p.ctx, &proof, &expected).expect("cong_n(g,[x0,x1],[y0,y1],[p0,p1]) : Id(A, g x0 x1, g y0 y1)");
    }

    #[test]
    fn cong_n_with_swapped_proofs_is_rejected() {
        // Adversarial: does cong_n's own construction actually get caught
        // when misused, or does it silently produce something that
        // typechecks regardless? Same setup as
        // cong_n_typechecks_for_a_binary_function, but pass p0/p1 in the
        // WRONG order (p1, meant for position 1, supplied for position 0
        // and vice versa) -- p1 : Id(A,x1,y1) doesn't witness Id(A,x0,y0)
        // (x0/x1/y0/y1 are four *distinct* postulates, unrelated to each
        // other), so the resulting term's underlying `J` node should be
        // ill-typed, not vacuously accepted.
        let mut p = Postulates::new();
        let a_ty_pos = p.push(sort(0));
        let g_pos = p.push(arrow(p.get(a_ty_pos), arrow(p.get(a_ty_pos), p.get(a_ty_pos))));
        let x0_pos = p.push(p.get(a_ty_pos));
        let y0_pos = p.push(p.get(a_ty_pos));
        let x1_pos = p.push(p.get(a_ty_pos));
        let y1_pos = p.push(p.get(a_ty_pos));
        let p0_pos = p.push(id(p.get(a_ty_pos), p.get(x0_pos), p.get(y0_pos)));
        let p1_pos = p.push(id(p.get(a_ty_pos), p.get(x1_pos), p.get(y1_pos)));

        let a_ty = p.get(a_ty_pos);
        let g = p.get(g_pos);
        let x0 = p.get(x0_pos);
        let y0 = p.get(y0_pos);
        let x1 = p.get(x1_pos);
        let y1 = p.get(y1_pos);
        let p0 = p.get(p0_pos);
        let p1 = p.get(p1_pos);

        // Sanity: correctly-ordered proofs typecheck (mirrors the test above).
        let good = cong_n(
            &a_ty,
            &a_ty,
            &g,
            &[x0.clone(), x1.clone()],
            &[y0.clone(), y1.clone()],
            vec![p0.clone(), p1.clone()],
        );
        let expected = id(a_ty.clone(), app(app(g.clone(), x0.clone()), x1.clone()), app(app(g.clone(), y0.clone()), y1.clone()));
        check(&p.ctx, &good, &expected).expect("correctly-ordered cong_n should typecheck");

        // Adversarial: swap the proof order.
        let bad = cong_n(&a_ty, &a_ty, &g, &[x0, x1], &[y0, y1], vec![p1, p0]);
        assert!(
            check(&p.ctx, &bad, &expected).is_err(),
            "cong_n with mismatched (swapped) proofs should be rejected, not silently accepted"
        );
    }

    #[test]
    fn close_pi_matches_hand_built_dependent_pi_chain() {
        // Postulate A : Type0, push x : A, y : A onto the context, build
        // body = Id(A, x, y), and check close_pi reproduces exactly the
        // hand-built `Pi x:A. Pi y:A. Id(A, x, y)`.
        let mut p = Postulates::new();
        let a_ty_pos = p.push(sort(0));
        let a_ty = p.get(a_ty_pos); // valid at the pre-push depth captured below

        let base_len = p.ctx.len();
        let x_pos = p.push(p.get(a_ty_pos)); // fresh reference, not `a_ty.clone()` -- ctx has grown
        let y_pos = p.push(p.get(a_ty_pos)); // fresh again -- ctx has grown once more
        let body = id(p.get(a_ty_pos), p.get(x_pos), p.get(y_pos));
        let closed = close_pi(base_len, &p.ctx, body);

        let expected = pi(a_ty.clone(), pi(shift(&a_ty, 0, 1), id(shift(&a_ty, 0, 2), var(1), var(0))));
        assert_eq!(closed, expected);

        // And it typechecks as exactly that Pi-type.
        p.ctx.truncate(base_len);
        assert!(typecheck(&closed).is_err()); // open term (references A) -- must check in ctx, not standalone
        check(&p.ctx, &closed, &sort(0)).expect("Pi x:A. Pi y:A. Id(A,x,y) : Type0");
    }

    #[test]
    fn close_lam_builds_a_value_of_the_close_pi_type() {
        // Postulate A : Type0, push x : A, build the TYPE `Pi x:A. Id(A,x,x)`
        // via close_pi and the VALUE `\x:A. refl x` (of that type) via
        // close_lam, and check the value against the type.
        let mut p = Postulates::new();
        let a_ty_pos = p.push(sort(0));

        let base_len = p.ctx.len();
        let x_pos = p.push(p.get(a_ty_pos));
        let ty_body = id(p.get(a_ty_pos), p.get(x_pos), p.get(x_pos));
        let value_body = refl(p.get(x_pos));
        let ty = close_pi(base_len, &p.ctx, ty_body);
        let value = close_lam(base_len, &p.ctx, value_body);

        p.ctx.truncate(base_len);
        check(&p.ctx, &value, &ty).expect("\\x:A. refl x : Pi x:A. Id(A,x,x)");
    }
}
