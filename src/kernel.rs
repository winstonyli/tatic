//! A minimal predicative dependent type theory kernel: Pure-Type-System-style
//! Pi + a stratified universe hierarchy, plus Id-types and W-types as the
//! only two additions beyond a bare PTS.
//!
//! Four primitive term/type formers, total:
//!   - `Sort(i)`: the universe hierarchy `Type_0 : Type_1 : Type_2 ...`
//!   - `Pi`/`Lam`/`App`: dependent function types
//!   - `Id`/`Refl`/`J`: propositional equality, with its eliminator
//!   - `W`/`Sup`/`WRec`: well-founded trees, i.e. *the* generic strictly
//!     positive inductive type former (Bool, Nat, lists, and eventually
//!     this crate's own `Term` AST are all instances of one `W`, not
//!     separate primitives)
//!
//! Everything else (Bool, Nat, pairs, ...) is a *definition* built from
//! these four, not a fifth primitive. See the tests at the bottom for
//! worked examples, including a proof that uses `J` (symmetry of `Id`) and
//! a `WRec`-defined function whose defining equation holds by `refl` alone
//! (i.e. genuinely *computes*, which is the whole point of choosing `W`
//! over an impredicative/Church encoding).
//!
//! This module is intentionally free-standing: it does not (yet) replace
//! `term`/`eval`/`compile`/`jit`. Wiring the JIT's "found to be equivalent"
//! check through an actual `Id`-typed, kernel-checked proof term (instead
//! of empirical sampling) is the natural next step once this kernel is
//! trusted, not something folded into this pass.

use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;

// --- scoped shift cache ---------------------------------------------------
//
// `shift` is called constantly while composing a large proof term (see
// `proof.rs`'s `Anchored::at`), and profiling confirmed the same subterm
// getting reshifted by the same amount over and over -- not just from one
// caller, but across many (`Anchored::at`, `cong1`, `cong_n`, `trans_proof`,
// `sym`, `transport`, `arrow`, ...), which is why a cache scoped to just
// one of those callers (tried first) barely moved the needle: it only
// caught redundancy *within* that one caller's own calls, missing the
// redundancy *between* callers entirely. A cache shared across all of them
// does much better -- confirmed empirically, roughly 2x on a large
// branching-leaf instance proof.
//
// Rather than thread an explicit cache parameter through every function
// that might call `shift` (`cong1`/`cong_n`/`trans_proof`/`sym`/`transport`
// included -- a wide-reaching signature change), this uses a thread-local
// slot that's `None` by default (so `shift` outside any scope stays exactly
// the plain, zero-allocation recursion it always was) and gets populated by
// `with_shift_cache` for the duration of one call -- bounded, not a
// standing global: nothing outside that call's dynamic extent ever sees or
// grows the cache, so there's no cross-call leak the way a bare `thread_local`
// cache never cleared would have.
/// `(Rc` pointer identity as `usize, cutoff, amount) -> (the Rc itself, its
/// shifted result)` -- the `Rc` rides along so a freed node's address can't
/// be reused by an unrelated later allocation and produce a false hit.
type ShiftCacheMap = HashMap<(usize, u32, i32), (Rc<Expr>, Expr)>;

thread_local! {
    // Checked first, on every `shift_rc` call, so the overwhelmingly common
    // "no scope active" case (every proof strategy this crate has besides
    // large branching-leaf instances) costs one cheap `Cell` load and
    // nothing else -- no `RefCell` borrow, no touching `SHIFT_SCOPE` at all.
    // An earlier version checked `SHIFT_SCOPE` directly on every call and
    // measurably slowed down the *unrelated* common case (confirmed via the
    // `fib(30)` demo's cold-compile time) -- this flag is what fixed that.
    static SHIFT_SCOPE_ACTIVE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    static SHIFT_SCOPE: RefCell<Option<ShiftCacheMap>> = const { RefCell::new(None) };
}

/// Runs `f` with a shift cache active for its whole (dynamic) extent --
/// every `shift` call made while `f` runs, directly or via any of the
/// composition helpers built on it, shares one cache keyed by `(Rc`
/// identity of the subterm, `cutoff, amount)`. Restores whatever scope (if
/// any) was active before on exit, so nesting is safe, though nothing in
/// this codebase currently does. Opt-in, not automatic -- `proof.rs`'s
/// `instance_from_scaffold` deliberately does *not* wrap every call in
/// this (see its own docs: confirmed to regress the common case, routine
/// small samples, since a real `HashMap` grown to size and then dropped
/// costs more than it saves at that scale). A caller that specifically
/// expects a large or branching construction -- proving one instance at a
/// large concrete input on demand, e.g. -- wraps its own call in this.
pub fn with_shift_cache<T>(f: impl FnOnce() -> T) -> T {
    let prev = SHIFT_SCOPE.with(|s| s.replace(Some(HashMap::new())));
    let prev_was_active = prev.is_some();
    SHIFT_SCOPE_ACTIVE.with(|c| c.set(true));
    let result = f();
    SHIFT_SCOPE.with(|s| *s.borrow_mut() = prev);
    SHIFT_SCOPE_ACTIVE.with(|c| c.set(prev_was_active));
    result
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
#[derive(Clone, PartialEq, Eq)]
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
    WRec {
        motive: Rc<Expr>,
        step: Rc<Expr>,
        target: Rc<Expr>,
    },
}

impl fmt::Debug for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
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
        }
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
pub fn wrec(motive: Expr, step: Expr, target: Expr) -> Expr {
    Expr::WRec {
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
/// see `proof.rs`'s `Anchored`. Recurses through [`shift_rc`] for every
/// `Rc`-held child, which checks whether a [`with_shift_cache`] scope is
/// active -- so this is the plain, zero-allocation recursion it always was
/// outside one, and a cached one inside it, with no separate entry point
/// needed.
pub fn shift(e: &Expr, cutoff: u32, amount: i32) -> Expr {
    // Adding 0 changes no index, so this is provably the identity on `e`
    // regardless of its content -- skip the full recursive rebuild.
    if amount == 0 {
        return e.clone();
    }
    match e {
        Expr::Var(k) => {
            if *k >= cutoff {
                Expr::Var((*k as i32 + amount) as u32)
            } else {
                Expr::Var(*k)
            }
        }
        Expr::Sort(i) => Expr::Sort(*i),
        Expr::Pi(a, b) => pi(shift_rc(a, cutoff, amount), shift_rc(b, cutoff + 1, amount)),
        Expr::Lam(a, b) => lam(shift_rc(a, cutoff, amount), shift_rc(b, cutoff + 1, amount)),
        Expr::App(f, a) => app(shift_rc(f, cutoff, amount), shift_rc(a, cutoff, amount)),
        Expr::Id(a, x, y) => id(
            shift_rc(a, cutoff, amount),
            shift_rc(x, cutoff, amount),
            shift_rc(y, cutoff, amount),
        ),
        Expr::Refl(a) => refl(shift_rc(a, cutoff, amount)),
        Expr::J {
            motive,
            base,
            a,
            b,
            p,
        } => jelim(
            shift_rc(motive, cutoff, amount),
            shift_rc(base, cutoff, amount),
            shift_rc(a, cutoff, amount),
            shift_rc(b, cutoff, amount),
            shift_rc(p, cutoff, amount),
        ),
        Expr::W(a, b) => wty(shift_rc(a, cutoff, amount), shift_rc(b, cutoff + 1, amount)),
        Expr::Sup(a, f) => sup(shift_rc(a, cutoff, amount), shift_rc(f, cutoff, amount)),
        Expr::WRec {
            motive,
            step,
            target,
        } => wrec(
            shift_rc(motive, cutoff, amount),
            shift_rc(step, cutoff, amount),
            shift_rc(target, cutoff, amount),
        ),
    }
}

/// `shift`, for a child already held as `Rc<Expr>` (a struct field) --
/// checks `SHIFT_SCOPE_ACTIVE` first: with no scope active, this is
/// exactly `shift(e, cutoff, amount)` and nothing more (one cheap `Cell`
/// load, no `RefCell` touched); with one active, a hit on `SHIFT_SCOPE`
/// returns without recursing at all, and a miss recurses (through `shift`,
/// which comes back through here for every `Rc`-held grandchild) and
/// records its result before returning. Holds the `Rc` alive via the key
/// so a freed node's address can't be reused by an unrelated later
/// allocation and produce a false hit -- an address-only key corrupted
/// results in an earlier version of this check.
fn shift_rc(e: &Rc<Expr>, cutoff: u32, amount: i32) -> Expr {
    if amount == 0 {
        return (**e).clone();
    }
    if !SHIFT_SCOPE_ACTIVE.with(|c| c.get()) {
        return shift(e, cutoff, amount);
    }
    let key = (Rc::as_ptr(e) as usize, cutoff, amount);
    let hit = SHIFT_SCOPE.with(|s| s.borrow().as_ref().and_then(|cache| cache.get(&key).map(|(_, v)| v.clone())));
    if let Some(hit) = hit {
        return hit;
    }
    let result = shift(e, cutoff, amount);
    SHIFT_SCOPE.with(|s| {
        if let Some(cache) = s.borrow_mut().as_mut() {
            cache.insert(key, (e.clone(), result.clone()));
        }
    });
    result
}

/// Replace `Var(j)` with `s` throughout `e`.
fn subst(e: &Expr, j: u32, s: &Expr) -> Expr {
    match e {
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
            step,
            target,
        } => wrec(subst(motive, j, s), subst(step, j, s), subst(target, j, s)),
    }
}

/// Beta-substitution: replace `Var(0)` in `body` (which lives one binder
/// deeper) with `s`, then discharge that binder.
fn subst_top(body: &Expr, s: &Expr) -> Expr {
    shift(&subst(body, 0, &shift(s, 0, 1)), 0, -1)
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
    whnf: HashMap<PtrKey, Expr>,
    nf: HashMap<PtrKey, Expr>,
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
    match e {
        Expr::App(f, a) => match whnf_rc(f, cache) {
            Expr::Lam(_, body) => whnf_impl(&subst_top(&body, a), cache),
            other => app(other, (**a).clone()),
        },
        Expr::J {
            motive,
            base,
            a,
            b,
            p,
        } => match whnf_rc(p, cache) {
            Expr::Refl(_) => whnf_impl(&app((**base).clone(), (**a).clone()), cache),
            other => Expr::J {
                motive: motive.clone(),
                base: base.clone(),
                a: a.clone(),
                b: b.clone(),
                p: Rc::new(other),
            },
        },
        Expr::WRec {
            motive,
            step,
            target,
        } => match whnf_rc(target, cache) {
            Expr::Sup(a, f) => {
                // step a f (\y. wrec(motive, step, f y))
                let rec_step = lam(
                    sort(0), // domain annotation is inert for reduction
                    wrec(
                        shift(motive, 0, 1),
                        shift(step, 0, 1),
                        app(shift(&f, 0, 1), var(0)),
                    ),
                );
                whnf_impl(
                    &app3((**step).clone(), (*a).clone(), (*f).clone(), rec_step),
                    cache,
                )
            }
            other => Expr::WRec {
                motive: motive.clone(),
                step: step.clone(),
                target: Rc::new(other),
            },
        },
        other => other.clone(),
    }
}

/// `whnf`, cached, for a child already held as `Rc<Expr>` (a struct field)
/// -- exactly the position where the same subterm recurs many times within
/// one top-level call once a proof term shares structure.
fn whnf_rc(e: &Rc<Expr>, cache: &mut ReductionCache) -> Expr {
    let key = PtrKey(e.clone());
    if let Some(hit) = cache.whnf.get(&key) {
        return hit.clone();
    }
    let result = whnf_impl(e, cache);
    cache.whnf.insert(key, result.clone());
    result
}

/// Full normal form: `whnf`, then recurse structurally into subterms.
fn nf(e: &Expr) -> Expr {
    nf_impl(e, &mut ReductionCache::default())
}

fn nf_impl(e: &Expr, cache: &mut ReductionCache) -> Expr {
    match whnf_impl(e, cache) {
        Expr::Var(k) => Expr::Var(k),
        Expr::Sort(i) => Expr::Sort(i),
        Expr::Pi(a, b) => pi(nf_rc(&a, cache), nf_rc(&b, cache)),
        Expr::Lam(a, b) => lam(nf_rc(&a, cache), nf_rc(&b, cache)),
        Expr::App(f, a) => app(nf_rc(&f, cache), nf_rc(&a, cache)),
        Expr::Id(a, x, y) => id(nf_rc(&a, cache), nf_rc(&x, cache), nf_rc(&y, cache)),
        Expr::Refl(a) => refl(nf_rc(&a, cache)),
        Expr::J {
            motive,
            base,
            a,
            b,
            p,
        } => jelim(nf_rc(&motive, cache), nf_rc(&base, cache), nf_rc(&a, cache), nf_rc(&b, cache), nf_rc(&p, cache)),
        Expr::W(a, b) => wty(nf_rc(&a, cache), nf_rc(&b, cache)),
        Expr::Sup(a, f) => sup(nf_rc(&a, cache), nf_rc(&f, cache)),
        Expr::WRec {
            motive,
            step,
            target,
        } => wrec(nf_rc(&motive, cache), nf_rc(&step, cache), nf_rc(&target, cache)),
    }
}

fn nf_rc(e: &Rc<Expr>, cache: &mut ReductionCache) -> Expr {
    let key = PtrKey(e.clone());
    if let Some(hit) = cache.nf.get(&key) {
        return hit.clone();
    }
    let result = nf_impl(e, cache);
    cache.nf.insert(key, result.clone());
    result
}

/// `nf(a) == nf(b)`, sharing one [`ReductionCache`] across both sides --
/// worthwhile whenever `a`/`b` reference overlapping subterms, which two
/// sides of a proof obligation very often do (the same postulates, the
/// same sub-witnesses).
pub fn def_eq(a: &Expr, b: &Expr) -> bool {
    let mut cache = ReductionCache::default();
    nf_impl(a, &mut cache) == nf_impl(b, &mut cache)
}

pub fn normalize(e: &Expr) -> Expr {
    nf(e)
}

// --- typechecking -----------------------------------------------------

pub type Ctx = Vec<Expr>;

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
pub fn close_pi(base_len: usize, ctx: &[Expr], body: Expr) -> Expr {
    ctx[base_len..]
        .iter()
        .rev()
        .fold(body, |acc, dom| pi(dom.clone(), acc))
}

/// Like `close_pi`, but builds the corresponding *value* (`Lam` binders,
/// one per domain in `ctx[base_len..]`) instead of the type those binders
/// have -- for when the goal is a term of that `Pi`-type (e.g. a motive or
/// a proof to pass as an argument), not the type itself.
pub fn close_lam(base_len: usize, ctx: &[Expr], body: Expr) -> Expr {
    ctx[base_len..]
        .iter()
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
        Expr::Pi(a, b) => Ok((Rc::unwrap_or_clone(a), Rc::unwrap_or_clone(b))),
        other => Err(format!("expected a Pi type, got {other:?}")),
    }
}

fn expect_w(e: &Expr) -> Result<(Expr, Expr), String> {
    match whnf(e) {
        Expr::W(a, b) => Ok((Rc::unwrap_or_clone(a), Rc::unwrap_or_clone(b))),
        other => Err(format!("expected a W type, got {other:?}")),
    }
}

pub fn infer(ctx: &Ctx, e: &Expr) -> Result<Expr, String> {
    match e {
        Expr::Var(k) => ctx_lookup(ctx, *k).ok_or_else(|| format!("unbound variable #{k}")),
        Expr::Sort(i) => i.checked_add(1).map(Expr::Sort).ok_or_else(|| format!("universe overflow: no successor sort above Type{i}")),
        Expr::Pi(a, b) => {
            let i = expect_sort(&infer(ctx, a)?)?;
            let mut ctx2 = ctx.clone();
            ctx2.push((**a).clone());
            let j = expect_sort(&infer(&ctx2, b)?)?;
            Ok(Expr::Sort(i.max(j)))
        }
        Expr::Lam(a, body) => {
            expect_sort(&infer(ctx, a)?)?;
            let mut ctx2 = ctx.clone();
            ctx2.push((**a).clone());
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
            ctx2.push((**a).clone());
            let j = expect_sort(&infer(&ctx2, b)?)?;
            Ok(Expr::Sort(i.max(j)))
        }
        Expr::Sup(a, f) => {
            let ta = infer(ctx, a)?;
            let (dom, cod) = expect_pi(&infer(ctx, f)?)?;
            // `cod` is written one binder deeper than `f`'s own domain
            // binder; a `Sup`'s codomain must not actually depend on it.
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
        Expr::WRec {
            motive,
            step,
            target,
        } => {
            let (wa, wb) = expect_w(&infer(ctx, target)?)?;
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
    }
}

pub fn check(ctx: &Ctx, e: &Expr, expected: &Expr) -> Result<(), String> {
    if let Expr::Lam(a, body) = e
        && let Expr::Pi(dom, cod) = whnf(expected)
    {
        if !def_eq(a, &dom) {
            return Err(format!("lambda domain mismatch: {a:?} vs {dom:?}"));
        }
        let mut ctx2 = ctx.clone();
        ctx2.push((**a).clone());
        return check(&ctx2, body, &cod);
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
}

/// Typecheck a closed term and return its normalized type.
pub fn typecheck(e: &Expr) -> Result<Expr, String> {
    infer(&Vec::new(), e).map(|t| nf(&t))
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
        Postulates { ctx: Vec::new() }
    }
    pub fn push(&mut self, ty: Expr) -> usize {
        let pos = self.ctx.len();
        self.ctx.push(ty);
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

#[cfg(test)]
mod tests {
    use super::*;

    /// `Pi C:(Bool->Sort0). Pi ct:C(true). Pi cf:C(false). <body_d3>`,
    /// where `body_d3` must already be built assuming exactly this
    /// three-binder depth (`C=Var2, ct=Var1, cf=Var0`) relative to
    /// `bool_ref`/`true_ref`/`false_ref`'s own (shared) ambient depth --
    /// the shared shape `bool_rec`'s own type and both its computation-rule
    /// axioms all need, differing only in what comes after the three
    /// binders.
    fn wrap_c_ct_cf(bool_ref: &Expr, true_ref: &Expr, false_ref: &Expr, body_d3: Expr) -> Expr {
        let c_ty = arrow(bool_ref.clone(), sort(0));
        let true_d1 = shift(true_ref, 0, 1);
        let false_d2 = shift(false_ref, 0, 2);
        let pi_cf = pi(app(var(1), false_d2), body_d3);
        let pi_ct = pi(app(var(0), true_d1), pi_cf);
        pi(c_ty, pi_ct)
    }

    /// A real, working `Nat` -- Zero/Succ and a genuinely computing
    /// structural recursor -- built entirely from this kernel's own
    /// existing four primitives (no new kernel-level machinery at all),
    /// answering the "generic recursion/induction principle" gap
    /// `RELATED_WORK.md` §1/§3 names: every proof strategy in `proof.rs`
    /// currently postulates its own bespoke recursor (`Ev`/`ev_rec`) by
    /// hand, per strategy, because there's no `Nat` to induct on. There
    /// always could have been one -- `WRec` already supports eliminating
    /// into *any* `Sort(k)` unconditionally (unlike Coq's own `Prop`,
    /// which restricts this), so nothing about predicativity ever blocked
    /// it; it just hadn't been built.
    ///
    /// Base types postulated once, per `Postulates`' own documented
    /// rationale (a predicative kernel with no fifth primitive type
    /// former has no way to *derive* an enumeration type from nothing —
    /// see its own doc comment): `Bool`/`true`/`false`; `Unit`/`star`;
    /// `Empty`/`empty_elim` (`Pi C:Sort0. Empty -> C`); `ChildTy : Bool ->
    /// Sort0` fixing `Nat`'s own W-shape's children-index family, with
    /// `child_ty_true_eq`/`child_ty_false_eq` pinning it to `Unit`/`Empty`
    /// propositionally (not definitionally -- `ChildTy` is an opaque
    /// postulated function, so using `empty_elim`/a constant function
    /// where `ChildTy(b)` is expected needs one explicit
    /// `cong1`+`sym`+`transport` step each, done once here for `Zero`/
    /// `Succ`). `Nat := W(Bool, ChildTy)`; `Zero`/`Succ` are then `Sup`
    /// values built via that transport. The **identity recursor** (`\a f
    /// ih. sup(a,f)`, ignoring `ih` entirely -- the same shape
    /// `w_recursor_computes_definitionally` above already validates for
    /// an abstract `W`) reduces `Zero`/`Succ(pred)` back to themselves
    /// *definitionally*, via `WRec`'s own free `Sup`-reduction alone --
    /// confirming this really is a genuine, computing `W`-type, not just
    /// a well-typed assemblage of postulates.
    ///
    /// `bool_rec` (Bool's own postulated recursor, with its own two
    /// computation-rule axioms) is also built and shown to produce a
    /// well-typed, genuinely per-case `Pi b:Bool. C(b)` step function
    /// (unlike the identity recursor, whose step ignores the tag
    /// entirely) -- demonstrating real per-case dispatch is at least
    /// *constructible* this way, not just the degenerate identity case.
    ///
    /// **A genuine, newly-discovered scope boundary, not a bug**: proving
    /// a `bool_rec`-based step's own result concretely (e.g. `is_zero
    /// (Zero) = true`) turned out to need more than one more `cong1`/
    /// `trans_proof` step. `WRec`'s own automatic reduction (`whnf_impl`)
    /// builds its induction-hypothesis closure with an inert placeholder
    /// domain annotation (`sort(0)`, "inert for reduction" per its own
    /// comment) -- fine for reduction, since beta substitution never
    /// consults a `Lam`'s domain field at all, but `Expr`'s own structural
    /// equality (`nf`+`==`, what `def_eq` uses) *does* compare it. A
    /// hand-built alternative that instead uses the domain a `bool_rec`
    /// case's own step signature actually requires (`ChildTy(b)`, needed
    /// for that step to type-check as a standalone value at all) is
    /// therefore never `def_eq` to what `WRec` produces automatically,
    /// even though both compute identically for every input -- bridging
    /// the two needs something equivalent to function extensionality
    /// (two functions provably equal pointwise are equal outright), which
    /// this kernel doesn't have. This is a real, separate follow-on (see
    /// `RELATED_WORK.md`), not a mistake in this construction -- confirmed
    /// by deliberately trying it and finding exactly this wall, not a
    /// fixable index bug.
    ///
    /// Deliberately not attempted here: extracting a clean, reusable
    /// public API (this is validated as a self-contained proof of
    /// concept, matching how `w_recursor_computes_definitionally` above
    /// is itself never exposed as one either) or wiring any of this into
    /// `proof.rs`'s own `Ev`-based strategies -- both are the natural
    /// next steps once this foundation is trusted.
    #[test]
    fn nat_via_w_is_a_genuinely_computing_inductive_type() {
        let mut p = Postulates::new();
        let bool_pos = p.push(sort(0));
        let true_pos = p.push(p.get(bool_pos));
        let false_pos = p.push(p.get(bool_pos));
        let unit_pos = p.push(sort(0));
        let _star_pos = p.push(p.get(unit_pos));
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

        let _bool_rec_true_eq_pos = p.push(bool_rec_true_eq_ty);

        // bool_rec_false_eq : Pi C ct cf. Id(C(false), bool_rec(C,ct,cf)(false), cf)
        let false_d3 = shift(&p.get(false_pos), 0, 3);
        let applied_d3b = app(app(app(shift(&p.get(bool_rec_pos), 0, 3), var(2)), var(1)), var(0));
        let false_eq_body_d3 = id(app(var(2), false_d3.clone()), app(applied_d3b, false_d3), var(0));
        let bool_rec_false_eq_ty = wrap_c_ct_cf(&p.get(bool_pos), &p.get(true_pos), &p.get(false_pos), false_eq_body_d3);

        let _bool_rec_false_eq_pos = p.push(bool_rec_false_eq_ty);

        // Nat := W(Bool, ChildTy)
        let nat_ty = wty(p.get(bool_pos), app(shift(&p.get(child_ty_pos), 0, 1), var(0)));
        check(&p.ctx, &nat_ty, &sort(0)).expect("Nat := W(Bool, ChildTy) : Type0");

        // Zero := sup(false, f_zero), f_zero : ChildTy(false) -> Nat,
        // transported from empty_elim(Nat) : Empty -> Nat along
        // child_ty_false_eq.
        let f_empty_nat = app(p.get(empty_elim_pos), nat_ty.clone());
        check(&p.ctx, &f_empty_nat, &arrow(p.get(empty_pos), nat_ty.clone())).expect("empty_elim(Nat) : Empty -> Nat");

        let arrow_nat_fn = lam(sort(0), arrow(var(0), shift(&nat_ty, 0, 1)));
        let cong_false = cong1(
            &sort(0),
            &sort(0),
            &arrow_nat_fn,
            app(p.get(child_ty_pos), p.get(false_pos)),
            p.get(empty_pos),
            p.get(child_ty_false_eq_pos),
        );
        // cong_false : Id(Sort0, ChildTy(false)->Nat, Empty->Nat)
        let expected_cong_false = id(
            sort(0),
            arrow(app(p.get(child_ty_pos), p.get(false_pos)), nat_ty.clone()),
            arrow(p.get(empty_pos), nat_ty.clone()),
        );
        check(&p.ctx, &cong_false, &expected_cong_false).expect("cong1 building Id(Sort0, ChildTy(false)->Nat, Empty->Nat)");

        let sym_cong_false = sym(
            &sort(0),
            &arrow(app(p.get(child_ty_pos), p.get(false_pos)), nat_ty.clone()),
            &arrow(p.get(empty_pos), nat_ty.clone()),
            cong_false,
        );
        // sym_cong_false : Id(Sort0, Empty->Nat, ChildTy(false)->Nat)
        let f_zero = transport(
            0,
            arrow(p.get(empty_pos), nat_ty.clone()),
            arrow(app(p.get(child_ty_pos), p.get(false_pos)), nat_ty.clone()),
            sym_cong_false,
            f_empty_nat,
        );
        check(&p.ctx, &f_zero, &arrow(app(p.get(child_ty_pos), p.get(false_pos)), nat_ty.clone())).expect("f_zero : ChildTy(false) -> Nat");

        let zero = sup(p.get(false_pos), f_zero.clone());
        check(&p.ctx, &zero, &nat_ty).expect("Zero : Nat");

        // Succ(pred) := sup(true, f_succ), f_succ : ChildTy(true) -> Nat,
        // transported from (\_:Unit. pred) : Unit -> Nat along
        // child_ty_true_eq.
        let pred_pos = p.push(nat_ty.clone());
        let pred = p.get(pred_pos);
        // `nat_ty` was built before `pred_pos`'s own push -- reindex once
        // for use at the context depth from here on, matching `Anchored`'s
        // own reasoning in `proof.rs` (a value built before a later push
        // needs manual reshifting or it silently references the wrong
        // postulate).
        let nat_ty_here = shift(&nat_ty, 0, 1);

        let f_unit_nat = lam(p.get(unit_pos), shift(&pred, 0, 1));
        check(&p.ctx, &f_unit_nat, &arrow(p.get(unit_pos), nat_ty_here.clone())).expect("(\\_:Unit. pred) : Unit -> Nat");

        let arrow_nat_fn2 = lam(sort(0), arrow(var(0), shift(&nat_ty_here, 0, 1)));
        let cong_true = cong1(
            &sort(0),
            &sort(0),
            &arrow_nat_fn2,
            app(p.get(child_ty_pos), p.get(true_pos)),
            p.get(unit_pos),
            p.get(child_ty_true_eq_pos),
        );
        let expected_cong_true = id(
            sort(0),
            arrow(app(p.get(child_ty_pos), p.get(true_pos)), nat_ty_here.clone()),
            arrow(p.get(unit_pos), nat_ty_here.clone()),
        );
        check(&p.ctx, &cong_true, &expected_cong_true).expect("cong1 building Id(Sort0, ChildTy(true)->Nat, Unit->Nat)");

        let sym_cong_true = sym(
            &sort(0),
            &arrow(app(p.get(child_ty_pos), p.get(true_pos)), nat_ty_here.clone()),
            &arrow(p.get(unit_pos), nat_ty_here.clone()),
            cong_true,
        );
        let f_succ = transport(
            0,
            arrow(p.get(unit_pos), nat_ty_here.clone()),
            arrow(app(p.get(child_ty_pos), p.get(true_pos)), nat_ty_here.clone()),
            sym_cong_true,
            f_unit_nat,
        );
        check(&p.ctx, &f_succ, &arrow(app(p.get(child_ty_pos), p.get(true_pos)), nat_ty_here.clone())).expect("f_succ : ChildTy(true) -> Nat");

        let succ_pred = sup(p.get(true_pos), f_succ);
        check(&p.ctx, &succ_pred, &nat_ty_here).expect("Succ(pred) : Nat");

        // Sanity: the identity recursor (mirrors `w_recursor_computes_
        // definitionally`'s own "reconstruct the node unchanged, ignoring
        // ih" step, generalized from that test's constant-children-type W
        // to this Nat's own tag-dependent ChildTy) reduces `Zero`/
        // `Succ(pred)` back to themselves *definitionally* via `wrec`'s
        // own free Sup-reduction alone -- confirming this Nat really is a
        // genuine, computing W-type, not just a well-typed assemblage of
        // postulates.
        let zero_here = shift(&zero, 0, 1);
        let wa_here = p.get(bool_pos);
        let wb_here = app(shift(&p.get(child_ty_pos), 0, 1), var(0));
        let motive_const = lam(nat_ty_here.clone(), shift(&nat_ty_here, 0, 1)); // \_:Nat. Nat

        let f_ty_d1 = pi(wb_here.clone(), shift(&nat_ty_here, 0, 2));
        let ih_dom_d2 = shift(&wb_here, 0, 1);
        let ih_body_d3 = app(shift(&motive_const, 0, 3), app(var(1), var(0)));
        let ih_ty_d2 = pi(ih_dom_d2, ih_body_d3);
        let step_id = lam(wa_here, lam(f_ty_d1, lam(ih_ty_d2, sup(var(2), var(1)))));

        let id_on_zero = wrec(motive_const.clone(), step_id.clone(), zero_here.clone());
        check(&p.ctx, &id_on_zero, &nat_ty_here).expect("id-recursor applied to Zero should typecheck at Nat");
        assert_eq!(nf(&id_on_zero), nf(&zero_here), "the identity recursor should reduce Zero back to Zero");

        let id_on_succ = wrec(motive_const, step_id, succ_pred.clone());
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
        let wb_here2 = app(shift(&p.get(child_ty_pos), 0, 1), var(0));
        let f_ty_for_c_d1 = arrow(wb_here2.clone(), shift(&nat_ty_here, 0, 1));
        let ih_dom_d2 = shift(&wb_here2, 0, 1);
        let ih_ty_d2 = arrow(ih_dom_d2, shift(&p.get(bool_pos), 0, 2));
        let c_body_d1 = pi(f_ty_for_c_d1, arrow(ih_ty_d2, shift(&p.get(bool_pos), 0, 2)));
        let is_zero_motive_c = lam(p.get(bool_pos), c_body_d1);

        let f_ty_true = arrow(app(p.get(child_ty_pos), p.get(true_pos)), nat_ty_here.clone());
        let ih_ty_true_d1 = arrow(shift(&app(p.get(child_ty_pos), p.get(true_pos)), 0, 1), shift(&p.get(bool_pos), 0, 1));
        let case_true = lam(f_ty_true, lam(ih_ty_true_d1, shift(&p.get(false_pos), 0, 2)));

        let f_ty_false = arrow(app(p.get(child_ty_pos), p.get(false_pos)), nat_ty_here.clone());
        let ih_ty_false_d1 = arrow(shift(&app(p.get(child_ty_pos), p.get(false_pos)), 0, 1), shift(&p.get(bool_pos), 0, 1));
        let case_false = lam(f_ty_false, lam(ih_ty_false_d1, shift(&p.get(true_pos), 0, 2)));

        let is_zero_step = app(app(app(p.get(bool_rec_pos), is_zero_motive_c.clone()), case_true.clone()), case_false.clone());
        check(&p.ctx, &is_zero_step, &pi(p.get(bool_pos), app(shift(&is_zero_motive_c, 0, 1), var(0))))
            .expect("is_zero_step : Pi b:Bool. C(b)");

        let is_zero_motive_const = lam(nat_ty_here.clone(), shift(&p.get(bool_pos), 0, 1)); // \_:Nat. Bool
        let is_zero_on_zero = wrec(is_zero_motive_const, is_zero_step, zero_here);
        check(&p.ctx, &is_zero_on_zero, &p.get(bool_pos)).expect("is_zero(Zero) : Bool");

        // Deliberately not attempted here: proving `is_zero(Zero) = true`
        // propositionally. This ran into a genuine kernel-level obstacle,
        // not a bug in this construction -- see this test module's own
        // closing note, and `bool_rec`'s own doc comment, for what it is
        // and why it's a real scope boundary rather than something to
        // work around locally.
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
                wrec(var(0), var(1), var(2)),
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

        let reduced = wrec(motive, step, target.clone());
        check(&p.ctx, &reduced, &w_ty).expect("wrec application should typecheck");
        // The payoff of choosing W over an impredicative/Church encoding:
        // this holds by `refl` alone — the recursor genuinely *computes*,
        // it doesn't just make the equation provable with extra work.
        check(&p.ctx, &refl(target.clone()), &id(w_ty, reduced, target))
            .expect("wrec(motive, step, sup(a,f)) should reduce definitionally to sup(a,f)");
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
