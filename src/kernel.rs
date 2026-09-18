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

use std::fmt;

#[derive(Clone, PartialEq, Eq)]
pub enum Expr {
    /// De Bruijn index; `Var(0)` is the innermost binder.
    Var(u32),
    /// `Type_i`.
    Sort(u32),
    /// `Pi(A, B)`: `B` is checked one binder deeper than `A` (i.e. `B` may
    /// mention the newly-bound variable of type `A` as `Var(0)`).
    Pi(Box<Expr>, Box<Expr>),
    /// `Lam(A, body)`: `A` is the domain annotation; `body` one binder deeper.
    Lam(Box<Expr>, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    /// `Id(A, a, b)`: the type of proofs that `a` and `b` (both `: A`) are equal.
    Id(Box<Expr>, Box<Expr>, Box<Expr>),
    /// `Refl(a) : Id(A, a, a)`, the only primitive way to construct an equality.
    Refl(Box<Expr>),
    /// Eliminator for `Id`. `motive` is `C : Pi x y : A. Id(A,x,y) -> Sort(k)`,
    /// `base` is `c : Pi x : A. C x x (refl x)`, `p : Id(A, a, b)`.
    /// Result type: `C a b p`. Reduces to `base a` when `p` reduces to a `Refl`.
    J {
        motive: Box<Expr>,
        base: Box<Expr>,
        a: Box<Expr>,
        b: Box<Expr>,
        p: Box<Expr>,
    },
    /// `W(A, B)`: `B` one binder deeper than `A`, i.e. `B` is the family
    /// `B(x)` for `x : A` giving the arity/shape of the children at tag `x`.
    W(Box<Expr>, Box<Expr>),
    /// `Sup(a, f) : W(A,B)` where `a : A` and `f : B(a) -> W(A,B)`.
    Sup(Box<Expr>, Box<Expr>),
    /// Eliminator (recursor) for `W`. `motive : W(A,B) -> Sort(k)`,
    /// `step : Pi a:A. Pi f:(B a -> W). (Pi y:B a. motive (f y)) -> motive (sup a f)`.
    /// Reduces on a `Sup` target by recursing into every child.
    WRec {
        motive: Box<Expr>,
        step: Box<Expr>,
        target: Box<Expr>,
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
    Expr::Pi(Box::new(a), Box::new(b))
}
pub fn lam(a: Expr, body: Expr) -> Expr {
    Expr::Lam(Box::new(a), Box::new(body))
}
pub fn app(f: Expr, a: Expr) -> Expr {
    Expr::App(Box::new(f), Box::new(a))
}
pub fn app2(f: Expr, a: Expr, b: Expr) -> Expr {
    app(app(f, a), b)
}
pub fn app3(f: Expr, a: Expr, b: Expr, c: Expr) -> Expr {
    app(app2(f, a, b), c)
}
pub fn id(a: Expr, x: Expr, y: Expr) -> Expr {
    Expr::Id(Box::new(a), Box::new(x), Box::new(y))
}
pub fn refl(a: Expr) -> Expr {
    Expr::Refl(Box::new(a))
}
pub fn jelim(motive: Expr, base: Expr, a: Expr, b: Expr, p: Expr) -> Expr {
    Expr::J {
        motive: Box::new(motive),
        base: Box::new(base),
        a: Box::new(a),
        b: Box::new(b),
        p: Box::new(p),
    }
}
pub fn wty(a: Expr, b: Expr) -> Expr {
    Expr::W(Box::new(a), Box::new(b))
}
pub fn sup(a: Expr, f: Expr) -> Expr {
    Expr::Sup(Box::new(a), Box::new(f))
}
pub fn wrec(motive: Expr, step: Expr, target: Expr) -> Expr {
    Expr::WRec {
        motive: Box::new(motive),
        step: Box::new(step),
        target: Box::new(target),
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
    match e {
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
            step,
            target,
        } => wrec(
            shift(motive, cutoff, amount),
            shift(step, cutoff, amount),
            shift(target, cutoff, amount),
        ),
    }
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

/// Weak head normal form: reduce only the outermost redex chain.
fn whnf(e: &Expr) -> Expr {
    match e {
        Expr::App(f, a) => match whnf(f) {
            Expr::Lam(_, body) => whnf(&subst_top(&body, a)),
            other => app(other, (**a).clone()),
        },
        Expr::J {
            motive,
            base,
            a,
            b,
            p,
        } => match whnf(p) {
            Expr::Refl(_) => whnf(&app(*base.clone(), *a.clone())),
            other => Expr::J {
                motive: motive.clone(),
                base: base.clone(),
                a: a.clone(),
                b: b.clone(),
                p: Box::new(other),
            },
        },
        Expr::WRec {
            motive,
            step,
            target,
        } => match whnf(target) {
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
                whnf(&app3(
                    (**step).clone(),
                    *a.clone(),
                    (*f).clone(),
                    rec_step,
                ))
            }
            other => Expr::WRec {
                motive: motive.clone(),
                step: step.clone(),
                target: Box::new(other),
            },
        },
        other => other.clone(),
    }
}

/// Full normal form: `whnf`, then recurse structurally into subterms.
fn nf(e: &Expr) -> Expr {
    match whnf(e) {
        Expr::Var(k) => Expr::Var(k),
        Expr::Sort(i) => Expr::Sort(i),
        Expr::Pi(a, b) => pi(nf(&a), nf(&b)),
        Expr::Lam(a, b) => lam(nf(&a), nf(&b)),
        Expr::App(f, a) => app(nf(&f), nf(&a)),
        Expr::Id(a, x, y) => id(nf(&a), nf(&x), nf(&y)),
        Expr::Refl(a) => refl(nf(&a)),
        Expr::J {
            motive,
            base,
            a,
            b,
            p,
        } => jelim(nf(&motive), nf(&base), nf(&a), nf(&b), nf(&p)),
        Expr::W(a, b) => wty(nf(&a), nf(&b)),
        Expr::Sup(a, f) => sup(nf(&a), nf(&f)),
        Expr::WRec {
            motive,
            step,
            target,
        } => wrec(nf(&motive), nf(&step), nf(&target)),
    }
}

pub fn def_eq(a: &Expr, b: &Expr) -> bool {
    nf(a) == nf(b)
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
        Expr::Pi(a, b) => Ok((*a, *b)),
        other => Err(format!("expected a Pi type, got {other:?}")),
    }
}

fn expect_w(e: &Expr) -> Result<(Expr, Expr), String> {
    match whnf(e) {
        Expr::W(a, b) => Ok((*a, *b)),
        other => Err(format!("expected a W type, got {other:?}")),
    }
}

pub fn infer(ctx: &Ctx, e: &Expr) -> Result<Expr, String> {
    match e {
        Expr::Var(k) => ctx_lookup(ctx, *k).ok_or_else(|| format!("unbound variable #{k}")),
        Expr::Sort(i) => Ok(Expr::Sort(i + 1)),
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

/// `cong1 f a b p : Id(A, f a, f b)`, given `p : Id(A, a, b)`. Congruence
/// for a unary function -- applying the same function to equal arguments
/// gives equal results, regardless of what `f` itself computes.
pub fn cong1(a_ty: &Expr, f: &Expr, a: Expr, b: Expr, p: Expr) -> Expr {
    // motive(a', b', _) := Id(A, f a', f b')
    let motive = lam(
        a_ty.clone(),
        lam(
            shift(a_ty, 0, 1),
            lam(
                id(shift(a_ty, 0, 2), var(1), var(0)),
                id(
                    shift(a_ty, 0, 3),
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
        let step = cong1(a_ty, &g, cur_args[i].clone(), ys[i].clone(), ps[i].clone());
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

    #[test]
    fn universes_stratify() {
        assert_eq!(typecheck(&sort(0)).unwrap(), sort(1));
        assert_eq!(typecheck(&sort(5)).unwrap(), sort(6));
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

        let c1 = cong1(&a_ty, &f, a.clone(), b.clone(), p1);
        check(&p.ctx, &c1, &id(a_ty.clone(), app(f.clone(), a.clone()), app(f.clone(), b.clone())))
            .expect("cong1(f,a,b,p1) : Id(A, f a, f b)");

        let c2 = cong1(&a_ty, &f, b.clone(), c.clone(), p2);
        check(&p.ctx, &c2, &id(a_ty.clone(), app(f.clone(), b.clone()), app(f.clone(), c.clone())))
            .expect("cong1(f,b,c,p2) : Id(A, f b, f c)");

        let chained = trans_proof(&a_ty, &app(f.clone(), a.clone()), &app(f.clone(), b.clone()), &app(f.clone(), c.clone()), c1, c2);
        check(&p.ctx, &chained, &id(a_ty, app(f.clone(), a), app(f, c)))
            .expect("trans(cong1(..p1), cong1(..p2)) : Id(A, f a, f c)");
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
