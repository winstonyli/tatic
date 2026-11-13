use super::*;

// --- shifting & substitution (standard de Bruijn machinery) -------------

/// Add `amount` to every free variable at or above `cutoff`. Exposed
/// (beyond this module's own substitution machinery) for moving a term
/// under a new binder, e.g. the `cong` motives in `proof.rs`.
pub fn shift(e: &Expr, cutoff: u32, amount: i32) -> Expr {
    with_spaces(|s| shift_in(s, e, cutoff, amount))
}

/// [`shift`] inside the kernel.
pub(super) fn shift_in(s: &Spaces, e: &Expr, cutoff: u32, amount: i32) -> Expr {
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
    s.tick();
    grow(|| match s.node(e) {
        Node::Var(k) if k >= cutoff => var((k as i32 + amount) as u32),
        Node::Var(_) | Node::Sort(_) | Node::Const(_) | Node::Free(_) => *e,
        n => s.mk(n.map_kids(|x, under| shift_child(s, &x, cutoff + under as u32, amount))),
    })
}

/// `shift` of one child: the child itself when it has nothing to shift, else memoised, shared or not (see [`hc`]).
fn shift_child(s: &Spaces, x: &Expr, cutoff: u32, amount: i32) -> Expr {
    if s.loose(x) <= cutoff {
        return *x;
    }
    if let Some(r) = hc::shift_get(s, x, cutoff, amount) {
        return r;
    }
    let r = shift_unchecked(s, x, cutoff, amount);
    hc::shift_put(s, x, cutoff, amount, &r);
    r
}


/// Beta-substitution: replace `Var(0)` in `body` (which lives one binder
/// deeper) with `a`, then discharge that binder. `a` is walked only where
/// `body` uses it, so not at all when `body` doesn't mention `Var(0)`:
/// `infer`'s `App` rule substitutes every argument into its function's
/// codomain, usually `Int`, and shifting the argument there cost a walk of
/// it per application (`docs/related-work/` §50, §58).
pub(super) fn subst_top(s: &Spaces, body: &Expr, a: &Expr) -> Expr {
    instantiate(s, body, a, 0)
}

/// `subst_top`'s substitution in one pass: under `d` binders of `e`,
/// `Var(d)` becomes `a` shifted past them, and `e`'s own free variables
/// above it drop by one for the discharged binder. Equal to substituting
/// `shift(a, 0, 1)` and then shifting the result by -1, but `a` is shifted
/// only where it's used, not at every binder crossed and again in the
/// result (`docs/related-work/` §52).
///
/// A subterm with no loose variable at or above its depth is kept as it is.
pub(super) fn instantiate(s: &Spaces, e: &Expr, a: &Expr, d: u32) -> Expr {
    instantiate_n(s, e, &[a], d)
}

/// `instantiate` for `args.len()` binders at once: `e` lives under that many binders, `args` are in
/// application order (so the last one is `Var(0)`), and the result is `e` with all of them
/// discharged. Equal to calling `subst_top` once per argument, outermost first, without building the
/// intermediate terms: each argument is shifted past the `d` binders it ends up under, and `e`'s own
/// free variables above the discharged ones drop by `args.len()`.
pub(super) fn instantiate_n(s: &Spaces, e: &Expr, args: &[&Expr], d: u32) -> Expr {
    if s.loose(e) <= d {
        return *e;
    }
    let id = hc::inst_args_id(s, args);
    if let Some(r) = hc::inst_get(s, e, d, id) {
        return r;
    }
    let r = inst_rec(s, e, args, d, id);
    hc::inst_put(s, e, d, id, &r);
    r
}

/// `instantiate_n`'s recursion; `id` is the argument list's (`hc::inst_args_id`). The memo lives for the region, so a
/// later call with the same list finds this one's entries.
fn inst_rec(s: &Spaces, e: &Expr, args: &[&Expr], d: u32, id: u32) -> Expr {
    s.tick();
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
        if memo && let Some(r) = hc::inst_get(s, &x, d, id) {
            return r;
        }
        let r = inst_rec(s, &x, args, d, id);
        if memo {
            hc::inst_put(s, &x, d, id, &r);
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
pub(super) fn is_var_free(s: &Spaces, e: &Expr, idx: u32) -> bool {
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

