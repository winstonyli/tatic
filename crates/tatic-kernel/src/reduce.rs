use super::*;

/// Weak head normal form: reduce only the outermost redex chain.
pub fn whnf(e: &Expr) -> Expr {
    scoped(|| with_spaces(|s| whnf_in(s, e)))
}

/// For an application `e`, its spine's head and its longest proper prefix with no loose variable
/// (`None` for none); `(e, None)` for anything else. Memoised for every application of two or more
/// arguments on the way down, so the levels of a stuck spine, each asking for its own, walk the
/// spine once in all, not once each: that made `nf` and `def_eq` quadratic in a stuck spine's
/// length (`docs/related-work/` §79). One argument is answered directly.
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
/// longer prefix holds only its sub-diagram (docs/tier-cycle/, "Full head normal form").
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
/// spine below it again (`docs/related-work/` §48, §59).
fn whnf_step(s: &Spaces, e: &Expr) -> Option<Expr> {
    s.tick();
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
/// result again, as `nf` and `def_eq` do with a stuck head, keeps its node. A tag `whnf_step` never
/// reduces is answered without the memo. Only `e` is stored, not its result: the first ask of a result
/// with a reducible tag is one `whnf_step` that finds it stuck and stores its own entry (unless a
/// recursive call already did), and later asks hit that.
pub(super) fn whnf_in(s: &Spaces, e: &Expr) -> Expr {
    if !matches!(s.node(e), Node::App(..) | Node::J { .. } | Node::WRec { .. } | Node::SigRec { .. }) {
        return *e;
    }
    if let Some(hit) = hc::whnf_get(s, e) {
        return hit;
    }
    let result = whnf_step(s, e).unwrap_or(*e);
    hc::whnf_put(s, e, &result);
    // The contract is that `result` is in whnf; the kernel's own tests check it, elsewhere the check would cost work.
    #[cfg(test)]
    assert!(s.same(&result, e) || whnf_step(s, &result).is_none(), "whnf_step's result is not in whnf");
    result
}

/// Full normal form: `whnf`, then recurse structurally into subterms, cached per node.
pub(super) fn nf_in(s: &Spaces, e: &Expr) -> Expr {
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
    s.tick();
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
pub(super) fn def_eq_in(s: &Spaces, a: &Expr, b: &Expr) -> bool {
    EQUAL.with(|m| m.borrow_mut().clear());
    conv(s, a, b)
}

thread_local! {
    /// The pairs one `def_eq` call has shown equal, as `key(a) << 32 | key(b)`.
    static EQUAL: std::cell::RefCell<hashbrown::HashSet<u64>> = std::cell::RefCell::new(hashbrown::HashSet::new());
}

/// `def_eq`'s comparison. Syntactically equal sides are equal without
/// reducing, since `nf` is a function; most calls from `infer` are
/// (`docs/related-work/` §56), and with the spaces hash-consed that test is
/// one id comparison. Else `nf(e)` is `whnf(e)`'s outermost constructor
/// over the `nf` of each child, so the normal forms are equal exactly when
/// the two weak head normal forms have the same constructor and pairwise
/// equal children's normal forms. Recursing on that reduces only where the
/// sides differ (`docs/related-work/` §57).
///
/// A pair already shown equal in this call is answered from `EQUAL`. Without
/// it the walk is a tree walk over shared nodes: two equal but distinct
/// subterms under a case tree that shares its tail (a borrow chain applied to
/// continuations) were compared once per path, 2^n times for n bits
/// (docs/tier-cycle/, "The countdown invariant was exponential"). Unequal
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
    s.tick();
    let (nx, ny) = (s.node(x), s.node(y));
    grow(|| nx.same_shape(&ny, |p, q| conv(s, p, q)))
}

pub fn normalize(e: &Expr) -> Expr {
    scoped(|| with_spaces(|s| nf_in(s, e)))
}

