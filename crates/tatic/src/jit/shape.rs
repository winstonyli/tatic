//! Term-shape analysis shared by the IR builder (`compile.rs`), the IR
//! (`ir.rs`) and the prover (`proof/*`): peeling a term into
//! `(arity, body, is_rec)`, `classify` (one level of a body's shape),
//! self-call matching, `free_vars` (what a lambda captures) and closure-arity
//! inference. None of it emits IR or WAT, so the prover depends on this file,
//! not on the code generator.

use hashbrown::HashMap;

use crate::jit::lower_wat::cmp_instr;
use crate::lang::term::{Hash, PrimOp, Term, TermStore};

/// Peel a term into `(arity, body, is_recursive)`:
/// - `Rec(Abs(Abs(...body)))` -> `(k, body, true)`, self bound at `Var(k)`,
///   `k > 0` (a 0-ary self-recursive definition would have no base case
///   reachable via any argument -- out of scope, not just unlikely).
/// - `Abs(Abs(...body))` (no `Rec`) -> `(k, body, false)`, `k` possibly
///   `0` (a closed expression with no top-level `Abs` at all, e.g. a
///   fully-saturated application of a couple of combinators -- evaluated
///   once, not called with arguments).
pub(crate) fn peel(store: &TermStore, h: Hash) -> Option<(usize, Hash, bool)> {
    match store.resolve(h) {
        Term::Rec(inner) => {
            let (k, body) = peel_abs(store, *inner);
            (k > 0).then_some((k, body, true))
        }
        _ => {
            let (k, body) = peel_abs(store, h);
            Some((k, body, false))
        }
    }
}

fn peel_abs(store: &TermStore, mut h: Hash) -> (usize, Hash) {
    let mut k = 0usize;
    loop {
        match store.resolve(h) {
            Term::Abs(body) => {
                k += 1;
                h = *body;
            }
            _ => return (k, h),
        }
    }
}

pub(crate) fn local_index(var: u32, arity: usize) -> Option<u32> {
    // `then_some` takes its argument by value, not lazily -- `a - 1 - var`
    // would underflow-panic for an out-of-range `var` before `then_some`
    // ever got to check the condition, so this needs an actual branch.
    let a = arity as u32;
    if var < a { Some(a - 1 - var) } else { None }
}

/// If `h` is a fully-saturated self-application (`self a1 a2 .. a_arity`),
/// return the argument hashes in application order.
pub(crate) fn match_self_call(
    store: &TermStore,
    h: Hash,
    arity: usize,
    self_idx: Option<u32>,
) -> Option<Vec<Hash>> {
    let self_idx = self_idx?;
    let mut args_rev = Vec::with_capacity(arity);
    let mut cur = h;
    for _ in 0..arity {
        match store.resolve(cur) {
            Term::App(f, a) => {
                args_rev.push(*a);
                cur = *f;
            }
            _ => return None,
        }
    }
    match store.resolve(cur) {
        Term::Var(i) if *i == self_idx => {
            args_rev.reverse();
            Some(args_rev)
        }
        _ => None,
    }
}

/// Unwinds a chain of `App` nodes into `(root, args)` -- `root` is the
/// first non-`App` node reached, `args` its arguments in application
/// order. `root == h` with `args` empty if `h` isn't an `App` at all.
pub(crate) fn unwind_app_spine(store: &TermStore, mut h: Hash) -> (Hash, Vec<Hash>) {
    let mut args = Vec::new();
    while let Term::App(f, a) = store.resolve(h) {
        args.push(*a);
        h = *f;
    }
    args.reverse();
    (h, args)
}

/// What shape one node of a function body is -- the case analysis
/// `build_node` and every walker in `proof.rs` that models it share, so
/// that the compiler and the proofs cannot disagree about which case a
/// term falls into (`docs/related-work/` 33). Each consumer still decides
/// for itself which shapes it supports and what they mean; only the
/// classification is common.
///
/// The one precedence rule: a saturated self-call is recognized before
/// any other application. Every other variant is a distinct `Term`
/// constructor.
pub(crate) enum Shape {
    If(Hash, Hash, Hash),
    /// `self a1 .. a_arity`, per [`match_self_call`]; arguments in
    /// application order.
    SelfCall(Vec<Hash>),
    /// An application headed by a variable (`root`, the `Var` node
    /// itself) -- a parameter or a captured free variable, whichever it
    /// resolves to.
    VarCall { root: Hash, var: u32, args: Vec<Hash> },
    /// An application headed by a literal lambda or `Rec` combinator that
    /// peels to `arity > 0`. `args.len()` against `arity` says whether it
    /// is exact, over- or partial application.
    CombinatorCall { root: Hash, arity: usize, args: Vec<Hash> },
    /// An application headed by anything else (a literal, a primitive, an
    /// `If`, a combinator that doesn't peel to a function): outside every
    /// fragment.
    OtherCall,
    Var(u32),
    Lit(i64),
    Prim(PrimOp, Hash, Hash),
    /// A literal lambda or `Rec` combinator used as a value. Consumers
    /// peel it themselves: they differ on whether they accept a `Rec`.
    Combinator { is_rec: bool },
}

/// Classifies `h` within a function of `arity` parameters whose own
/// self-reference, if it is recursive, is `Var(self_idx)`. See [`Shape`].
pub(crate) fn classify(store: &TermStore, h: Hash, arity: usize, self_idx: Option<u32>) -> Shape {
    if let Some(args) = match_self_call(store, h, arity, self_idx) {
        return Shape::SelfCall(args);
    }
    match store.resolve(h) {
        Term::If(c, t, e) => Shape::If(*c, *t, *e),
        Term::App(..) => {
            let (root, args) = unwind_app_spine(store, h);
            match store.resolve(root) {
                Term::Var(i) => Shape::VarCall { root, var: *i, args },
                Term::Abs(_) | Term::Rec(_) => match peel(store, root) {
                    Some((arity, _, _)) if arity > 0 => Shape::CombinatorCall { root, arity, args },
                    _ => Shape::OtherCall,
                },
                _ => Shape::OtherCall,
            }
        }
        Term::Var(i) => Shape::Var(*i),
        Term::Lit(n) => Shape::Lit(*n),
        Term::Prim(op, a, b) => Shape::Prim(*op, *a, *b),
        Term::Abs(_) => Shape::Combinator { is_rec: false },
        Term::Rec(_) => Shape::Combinator { is_rec: true },
    }
}

/// Whether `op` is one `build_node`'s `If` arm accepts as a condition --
/// and so one that only ever evaluates to `0` or `1`, which `proof.rs`'s
/// `classify_tree` relies on for soundness. Defined by `cmp_instr` itself
/// so the two cannot drift.
pub(crate) fn is_comparison(op: PrimOp) -> bool {
    cmp_instr(op).is_some()
}

/// Finds what a lambda literal (peeled to `own_arity`/`body`/`is_rec`,
/// same shape `peel` returns) captures from its enclosing scope: every
/// `Var` in `body` that isn't bound within `body` itself, expressed as
/// how far *beyond* `own_arity` it reaches (`0` = the nearest enclosing
/// binding, `1` = the next one out, ...), deduped and sorted ascending --
/// this becomes the closure's environment slot layout (slot `j` holds
/// whatever denoted relative depth `result[j]` at the point the closure
/// was created). Follows into a lambda nested inside `body` and used
/// there as a plain value too (not just `body`'s own top level), since a
/// closure nested inside another one still captures from the very same
/// enclosing scope this one does.
///
/// A self-recursive value's own self-reference (`Var(own_arity)`, exactly
/// where `Rec`'s binder sits, whenever `is_rec`) is deliberately excluded
/// here, at every depth it's found, not just `body`'s own top level --
/// it's resolved separately by `match_self_call`/an ordinary recursive
/// `call`, and (like before this function existed at all) still can't be
/// read as a plain value; without this exclusion *every* self-recursive
/// function would show up as having an uncapturable "capture" the moment
/// it made its own recursive call.
pub(crate) fn free_vars(store: &TermStore, body: Hash, own_arity: usize, is_rec: bool) -> Vec<u32> {
    let mut found = std::collections::BTreeSet::new();
    collect_free_vars(store, body, own_arity as u32, is_rec, 0, &mut found);
    found.into_iter().collect()
}

fn collect_free_vars(
    store: &TermStore,
    h: Hash,
    own_arity: u32,
    is_rec: bool,
    depth: u32,
    found: &mut std::collections::BTreeSet<u32>,
) {
    match store.resolve(h) {
        Term::Var(i) => {
            let i = *i;
            if i < depth {
                return; // bound by a binder nested inside `body` itself
            }
            let rel = i - depth;
            if rel < own_arity {
                return; // bound by this lambda's own parameters
            }
            if is_rec && rel == own_arity {
                return; // the self-reference `Rec` binds, not a capture
            }
            let capture_base = if is_rec { own_arity + 1 } else { own_arity };
            found.insert(rel - capture_base);
        }
        Term::Lit(_) => {}
        Term::Abs(inner) => collect_free_vars(store, *inner, own_arity, is_rec, depth + 1, found),
        Term::Rec(inner) => collect_free_vars(store, *inner, own_arity, is_rec, depth + 1, found),
        Term::App(f, a) => {
            let (f, a) = (*f, *a);
            collect_free_vars(store, f, own_arity, is_rec, depth, found);
            collect_free_vars(store, a, own_arity, is_rec, depth, found);
        }
        Term::Prim(_, a, b) => {
            let (a, b) = (*a, *b);
            collect_free_vars(store, a, own_arity, is_rec, depth, found);
            collect_free_vars(store, b, own_arity, is_rec, depth, found);
        }
        Term::If(c, t, e) => {
            let (c, t, e) = (*c, *t, *e);
            collect_free_vars(store, c, own_arity, is_rec, depth, found);
            collect_free_vars(store, t, own_arity, is_rec, depth, found);
            collect_free_vars(store, e, own_arity, is_rec, depth, found);
        }
    }
}

/// The result of scanning every use of one absolute `Var` index as an
/// application's callee, anywhere within one function body:
/// `Consistent(k)` if every such use applied it to exactly `k` arguments;
/// `Inconsistent` if at least two uses disagreed (e.g. `f(x)` *and*
/// `f(x,y)`). A `Var` never used as a callee at all (just read as a
/// value) simply has no entry in the map `scan_for_closure_calls`
/// produces.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ArityUse {
    Consistent(usize),
    Inconsistent,
}

/// For every absolute `Var` index in `h` (a parameter of the function
/// being compiled, *or* a captured free variable -- this doesn't
/// distinguish the two, since a closure-typed value read resolves the
/// same way either way, see `build_read`), classifies whether it's
/// ever used as an application's callee and, if so, whether every such
/// use agrees on the argument count (see `ArityUse`). This function
/// itself never rejects a whole scan just because one `Var` is used
/// inconsistently -- scanning continues, and every other `Var`'s own
/// classification is still reported -- so callers that don't yet handle
/// `ArityUse::Inconsistent` (everything as of this writing) must check
/// for it themselves and decline accordingly, exactly as they declined
/// on this function returning `None` before this classification existed.
/// `None` is still returned for a genuinely out-of-fragment callee shape
/// (neither a variable nor a literal lambda/combinator).
pub(crate) fn infer_closure_arities(store: &TermStore, h: Hash, arity: usize, self_idx: Option<u32>) -> Option<HashMap<u32, ArityUse>> {
    let mut found = HashMap::new();
    scan_for_closure_calls(store, h, arity, self_idx, &mut found)?;
    Some(found)
}

fn scan_for_closure_calls(
    store: &TermStore,
    h: Hash,
    arity: usize,
    self_idx: Option<u32>,
    found: &mut HashMap<u32, ArityUse>,
) -> Option<()> {
    let args = match classify(store, h, arity, self_idx) {
        Shape::If(c, t, e) => vec![c, t, e],
        Shape::SelfCall(args) => args,
        // A parameter *or* a captured free variable used as a callee --
        // both resolve to a packed closure value the same way
        // (`build_read`), so both get tracked here uniformly;
        // whether `i` actually resolves to anything at all is checked
        // later, by `build_read`.
        Shape::VarCall { var: i, args, .. } => {
            match found.get(&i) {
                None => {
                    found.insert(i, ArityUse::Consistent(args.len()));
                }
                Some(ArityUse::Consistent(k)) if *k == args.len() => {}
                Some(ArityUse::Consistent(_)) => {
                    found.insert(i, ArityUse::Inconsistent);
                }
                Some(ArityUse::Inconsistent) => {} // already marked; nothing new to record
            }
            args
        }
        // A literal redex callee (possibly self-recursive) -- fine,
        // checked again at build.
        Shape::CombinatorCall { args, .. } => args,
        Shape::OtherCall => return None,
        Shape::Prim(_, a, b) => vec![a, b],
        // A lambda -- or a named self-recursive value, e.g. one bound by
        // `let fact = rec f n = .. in ..` and later called through that
        // binding -- used as a plain value (an argument, a branch
        // result, ...).
        Shape::Var(_) | Shape::Lit(_) | Shape::Combinator { .. } => vec![],
    };
    for a in args {
        scan_for_closure_calls(store, a, arity, self_idx, found)?;
    }
    Some(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `classify` is the one place both `build_node` and every
    /// `proof.rs` walker learn which case a node is, so its two
    /// non-obvious rules are pinned here: a saturated self-call wins over
    /// a plain variable call (and only when saturated), and a `Rec` that
    /// doesn't peel to a function is no callee at all.
    #[test]
    fn classify_recognizes_only_a_saturated_self_call_and_only_a_peelable_callee() {
        let mut s = TermStore::new();
        // Hand-built: classify takes an open body (f, a, b free); the parser accepts only closed terms.
        // Inside `rec f a b = ..`: `a` is Var(1), `b` Var(0), `f` Var(2).
        let (a, b, f) = (s.var(1), s.var(0), s.var(2));
        let saturated = s.app2(f, a, b);
        let partial = s.app(f, a);
        let over = s.app(saturated, b);
        let (arity, self_idx) = (2, Some(2));

        assert!(matches!(classify(&s, saturated, arity, self_idx), Shape::SelfCall(ref args) if *args == vec![a, b]));
        assert!(matches!(classify(&s, partial, arity, self_idx), Shape::VarCall { var: 2, ref args, .. } if args.len() == 1));
        assert!(matches!(classify(&s, over, arity, self_idx), Shape::VarCall { var: 2, ref args, .. } if args.len() == 3));
        // Outside a recursive function the same term is just a variable call.
        assert!(matches!(classify(&s, saturated, arity, None), Shape::VarCall { var: 2, .. }));

        let five = s.lit(5);
        let not_a_function = s.rec(five);
        let bad_call = s.app(not_a_function, a);
        assert!(matches!(classify(&s, bad_call, arity, None), Shape::OtherCall));
        let id_body = s.var(0);
        let id = s.abs(id_body);
        let good_call = s.app(id, a);
        assert!(matches!(classify(&s, good_call, arity, None), Shape::CombinatorCall { arity: 1, .. }));
    }
}
