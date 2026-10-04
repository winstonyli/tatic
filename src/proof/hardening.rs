use super::*;

// --- hardening against composition bugs -----------------------------------
//
// A function composing an `Expr` from more than one recursive sub-call can
// still make a composition mistake, even though a pushed `Const` shifts
// nothing (`RELATED_WORK.md` §68, §69).
//
// This helper turns any such mistake into an immediate, precisely located
// panic instead: called once at the *return point* of any function that
// composes sub-`Expr`s from more than one recursive call (`denote_closure`,
// `eval_and_prove`, `build_ev_witness`), it confirms the value this call is
// about to hand back has the *exact* type expected -- known statically at
// each call site (`Int`, `Clo`, or, for `build_ev_witness`, `Ev(params, v)`
// itself, now that `ev_pos` is available to build it) -- before it can be
// embedded, unchecked, into a caller's own larger expression. Checking once
// per call,
// at return, is enough to localize a bug to the exact (innermost) call that
// introduced it: by induction, a bug in any deeper call would already have
// panicked there first, before this call ever got to compose its own
// result from it. Debug-only (`kernel::check`/`infer` cost real time, see
// the Benchmarks section) -- a no-op, zero-cost in release builds, exactly
// like the sample-verification/kernel-proof split this whole project
// already relies on: this is an *additional* internal consistency check on
// top of (not instead of) the real trust gate, which is still `kernel::check`
// at each function's own already-existing, unconditional call site.
#[cfg(debug_assertions)]
pub(super) fn debug_assert_has_type(p: &Postulates, e: &Expr, expected: &Expr, label: &str) {
    if let Err(err) = p.check_open(e, expected) {
        panic!(
            "composition bug in {label}: the value doesn't have its expected type.\n  \
             error: {err}\n  value: {e:?}\n  expected type: {expected:?}"
        );
    }
}
#[cfg(not(debug_assertions))]
pub(super) fn debug_assert_has_type(_p: &Postulates, _e: &Expr, _expected: &Expr, _label: &str) {}

/// `combine`'s value at `params`/`ihs` (both hoisted to a free function --
/// not just a closure local to `prove_tail_recursive_universal` -- so
/// `build_ev_witness` can reuse it too).
pub(super) fn combine_of(combine: &Expr, params: &[Expr], ihs: &[Expr]) -> Expr {
    apply_n(combine.clone(), params.iter().cloned().chain(ihs.iter().cloned()))
}

/// The shape `prove_tail_recursive_universal`'s `body` must be: an
/// arbitrary tree of nested `If`s (matching what `build_node` already
/// accepts), each leaf an arithmetic expression (`Var`/`Lit`/`Prim`/`If`)
/// that may itself contain any number of self-call occurrences (zero, for
/// a base case; one in tail position, for the old tail-recursion special
/// case; one or more anywhere else, e.g. `f(n-1) + f(n-2)`, including
/// inside a further, purely-arithmetic nested `If`, e.g.
/// `n + (if c then f(n-1) else f(n-2))`) -- `classify_tree` only extracts
/// an `If` that's the *whole* body of some branch into the tree itself;
/// one embedded as a sub-expression of a leaf just stays part of that
/// leaf's own expression, handled by `find_self_calls`/
/// `denote_with_placeholders` the same way a `Prim` is.
#[derive(Clone)]
pub(super) enum DecisionTree {
    If { cond: Hash, then_branch: Box<DecisionTree>, else_branch: Box<DecisionTree> },
    Leaf(Hash),
}

/// Classifies `h` into a [`DecisionTree`]. Every `If`'s condition must be
/// a direct comparison (same restriction `build_node`'s `If` arm in `compile.rs`
/// already imposes, and what lets `cond_premise` below use plain `Id`
/// equality -- a comparison only ever denotes to `0` or `1`).
pub(super) fn classify_tree(store: &TermStore, h: Hash) -> Option<DecisionTree> {
    if let Term::If(c, t, e) = store.resolve(h) {
        let (c, t, e) = (*c, *t, *e);
        if !matches!(store.resolve(c), Term::Prim(op, _, _) if compile::is_comparison(*op)) {
            return None;
        }
        let then_branch = Box::new(classify_tree(store, t)?);
        let else_branch = Box::new(classify_tree(store, e)?);
        return Some(DecisionTree::If { cond: c, then_branch, else_branch });
    }
    Some(DecisionTree::Leaf(h))
}

/// One leaf of a [`DecisionTree`]: the path of `(cond, literal)` premises
/// from the root that must all hold for this leaf to be the one reached
/// (`1` for a `then`-branch taken, `0` for an `else`-branch), plus every
/// self-call occurrence within it (each entry its own argument list),
/// found and ordered left-to-right/depth-first the same way
/// `denote_with_placeholders` walks the same expression -- the two must
/// agree, since a leaf's `i`-th `Ev`/induction-hypothesis premise and its
/// `i`-th occurrence in the rebuilt expression have to be the same call.
#[derive(Clone)]
pub(super) struct Leaf {
    pub(super) path: Vec<(Hash, i64)>,
    pub(super) expr: Hash,
    pub(super) calls: Vec<Vec<Hash>>,
}

/// `arity`/`self_idx` bundled together -- the pair `find_self_calls` and
/// `denote_with_placeholders` both need on every recursive call, purely to
/// forward to `compile::match_self_call` at each node.
#[derive(Clone, Copy)]
pub(super) struct SelfCall {
    pub(super) arity: usize,
    pub(super) idx: u32,
}

/// Flattens a [`DecisionTree`] into its leaves (with their paths), then
/// locates each leaf's self-call occurrences via `find_self_calls`.
/// Returns `None` if any leaf falls outside the fragment `denote`/
/// `find_self_calls` cover (a `Clo`-typed nested-`If` value, a
/// non-tail-recursion `Abs`, a free `App`, ...).
pub(super) fn flatten_tree(store: &TermStore, tree: &DecisionTree, self_call: SelfCall, param_types: &[Option<usize>]) -> Option<Vec<Leaf>> {
    fn go(tree: &DecisionTree, path: &mut Vec<(Hash, i64)>, out: &mut Vec<(Vec<(Hash, i64)>, Hash)>) {
        match tree {
            DecisionTree::If { cond, then_branch, else_branch } => {
                path.push((*cond, 1));
                go(then_branch, path, out);
                path.pop();
                path.push((*cond, 0));
                go(else_branch, path, out);
                path.pop();
            }
            DecisionTree::Leaf(h) => out.push((path.clone(), *h)),
        }
    }
    let mut raw = Vec::new();
    let mut path = Vec::new();
    go(tree, &mut path, &mut raw);

    raw.into_iter()
        .map(|(path, expr)| {
            let mut calls = Vec::new();
            find_self_calls(store, expr, self_call, param_types, &mut calls)
                .then_some(())
                .map(|()| Leaf { path, expr, calls })
        })
        .collect()
}

/// Walks a leaf's `Var`/`Lit`/`Prim`/`If`/closure-call structure (anything
/// else outside the fragment fails), appending each self-call occurrence's
/// argument list to `out` in the same left-to-right, depth-first order
/// `denote_with_placeholders` will later substitute them in. A fully-
/// saturated call through a `Clo`-typed parameter (`Var(i)` with
/// `param_types[i] = Some(k)`, `k` arguments -- `param_types[i] = None`
/// throughout for a term with no closures at all, the same
/// closures-blind behavior as before) is recursed into (its own arguments
/// may still contain further self-call occurrences), not rejected outright.
/// A nested `If`'s condition/branches are recursed into the same way (a
/// self-call may occur in any of them), whether it stays purely
/// arithmetic or chooses between two `Clo`-typed values (e.g. a self-call
/// argument `f(n-1, if c then g else h)`) -- which of those it is doesn't
/// matter here (only to `denote_with_placeholders`'s own type-directed
/// dispatch), since finding a self-call occurrence never depends on the
/// type of the expression it's found in.
pub(super) fn find_self_calls(store: &TermStore, h: Hash, self_call: SelfCall, param_types: &[Option<usize>], out: &mut Vec<Vec<Hash>>) -> bool {
    let all = |hs: &[Hash], out: &mut Vec<Vec<Hash>>| hs.iter().all(|&a| find_self_calls(store, a, self_call, param_types, out));
    match compile::classify(store, h, self_call.arity, Some(self_call.idx)) {
        Shape::SelfCall(args) => {
            out.push(args);
            true
        }
        Shape::VarCall { var, args, .. } => param_types.get(var as usize).copied().flatten() == Some(args.len()) && all(&args, out),
        // A closure created and (fully or partially) called right here --
        // see `denote_with_placeholders`'s own docs. Recurses into the
        // arguments only, never into the combinator's own body: a genuine
        // self-call occurring *inside* a nested closure's body would need
        // `self_call.idx` shifted by that closure's own arity to still
        // refer to the same absolute position, which
        // `compile::match_self_call`'s unadjusted check can't see -- the
        // combinator's body is opaque here for the same reason it already
        // is to `collect_literals`.
        Shape::CombinatorCall { args, .. } => all(&args, out),
        Shape::OtherCall => false,
        Shape::Var(_) | Shape::Lit(_) => true,
        Shape::Prim(_, a, b) => all(&[a, b], out),
        // A closure used as a bare value (not applied here) -- opaque,
        // nothing inside it to search for a self-call occurrence, the
        // same reasoning as the combinator-call case just above.
        Shape::Combinator { is_rec } => !is_rec,
        // A nested `If` (only Int-typed condition/branches -- see
        // `denote_with_placeholders`'s matching arm): recurse into all
        // three the same way `Prim` does, so a self-call inside either
        // branch is still found, in the same left-to-right, depth-first
        // order `denote_with_placeholders` will later walk.
        Shape::If(c, t, e) => all(&[c, t, e], out),
    }
}

/// Like [`denote_closure_typed`] below, but for a leaf already classified
/// by `find_self_calls`: each self-call occurrence is replaced by the next
/// entry of `placeholders` (consumed left-to-right, matching
/// `find_self_calls`'s order, always `Int`-typed -- a self-call's own
/// result is always `Int`) instead of failing. Used both to build a leaf's
/// `combine` function's body (`placeholders` = the `Ev`-bound values) and
/// nowhere else -- everywhere `combine` is *used* at a different
/// instantiation, it's applied as a value via `combine_of`, not re-walked.
/// A nested `If` is handled the same way `denote_closure_typed` handles
/// one, purely arithmetic or choosing between two `Clo`-typed values
/// alike. `params` are the scope's bound parameters, as for
/// `denote_closure_typed`.
#[allow(clippy::too_many_arguments)]
pub(super) fn denote_with_placeholders(
    store: &TermStore,
    h: Hash,
    self_call: SelfCall,
    param_types: &[Option<usize>],
    combinators: &mut ClosureCombinators<'_>,
    params: &[Expr],
    placeholders: &[Expr],
    next: &mut usize,
) -> Option<Denoted> {
    match compile::classify(store, h, self_call.arity, Some(self_call.idx)) {
        Shape::SelfCall(_) => {
            let v = placeholders.get(*next).cloned();
            *next += 1;
            v.map(Denoted::Int)
        }
        shape @ (Shape::VarCall { .. } | Shape::CombinatorCall { .. }) => match app_shape(store, shape, param_types)? {
            AppShape::ParamCall { root, k, args } => {
                let callee = denote_with_placeholders(store, root, self_call, param_types, combinators, params, placeholders, next)?.clo()?;
                let mut arg_exprs = Vec::with_capacity(k);
                for &a in &args {
                    let e = denote_with_placeholders(store, a, self_call, param_types, combinators, params, placeholders, next)?.int()?;
                    arg_exprs.push(e);
                }
                let applied = apply_n(callee, arg_exprs);
                let int_ty = combinators.cp.arith.int_ty();
                debug_assert_has_type(&combinators.cp.arith.p, &applied, &int_ty, "denote_with_placeholders: call_indirect application");
                Some(Denoted::Int(applied))
            }
            // A closure created and (fully or partially) called right
            // here, within the leaf's own expression -- mirrors
            // `denote_closure_typed`'s own `AppShape::LitLambda*` arms
            // (and, through it, `denote_closure`'s) exactly, including its
            // `combinator_return_type`-gated over-application dispatch,
            // just checking for a self-call occurrence in each argument
            // first.
            AppShape::LitLambdaPartial { root, args, callee_param_types } => {
                let arity = callee_param_types.len();
                let k = args.len();
                let (root_arity, root_body, root_is_rec) = compile::peel(store, root)?;
                let root_captures = compile::free_vars(store, root_body, root_arity, root_is_rec);
                let pap_fn = combinators.pap_ref(root, k, param_types)?;
                let env_expr = if root_captures.is_empty() {
                    None
                } else {
                    let e = build_env_expr(combinators, &root_captures, params, param_types)?;
                    Some(e)
                };
                let mut arg_exprs = Vec::with_capacity(k);
                for (j, &a) in args.iter().enumerate() {
                    let d = denote_with_placeholders(store, a, self_call, param_types, combinators, params, placeholders, next)?;
                    let e = arg_denotation(d, callee_param_types[arity - 1 - j], || return_type_of(store, a, self_call.arity, Some(self_call.idx), param_types))?;
                    arg_exprs.push(e);
                }
                let mut all_args = Vec::with_capacity(1 + arg_exprs.len());
                if let Some(env_expr) = &env_expr {
                    all_args.push(env_expr.clone());
                }
                all_args.extend(arg_exprs.iter().cloned());
                let applied = apply_n(pap_fn, all_args);
                let clo_ty = combinators.cp.clo_ty(arity - k + pap_extra_arity(store, root));
                debug_assert_has_type(&combinators.cp.arith.p, &applied, &clo_ty, "denote_with_placeholders: partial application");
                Some(Denoted::Clo(applied))
            }
            AppShape::LitLambdaExact { root, args, callee_param_types } | AppShape::LitLambdaOver { root, args, callee_param_types } => {
                let arity = callee_param_types.len();
                let sat_args = &args[..arity];
                let (c_arity, c_body, c_is_rec) = compile::peel(store, root)?;
                let captures = compile::free_vars(store, c_body, c_arity, c_is_rec);
                let call_fn = combinators.call_ref(root, &captures, param_types)?;
                let env_expr = if captures.is_empty() {
                    None
                } else {
                    let e = build_env_expr(combinators, &captures, params, param_types)?;
                    Some(e)
                };
                let mut arg_exprs = Vec::with_capacity(arity);
                for (j, &a) in sat_args.iter().enumerate() {
                    let d = denote_with_placeholders(store, a, self_call, param_types, combinators, params, placeholders, next)?;
                    let e = arg_denotation(d, callee_param_types[arity - 1 - j], || return_type_of(store, a, self_call.arity, Some(self_call.idx), param_types))?;
                    arg_exprs.push(e);
                }
                let mut all_args = Vec::with_capacity(1 + arg_exprs.len());
                if let Some(env_expr) = &env_expr {
                    all_args.push(env_expr.clone());
                }
                all_args.extend(arg_exprs.iter().cloned());
                let sat_applied = apply_n(call_fn, all_args);
                let return_ty = combinator_return_type(store, root).unwrap_or(None);
                let returns_clo = return_ty.is_some();
                let sat_ty = match return_ty {
                    Some(k) => combinators.cp.clo_ty(k),
                    None => combinators.cp.arith.int_ty(),
                };
                debug_assert_has_type(&combinators.cp.arith.p, &sat_applied, &sat_ty, "denote_with_placeholders: direct combinator call");

                if args.len() == arity {
                    return Some(if returns_clo { Denoted::Clo(sat_applied) } else { Denoted::Int(sat_applied) });
                }

                if !returns_clo {
                    return None; // over-application of a plain Int result: genuinely out of scope
                }
                let extra_args = &args[arity..];
                let mut extra_arg_exprs = Vec::with_capacity(extra_args.len());
                for &a in extra_args {
                    let e = denote_with_placeholders(store, a, self_call, param_types, combinators, params, placeholders, next)?.int()?;
                    extra_arg_exprs.push(e);
                }
                let applied = apply_n(sat_applied, extra_arg_exprs);
                let int_ty = combinators.cp.arith.int_ty();
                debug_assert_has_type(&combinators.cp.arith.p, &applied, &int_ty, "denote_with_placeholders: over-application dispatch");
                Some(Denoted::Int(applied))
            }
        },
        Shape::OtherCall => None,
        Shape::Var(i) => {
            let i = i as usize;
            let p = params.get(i)?.clone();
            match *param_types.get(i)? {
                Some(_) => Some(Denoted::Clo(p)),
                None => Some(Denoted::Int(p)),
            }
        }
        Shape::Lit(n) => Some(Denoted::Int(combinators.cp.arith.lit_ref(n))),
        Shape::Prim(op, a, b) => {
            let da = denote_with_placeholders(store, a, self_call, param_types, combinators, params, placeholders, next)?.int()?;
            let db = denote_with_placeholders(store, b, self_call, param_types, combinators, params, placeholders, next)?.int()?;
            let op_ref = combinators.cp.arith.op_ref(op);
            let applied = kernel::app2(op_ref, da, db);
            let int_ty = combinators.cp.arith.int_ty();
            debug_assert_has_type(&combinators.cp.arith.p, &applied, &int_ty, "denote_with_placeholders: Prim");
            Some(Denoted::Int(applied))
        }
        // A freshly-created closure *value*, not (yet) called -- mirrors
        // `denote_closure`'s own value-leaf `Term::Abs | Term::Rec` case.
        Shape::Combinator { is_rec: false } => {
            let (arity, body, is_rec) = compile::peel(store, h)?;
            if arity == 0 {
                return None;
            }
            let captures = compile::free_vars(store, body, arity, is_rec);
            let sym = combinators.register(h, &captures, param_types)?;
            if captures.is_empty() {
                return Some(Denoted::Clo(sym));
            }
            let env = build_env_expr(combinators, &captures, params, param_types)?;
            let applied = kernel::app(sym, env);
            let clo_ty = combinators.cp.clo_ty(arity);
            debug_assert_has_type(&combinators.cp.arith.p, &applied, &clo_ty, "denote_with_placeholders: capturing closure value");
            Some(Denoted::Clo(applied))
        }
        // A nested `If`: mirrors `denote_closure`'s identical three-way
        // match (both branches `Int` via `ite_ref`, both `Clo` via
        // `ite_clo_ref`, a mismatch rejected), threading
        // `placeholders`/`next` through each branch so a self-call inside
        // any of them still gets substituted, in the same left-to-right
        // order `find_self_calls` just walked it in -- e.g. a self-call
        // argument `f(n-1, if c then g else h)`, choosing which
        // `Clo`-typed value to thread into the next iteration.
        Shape::If(c, t, e) => {
            let dc = denote_with_placeholders(store, c, self_call, param_types, combinators, params, placeholders, next)?.int()?;
            let dt = denote_with_placeholders(store, t, self_call, param_types, combinators, params, placeholders, next)?;
            let dt_is_clo = matches!(dt, Denoted::Clo(_));
            let dt = match dt {
                Denoted::Int(e) | Denoted::Clo(e) => e,
            };
            let de = denote_with_placeholders(store, e, self_call, param_types, combinators, params, placeholders, next)?;
            let de_is_clo = matches!(de, Denoted::Clo(_));
            let de = match de {
                Denoted::Int(e) | Denoted::Clo(e) => e,
            };
            match (dt_is_clo, de_is_clo) {
                (false, false) => {
                    let ite = combinators.cp.arith.ite_ref();
                    let applied = kernel::app3(ite, dc, dt, de);
                    let int_ty = combinators.cp.arith.int_ty();
                    debug_assert_has_type(&combinators.cp.arith.p, &applied, &int_ty, "denote_with_placeholders: nested If (Int branches)");
                    Some(Denoted::Int(applied))
                }
                (true, true) => {
                    // Which arity's `ite_clo_ref`/`clo_ty` to use isn't
                    // carried by `Denoted::Clo` itself -- re-derived
                    // structurally via `return_type_of`, kept in lockstep
                    // with every `Denoted::Clo`-producing case above (see
                    // its own docs); a mismatch between `t`'s and `e`'s own
                    // arity is rejected here, at the Rust level, rather
                    // than left for the kernel to reject a mismatched
                    // `ite_clo_arity` application after the fact.
                    let t_arity = return_type_of(store, t, self_call.arity, Some(self_call.idx), param_types).flatten()?;
                    let e_arity = return_type_of(store, e, self_call.arity, Some(self_call.idx), param_types).flatten()?;
                    if t_arity != e_arity {
                        return None;
                    }
                    let ite_clo = combinators.cp.ite_clo_ref(t_arity);
                    let applied = kernel::app3(ite_clo, dc, dt, de);
                    let clo_ty = combinators.cp.clo_ty(t_arity);
                    debug_assert_has_type(&combinators.cp.arith.p, &applied, &clo_ty, "denote_with_placeholders: nested If (Clo branches)");
                    Some(Denoted::Clo(applied))
                }
                _ => None,
            }
        }
        Shape::Combinator { .. } => None, // a bare `Term::Rec` is out of scope when there is a self-call,
    }
}

/// Translates a self-call argument expression into a kernel `Int`- or
/// `Clo`-typed value (`denote`, widened with closure-call *and closure-
/// creation* support, for the fragment `new_params_for` needs -- a
/// loop-carried `Clo`-typed value threaded through recursion, a plain
/// `Int` argument possibly computed by calling one, e.g. `f(n-1, g,
/// g(acc))`, or one computed by *creating* a fresh closure and calling it
/// immediately, e.g. `f(n-1, (\y. acc+y)(n))` -- the exact shape
/// `compile.rs`'s own
/// `self_recursion_creating_a_fresh_capturing_closure_every_iteration_compiles`
/// test and `capturing_closure_loop` benchmark exercise, previously
/// compiled but never proven). Unlike [`denote_with_placeholders`], never
/// substitutes a self-call occurrence (there is nothing to substitute it
/// *with* here, and `find_self_calls` never searches inside a self-call's
/// own arguments to begin with, so one structurally can't appear --
/// `param_types` is only ever indexed `0..arity`, `self_idx == arity`
/// falls outside it, so a self-call's own `Var(self_idx)` callee position
/// simply fails to resolve as a closure call and is rejected, the same as
/// any other unrecognized shape); like `denote_with_placeholders`, does
/// allow a nested `If`, both branches `Int` (via `ite_ref`) or both `Clo`
/// (via `ite_clo_ref`, matching `denote_closure`'s own three-way match),
/// since a self-call argument was already allowed to be `if c then x
/// else y` before closures existed here.
///
/// `params` are the enclosing scope's bound parameters, which no push
/// shifts. `register`/`call_ref`/`pap_ref` each may push a
/// postulate on first use. A bare `Term::Rec` (a
/// self-recursive combinator *nested* inside another one's body) stays
/// out of scope, unlike `denote_closure`'s own fragment -- proving one induction correct while assuming another is a genuinely
/// different, unexplored problem, not attempted here.
pub(super) fn denote_closure_typed(
    store: &TermStore,
    h: Hash,
    self_call: Option<SelfCall>,
    param_types: &[Option<usize>],
    combinators: &mut ClosureCombinators<'_>,
    params: &[Expr],
) -> Option<Denoted> {
    // with a self-call: its arity and index; without one (`denote_closure`), the function's own parameter counts and no index
    let (classify_arity, classify_idx, ret_arity, ret_idx) = match self_call {
        Some(sc) => (sc.arity, Some(sc.idx), sc.arity, Some(sc.idx)),
        None => (params.len(), None, param_types.len(), None),
    };
    match compile::classify(store, h, classify_arity, classify_idx) {
        // Never substituted here -- see this function's own docs.
        Shape::SelfCall(_) => None,
        shape @ (Shape::VarCall { .. } | Shape::CombinatorCall { .. }) => match app_shape(store, shape, param_types)? {
            AppShape::ParamCall { root, k, args } => {
                let callee = denote_closure_typed(store, root, self_call, param_types, combinators, params)?.clo()?;
                let mut arg_exprs = Vec::with_capacity(k);
                for &a in &args {
                    let e = denote_closure_typed(store, a, self_call, param_types, combinators, params)?.int()?;
                    arg_exprs.push(e);
                }
                let applied = apply_n(callee, arg_exprs);
                let int_ty = combinators.cp.arith.int_ty();
                debug_assert_has_type(&combinators.cp.arith.p, &applied, &int_ty, "denote_closure_typed: call_indirect application");
                Some(Denoted::Int(applied))
            }
            // A literal lambda -- or a named self-recursive combinator --
            // created and (fully or partially) called right here, in a
            // self-call argument position: mirrors `denote_closure`'s own
            // `AppShape::LitLambda*` arms exactly (same
            // direct-call/partial-application/over-application 3-way,
            // same `pap_ref`-still-rejects-a-recursive-root narrowing,
            // same `combinator_return_type`-gated over-application
            // dispatch), just against `combinators` directly instead of
            // through a wrapper.
            AppShape::LitLambdaPartial { root, args, callee_param_types } => {
                let arity = callee_param_types.len();
                let k = args.len();
                let (root_arity, root_body, root_is_rec) = compile::peel(store, root)?;
                let root_captures = compile::free_vars(store, root_body, root_arity, root_is_rec);
                let pap_fn = combinators.pap_ref(root, k, param_types)?;
                let env_expr = if root_captures.is_empty() {
                    None
                } else {
                    let e = build_env_expr(combinators, &root_captures, params, param_types)?;
                    Some(e)
                };
                let mut arg_exprs = Vec::with_capacity(k);
                for (j, &a) in args.iter().enumerate() {
                    let d = denote_closure_typed(store, a, self_call, param_types, combinators, params)?;
                    let e = arg_denotation(d, callee_param_types[arity - 1 - j], || return_type_of(store, a, ret_arity, ret_idx, param_types))?;
                    arg_exprs.push(e);
                }
                let mut all_args = Vec::with_capacity(1 + arg_exprs.len());
                if let Some(env_expr) = &env_expr {
                    all_args.push(env_expr.clone());
                }
                all_args.extend(arg_exprs.iter().cloned());
                let applied = apply_n(pap_fn, all_args);
                let clo_ty = combinators.cp.clo_ty(arity - k + pap_extra_arity(store, root));
                debug_assert_has_type(&combinators.cp.arith.p, &applied, &clo_ty, "denote_closure_typed: partial application");
                Some(Denoted::Clo(applied))
            }
            AppShape::LitLambdaExact { root, args, callee_param_types } | AppShape::LitLambdaOver { root, args, callee_param_types } => {
                let arity = callee_param_types.len();
                let sat_args = &args[..arity];
                let (c_arity, c_body, c_is_rec) = compile::peel(store, root)?;
                let captures = compile::free_vars(store, c_body, c_arity, c_is_rec);
                let call_fn = combinators.call_ref(root, &captures, param_types)?;
                let env_expr = if captures.is_empty() {
                    None
                } else {
                    let e = build_env_expr(combinators, &captures, params, param_types)?;
                    Some(e)
                };
                let mut arg_exprs = Vec::with_capacity(arity);
                for (j, &a) in sat_args.iter().enumerate() {
                    let d = denote_closure_typed(store, a, self_call, param_types, combinators, params)?;
                    let e = arg_denotation(d, callee_param_types[arity - 1 - j], || return_type_of(store, a, ret_arity, ret_idx, param_types))?;
                    arg_exprs.push(e);
                }
                let mut all_args = Vec::with_capacity(1 + arg_exprs.len());
                if let Some(env_expr) = &env_expr {
                    all_args.push(env_expr.clone());
                }
                all_args.extend(arg_exprs.iter().cloned());
                let sat_applied = apply_n(call_fn, all_args);
                let return_ty = combinator_return_type(store, root).unwrap_or(None);
                let returns_clo = return_ty.is_some();
                let sat_ty = match return_ty {
                    Some(k) => combinators.cp.clo_ty(k),
                    None => combinators.cp.arith.int_ty(),
                };
                debug_assert_has_type(&combinators.cp.arith.p, &sat_applied, &sat_ty, "denote_closure_typed: direct combinator call");

                if args.len() == arity {
                    return Some(if returns_clo { Denoted::Clo(sat_applied) } else { Denoted::Int(sat_applied) });
                }

                if !returns_clo {
                    return None; // over-application of a plain Int result: genuinely out of scope
                }
                let extra_args = &args[arity..];
                let mut extra_arg_exprs = Vec::with_capacity(extra_args.len());
                for &a in extra_args {
                    let e = denote_closure_typed(store, a, self_call, param_types, combinators, params)?.int()?;
                    extra_arg_exprs.push(e);
                }
                let applied = apply_n(sat_applied, extra_arg_exprs);
                let int_ty = combinators.cp.arith.int_ty();
                debug_assert_has_type(&combinators.cp.arith.p, &applied, &int_ty, "denote_closure_typed: over-application dispatch");
                Some(Denoted::Int(applied))
            }
        },
        Shape::OtherCall => None,
        Shape::Var(i) => {
            let i = i as usize;
            let p = params.get(i)?.clone();
            match *param_types.get(i)? {
                Some(_) => Some(Denoted::Clo(p)),
                None => Some(Denoted::Int(p)),
            }
        }
        Shape::Lit(n) => Some(Denoted::Int(combinators.cp.arith.lit_ref(n))),
        Shape::Prim(op, a, b) => {
            let da = denote_closure_typed(store, a, self_call, param_types, combinators, params)?.int()?;
            let db = denote_closure_typed(store, b, self_call, param_types, combinators, params)?.int()?;
            let op_ref = combinators.cp.arith.op_ref(op);
            let applied = kernel::app2(op_ref, da, db);
            let int_ty = combinators.cp.arith.int_ty();
            debug_assert_has_type(&combinators.cp.arith.p, &applied, &int_ty, "denote_closure_typed: Prim");
            Some(Denoted::Int(applied))
        }
        // Mirrors `denote_closure`'s identical three-way match: both
        // branches `Int` via `ite_ref`, both `Clo` via `ite_clo_ref`
        // (e.g. a self-call argument `f(n-1, if c then g else h)`,
        // choosing which `Clo`-typed value to thread onward), a mismatch
        // rejected.
        Shape::If(c, t, e) => {
            let dc = denote_closure_typed(store, c, self_call, param_types, combinators, params)?.int()?;
            let dt = denote_closure_typed(store, t, self_call, param_types, combinators, params)?;
            let dt_is_clo = matches!(dt, Denoted::Clo(_));
            let dt = match dt {
                Denoted::Int(e) | Denoted::Clo(e) => e,
            };
            let de = denote_closure_typed(store, e, self_call, param_types, combinators, params)?;
            let de_is_clo = matches!(de, Denoted::Clo(_));
            let de = match de {
                Denoted::Int(e) | Denoted::Clo(e) => e,
            };
            match (dt_is_clo, de_is_clo) {
                (false, false) => {
                    let ite = combinators.cp.arith.ite_ref();
                    let applied = kernel::app3(ite, dc, dt, de);
                    let int_ty = combinators.cp.arith.int_ty();
                    debug_assert_has_type(&combinators.cp.arith.p, &applied, &int_ty, "denote_closure_typed: If (Int branches)");
                    Some(Denoted::Int(applied))
                }
                (true, true) => {
                    // See `denote_with_placeholders`'s identical case for
                    // why `return_type_of` (not `Denoted::Clo` itself) is
                    // the source of the shared arity here.
                    let t_arity = return_type_of(store, t, ret_arity, ret_idx, param_types).flatten()?;
                    let e_arity = return_type_of(store, e, ret_arity, ret_idx, param_types).flatten()?;
                    if t_arity != e_arity {
                        return None;
                    }
                    let ite_clo = combinators.cp.ite_clo_ref(t_arity);
                    let applied = kernel::app3(ite_clo, dc, dt, de);
                    let clo_ty = combinators.cp.clo_ty(t_arity);
                    debug_assert_has_type(&combinators.cp.arith.p, &applied, &clo_ty, "denote_closure_typed: If (Clo branches)");
                    Some(Denoted::Clo(applied))
                }
                _ => None,
            }
        }
        // A freshly-created closure *value*, not (yet) called -- e.g.
        // threaded onward as the next iteration's own closure-typed
        // parameter, `f(n-1, \y. acc+y)`. Mirrors `denote_closure`'s own
        // value-leaf `Term::Abs | Term::Rec` case exactly.
        Shape::Combinator { is_rec } if !(is_rec && self_call.is_some()) => {
            let (arity, body, is_rec) = compile::peel(store, h)?;
            if arity == 0 {
                return None;
            }
            let captures = compile::free_vars(store, body, arity, is_rec);
            let sym = combinators.register(h, &captures, param_types)?;
            if captures.is_empty() {
                return Some(Denoted::Clo(sym));
            }
            let env = build_env_expr(combinators, &captures, params, param_types)?;
            let applied = kernel::app(sym, env);
            let clo_ty = combinators.cp.clo_ty(arity);
            debug_assert_has_type(&combinators.cp.arith.p, &applied, &clo_ty, "denote_closure_typed: capturing closure value");
            Some(Denoted::Clo(applied))
        }
        Shape::Combinator { .. } => None, // a bare `Term::Rec` is out of scope when there is a self-call,
    }
}

/// Binds `n` fresh `Int`-typed parameters in a new scope, lets `build`
/// bind more of its own and construct a body term, then closes
/// *everything* bound since entry (the `n` params plus anything `build`
/// itself bound, e.g. `v` or `e`) into nested binders around that body,
/// rolling them back afterward. Pass `kernel::Binder::Pi` to build a
/// *type* (quantifying over these params) or `kernel::Binder::Lam` to build a *value* of that
/// type (e.g. a motive or a proof to pass as an argument) -- getting this
/// wrong is a real, easy-to-make mistake (a `Pi` where a `Lam` was
/// needed), not a hypothetical one.
pub(super) fn params_and_close(
    arith: &mut ArithPostulates,
    n: usize,
    binder: kernel::Binder,
    build: impl FnOnce(&mut ArithPostulates, &[Expr]) -> Option<Expr>,
) -> Option<Expr> {
    let s = arith.p.open();
    let params: Vec<Expr> = (0..n)
        .map(|_| {
            let ty = arith.int_ty();
            arith.p.bind(ty)
        })
        .collect();
    match build(arith, &params) {
        Some(b) => Some(arith.p.close(s, binder, b)),
        None => {
            arith.p.abandon(s);
            None
        }
    }
}

/// Like [`params_and_close`], but for `build_universal`'s own closure-aware
/// pipeline: binds one fresh parameter per entry of `param_types`, typed
/// `Clo_k` or `Int` to match, so `build`'s own params may be mixed-typed.
pub(super) fn params_and_close_typed(
    arith: &mut ClosureCombinators<'_>,
    param_types: &[Option<usize>],
    binder: kernel::Binder,
    build: impl FnOnce(&mut ClosureCombinators<'_>, &[Expr]) -> Option<Expr>,
) -> Option<Expr> {
    let s = arith.p.open();
    let mut params = Vec::with_capacity(param_types.len());
    for pt in param_types {
        let ty = match pt {
            Some(k) => arith.clo_ty(*k),
            None => arith.int_ty(),
        };
        params.push(arith.p.bind(ty));
    }
    match build(arith, &params) {
        Some(b) => Some(arith.p.close(s, binder, b)),
        None => {
            arith.p.abandon(s);
            None
        }
    }
}

/// A kernel-checked universal theorem: for every input, the witness that
/// unrolling the recursion terminates (`Ev`) determines the same value the
/// compiled code's own recursive structure (`loop_val`) reconstructs from
/// that witness -- covers tail recursion and general (non-tail) recursion
/// alike (see module docs).
pub struct UniversalTailProof {
    pub globals: Globals,
    pub arity: usize,
    /// `: Pi p_0..p_{arity-1} v (e : Ev(p_0,..,v)). Id(Int, loop_val(..,e), v)`.
    pub theorem_ty: Expr,
    pub theorem_proof: Expr,
}

/// Everything `prove_tail_recursive_universal`'s theorem was built from,
/// kept around (instead of dropped) so `prove_tail_recursive_instance` can
/// reuse it to build a concrete `Ev`-witness afterward, without redoing any
/// of the theorem's own construction. Witness-building pushes further
/// postulates onto `arith.p.globals` (fresh literal constants,
/// `assume_prim_fact` axioms) after this scaffold is built.
///
/// Cloneable so a caller that wants several concrete instances (`jit.rs`'s
/// `kernel_verify`, trying a handful of sample calls) can build this once
/// and clone it per attempt, instead of paying for `build_universal`'s full
/// construction -- the expensive part, dominated by `kernel::cong_n`/
/// `trans_proof` chaining and a `kernel::check` re-verification -- again
/// for every sample.
#[derive(Clone)]
pub(super) struct UniversalScaffold<'a> {
    pub(super) combinators: ClosureCombinators<'a>,
    pub(super) arity: usize,
    /// `param_types[i]` is `Some(k)` for a `Var(i)` parameter that's a
    /// `Clo`, always called with `k` arguments (the same convention
    /// `denote_closure`'s own `param_types` uses -- see its docs), `None`
    /// for a plain `Int` parameter. Never itself involving a captured
    /// free variable or a literal-lambda call (see `build_universal`'s own
    /// docs for the scope this narrows to) -- only ever consulted to
    /// decide whether `instance_from_scaffold` can even attempt a concrete
    /// instance (it can't, for any `Some(_)` entry -- see its own docs).
    pub(super) param_types: Vec<Option<usize>>,
    pub(super) self_call: SelfCall,
    pub(super) leaves: Vec<Leaf>,
    pub(super) combines: Vec<Expr>,
    pub(super) ev_leaf_positions: Vec<usize>,
    /// `Ev`'s own postulate position (see `build_universal`) -- needed by
    /// `build_ev_witness`'s branching-leaf recasting, which builds `Ev(...)`
    /// applications directly rather than through a leaf-specific constructor.
    pub(super) ev_pos: usize,
    pub(super) theorem_ty: Expr,
    pub(super) theorem_proof: Expr,
}

pub(super) fn build_universal(store: &TermStore, h: Hash) -> Option<UniversalScaffold<'_>> {
    let (arity, body, is_rec) = compile::peel(store, h)?;
    if !is_rec || arity == 0 {
        return None;
    }
    let self_idx = arity as u32;
    let self_call = SelfCall { arity, idx: self_idx };

    // `Var(i)` for `i < arity` that's always called, elsewhere in `body`,
    // with a fixed number of arguments (through a parameter, never a
    // captured free variable -- `self_idx` sits just outside `0..arity`,
    // so a self-call's own callee position never gets misclassified as one
    // of these) is treated as `Clo`-typed throughout this function.
    // `denote_closure_typed` (used by `new_params_for` below) also covers
    // closure *creation* inside a self-call argument -- registering a
    // combinator, calling one directly, or partially applying one -- and a
    // nested `If` choosing between two `Clo`-typed values, both via the
    // same `ClosureCombinators` machinery `prove_closure_expr` itself uses.
    // Still out of scope: a captured free variable used as a closure here
    // (this function has no enclosing frame to resolve one against).
    let found = compile::infer_closure_arities(store, body, arity, Some(self_idx))?;
    // See `param_types_for`'s own docs: an inconsistently-called `Var` is
    // declined the same way an absent one already is.
    let param_types: Vec<Option<usize>> = (0..arity as u32)
        .map(|i| match found.get(&i) {
            Some(compile::ArityUse::Consistent(k)) => Some(*k),
            Some(compile::ArityUse::Inconsistent) | None => None,
        })
        .collect();

    let tree = classify_tree(store, body)?;
    let leaves = flatten_tree(store, &tree, self_call, &param_types)?;
    if leaves.iter().all(|l| l.calls.is_empty()) {
        return None; // no recursion anywhere: not this function's job (see `prove_pure_expr`)
    }

    let mut lits = Vec::new();
    if !collect_literals(store, body, arity, Some(self_idx), Some(&param_types), &mut lits) {
        return None;
    }

    let mut arith = ClosureCombinators::new(store);
    for n in lits {
        arith.lit(n);
    }
    arith.lit(0);
    arith.lit(1); // `cond_premise` below needs both regardless of whether the source uses them

    // cond_premise(cond, params, lit): "cond(params) = lit" -- the
    // hypothesis each leaf's path premises are built from below, tying
    // `Ev`'s constructors to whichever branch `cond` actually selects
    // instead of admitting a witness unconditionally (see module docs).
    // Uses the caller-supplied `params` directly, same convention as
    // `ev_of`. Stays purely arithmetic (`classify_tree` already requires a
    // direct comparison here, closures or not).
    let cond_premise = |arith: &ArithPostulates, cond: Hash, params: &[Expr], lit: i64| -> Option<Expr> {
        let d = denote(store, cond, arith, params)?;
        Some(kernel::id(arith.int_ty(), d, arith.lit_ref(lit)))
    };

    // Binds one premise per `(cond, lit)` on `path` (a leaf's whole
    // ancestry, root to leaf), returning them. Each premise's own type
    // only depends on `params`.
    let push_path = |arith: &mut ArithPostulates, pp: &[Expr], path: &[(Hash, i64)]| -> Option<Vec<Expr>> {
        let mut premises = Vec::with_capacity(path.len());
        for &(cond, lit) in path {
            let pf_ty = cond_premise(arith, cond, pp, lit)?;
            premises.push(arith.p.bind(pf_ty));
        }
        Some(premises)
    };

    // new_params_for(call_args, params): one self-call occurrence's own
    // argument expressions denoted in terms of `params`, reindexed from
    // application order to by-`Var` order (matching
    // `prove_tail_recursive_call`'s convention exactly) -- closure-aware
    // via `denote_closure_typed` (a loop-carried `Clo`-typed argument, or a
    // plain `Int` one possibly computed by calling one), each checked
    // against `param_types[i]`, the *target* slot's own type.
    let new_params_for = |arith: &mut ClosureCombinators<'_>, call_args: &[Hash], params: &[Expr]| -> Option<Vec<Expr>> {
        (0..arity)
            .map(|i| {
                let d = denote_closure_typed(store, call_args[arity - 1 - i], Some(self_call), &param_types, arith, params)?;
                match param_types[i] {
                    Some(_) => d.clo(),
                    None => d.int(),
                }
            })
            .collect()
    };

    // Ev : T_0 -> .. -> T_{arity-1} -> Int -> Sort(0), each `T_i` `Clo` or
    // `Int` per `param_types[i]`. `v` (innermost) is wrapped first, then
    // `param_types` in *reverse*, matching `ev_of`/`apply_n`'s own
    // left-to-right application order (`params[0]` applied first, ending
    // up outermost; `v` applied last, ending up innermost).
    let ev_ty = {
        let mut doms = Vec::with_capacity(param_types.len());
        for pt in &param_types {
            let dom = match pt {
                Some(k) => arith.clo_ty(*k),
                None => arith.int_ty(),
            };
            doms.push(dom);
        }
        let mut ty = kernel::arrow(arith.int_ty(), kernel::sort(0)); // v : Int
        for dom in doms.iter().rev() {
            ty = kernel::arrow(dom.clone(), ty);
        }
        ty
    };
    let ev_pos = arith.p.push(ev_ty);
    let ev_of = |arith: &ArithPostulates, params: &[Expr], v: Expr| -> Expr { ev_of(arith, ev_pos, params, v) };

    // Binds `v_1:Int .. v_k:Int` then `e_1:Ev(new_params_1,v_1) ..
    // e_k:Ev(new_params_k,v_k)` for a leaf's `calls` (one `(v,e)` pair per
    // self-call occurrence, grouped -- all `v`s then all `e`s -- rather
    // than interleaved; each `e_j`'s type only needs its *own* `v_j`, so
    // grouping is no less correct than interleaving and is simpler for
    // every caller below to zip).
    let push_calls = |arith: &mut ClosureCombinators<'_>, pp: &[Expr], calls: &[Vec<Hash>]| -> Option<(Vec<Expr>, Vec<Expr>)> {
        let mut vs = Vec::with_capacity(calls.len());
        for _ in calls {
            vs.push({ let ty = arith.int_ty(); arith.p.bind(ty) });
        }
        let mut es = Vec::with_capacity(calls.len());
        for (call, v) in calls.iter().zip(&vs) {
            let np = new_params_for(arith, call, pp)?;
            let ev_np = ev_of(arith, &np, v.clone());
            es.push(arith.p.bind(ev_np));
        }
        Some((vs, es))
    };

    // combine_i : Pi params. Pi ih_1:Int .. ih_{k_i}:Int. Int -- leaf i's
    // own arithmetic expression with each self-call occurrence replaced
    // by the corresponding `ih_j` (`denote_with_placeholders`), closed
    // over `params` *and* the `k_i` placeholders as one value, reused
    // (referenced from several deeper points below) both to state what
    // value leaf `i` produces and, later, to recombine the actually-
    // recursively-computed values. `k_i == 0`
    // (`combine_i() = denote(leaf, params)`) is the old base-case shape;
    // `k_i == 1` with the self-call as the *whole* leaf
    // (`combine_i(ih) = ih`) is the old tail-call shape; anything else
    // (`n * ih`, `ih_1 + ih_2`, ...) is genuinely new.
    let no_closures = |n: usize| vec![None; n];
    let mut combines = Vec::with_capacity(leaves.len());
    for leaf in &leaves {
        let expr = params_and_close_typed(&mut arith, &param_types, kernel::Binder::Lam, |arith, pp| {
            params_and_close_typed(arith, &no_closures(leaf.calls.len()), kernel::Binder::Lam, |arith, pp2| {
                denote_with_placeholders(store, leaf.expr, self_call, &param_types, arith, pp, pp2, &mut 0)?.int()
            })
        })?;
        combines.push(expr);
    }

    // ev_leaf_i : Pi params. Pi (leaf i's path premises). Pi v_1..v_{k_i}
    //             (e_1:Ev(new_params_1,v_1))..(e_{k_i}:..). Ev(params, combine_i(params,vs))
    // -- one constructor per leaf.
    let mut ev_leaf_positions = Vec::with_capacity(leaves.len());
    for (leaf, combine) in leaves.iter().zip(&combines) {
        let ty = params_and_close_typed(&mut arith, &param_types, kernel::Binder::Pi, |arith, pp| {
            push_path(arith, pp, &leaf.path)?;
            let (vs, _es) = push_calls(arith, pp, &leaf.calls)?;
            let combine_v = combine_of(combine, pp, &vs);
            Some(ev_of(arith, pp, combine_v))
        })?;
        ev_leaf_positions.push(arith.p.push(ty));
    }

    // Generic recursor:
    // ev_rec : Pi P:(Pi params:Int^arity. Pi v:Int. Ev(params,v) -> Sort(0)).
    //          (leaf_case_ty for leaf 0) -> .. -> (leaf_case_ty for the last leaf)
    //       -> Pi params v (e:Ev(params,v)). P(params,v,e)
    //
    // NB: unlike `ev_ty` above, this is genuinely *dependent* -- P's third
    // argument's type, `Ev(params,v)`, depends on the first `arity+1`
    // arguments' values, so it can't be a flat non-dependent arrow chain
    // the way `Ev`'s own (params,v both just `Int`, independent) type is.
    let motive_ty = params_and_close_typed(&mut arith, &param_types, kernel::Binder::Pi, |arith, pp| {
        let v = { let ty = arith.int_ty(); arith.p.bind(ty) };
        let ev_pv = ev_of(arith, pp, v);
        arith.p.bind(ev_pv);
        Some(kernel::sort(0))
    })?;
    let p_scope = arith.p.open();
    let p_ref = arith.p.bind(motive_ty);
    let p_of = |_arith: &ArithPostulates, params: &[Expr], v: Expr, e: Expr| -> Expr {
        apply_n(p_ref.clone(), params.iter().cloned().chain([v, e]))
    };

    // leaf_case_ty_i : Pi params. Pi (path premises) v_1..v_{k_i} (e_1..e_{k_i}).
    //                  P(new_params_1,v_1,e_1) -> .. -> P(new_params_{k_i},v_{k_i},e_{k_i})
    //               -> P(params, combine_i(params,vs), ev_leaf_i(params,premises,vs,es))
    // -- `k_i == 0` gives the old (implication-free) base-case type;
    // `k_i == 1` gives the old step-case type.
    let mut leaf_case_tys = Vec::with_capacity(leaves.len());
    for (leaf, (&ev_leaf_pos, combine)) in leaves.iter().zip(ev_leaf_positions.iter().zip(&combines)) {
        let ty = params_and_close_typed(&mut arith, &param_types, kernel::Binder::Pi, |arith, pp| {
            let premises = push_path(arith, pp, &leaf.path)?;
            let (vs, es) = push_calls(arith, pp, &leaf.calls)?;
            let mut ih_tys = Vec::with_capacity(leaf.calls.len());
            for ((call, v), e) in leaf.calls.iter().zip(&vs).zip(&es) {
                let np = new_params_for(arith, call, pp)?;
                ih_tys.push(p_of(arith, &np, v.clone(), e.clone()));
            }
            let combine_v = combine_of(combine, pp, &vs);
            let ev_leaf_applied = apply_n(
                arith.p.get(ev_leaf_pos),
                pp.iter().cloned().chain(premises).chain(vs.iter().cloned()).chain(es.iter().cloned()),
            );
            let concl = p_of(arith, pp, combine_v, ev_leaf_applied);
            Some(ih_tys.into_iter().rev().fold(concl, |acc, ih_ty| kernel::arrow(ih_ty, acc)))
        });
        // `params_and_close_typed` already rolls back its own (inner) scope
        // on `None`; a `?` here would still skip past this loop straight
        // out of `build_universal`, leaving `p_scope` (and `P`) open.
        let ty = match ty {
            Some(ty) => ty,
            None => {
                arith.p.abandon(p_scope);
                return None;
            }
        };
        leaf_case_tys.push(ty);
    }
    let concl_ty = params_and_close_typed(&mut arith, &param_types, kernel::Binder::Pi, |arith, pp| {
        let v = { let ty = arith.int_ty(); arith.p.bind(ty) };
        let ev_pv = ev_of(arith, pp, v.clone());
        let e = arith.p.bind(ev_pv);
        Some(p_of(arith, pp, v, e))
    });
    // Same reasoning as the loop above: abandon `p_scope` before giving up.
    let concl_ty = match concl_ty {
        Some(concl_ty) => concl_ty,
        None => {
            arith.p.abandon(p_scope);
            return None;
        }
    };

    let ev_rec_ty_body = leaf_case_tys.iter().rev().fold(concl_ty, |acc, ty| kernel::arrow(ty.clone(), acc));
    let ev_rec_ty = arith.p.close(p_scope, kernel::Binder::Pi, ev_rec_ty_body);
    let ev_rec_pos = arith.p.push(ev_rec_ty);
    let ev_rec_ref = |arith: &ArithPostulates, motive: Expr, cases: &[Expr], params: &[Expr], v: Expr, e: Expr| -> Expr {
        apply_n(
            arith.p.get(ev_rec_pos),
            [motive].into_iter().chain(cases.iter().cloned()).chain(params.iter().cloned()).chain([v, e]),
        )
    };

    // loop_val's arguments to ev_rec, using the constant motive `Int`:
    //   leaf_i' : Pi params (path premises) v_1..v_{k_i} (e_1..e_{k_i}) (ih_1:Int)..(ih_{k_i}:Int).
    //             Int  =  \.. . combine_i(params, ihs)
    // The motive's *body* ignores `v`/`e`, but its binder *domains* still
    // have to match `motive_ty` exactly for these to actually have that
    // type -- `e`'s domain is genuinely `Ev(params,v)`, not a placeholder
    // `Int` (an earlier version of this used `Int` there and failed to
    // typecheck for exactly that reason).
    let const_int_motive = params_and_close_typed(&mut arith, &param_types, kernel::Binder::Lam, |arith, pp| {
        let v = { let ty = arith.int_ty(); arith.p.bind(ty) };
        let ev_pv = ev_of(arith, pp, v);
        arith.p.bind(ev_pv); // e : Ev(params, v)
        Some(arith.int_ty())
    })?;

    let mut loop_leaves = Vec::with_capacity(leaves.len());
    for (leaf, combine) in leaves.iter().zip(&combines) {
        let expr = params_and_close_typed(&mut arith, &param_types, kernel::Binder::Lam, |arith, pp| {
            push_path(arith, pp, &leaf.path)?; // matches leaf_case_ty's premise binders, unused in the body
            push_calls(arith, pp, &leaf.calls)?; // v/e binders, also unused in the body
            let mut ihs = Vec::with_capacity(leaf.calls.len());
            for _ in &leaf.calls {
                ihs.push({ let ty = arith.int_ty(); arith.p.bind(ty) });
            }
            Some(combine_of(combine, pp, &ihs))
        })?;
        loop_leaves.push(expr);
    }

    let loop_val = |arith: &ArithPostulates, params: &[Expr], v: Expr, e: Expr| -> Expr {
        ev_rec_ref(arith, const_int_motive.clone(), &loop_leaves, params, v, e)
    };

    // loop_val_leaf_eq_i : Pi params (path premises) v_1..v_{k_i} (e_1..e_{k_i}).
    //   Id(Int, loop_val(params, combine_i(params,vs), ev_leaf_i(params,premises,vs,es)),
    //            combine_i(params, [loop_val(new_params_j,v_j,e_j) for each j]))
    // -- the computation-rule axiom for *this specific* `loop_val` (not a
    // generic "for any motive" schema -- see module docs), one per leaf.
    let mut loop_val_leaf_eq_positions = Vec::with_capacity(leaves.len());
    for (leaf, (&ev_leaf_pos, combine)) in leaves.iter().zip(ev_leaf_positions.iter().zip(&combines)) {
        let ty = params_and_close_typed(&mut arith, &param_types, kernel::Binder::Pi, |arith, pp| {
            let premises = push_path(arith, pp, &leaf.path)?;
            let (vs, es) = push_calls(arith, pp, &leaf.calls)?;
            let eb = apply_n(
                arith.p.get(ev_leaf_pos),
                pp.iter().cloned().chain(premises).chain(vs.iter().cloned()).chain(es.iter().cloned()),
            );
            let lhs = loop_val(arith, pp, combine_of(combine, pp, &vs), eb);
            let mut recursive_vals = Vec::with_capacity(leaf.calls.len());
            for ((call, v), e) in leaf.calls.iter().zip(&vs).zip(&es) {
                let np = new_params_for(arith, call, pp)?;
                recursive_vals.push(loop_val(arith, &np, v.clone(), e.clone()));
            }
            let rhs = combine_of(combine, pp, &recursive_vals);
            Some(kernel::id(arith.int_ty(), lhs, rhs))
        })?;
        loop_val_leaf_eq_positions.push(arith.p.push(ty));
    }

    // Theorem: Pi params v e. Id(Int, loop_val(params,v,e), v), proved via
    // ev_rec with motive `\params v e. Id(Int, loop_val(params,v,e), v)`.
    let id_motive = params_and_close_typed(&mut arith, &param_types, kernel::Binder::Lam, |arith, pp| {
        let v = { let ty = arith.int_ty(); arith.p.bind(ty) };
        let ev_pv = ev_of(arith, pp, v.clone());
        let e = arith.p.bind(ev_pv);
        Some(kernel::id(arith.int_ty(), loop_val(arith, pp, v.clone(), e), v))
    })?;

    // Leaf `i`'s theorem case: given `ih_j : loop_val(new_params_j,v_j,e_j)
    // = v_j` for each of its self-calls, prove
    // `loop_val(params, combine_i(vs), ev_leaf_i(..)) = combine_i(vs)` by
    // chaining `loop_val_leaf_eq_i` (relates `loop_val` to
    // `combine_i([loop_val(new_params_j,v_j,e_j)])`) with `cong_n` (that
    // equals `combine_i(vs)`, substituting each recursively-computed value
    // for its claimed one via the matching `ih_j` -- the actual congruence-
    // closure step this generalization needed over the old tail-recursion
    // proof, where `k <= 1` and an identity `combine` made this trivial).
    let mut theorem_leaves = Vec::with_capacity(leaves.len());
    for (leaf, ((&ev_leaf_pos, &loop_val_leaf_eq_pos), combine)) in
        leaves.iter().zip(ev_leaf_positions.iter().zip(&loop_val_leaf_eq_positions).zip(&combines))
    {
        let expr = params_and_close_typed(&mut arith, &param_types, kernel::Binder::Lam, |arith, pp| {
            let premises = push_path(arith, pp, &leaf.path)?;
            let (vs, es) = push_calls(arith, pp, &leaf.calls)?;
            let mut ihs = Vec::with_capacity(leaf.calls.len());
            for ((call, v), e) in leaf.calls.iter().zip(&vs).zip(&es) {
                let np = new_params_for(arith, call, pp)?;
                let ih_ty = kernel::id(arith.int_ty(), loop_val(arith, &np, v.clone(), e.clone()), v.clone());
                ihs.push(arith.p.bind(ih_ty));
            }

            let mut recursive_vals = Vec::with_capacity(leaf.calls.len());
            for ((call, v), e) in leaf.calls.iter().zip(&vs).zip(&es) {
                let np = new_params_for(arith, call, pp)?;
                recursive_vals.push(loop_val(arith, &np, v.clone(), e.clone()));
            }

            let eb = apply_n(
                arith.p.get(ev_leaf_pos),
                pp.iter().cloned().chain(premises.iter().cloned()).chain(vs.iter().cloned()).chain(es.iter().cloned()),
            );
            let step_eq = apply_n(
                arith.p.get(loop_val_leaf_eq_pos),
                pp.iter().cloned().chain(premises).chain(vs.iter().cloned()).chain(es),
            );
            let f_partial = apply_n(combine.clone(), pp.iter().cloned());
            let cong_step = kernel::cong_n(&arith.int_ty(), &arith.int_ty(), &f_partial, &recursive_vals, &vs, ihs);

            let lhs = loop_val(arith, pp, combine_of(combine, pp, &vs), eb);
            let mid = combine_of(combine, pp, &recursive_vals);
            let rhs = combine_of(combine, pp, &vs);
            Some(kernel::trans_proof(&arith.int_ty(), &lhs, &mid, &rhs, step_eq, cong_step))
        })?;
        theorem_leaves.push(expr);
    }

    let theorem_ty = params_and_close_typed(&mut arith, &param_types, kernel::Binder::Pi, |arith, pp| {
        let v = { let ty = arith.int_ty(); arith.p.bind(ty) };
        let ev_pv = ev_of(arith, pp, v.clone());
        let e = arith.p.bind(ev_pv);
        Some(kernel::id(arith.int_ty(), loop_val(arith, pp, v.clone(), e), v))
    })?;

    let theorem_proof = params_and_close_typed(&mut arith, &param_types, kernel::Binder::Lam, |arith, pp| {
        let v = { let ty = arith.int_ty(); arith.p.bind(ty) };
        let ev_pv = ev_of(arith, pp, v.clone());
        let e = arith.p.bind(ev_pv);
        Some(ev_rec_ref(arith, id_motive.clone(), &theorem_leaves, pp, v, e))
    })?;

    arith.p.check(&theorem_proof, &theorem_ty).ok()?;

    Some(UniversalScaffold {
        theorem_ty,
        theorem_proof,
        arity,
        param_types,
        self_call,
        leaves,
        combines,
        ev_leaf_positions,
        ev_pos,
        combinators: arith,
    })
}

/// Attempts to build a [`UniversalTailProof`] for `h`. Returns `None` for
/// anything outside the covered fragment: not `Rec`-wrapped, zero arity, a
/// body that doesn't classify as a [`DecisionTree`] (every `If` on the way
/// to a leaf must be a direct comparison), or one with no self-call
/// anywhere in it. A closure-typed *parameter*, threaded through the
/// recursion or called via ordinary application (`Clo_k` is a literal
/// Pi type, not an opaque postulate -- see `ClosurePostulates::clo_ty`),
/// is covered; so is a closure
/// genuinely created and (fully or partially) called anywhere in the body
/// -- a self-call argument (`f(n-1, (\y. acc+y)(n))`) or a leaf's own
/// top-level expression (`(\y. n+y)(5) + f(n-1)`) alike (see module
/// docs). A leaf may itself contain a further nested `If`, purely
/// arithmetic or choosing between two `Clo`-typed values.
pub fn prove_tail_recursive_universal(store: &TermStore, h: Hash) -> Option<UniversalTailProof> {
    let scaffold = build_universal(store, h)?;
    let theorem_ty = scaffold.theorem_ty.clone();
    let theorem_proof = scaffold.theorem_proof.clone();
    Some(UniversalTailProof {
        globals: scaffold.combinators.cp.arith.p.globals,
        arity: scaffold.arity,
        theorem_ty,
        theorem_proof,
    })
}
