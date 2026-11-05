use super::*;

// --- hardening against composition bugs -----------------------------------
//
// A function composing an `Expr` from more than one recursive sub-call can
// still make a composition mistake, even though a pushed `Const` shifts
// nothing (`docs/related-work/` §68, §69).
//
// This helper turns any such mistake into an immediate, precisely located
// panic instead: called once at the *return point* of any function that
// composes sub-`Expr`s from more than one recursive call (`denote_closure`),
// it confirms the value this call is
// about to hand back has the *exact* type expected -- known statically at
// each call site (`Int` or `Clo`) -- before it can be
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
pub(super) fn debug_assert_has_type(p: &Postulates, e: &Expr, expected: &Expr, label: &str) {
    if !cfg!(debug_assertions) {
        return;
    }
    if let Err(err) = p.check_open(e, expected) {
        panic!(
            "composition bug in {label}: the value doesn't have its expected type.\n  \
             error: {err}\n  value: {e:?}\n  expected type: {expected:?}"
        );
    }
}

/// `f` applied to each of `args` in order (left to right).
pub(super) fn apply_n(f: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(f, kernel::app)
}

/// `arity`/`self_idx` bundled together -- the pair `find_self_calls` and
/// `denote_closure` both need on every recursive call, purely to
/// forward to `shape::match_self_call` at each node.
#[derive(Clone, Copy)]
pub(super) struct SelfCall {
    pub(super) arity: usize,
    pub(super) idx: u32,
}

/// What a self-call (`Shape::SelfCall`) means to [`denote_closure`].
pub(super) enum SelfCalls<'a> {
    /// No self-call in scope: a whole function body, read against its own parameters.
    None,
    /// A self-call's own argument: a self-call cannot appear inside it (`find_self_calls` never searches there), so
    /// one is rejected.
    Reject(SelfCall),
    /// A leaf's `combine` body: each self-call is the next placeholder (the `Ev`-bound values, always `Int`),
    /// consumed left to right in `find_self_calls`'s order.
    Placeholders(SelfCall, &'a [Expr], usize),
}

impl SelfCalls<'_> {
    fn self_call(&self) -> Option<SelfCall> {
        match self {
            SelfCalls::None => None,
            SelfCalls::Reject(sc) | SelfCalls::Placeholders(sc, ..) => Some(*sc),
        }
    }
}

/// Translates `h` into a kernel `Int`- or `Clo`-typed value: `denote` widened with closure calls and closure creation,
/// for the closures fragment `compile.rs` compiles. One walker for three readings (`self_calls`): a whole function body
/// (`prove_closure_expr`), a self-call's argument (`new_params_for`: a loop-carried `Clo` value, or an `Int` computed
/// by calling or creating one, e.g. `f(n-1, (\y. acc+y)(n))`), and a recursive leaf's `combine` body with its
/// self-calls replaced by placeholders.
///
/// A nested `If` takes both branches `Int` (via `ite_ref`) or both `Clo` of one arity (via `ite_clo_ref`); a mismatch
/// is rejected. `params[i]`/`param_types[i]` describe `Var(i)`: `param_types[i] = Some(k)` for a closure-typed
/// parameter always called with `k` arguments (`shape::infer_closure_arities`, reindexed by `Var`), `None` for an
/// `Int`. `params` are postulates as `Const`s, which no later push shifts; `register`/`call_ref`/`pap_ref` may each push
/// a postulate on first use. With a self-call in scope, a bare `Term::Rec` (a self-recursive combinator nested inside
/// another's body) stays out of scope: proving one induction while assuming another is a different problem.
pub(super) fn denote_closure(
    h: Hash,
    self_calls: &mut SelfCalls,
    param_types: &[Option<usize>],
    combinators: &mut ClosureCombinators<'_>,
    params: &[Expr],
) -> Option<Denoted> {
    let store = combinators.store;
    // with a self-call: its arity and index; without one, the function's own parameter counts and no index
    let self_call = self_calls.self_call();
    let (classify_arity, classify_idx, ret_arity, ret_idx) = match self_call {
        Some(sc) => (sc.arity, Some(sc.idx), sc.arity, Some(sc.idx)),
        None => (params.len(), None, param_types.len(), None),
    };
    match shape::classify(store, h, classify_arity, classify_idx) {
        Shape::SelfCall(_) => match self_calls {
            SelfCalls::Placeholders(_, placeholders, next) => {
                let v = placeholders.get(*next).copied();
                *next += 1;
                v.map(Denoted::Int)
            }
            _ => None,
        },
        shape @ (Shape::VarCall { .. } | Shape::CombinatorCall { .. }) => match app_shape(store, shape, param_types)? {
            AppShape::ParamCall { root, k, args } => {
                let callee = denote_closure(root, self_calls, param_types, combinators, params)?.clo()?;
                let mut arg_exprs = Vec::with_capacity(k);
                for &a in &args {
                    let e = denote_closure(a, self_calls, param_types, combinators, params)?.int()?;
                    arg_exprs.push(e);
                }
                let applied = apply_n(callee, arg_exprs);
                let int_ty = combinators.cp.arith.int_ty();
                debug_assert_has_type(&combinators.cp.arith.p, &applied, &int_ty, "denote_closure: call_indirect application");
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
                let (root_arity, root_body, root_is_rec) = shape::peel(store, root)?;
                let root_captures = shape::free_vars(store, root_body, root_arity, root_is_rec);
                let pap_fn = combinators.pap_ref(root, k, param_types)?;
                let env_expr = if root_captures.is_empty() {
                    None
                } else {
                    let e = build_env_expr(combinators, &root_captures, params, param_types)?;
                    Some(e)
                };
                let mut arg_exprs = Vec::with_capacity(k);
                for (j, &a) in args.iter().enumerate() {
                    let d = denote_closure(a, self_calls, param_types, combinators, params)?;
                    let e = arg_denotation(d, callee_param_types[arity - 1 - j], || return_type_of(store, a, ret_arity, ret_idx, param_types))?;
                    arg_exprs.push(e);
                }
                let mut all_args = Vec::with_capacity(1 + arg_exprs.len());
                if let Some(env_expr) = &env_expr {
                    all_args.push(*env_expr);
                }
                all_args.extend(arg_exprs.iter().cloned());
                let applied = apply_n(pap_fn, all_args);
                let clo_ty = combinators.cp.clo_ty(arity - k + pap_extra_arity(store, root));
                debug_assert_has_type(&combinators.cp.arith.p, &applied, &clo_ty, "denote_closure: partial application");
                Some(Denoted::Clo(applied))
            }
            AppShape::LitLambdaExact { root, args, callee_param_types } | AppShape::LitLambdaOver { root, args, callee_param_types } => {
                let arity = callee_param_types.len();
                let sat_args = &args[..arity];
                let (c_arity, c_body, c_is_rec) = shape::peel(store, root)?;
                let captures = shape::free_vars(store, c_body, c_arity, c_is_rec);
                let call_fn = combinators.call_ref(root, &captures, param_types)?;
                let env_expr = if captures.is_empty() {
                    None
                } else {
                    let e = build_env_expr(combinators, &captures, params, param_types)?;
                    Some(e)
                };
                let mut arg_exprs = Vec::with_capacity(arity);
                for (j, &a) in sat_args.iter().enumerate() {
                    let d = denote_closure(a, self_calls, param_types, combinators, params)?;
                    let e = arg_denotation(d, callee_param_types[arity - 1 - j], || return_type_of(store, a, ret_arity, ret_idx, param_types))?;
                    arg_exprs.push(e);
                }
                let mut all_args = Vec::with_capacity(1 + arg_exprs.len());
                if let Some(env_expr) = &env_expr {
                    all_args.push(*env_expr);
                }
                all_args.extend(arg_exprs.iter().cloned());
                let sat_applied = apply_n(call_fn, all_args);
                let return_ty = combinator_return_type(store, root).unwrap_or(None);
                let returns_clo = return_ty.is_some();
                let sat_ty = match return_ty {
                    Some(k) => combinators.cp.clo_ty(k),
                    None => combinators.cp.arith.int_ty(),
                };
                debug_assert_has_type(&combinators.cp.arith.p, &sat_applied, &sat_ty, "denote_closure: direct combinator call");

                if args.len() == arity {
                    return Some(if returns_clo { Denoted::Clo(sat_applied) } else { Denoted::Int(sat_applied) });
                }

                if !returns_clo {
                    return None; // over-application of a plain Int result: genuinely out of scope
                }
                let extra_args = &args[arity..];
                let mut extra_arg_exprs = Vec::with_capacity(extra_args.len());
                for &a in extra_args {
                    let e = denote_closure(a, self_calls, param_types, combinators, params)?.int()?;
                    extra_arg_exprs.push(e);
                }
                let applied = apply_n(sat_applied, extra_arg_exprs);
                let int_ty = combinators.cp.arith.int_ty();
                debug_assert_has_type(&combinators.cp.arith.p, &applied, &int_ty, "denote_closure: over-application dispatch");
                Some(Denoted::Int(applied))
            }
        },
        Shape::OtherCall => None,
        Shape::Var(i) => {
            let i = i as usize;
            let p = *params.get(i)?;
            match *param_types.get(i)? {
                Some(_) => Some(Denoted::Clo(p)),
                None => Some(Denoted::Int(p)),
            }
        }
        Shape::Lit(n) => Some(Denoted::Int(combinators.cp.arith.lit_ref(n))),
        Shape::Prim(op, a, b) => {
            let da = denote_closure(a, self_calls, param_types, combinators, params)?.int()?;
            let db = denote_closure(b, self_calls, param_types, combinators, params)?.int()?;
            let op_ref = combinators.cp.arith.op_ref(op);
            let applied = kernel::app2(op_ref, da, db);
            let int_ty = combinators.cp.arith.int_ty();
            debug_assert_has_type(&combinators.cp.arith.p, &applied, &int_ty, "denote_closure: Prim");
            Some(Denoted::Int(applied))
        }
        // Mirrors `denote_closure`'s identical three-way match: both
        // branches `Int` via `ite_ref`, both `Clo` via `ite_clo_ref`
        // (e.g. a self-call argument `f(n-1, if c then g else h)`,
        // choosing which `Clo`-typed value to thread onward), a mismatch
        // rejected.
        Shape::If(c, t, e) => {
            let dc = denote_closure(c, self_calls, param_types, combinators, params)?.int()?;
            let dt = denote_closure(t, self_calls, param_types, combinators, params)?;
            let dt_is_clo = matches!(dt, Denoted::Clo(_));
            let dt = match dt {
                Denoted::Int(e) | Denoted::Clo(e) => e,
            };
            let de = denote_closure(e, self_calls, param_types, combinators, params)?;
            let de_is_clo = matches!(de, Denoted::Clo(_));
            let de = match de {
                Denoted::Int(e) | Denoted::Clo(e) => e,
            };
            match (dt_is_clo, de_is_clo) {
                (false, false) => {
                    let ite = combinators.cp.arith.ite_ref();
                    let applied = kernel::app3(ite, dc, dt, de);
                    let int_ty = combinators.cp.arith.int_ty();
                    debug_assert_has_type(&combinators.cp.arith.p, &applied, &int_ty, "denote_closure: If (Int branches)");
                    Some(Denoted::Int(applied))
                }
                (true, true) => {
                    // `Denoted::Clo` doesn't carry its arity: `return_type_of` re-derives it structurally, in
                    // lockstep with every `Clo`-producing arm above, so two branches of different arity are
                    // rejected here rather than left for the kernel to reject.
                    let t_arity = return_type_of(store, t, ret_arity, ret_idx, param_types).flatten()?;
                    let e_arity = return_type_of(store, e, ret_arity, ret_idx, param_types).flatten()?;
                    if t_arity != e_arity {
                        return None;
                    }
                    let ite_clo = combinators.cp.ite_clo_ref(t_arity);
                    let applied = kernel::app3(ite_clo, dc, dt, de);
                    let clo_ty = combinators.cp.clo_ty(t_arity);
                    debug_assert_has_type(&combinators.cp.arith.p, &applied, &clo_ty, "denote_closure: If (Clo branches)");
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
            let (arity, body, is_rec) = shape::peel(store, h)?;
            if arity == 0 {
                return None;
            }
            let captures = shape::free_vars(store, body, arity, is_rec);
            let sym = combinators.register(h, &captures, param_types)?;
            if captures.is_empty() {
                return Some(Denoted::Clo(sym));
            }
            let env = build_env_expr(combinators, &captures, params, param_types)?;
            let applied = kernel::app(sym, env);
            let clo_ty = combinators.cp.clo_ty(arity);
            debug_assert_has_type(&combinators.cp.arith.p, &applied, &clo_ty, "denote_closure: capturing closure value");
            Some(Denoted::Clo(applied))
        }
        Shape::Combinator { .. } => None, // a bare `Term::Rec` is out of scope when there is a self-call,
    }
}
