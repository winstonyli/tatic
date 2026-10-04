use super::*;

// --- instantiating the universal theorem at a concrete call -------------
//
// The theorem above is a *reusable lemma*: proved once, it says nothing yet
// about any specific call until it's applied to an actual `e : Ev(params,
// v)` witness for that call's `params`. Building that witness is the
// concrete counterpart of `denote`: `denote` builds a symbolic `Int`
// expression for a `Var`/`Lit`/`Prim` term; `eval_and_prove` builds that
// same expression *and* a kernel proof that it computes to a specific
// literal, by recursing the same way `eval_concrete` does, grounded in
// `ArithPostulates::assume_prim_fact` for each primitive application (the
// concrete counterpart of postulating `Int`'s operators abstractly) and, at
// each `Var`, in a `param_facts` proof supplied by whoever introduced that
// parameter -- either `refl` for a freshly-postulated top-level literal, or
// (for a self-call's argument, itself possibly a compound expression) the
// very proof `eval_and_prove` produced when denoting it one level up.
// `build_ev_witness` then walks the same leaves `flatten_tree` already
// found, using `eval_and_prove` to discharge each leaf's path premises and
// recursing into each self-call occurrence to obtain its own witness,
// before applying the leaf's `Ev` constructor.
//
// Scope: any number of self-calls per leaf (e.g. naive Fibonacci's
// `f(n-1) + f(n-2)`), via a DP cache (`memo`) plus a congruence-based
// "recast" -- worth spelling out why the recast is needed at all. A leaf's
// own `Ev` constructor (built once, symbolically, in `build_universal`)
// expects each self-call's `e_i` argument typed *exactly*
// `Ev(denote(call_i_args, params), v_i)` -- the actual denoted expression
// of that call's arguments, not just their value (a postulated operator
// has no built-in reduction rule, so `Id`/`def_eq` can't equate, say,
// `sub_ref(8,1)` with `lit_ref(7)` on its own, even though both denote 7).
// That rules out memoizing by concrete value alone: two calls reaching the
// same value via different argument expressions (`n-1` from one caller,
// `m-2` from another) would produce witnesses whose types don't match
// wherever they're used -- confirmed empirically: an earlier attempt at
// exactly that was correctly rejected by the kernel's own re-check rather
// than silently accepted.
//
// The fix: `build_ev_witness` always computes *internally* in terms of the
// canonical literal params (`lit_ref(concrete[i])`), never a caller's own
// denoted call-argument expressions -- trivially self-consistent
// (`refl`-provable), and identical regardless of which call site reaches a
// given concrete argument tuple, so `memo` (keyed on `concrete` alone) is
// always valid to reuse. The one place this canonical form doesn't already
// match what's needed is exactly where a recursive call's result becomes
// an argument to *this* leaf's own `Ev` constructor: the caller recasts
// the canonical witness to the shape its own constructor expects via
// `kernel::sym` + `kernel::cong_n` + `kernel::transport` (congruence for
// `Ev` over the params, then transport along the resulting type equality)
// -- applied identically whether the inner call was a fresh derivation or
// a `memo` hit, so there's no separate code path for either case.
// `WITNESS_NODE_BUDGET` still guards the number of newly-*derived* calls
// (a `memo` hit doesn't count against it, since it does no new derivation).
// `prove_tail_recursive_universal`'s theorem itself never needed any of
// this -- it already covers any number of self-calls per leaf (via
// `kernel::cong_n`), so a branching-recursion term always got
// `kernel_verified = true` from the theorem's existence alone (see
// `jit.rs`); only per-call instantiation was missing it.

/// Recursively evaluates `h` (the `Var`/`Lit`/`Prim` fragment `denote` and
/// `eval_concrete` both cover) at `concrete`, building a kernel proof
/// alongside it that `denote(h, arith, params)` -- returned too, so callers
/// don't need to rebuild it separately -- equals that concrete result.
/// `param_facts[i] : Id(Int, params[i], lit_ref(concrete[i]))` is the
/// caller-supplied ground truth for each parameter (see the section docs
/// above for where it comes from).
///
/// `params`/`param_facts`, and every intermediate value this function
/// builds, need no anchoring: a postulate is a `Const` and a scope
/// parameter is a `Free` (`RELATED_WORK.md` §§69-70), so `assume_prim_fact`
/// (and recursing into a sibling sub-expression) pushing further postulates
/// onto `arith.p.globals` never shifts a value already resolved here.
pub(super) fn eval_and_prove(
    store: &TermStore,
    h: Hash,
    combinators: &mut ClosureCombinators<'_>,
    params: &[Expr],
    concrete: &[i64],
    param_facts: &[Expr],
) -> Option<(i64, Expr, Expr)> {
    match compile::classify(store, h, params.len(), None) {
        // `param_types` is always empty here: every caller of this
        // function (via `instance_from_scaffold`'s own precondition) only
        // ever runs where the *outer* frame is entirely `Int`-typed, so
        // `AppShape::ParamCall` can never legitimately classify -- passing
        // `&[]` makes `app_shape`'s own `VarCall` case fail cleanly (an
        // out-of-range lookup), the same as an explicit all-`None` array
        // would, without needing to fabricate one.
        shape @ (Shape::VarCall { .. } | Shape::CombinatorCall { .. }) => match app_shape(store, shape, &[])? {
            AppShape::LitLambdaExact { root, args, callee_param_types } => {
                eval_and_prove_call(store, root, &args, &callee_param_types, combinators, params, concrete, param_facts)
            }
            // `root`'s own saturated call returns a `Clo_k`, then the
            // extra arguments are dispatched against it directly -- see
            // `eval_and_prove_call_over`'s own docs.
            AppShape::LitLambdaOver { root, args, callee_param_types } => {
                eval_and_prove_call_over(store, root, &args, &callee_param_types, combinators, params, concrete, param_facts)
            }
            // A `Clo`-typed result (`LitLambdaPartial`) has no concrete
            // representation at all (see `instance_from_scaffold`'s own
            // docs); `ParamCall` is structurally unreachable (see above).
            AppShape::ParamCall { .. } | AppShape::LitLambdaPartial { .. } => None,
        },
        Shape::Var(i) => {
            let i = i as usize;
            Some((*concrete.get(i)?, params.get(i)?.clone(), param_facts.get(i)?.clone()))
        }
        Shape::Lit(n) => {
            let l = combinators.cp.arith.lit_ref(n);
            Some((n, l.clone(), kernel::refl(l)))
        }
        Shape::Prim(op, a, b) => {
            let (xa, da, pa) = eval_and_prove(store, a, combinators, params, concrete, param_facts)?;
            let (xb, db, pb) = eval_and_prove(store, b, combinators, params, concrete, param_facts)?;
            let fact = combinators.cp.arith.assume_prim_fact(op, xa, xb);
            let result = apply_prim_concrete(op, xa, xb);

            let int_ty = combinators.cp.arith.int_ty();
            let f = combinators.cp.arith.op_ref(op);
            let cong = kernel::cong_n(
                &int_ty,
                &int_ty,
                &f,
                &[da.clone(), db.clone()],
                &[combinators.cp.arith.lit_ref(xa), combinators.cp.arith.lit_ref(xb)],
                vec![pa, pb],
            );
            let lhs = kernel::app2(f.clone(), da, db);
            let mid = kernel::app2(f, combinators.cp.arith.lit_ref(xa), combinators.cp.arith.lit_ref(xb));
            let rhs = combinators.cp.arith.lit_ref(result);
            let proof = kernel::trans_proof(&int_ty, &lhs, &mid, &rhs, cong, fact);
            debug_assert_has_type(&combinators.cp.arith.p, &proof, &kernel::id(int_ty, lhs.clone(), rhs), "eval_and_prove: Prim proof");
            Some((result, lhs, proof))
        }
        // Mirrors the `Prim` case just above, via `assume_ite_fact`
        // instead of `assume_prim_fact`: `denote`/`ite_ref` embeds an `If`
        // as fully opaque (both branches always denoted, never
        // short-circuited), so a concrete witness needs the concrete
        // evaluation of *all three* subterms -- `t` and `e` alike, even
        // though only one is the branch `eval_concrete` actually takes --
        // to discharge `app3(ite_ref, dc, dt, de) = lit_ref(result)`.
        Shape::If(c, t, e) => {
            let (xc, dc, pc) = eval_and_prove(store, c, combinators, params, concrete, param_facts)?;
            let (xt, dt, pt) = eval_and_prove(store, t, combinators, params, concrete, param_facts)?;
            let (xe, de, pe) = eval_and_prove(store, e, combinators, params, concrete, param_facts)?;
            let fact = combinators.cp.arith.assume_ite_fact(xc, xt, xe);
            let result = if xc != 0 { xt } else { xe };

            let int_ty = combinators.cp.arith.int_ty();
            let f = combinators.cp.arith.ite_ref();
            let cong = kernel::cong_n(
                &int_ty,
                &int_ty,
                &f,
                &[dc.clone(), dt.clone(), de.clone()],
                &[combinators.cp.arith.lit_ref(xc), combinators.cp.arith.lit_ref(xt), combinators.cp.arith.lit_ref(xe)],
                vec![pc, pt, pe],
            );
            let lhs = kernel::app3(f.clone(), dc, dt, de);
            let mid = kernel::app3(f, combinators.cp.arith.lit_ref(xc), combinators.cp.arith.lit_ref(xt), combinators.cp.arith.lit_ref(xe));
            let rhs = combinators.cp.arith.lit_ref(result);
            let proof = kernel::trans_proof(&int_ty, &lhs, &mid, &rhs, cong, fact);
            debug_assert_has_type(&combinators.cp.arith.p, &proof, &kernel::id(int_ty, lhs.clone(), rhs), "eval_and_prove: If proof");
            Some((result, lhs, proof))
        }
        Shape::SelfCall(_) | Shape::OtherCall | Shape::Combinator { .. } => None,
    }
}

/// `eval_and_prove`'s own `AppShape::LitLambdaExact` case, split out for
/// its own size: a self-call argument (or leaf expression) that creates
/// and calls a literal lambda `root` (own arity `root_arity`) to produce a
/// fresh `Int`. See `call_eq_ref`'s own docs for why this needs a
/// computation-rule axiom rather than denoting `root`'s body directly, and
/// this module's own docs for the restriction this is scoped to (`root`'s
/// own body must be `Var`/`Lit`/`Prim`/`If`, no further `Abs`/`App`, and
/// every one of `root`'s own params/captures must be `Int`-typed --
/// `call_eq_ref` itself enforces both and returns `None` otherwise).
///
/// `args` is in *application* order (`args[0]` is `root`'s first-applied
/// argument, `Var(root_arity-1)`) -- this already matches `call_ref`'s own
/// argument order directly (no `arity-1-j` remapping needed the way
/// `denote_closure`'s own arm needs it, since that also has to look up
/// each argument's own *type*, `Int` or `Clo`; here every argument is
/// already known to be `Int`).
#[allow(clippy::too_many_arguments)]
pub(super) fn eval_and_prove_call(
    store: &TermStore,
    root: Hash,
    args: &[Hash],
    callee_param_types: &[Option<usize>],
    combinators: &mut ClosureCombinators<'_>,
    params: &[Expr],
    concrete: &[i64],
    param_facts: &[Expr],
) -> Option<(i64, Expr, Expr)> {
    if callee_param_types.iter().any(Option::is_some) {
        return None;
    }

    // Evaluate each argument in the *outer* frame, application order.
    let mut arg_triples = Vec::with_capacity(args.len());
    for &a in args {
        let (x, d, p) = eval_and_prove(store, a, combinators, params, concrete, param_facts)?;
        arg_triples.push((x, d, p));
    }

    // Resolve `root`'s own captures against the *outer* frame too --
    // mirrors this function's sibling's own `Term::Var(i)` case, just
    // picking existing entries (`rel`, the capture's own relative index,
    // is the outer frame's own absolute `Var` index) rather than
    // recursing, the same way `build_env_expr` does for the symbolic
    // side.
    let (root_arity, root_body, root_is_rec) = compile::peel(store, root)?;
    let root_captures = compile::free_vars(store, root_body, root_arity, root_is_rec);
    let mut cap_triples = Vec::with_capacity(root_captures.len());
    for &rel in &root_captures {
        let rel = rel as usize;
        let x = *concrete.get(rel)?;
        let d = params.get(rel)?.clone();
        let p = param_facts.get(rel)?.clone();
        cap_triples.push((x, d, p));
    }

    eval_and_prove_direct_call(store, root, combinators, &cap_triples, &arg_triples)
}

/// `eval_and_prove_call`'s own reusable core, once `root`'s own captures
/// and call args have each already been resolved to a concrete `(i64,
/// denoted, proof)` triple -- factored out so `eval_and_prove_call`'s
/// over-application sibling (a self-call argument that over-applies a
/// literal lambda returning a closure, then calls the result -- see
/// `AppShape::LitLambdaOver`) can reuse this same `call_eq_ref`-based
/// construction for its own *inner*, concretely-chosen closure, whose own
/// captures resolve against `root`'s own frame while its own call args
/// (the over-application's *extra* arguments) resolve against the
/// *outer* frame -- two distinct frames `eval_and_prove_call`'s own
/// single-frame signature can't express. `cap_triples` must be in exactly
/// `compile::free_vars(store, root_body, root_arity, root_is_rec)`'s own
/// order (the same invariant `eval_and_prove_call` above already
/// maintains) -- every caller re-derives `root_body`/`root_arity` from
/// `root` itself (cheap, deterministic, and `compile::peel`/
/// `compile::free_vars` are already needed again just below) rather than
/// threading them through as extra parameters.
pub(super) fn eval_and_prove_direct_call(
    store: &TermStore,
    root: Hash,
    combinators: &mut ClosureCombinators<'_>,
    cap_triples: &[(i64, Expr, Expr)],
    arg_triples: &[(i64, Expr, Expr)],
) -> Option<(i64, Expr, Expr)> {
    let (root_arity, root_body, root_is_rec) = compile::peel(store, root)?;
    let root_captures = compile::free_vars(store, root_body, root_arity, root_is_rec);
    let n = root_captures.len();

    // The computation-rule axiom for `root` -- its own first use for this
    // `Hash` may lazily push (and, transitively, `call_ref`/`mk_env_ref`
    // for this exact shape too).
    let axiom = combinators.call_eq_ref(root)?;

    let sig: Vec<Option<usize>> = vec![None; n];
    let int_ty = combinators.cp.arith.int_ty();

    // Congruence bridge: `call_ref(root)` applied to the outer frame's own
    // *denoted* env/args equals `call_ref(root)` applied to their
    // *literal* values -- in up to two steps (the `Env_sig` argument, then
    // the `root_arity` `Int` arguments), since `kernel::cong_n` needs one
    // uniform domain type and `call_ref`'s own argument list mixes
    // `Env_sig` (if `root` captures) with `Int`.
    let env_bridge = if n > 0 {
        let mk_env_expr = combinators.cp.mk_env_ref(&sig);
        let env_ty_expr = combinators.cp.env_ty(&sig);
        let cd: Vec<Expr> = cap_triples.iter().map(|(_, d, _)| d.clone()).collect();
        let lit_c: Vec<Expr> = cap_triples
            .iter()
            .map(|&(x, _, _)| {
                combinators.cp.arith.lit(x);
                combinators.cp.arith.lit_ref(x)
            })
            .collect();
        let cp: Vec<Expr> = cap_triples.iter().map(|(_, _, p)| p.clone()).collect();
        let env_eq = kernel::cong_n(&int_ty, &env_ty_expr, &mk_env_expr, &cd, &lit_c, cp);
        let denoted_env = apply_n(mk_env_expr.clone(), cd);
        let lit_env = apply_n(mk_env_expr, lit_c);
        Some((denoted_env, lit_env, env_eq, env_ty_expr))
    } else {
        None
    };

    let call_fn = combinators.call_ref(root, &root_captures, &[])?;
    let d_args: Vec<Expr> = arg_triples.iter().map(|(_, d, _)| d.clone()).collect();
    let lit_args: Vec<Expr> = arg_triples
        .iter()
        .map(|&(x, _, _)| {
            combinators.cp.arith.lit(x);
            combinators.cp.arith.lit_ref(x)
        })
        .collect();
    let p_args: Vec<Expr> = arg_triples.iter().map(|(_, _, p)| p.clone()).collect();

    let (call_at_denoted, call_env_to_lit_step) = match &env_bridge {
        Some((denoted_env, lit_env, env_eq, env_ty_expr)) => {
            // cong1 over call_ref(root)'s own `Env_sig` argument, the
            // `root_arity` `Int` args held fixed at their *denoted*
            // values.
            let mut f_env_body = kernel::app(kernel::shift(&call_fn, 0, 1), kernel::var(0));
            for d in &d_args {
                f_env_body = kernel::app(f_env_body, kernel::shift(d, 0, 1));
            }
            let f_env = kernel::lam(env_ty_expr.clone(), f_env_body);
            let step = kernel::cong1(env_ty_expr, &int_ty, &f_env, denoted_env.clone(), lit_env.clone(), env_eq.clone());
            let call_at_denoted = apply_n(call_fn.clone(), std::iter::once(denoted_env.clone()).chain(d_args.iter().cloned()));
            (call_at_denoted, step)
        }
        None => {
            let call_at_denoted = apply_n(call_fn.clone(), d_args.iter().cloned());
            let step = kernel::refl(call_at_denoted.clone());
            (call_at_denoted, step)
        }
    };

    // cong_n over call_ref(root)'s own `root_arity` `Int` arguments,
    // `Env_sig` (if any) held fixed at its *literal* value from the step
    // above.
    let f_ints = match &env_bridge {
        Some((_, lit_env, _, _)) => apply_n(call_fn.clone(), std::iter::once(lit_env.clone())),
        None => call_fn.clone(),
    };
    let args_eq = kernel::cong_n(&int_ty, &int_ty, &f_ints, &d_args, &lit_args, p_args);
    let call_at_lit_env_denoted_args = apply_n(f_ints.clone(), d_args);
    let call_at_lit_env_lit_args = apply_n(f_ints, lit_args);

    let bridge = kernel::trans_proof(
        &int_ty,
        &call_at_denoted,
        &call_at_lit_env_denoted_args,
        &call_at_lit_env_lit_args,
        call_env_to_lit_step,
        args_eq,
    );

    // Instantiate the axiom at the literal captures/args -- ascending
    // `Var`-index order, matching `call_eq_ref`'s own quantification
    // order (captures, slot order, then `root`'s own params, ascending;
    // `args` is in application order, i.e. *descending* `Var`-index order,
    // so only it needs reversing).
    let axiom_args: Vec<Expr> = cap_triples
        .iter()
        .map(|&(x, _, _)| combinators.cp.arith.lit_ref(x)) // already lit()'d building `lit_c` above
        .chain(arg_triples.iter().rev().map(|&(x, _, _)| combinators.cp.arith.lit_ref(x)))
        .collect();
    let axiom_at_literals = apply_n(axiom.clone(), axiom_args);

    // Concrete value of `root`'s own body, at the literal args/captures --
    // recurses into the *same* `Var`/`Lit`/`Prim`/`If` fragment
    // `eval_and_prove` already covers (`root`'s own body is restricted to
    // it by `call_eq_ref`), so no new base cases are needed. Frame layout
    // mirrors `call_eq_ref`'s own `params_full` construction exactly:
    // `root`'s own params first (ascending `Var` order), then captures
    // sparsely placed at `root_arity + rel` for each one's own relative
    // index.
    let mut inner_params = Vec::with_capacity(root_arity + n);
    let mut inner_concrete = Vec::with_capacity(root_arity + n);
    let mut inner_facts = Vec::with_capacity(root_arity + n);
    for &(x, _, _) in arg_triples.iter().rev() {
        combinators.cp.arith.lit(x);
        let l = combinators.cp.arith.lit_ref(x);
        inner_params.push(l.clone());
        inner_concrete.push(x);
        inner_facts.push(kernel::refl(l));
    }
    if let Some(&max_rel) = root_captures.iter().max() {
        let pad_len = root_arity + max_rel as usize + 1;
        let (fx0, _, _) = cap_triples[0];
        combinators.cp.arith.lit(fx0);
        let filler = combinators.cp.arith.lit_ref(fx0);
        while inner_params.len() < pad_len {
            inner_concrete.push(fx0);
            inner_params.push(filler.clone());
            inner_facts.push(kernel::refl(filler.clone()));
        }
        for (j, &rel) in root_captures.iter().enumerate() {
            let (cx, _, _) = cap_triples[j];
            combinators.cp.arith.lit(cx);
            let l = combinators.cp.arith.lit_ref(cx);
            let idx = root_arity + rel as usize;
            inner_concrete[idx] = cx;
            inner_params[idx] = l.clone();
            inner_facts[idx] = kernel::refl(l);
        }
    }
    // `eval_and_prove`'s own recursion below (over `root_body`) may push
    // further postulates (`assume_prim_fact`/`assume_ite_fact`, fresh
    // literals); a pushed `Const` shifts nothing already built above
    // (`RELATED_WORK.md` §69), so nothing here needs re-resolving after it.
    let (result, denote_lit, proof_d) = eval_and_prove(store, root_body, combinators, &inner_params, &inner_concrete, &inner_facts)?;

    // Chain: call_at_denoted = call_at_lit_env_lit_args (bridge)
    //      = denote(root_body, [lit_args, lit_caps]) (axiom_at_literals)
    //      = lit_ref(result) (proof_d)
    let int_ty2 = combinators.cp.arith.int_ty();
    let result_ref = combinators.cp.arith.lit_ref(result);
    let bridge_to_denote =
        kernel::trans_proof(&int_ty2, &call_at_denoted, &call_at_lit_env_lit_args, &denote_lit, bridge, axiom_at_literals);
    let final_proof = kernel::trans_proof(&int_ty2, &call_at_denoted, &denote_lit, &result_ref, bridge_to_denote, proof_d);
    debug_assert_has_type(
        &combinators.cp.arith.p,
        &final_proof,
        &kernel::id(int_ty2, call_at_denoted.clone(), result_ref),
        "eval_and_prove_call: final proof",
    );
    Some((result, call_at_denoted, final_proof))
}

/// `register`/`mk_env_ref`'s own value expression for `inner` (`clo_eq_ref`'s
/// own `inner_t`/`inner_e` -- a bare literal lambda embedded directly in
/// some `root`'s own body, one branch of the `If` its saturated call
/// chooses between), at the *concrete literal* values `root`'s own inner
/// frame (`inner_params`/`inner_concrete`/`inner_facts`) holds for
/// `inner`'s own captures -- the same construction `clo_eq_ref`'s own
/// `value_expr` closure builds *abstractly* (see its docs), specialized
/// to literals, the same dual use `denote`/`eval_and_prove` themselves
/// already rely on (structurally identical either way, since neither
/// `register` nor `mk_env_ref` inspect the *values* passed to them, only
/// combine them). This is what lets `axiom_at_literals`'s own RHS
/// (`clo_eq_ref`'s axiom, instantiated) be matched, term-for-term,
/// against a value built here independently. Also returns `inner`'s own
/// captures resolved to `(i64, Expr, Expr)` triples, ready for
/// `eval_and_prove_direct_call` once a value is actually *called* (not
/// merely *created*) -- whichever branch the `If` concretely selects.
/// `None` if `inner` is itself self-recursive (not expected to arise here
/// -- `clo_eq_ref`'s own classification already requires a bare
/// `Term::Abs`, never `Term::Rec` -- but checked rather than assumed).
/// A concrete `(value, denoted, proof)` triple per resolved argument or
/// capture -- shared alias for the `Vec` of these `eval_and_prove_call`'s
/// own family of functions passes around, just to keep the type simple
/// enough for `clippy::type_complexity` not to flag it.
pub(super) type ValueTriples = Vec<(i64, Expr, Expr)>;

/// `build_clo_call_bridge`'s own return: `(call_at_denoted,
/// call_at_lit_env_lit_args, bridge, axiom_at_literals, inner_params,
/// inner_concrete, inner_facts, k, shape)` -- see its own docs. A type
/// alias purely to keep this under `clippy::type_complexity`'s own
/// threshold, same rationale as `ValueTriples`.
pub(super) type CloCallBridge = (Expr, Expr, Expr, Expr, Vec<Expr>, Vec<i64>, Vec<Expr>, usize, ClosureRhsShape);

pub(super) fn inner_closure_literal_value(
    combinators: &mut ClosureCombinators<'_>,
    inner: Hash,
    inner_params: &[Expr],
    inner_concrete: &[i64],
    inner_facts: &[Expr],
) -> Option<(Expr, ValueTriples)> {
    let (inner_arity, inner_body, inner_is_rec) = compile::peel(combinators.store, inner)?;
    if inner_is_rec {
        return None;
    }
    let inner_captures = compile::free_vars(combinators.store, inner_body, inner_arity, inner_is_rec);
    let mut cap_triples = Vec::with_capacity(inner_captures.len());
    for &rel in &inner_captures {
        let rel = rel as usize;
        let x = *inner_concrete.get(rel)?;
        let d = inner_params.get(rel)?.clone();
        let p = inner_facts.get(rel)?.clone();
        cap_triples.push((x, d, p));
    }
    let inner_dummy: Vec<Option<usize>> = vec![None; inner_captures.iter().map(|&r| r as usize + 1).max().unwrap_or(0)];
    let sym = combinators.register(inner, &inner_captures, &inner_dummy)?;
    let value = if cap_triples.is_empty() {
        sym
    } else {
        let inner_sig: Vec<Option<usize>> = vec![None; cap_triples.len()];
        let lit_c: Vec<Expr> = cap_triples
            .iter()
            .map(|&(x, _, _)| {
                combinators.cp.arith.lit(x);
                combinators.cp.arith.lit_ref(x)
            })
            .collect();
        let mk_env_expr = combinators.cp.mk_env_ref(&inner_sig);
        kernel::app(sym, apply_n(mk_env_expr, lit_c))
    };
    Some((value, cap_triples))
}

/// `eval_and_prove`'s own `AppShape::LitLambdaOver` case: a self-call
/// argument (or leaf expression) that over-applies a literal lambda
/// `root` -- `root`'s own saturated call (its first `root_arity`
/// arguments) returns a `Clo_k`, and the *extra* `k` arguments are then
/// dispatched against that closure directly. See `clo_eq_ref`'s
/// own docs for why this needs a second computation-rule axiom (root's
/// saturated call is just as opaque, `Clo`-typed, as a `call_eq_ref`-
/// covered `Int`-typed one), `ite_clo_eq_ref`'s own docs for the branch-
/// selection bridge an `If`-shaped body needs, and `apply_clo_eq_ref`'s
/// own docs for tying whichever closure value is concretely produced to
/// `call_ref(root)`'s own value.
///
/// Guarded by `combinator_return_type(root) == Some(Some(k))` and
/// `args.len() == root_arity + k` (the whole thing fully resolves to
/// `Int` -- matches `denote_with_placeholders`'s own identical
/// requirement, enforced there by calling the `Clo_k` value directly with
/// exactly `k` `Int` arguments) -- `None` otherwise, not an error: a
/// partial or chained over-application, or one whose own saturated call stays `Int`
/// (`call_eq_ref`'s own shape, handled by this function's sibling), is
/// genuinely out of scope here.
/// Shared core of `eval_and_prove_call_over`'s own preamble -- given a
/// combinator `subject` whose own saturated call denotes a `Clo_k`
/// (`combinator_return_type`), its own `sat_arg_triples` (concrete
/// `(value, denoted, proof)` triples for its own saturating arguments,
/// already evaluated by the caller against whichever frame those
/// arguments actually live in -- the *outer* frame for `root` itself, or
/// `root`'s own *inner* frame for a `Call`'s own further indirection's
/// `g` -- and `subject`'s own captures resolved against
/// `outer_{params,concrete,facts}`), builds `subject`'s own `clo_eq_ref`
/// axiom instantiated at literals (`axiom_at_literals`, the formula this
/// axiom's RHS denotes once concretized) together with the congruence
/// bridge proving `subject`'s own saturated call (denoted against
/// `outer_*`) equals that literal instantiation (`call_at_denoted`/
/// `call_at_lit_env_lit_args`/`bridge`), plus `subject`'s own *inner*
/// frame (`inner_params`/`inner_concrete`/`inner_facts`, arity-then-
/// captures, densely laid out) for a caller that needs to recurse into
/// `subject`'s own body (a branch condition, a further indirect call's
/// own args, ...).
///
/// Originally `eval_and_prove_call_over`'s own inline preamble, specific
/// to `root`; factored out, parametrized over `subject`, so
/// `resolve_closure_shape_to_leaf`'s own `Call` arm can build the
/// identical thing for a further indirect call's own callee, recursively.
#[allow(clippy::too_many_arguments)]
pub(super) fn build_clo_call_bridge(
    store: &TermStore,
    combinators: &mut ClosureCombinators<'_>,
    subject: Hash,
    sat_arg_triples: &[(i64, Expr, Expr)],
    outer_params: &[Expr],
    outer_concrete: &[i64],
    outer_facts: &[Expr],
) -> Option<CloCallBridge> {
    let (subject_arity, subject_body, subject_is_rec) = compile::peel(store, subject)?;
    let k = match combinator_return_type(store, subject) {
        Some(Some(k)) => k,
        _ => return None,
    };
    if sat_arg_triples.len() != subject_arity {
        return None;
    }

    let subject_captures = compile::free_vars(store, subject_body, subject_arity, subject_is_rec);
    let mut cap_triples = Vec::with_capacity(subject_captures.len());
    for &rel in &subject_captures {
        let rel = rel as usize;
        let x = *outer_concrete.get(rel)?;
        let d = outer_params.get(rel)?.clone();
        let p = outer_facts.get(rel)?.clone();
        cap_triples.push((x, d, p));
    }
    let n = subject_captures.len();

    // The `Clo_k`-typed computation-rule axiom for `subject`'s own
    // saturated call -- its own first use for this `Hash` may lazily push
    // (and transitively `call_ref`/`mk_env_ref`/`register`/`ite_clo_ref`
    // for this exact shape too, see its own docs).
    let (axiom, shape) = combinators.clo_eq_ref(subject)?;

    let sig: Vec<Option<usize>> = vec![None; n];

    // Congruence bridge over `call_ref(subject)`'s own arguments --
    // identical construction to `eval_and_prove_direct_call`'s own (see
    // its docs), generalized to the `Clo_k` codomain here instead of
    // `Int`. `int_ty` is an already-pushed postulate's `Const`; `clo_ty`
    // is pure and never pushes -- a later push elsewhere can't invalidate
    // either (`RELATED_WORK.md` §69).
    let env_bridge = if n > 0 {
        let mk_env_expr = combinators.cp.mk_env_ref(&sig);
        let env_ty_expr = combinators.cp.env_ty(&sig);
        let cd: Vec<Expr> = cap_triples.iter().map(|(_, d, _)| d.clone()).collect();
        let lit_c: Vec<Expr> = cap_triples
            .iter()
            .map(|&(x, _, _)| {
                combinators.cp.arith.lit(x);
                combinators.cp.arith.lit_ref(x)
            })
            .collect();
        let cp: Vec<Expr> = cap_triples.iter().map(|(_, _, p)| p.clone()).collect();
        let int_ty = combinators.cp.arith.int_ty();
        let env_eq = kernel::cong_n(&int_ty, &env_ty_expr, &mk_env_expr, &cd, &lit_c, cp);
        let denoted_env = apply_n(mk_env_expr.clone(), cd);
        let lit_env = apply_n(mk_env_expr, lit_c);
        Some((denoted_env, lit_env, env_eq, env_ty_expr))
    } else {
        None
    };

    let call_fn = combinators.call_ref(subject, &subject_captures, &[])?;
    let d_sat_args: Vec<Expr> = sat_arg_triples.iter().map(|(_, d, _)| d.clone()).collect();
    let lit_sat_args: Vec<Expr> = sat_arg_triples
        .iter()
        .map(|&(x, _, _)| {
            combinators.cp.arith.lit(x);
            combinators.cp.arith.lit_ref(x)
        })
        .collect();
    let p_sat_args: Vec<Expr> = sat_arg_triples.iter().map(|(_, _, p)| p.clone()).collect();

    let (call_at_denoted, call_env_to_lit_step) = match &env_bridge {
        Some((denoted_env, lit_env, env_eq, env_ty_expr)) => {
            let mut f_env_body = kernel::app(kernel::shift(&call_fn, 0, 1), kernel::var(0));
            for d in &d_sat_args {
                f_env_body = kernel::app(f_env_body, kernel::shift(d, 0, 1));
            }
            let f_env = kernel::lam(env_ty_expr.clone(), f_env_body);
            let clo_ty = combinators.cp.clo_ty(k);
            let step = kernel::cong1(env_ty_expr, &clo_ty, &f_env, denoted_env.clone(), lit_env.clone(), env_eq.clone());
            let call_at_denoted = apply_n(call_fn.clone(), std::iter::once(denoted_env.clone()).chain(d_sat_args.iter().cloned()));
            (call_at_denoted, step)
        }
        None => {
            let call_at_denoted = apply_n(call_fn.clone(), d_sat_args.iter().cloned());
            let step = kernel::refl(call_at_denoted.clone());
            (call_at_denoted, step)
        }
    };

    let f_ints = match &env_bridge {
        Some((_, lit_env, _, _)) => apply_n(call_fn.clone(), std::iter::once(lit_env.clone())),
        None => call_fn.clone(),
    };
    let int_ty = combinators.cp.arith.int_ty();
    let clo_ty = combinators.cp.clo_ty(k);
    let args_eq = kernel::cong_n(&int_ty, &clo_ty, &f_ints, &d_sat_args, &lit_sat_args, p_sat_args);
    let call_at_lit_env_denoted_args = apply_n(f_ints.clone(), d_sat_args);
    let call_at_lit_env_lit_args = apply_n(f_ints, lit_sat_args);

    let bridge = kernel::trans_proof(
        &clo_ty,
        &call_at_denoted,
        &call_at_lit_env_denoted_args,
        &call_at_lit_env_lit_args,
        call_env_to_lit_step,
        args_eq,
    );

    // Instantiate the axiom at the literal captures/saturating args --
    // same order convention `eval_and_prove_direct_call` already uses.
    let axiom_args: Vec<Expr> = cap_triples
        .iter()
        .map(|&(x, _, _)| combinators.cp.arith.lit_ref(x))
        .chain(sat_arg_triples.iter().rev().map(|&(x, _, _)| combinators.cp.arith.lit_ref(x)))
        .collect();
    let axiom_at_literals = apply_n(axiom.clone(), axiom_args);

    // `subject`'s own inner frame -- same sparse construction
    // `eval_and_prove_direct_call` builds for its own recursive body
    // evaluation, reused here so a caller's own further recursion
    // (`cond`, a further nested call's own args, ...) can resolve
    // `subject`'s own captures (relative to `subject`'s own frame).
    let mut inner_params = Vec::with_capacity(subject_arity + n);
    let mut inner_concrete = Vec::with_capacity(subject_arity + n);
    let mut inner_facts = Vec::with_capacity(subject_arity + n);
    for &(x, _, _) in sat_arg_triples.iter().rev() {
        combinators.cp.arith.lit(x);
        let l = combinators.cp.arith.lit_ref(x);
        inner_params.push(l.clone());
        inner_concrete.push(x);
        inner_facts.push(kernel::refl(l));
    }
    if let Some(&max_rel) = subject_captures.iter().max() {
        let pad_len = subject_arity + max_rel as usize + 1;
        let (fx0, _, _) = cap_triples[0];
        combinators.cp.arith.lit(fx0);
        let filler = combinators.cp.arith.lit_ref(fx0);
        while inner_params.len() < pad_len {
            inner_concrete.push(fx0);
            inner_params.push(filler.clone());
            inner_facts.push(kernel::refl(filler.clone()));
        }
        for (j, &rel) in subject_captures.iter().enumerate() {
            let (cx, _, _) = cap_triples[j];
            combinators.cp.arith.lit(cx);
            let l = combinators.cp.arith.lit_ref(cx);
            let idx = subject_arity + rel as usize;
            inner_concrete[idx] = cx;
            inner_params[idx] = l.clone();
            inner_facts[idx] = kernel::refl(l);
        }
    }

    Some((call_at_denoted, call_at_lit_env_lit_args, bridge, axiom_at_literals, inner_params, inner_concrete, inner_facts, k, shape))
}

/// Resolves `subject`'s own `ClosureRhsShape` (whichever kind
/// `clo_eq_ref(subject)` produced, already reflected in
/// `call_at_denoted`/`call_at_lit_env_lit_args`/`bridge`/
/// `axiom_at_literals` -- `build_clo_call_bridge`'s own output for
/// `subject`) down to a genuine literal-lambda leaf, given `subject`'s
/// own concrete inner frame. Originally `eval_and_prove_call_over`'s own
/// inline `match shape` block; factored out so a `Call` shape's own
/// further indirection can recurse through this same resolution,
/// composing with `IfTree`'s nested branches or a further `Pap` exactly
/// the way each of those already composes with itself.
///
/// `extra_arg_triples`/`k` are the *outermost* over-application's own
/// values -- invariant across however many `Call` hops this recurses
/// through (there is only ever one final `apply_*_eq_ref` step in the
/// whole chain, applied once `chosen` is finally reached), so every
/// recursive call threads the same ones through unchanged.
///
/// Returns `(chosen, chosen_cap_triples, chosen_arg_triples, chosen_value,
/// subject_to_chosen, apply_eq_chosen)`: which `Hash` to recurse into,
/// its own captures resolved to literal triples, the full argument list
/// for that recursive call (`chosen_arg_triples` -- just
/// `extra_arg_triples` when `chosen` is already exactly `k`-ary;
/// `chosen`'s own supplied args *then* `extra_arg_triples` when `chosen`
/// is a `Pap`'s own `g`, whose own arity is `s + k`), a proof that
/// `call_at_denoted` (the parameter, `subject`'s own saturated call)
/// equals `chosen_value`, and the instantiated `apply_*_eq_ref` fact
/// bridging `chosen_value`, called directly, down to a direct call on
/// `chosen`.
#[allow(clippy::too_many_arguments)]
pub(super) fn resolve_closure_shape_to_leaf(
    store: &TermStore,
    combinators: &mut ClosureCombinators<'_>,
    call_at_denoted: &Expr,
    call_at_lit_env_lit_args: &Expr,
    bridge: &Expr,
    axiom_at_literals: &Expr,
    shape: &ClosureRhsShape,
    inner_params: &[Expr],
    inner_concrete: &[i64],
    inner_facts: &[Expr],
    k: usize,
    extra_arg_triples: &[(i64, Expr, Expr)],
) -> Option<(Hash, ValueTriples, ValueTriples, Expr, Expr, Expr)> {

    match shape {
        ClosureRhsShape::IfTree(tree) => {
            let leaf_shapes = classify_closure_if_tree_leaves(store, tree, k)?;
            let (resolution, tree_value_at_literals, leaf_value, tree_to_leaf_value) =
                resolve_closure_if_tree(store, combinators, tree, &leaf_shapes, inner_params, inner_concrete, inner_facts, k, extra_arg_triples)?;

            let call_at_denoted_here = call_at_denoted.clone();
            let call_at_lit_env_lit_args_here = call_at_lit_env_lit_args.clone();
            let bridge_here = bridge.clone();
            let axiom_at_literals_here = axiom_at_literals.clone();
            let clo_ty = combinators.cp.clo_ty(k);

            // `axiom_at_literals`'s own RHS is exactly the tree's own
            // formula at literals (`tree_value_at_literals`, independently
            // reconstructed here the same way `resolve_closure_if_tree`'s
            // own recursive descent builds it) -- bridge `subject`'s call
            // to that formula, then to the concretely-reached leaf's own
            // *canonical* value, via `tree_to_leaf_value` (one
            // `ite_clo_eq_ref` step per internal node on the path actually
            // taken). For a `Direct` (`Abs`/`Pap`) leaf, that canonical
            // value already *is* the final `chosen_value`; for an
            // `Indirect` (`Call`-shaped) leaf, one further bridge
            // (`leaf_to_chosen`, already built by `resolve_closure_if_tree`'s
            // own recursion) is composed below.
            let root_to_tree_value =
                kernel::trans_proof(&clo_ty, &call_at_denoted_here, &call_at_lit_env_lit_args_here, &tree_value_at_literals, bridge_here, axiom_at_literals_here);
            let root_to_leaf_value = kernel::trans_proof(&clo_ty, &call_at_denoted_here, &tree_value_at_literals, &leaf_value, root_to_tree_value, tree_to_leaf_value);

            match resolution {
                IfTreeLeafResolution::Direct { chosen, cap_triples: chosen_cap_triples, arg_prefix: chosen_arg_prefix } => {
                    // `apply_clo_eq_ref(chosen)` (a bare `Abs`-shaped leaf,
                    // exactly `k`-ary already) or `apply_pap_eq_ref(chosen, s)`
                    // (a `Pap`-shaped leaf, `chosen` there being `g`, whose
                    // own arity is `s + k`) -- `chosen_arg_prefix` is empty
                    // for the former and non-empty for the latter (a
                    // `Pap`-shaped leaf's own classification requires at
                    // least one supplied arg, see
                    // `classify_closure_if_tree_leaf`), so it doubles as the
                    // dispatch signal here without threading a separate
                    // flag.
                    let s = chosen_arg_prefix.len();
                    let apply_axiom = if s == 0 { combinators.apply_clo_eq_ref(chosen)? } else { combinators.apply_pap_eq_ref(chosen, s)? };

                    let root_to_chosen = root_to_leaf_value.clone();
                    let chosen_value_lit = leaf_value.clone();

                    // Instantiate at `chosen`'s own raw literal captures
                    // (ascending, matching `chosen_cap_triples`'s own order),
                    // then -- for a `Pap`-shaped leaf only -- its own supplied
                    // args' *denoted* values in the same (unreversed) order
                    // `chosen_value_lit`'s own `pap_ref(...)` formula already
                    // used (matching `ClosureRhsShape::Pap`'s own identical
                    // convention, see its own docs for why it isn't reversed the
                    // way the extra args are), then the extra args' own *denoted*
                    // values (ascending -- `extra_arg_triples` is in application
                    // order, so reversed here, the same convention
                    // `eval_and_prove_direct_call`'s own `axiom_args` already
                    // uses). Both axioms are universally quantified over
                    // `Int`-typed values, so instantiating directly at these
                    // denoted expressions needs no separate "route through
                    // literals first" step.
                    let apply_axiom_args: Vec<Expr> = chosen_cap_triples
                        .iter()
                        .map(|&(x, _, _)| combinators.cp.arith.lit_ref(x))
                        .chain(chosen_arg_prefix.iter().map(|(_, d, _)| d.clone()))
                        .chain(extra_arg_triples.iter().rev().map(|(_, d, _)| d.clone()))
                        .collect();
                    let apply_eq_chosen = apply_n(apply_axiom.clone(), apply_axiom_args);

                    let mut chosen_arg_triples = chosen_arg_prefix;
                    chosen_arg_triples.extend(extra_arg_triples.iter().cloned());

                    Some((chosen, chosen_cap_triples, chosen_arg_triples, chosen_value_lit, root_to_chosen, apply_eq_chosen))
                }
                IfTreeLeafResolution::Indirect { chosen, chosen_cap_triples, chosen_arg_triples, chosen_value, leaf_to_chosen, apply_eq_chosen } => {
                    // The reached leaf was itself `Call`-shaped:
                    // `leaf_value` (this level's own canonical value for
                    // it) already has its own further resolution down to a
                    // genuine literal-lambda `chosen`, fully composed by
                    // `resolve_closure_if_tree`'s own recursive
                    // `resolve_closure_shape_to_leaf` call -- compose
                    // `root_to_leaf_value` with `leaf_to_chosen` to reach
                    // `chosen_value`, and reuse `apply_eq_chosen` as-is (it
                    // already covers the full "call with all args" fact --
                    // building a second one here would double-count).
                    let root_to_chosen = kernel::trans_proof(&clo_ty, &call_at_denoted_here, &leaf_value, &chosen_value, root_to_leaf_value, leaf_to_chosen);
                    Some((chosen, chosen_cap_triples, chosen_arg_triples, chosen_value, root_to_chosen, apply_eq_chosen))
                }
            }
        }
        ClosureRhsShape::Pap { g, args } => {
            let g = *g;
            let (g_arity, g_body, g_is_rec) = compile::peel(store, g)?;
            let g_captures = compile::free_vars(store, g_body, g_arity, g_is_rec);
            let s = args.len();

            let mut g_cap_triples = Vec::with_capacity(g_captures.len());
            for &rel in &g_captures {
                let rel = rel as usize;
                let x = *inner_concrete.get(rel)?;
                let d = inner_params.get(rel)?.clone();
                let p = inner_facts.get(rel)?.clone();
                g_cap_triples.push((x, d, p));
            }

            let mut supplied_triples = Vec::with_capacity(s);
            for &a in args {
                let (x, d, p) = eval_and_prove(store, a, combinators, inner_params, inner_concrete, inner_facts)?;
                supplied_triples.push((x, d, p));
            }

            // `pap_at_denoted`: `pap_ref(g, s)(g_env?, denote(args[0],
            // subject's own literal inner frame), ...)` -- built
            // independently here, matching `clo_eq_ref_pap`'s own
            // RHS-formula exactly (same construction, `params_full` now
            // subject's own *concrete* literal values instead of abstract
            // quantified vars), so it's syntactically the same term
            // `axiom_at_literals`'s own (opaque, uninstantiated) RHS
            // denotes once substituted -- mirrors `ite_at_denote_c`'s
            // identical role in the `IfTree` branch above.
            let g_dummy: Vec<Option<usize>> = vec![None; g_captures.iter().map(|&r| r as usize + 1).max().unwrap_or(0)];
            let pap_fn = combinators.pap_ref(g, s, &g_dummy)?;

            let call_at_denoted_here = call_at_denoted.clone();
            let call_at_lit_env_lit_args_here = call_at_lit_env_lit_args.clone();
            let bridge_here = bridge.clone();
            let axiom_at_literals_here = axiom_at_literals.clone();
            let clo_ty = combinators.cp.clo_ty(k);

            let g_env_denoted = if g_cap_triples.is_empty() {
                None
            } else {
                let g_sig: Vec<Option<usize>> = vec![None; g_captures.len()];
                let mk_env_expr = combinators.cp.mk_env_ref(&g_sig);
                let cd: Vec<Expr> = g_cap_triples.iter().map(|(_, d, _)| d.clone()).collect();
                Some(apply_n(mk_env_expr, cd))
            };
            let d_supplied: Vec<Expr> = supplied_triples.iter().map(|(_, d, _)| d.clone()).collect();
            let mut pap_args = Vec::with_capacity(1 + s);
            pap_args.extend(g_env_denoted);
            pap_args.extend(d_supplied);
            let pap_at_denoted = apply_n(pap_fn, pap_args);

            let root_to_chosen =
                kernel::trans_proof(&clo_ty, &call_at_denoted_here, &call_at_lit_env_lit_args_here, &pap_at_denoted, bridge_here, axiom_at_literals_here);

            // `apply_pap_eq_ref(g, s)` -- its own first use for this
            // `(g, s)` may lazily push.
            let apply_axiom = combinators.apply_pap_eq_ref(g, s)?;

            // Instantiate `apply_pap_eq_ref(g, s)` at `g`'s own raw
            // literal captures, then the `s` supplied args' own *denoted*
            // values in the *same* (unreversed) order `pap_at_denoted`
            // above already used (matching the axiom's own LHS/RHS
            // convention for this group -- see its own docs for why it
            // isn't reversed the way `more` is), then the `k` extra args'
            // own *denoted* values (reversed, matching
            // `eval_and_prove_direct_call`'s own `axiom_args` convention).
            // Universally quantified over `Int`-typed values, same as
            // `apply_clo_eq_ref`'s own axiom, so no "route through
            // literals first" step is needed for either group.
            let apply_axiom_args: Vec<Expr> = g_cap_triples
                .iter()
                .map(|&(x, _, _)| combinators.cp.arith.lit_ref(x))
                .chain(supplied_triples.iter().map(|(_, d, _)| d.clone()))
                .chain(extra_arg_triples.iter().rev().map(|(_, d, _)| d.clone()))
                .collect();
            let apply_eq_chosen = apply_n(apply_axiom.clone(), apply_axiom_args);

            let mut chosen_arg_triples = supplied_triples;
            chosen_arg_triples.extend(extra_arg_triples.iter().cloned());

            Some((g, g_cap_triples, chosen_arg_triples, pap_at_denoted, root_to_chosen, apply_eq_chosen))
        }
        ClosureRhsShape::Call { g, args } => {
            // Evaluate `g`'s own args using *this* level's own inner
            // frame (they live in `subject`'s own body, exactly where
            // `cond`/`args` live for the other two shapes above), then
            // build `g`'s own bridge the same way `eval_and_prove_call_over`
            // itself builds `subject`'s -- `g`'s own captures, in turn,
            // resolve against *this* level's own inner frame too (`g`
            // sits within `subject`'s own body, at `subject`'s own scope
            // depth).
            let mut g_arg_triples = Vec::with_capacity(args.len());
            for &a in args {
                let (x, d, p) = eval_and_prove(store, a, combinators, inner_params, inner_concrete, inner_facts)?;
                g_arg_triples.push((x, d, p));
            }
            let (g_call_at_denoted, g_call_at_lit_env_lit_args, g_bridge, g_axiom_at_literals, g_inner_params, g_inner_concrete, g_inner_facts, g_k, g_shape) =
                build_clo_call_bridge(store, combinators, *g, &g_arg_triples, inner_params, inner_concrete, inner_facts)?;
            if g_k != k {
                return None; // should be unreachable given clo_eq_ref_call's own validation, but stay defensive
            }

            // `axiom_at_literals`'s own RHS (built via plain `denote`
            // against `subject`'s own literal inner frame, in
            // `clo_eq_ref_call`'s own axiom construction) is exactly
            // `g_call_at_denoted` (built via `eval_and_prove`'s own `d`
            // against the very same frame) -- both recursively rebuild
            // the same term skeleton (`Var`->frame entry, `Lit`->`lit_ref`,
            // `Prim`->`app2`, `If`->`app3`) from the same source
            // expressions and the same concrete values, so they always
            // agree syntactically (the same reliance `clo_eq_ref_pap`'s
            // own `pap_at_denoted` construction above already makes).
            let call_at_denoted_here = call_at_denoted.clone();
            let call_at_lit_env_lit_args_here = call_at_lit_env_lit_args.clone();
            let bridge_here = bridge.clone();
            let axiom_at_literals_here = axiom_at_literals.clone();
            let clo_ty = combinators.cp.clo_ty(k);
            let root_to_g = kernel::trans_proof(&clo_ty, &call_at_denoted_here, &call_at_lit_env_lit_args_here, &g_call_at_denoted, bridge_here, axiom_at_literals_here);

            let (chosen, chosen_cap_triples, chosen_arg_triples, chosen_value, g_to_chosen, apply_eq_chosen) = resolve_closure_shape_to_leaf(
                store,
                combinators,
                &g_call_at_denoted.clone(),
                &g_call_at_lit_env_lit_args,
                &g_bridge,
                &g_axiom_at_literals,
                &g_shape,
                &g_inner_params,
                &g_inner_concrete,
                &g_inner_facts,
                k,
                extra_arg_triples,
            )?;

            let clo_ty = combinators.cp.clo_ty(k);
            let root_to_chosen = kernel::trans_proof(&clo_ty, call_at_denoted, &g_call_at_denoted, &chosen_value, root_to_g, g_to_chosen);
            debug_assert_has_type(
                &combinators.cp.arith.p,
                &root_to_chosen,
                &kernel::id(clo_ty, call_at_denoted.clone(), chosen_value.clone()),
                "resolve_closure_shape_to_leaf: Call arm's own root_to_chosen",
            );

            Some((chosen, chosen_cap_triples, chosen_arg_triples, chosen_value, root_to_chosen, apply_eq_chosen))
        }
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn eval_and_prove_call_over(
    store: &TermStore,
    root: Hash,
    args: &[Hash],
    callee_param_types: &[Option<usize>],
    combinators: &mut ClosureCombinators<'_>,
    params: &[Expr],
    concrete: &[i64],
    param_facts: &[Expr],
) -> Option<(i64, Expr, Expr)> {
    if callee_param_types.iter().any(Option::is_some) {
        return None;
    }
    let (root_arity, _root_body, _root_is_rec) = compile::peel(store, root)?;
    let k_check = match combinator_return_type(store, root) {
        Some(Some(k)) => k,
        _ => return None,
    };
    if args.len() != root_arity + k_check {
        return None;
    }

    // Evaluate every argument (both `root`'s own saturating ones and the
    // `k` extra ones) in the *outer* frame, application order -- same
    // resolution `eval_and_prove_call` already does, split after.
    let mut arg_triples = Vec::with_capacity(args.len());
    for &a in args {
        let (x, d, p) = eval_and_prove(store, a, combinators, params, concrete, param_facts)?;
        arg_triples.push((x, d, p));
    }
    let (sat_arg_triples, extra_arg_triples) = arg_triples.split_at(root_arity);

    let (call_at_denoted, call_at_lit_env_lit_args, bridge, axiom_at_literals, inner_params, inner_concrete, inner_facts, k, shape) =
        build_clo_call_bridge(store, combinators, root, sat_arg_triples, params, concrete, param_facts)?;
    debug_assert_eq!(k, k_check, "eval_and_prove_call_over: build_clo_call_bridge's own k must match combinator_return_type(root)");

    // `resolve_closure_shape_to_leaf` below may lazily push further
    // postulates (its own recursion into a `Call`'s own `g`, reaching
    // `apply_clo_eq_ref`/`apply_pap_eq_ref`, ...); `call_at_denoted` is
    // still needed afterward (below), the other three are only consumed
    // (cloned) inside that call.

    // Resolve which concrete closure applies (`IfTree`: evaluating
    // `cond` within `root`'s own inner frame; `Pap`: there's only ever
    // one; `Call`: recursively, through however many further indirect
    // calls this reaches -- see `resolve_closure_shape_to_leaf`'s own
    // docs), and bridge `root`'s own saturated call (denoted) all the way
    // to that closure's own value expression (`root_to_chosen`) -- plus
    // everything the shared tail below needs to finish the call: which
    // `Hash` to recurse into (`chosen`), its own captures resolved to
    // literal triples (`chosen_cap_triples`), the full argument list for
    // that recursive call (`chosen_arg_triples`), and the instantiated
    // `apply_*_eq_ref` fact bridging `chosen_value` called directly down
    // to a direct call on `chosen`.
    let (chosen, chosen_cap_triples, chosen_arg_triples, chosen_value, root_to_chosen, apply_eq_chosen) = resolve_closure_shape_to_leaf(
        store,
        combinators,
        &call_at_denoted,
        &call_at_lit_env_lit_args,
        &bridge,
        &axiom_at_literals,
        &shape,
        &inner_params,
        &inner_concrete,
        &inner_facts,
        k,
        extra_arg_triples,
    )?;

    let int_ty2 = combinators.cp.arith.int_ty();
    let clo_ty = combinators.cp.clo_ty(k);

    // The outer frame's own *denoted* value for each extra argument,
    // application order -- possibly a complex expression, not necessarily
    // already-literal (unlike `chosen`'s own captures just resolved above,
    // which came from `root`'s own *literal* inner frame). Unlike
    // `call_ref(root)`'s own bridge above (needed so `axiom_at_literals`,
    // itself only ever stated in terms of literals, could apply at all),
    // `apply_clo_eq_ref`'s/`apply_pap_eq_ref`'s own axiom is universally
    // quantified over `Int`-typed values, so it can be instantiated
    // directly at these denoted expressions -- no separate "route through
    // literals first" step is needed at all.
    let d_extra_args: Vec<Expr> = extra_arg_triples.iter().map(|(_, d, _)| d.clone()).collect();

    // `cong1` over a `Clo_k`-typed value's own use as the callee, the `k`
    // extra args held fixed at their denoted values, using
    // `root_to_chosen` to turn `call_at_denoted` into `chosen_value` --
    // called directly (`c(args)`, no `apply_ref` axiom to route through,
    // see `RELATED_WORK.md` section 11).
    let mut f_clo_body = kernel::var(0);
    for d in &d_extra_args {
        f_clo_body = kernel::app(f_clo_body, kernel::shift(d, 0, 1));
    }
    let f_clo = kernel::lam(clo_ty.clone(), f_clo_body);
    let clo_step = kernel::cong1(&clo_ty, &int_ty2, &f_clo, call_at_denoted.clone(), chosen_value.clone(), root_to_chosen);
    let apply_at_denoted = apply_n(call_at_denoted, d_extra_args.iter().cloned());
    let apply_at_chosen_denoted_args = apply_n(chosen_value, d_extra_args.iter().cloned());

    // `eval_and_prove_direct_call`'s own recursion below (into `chosen`'s
    // own body) may push further postulates.
    let (result, call_at_denoted_for_chosen, proof_for_chosen) =
        eval_and_prove_direct_call(store, chosen, combinators, &chosen_cap_triples, &chosen_arg_triples)?;

    // Chain: apply_at_denoted = apply_at_chosen_denoted_args (clo_step)
    //      = call_at_denoted_for_chosen (apply_eq_chosen -- its own RHS,
    //        `call_ref(chosen)` applied to `chosen`'s own literal captures
    //        and the *same* `d_extra_args`, is exactly what
    //        `eval_and_prove_direct_call` itself builds as
    //        `call_at_denoted_for_chosen` when given those same triples)
    //      = lit_ref(result) (proof_for_chosen)
    let int_ty3 = combinators.cp.arith.int_ty();
    let result_ref = combinators.cp.arith.lit_ref(result);
    let bridge_to_call = kernel::trans_proof(
        &int_ty3,
        &apply_at_denoted,
        &apply_at_chosen_denoted_args,
        &call_at_denoted_for_chosen,
        clo_step,
        apply_eq_chosen,
    );
    let final_proof = kernel::trans_proof(&int_ty3, &apply_at_denoted, &call_at_denoted_for_chosen, &result_ref, bridge_to_call, proof_for_chosen);
    debug_assert_has_type(
        &combinators.cp.arith.p,
        &final_proof,
        &kernel::id(int_ty3, apply_at_denoted.clone(), result_ref),
        "eval_and_prove_call_over: final proof",
    );
    Some((result, apply_at_denoted, final_proof))
}

/// See the section docs above for what this guards against.
pub(super) const WITNESS_NODE_BUDGET: usize = 256;

/// The leaf `concrete`'s trace reaches: the one whose every condition
/// evaluates to its recorded outcome.
pub(super) fn trace_leaf(store: &TermStore, leaves: &[Leaf], concrete: &[i64]) -> Option<usize> {
    leaves.iter().position(|leaf| leaf.path.iter().all(|&(cond, lit)| eval_concrete(store, cond, concrete) == Some(lit)))
}

/// Canonical params for one call: literals, trivially equal to themselves
/// -- see the section docs above for why this (not a caller-supplied
/// denoted expression) is what makes `build_ev_witness`'s `memo` sound.
pub(super) fn canonical_params(combinators: &ClosureCombinators<'_>, concrete: &[i64]) -> (Vec<Expr>, Vec<Expr>) {
    let arith = &combinators.cp.arith;
    let params: Vec<Expr> = concrete.iter().map(|&c| arith.lit_ref(c)).collect();
    let param_facts = params.iter().map(|p| kernel::refl(p.clone())).collect();
    (params, param_facts)
}

/// Builds an actual `e : Ev(params, v)` witness for one specific call,
/// following the real trace `concrete` determines (mirroring
/// `classify_step`, but for any leaf `flatten_tree` found, not just a tail
/// loop) and recursing into every self-call occurrence found along the way.
/// Returns `(v, e)`; a caller may hold either across further postulate
/// pushes (as every caller here does) with no extra care, since a pushed
/// postulate is a `Const` and shifts nothing (`RELATED_WORK.md` §69).
/// `params`/`param_facts` are
/// never taken as input (see the section docs above): this function always
/// works in terms of the canonical literal params for `concrete`, which is
/// what makes `memo` (keyed on `concrete` alone) sound. `budget` bounds the
/// number of newly-*derived* calls; a `memo` hit doesn't touch it.
#[allow(clippy::too_many_arguments)]
pub(super) fn build_ev_witness(
    store: &TermStore,
    combinators: &mut ClosureCombinators<'_>,
    self_call: SelfCall,
    leaves: &[Leaf],
    ev_leaf_positions: &[usize],
    combines: &[Expr],
    ev_pos: usize,
    concrete: &[i64],
    budget: &mut usize,
    memo: &mut HashMap<Vec<i64>, (Expr, Expr)>,
) -> Option<(Expr, Expr)> {
    if let Some((v, e)) = memo.get(concrete) {
        return Some((v.clone(), e.clone()));
    }
    *budget = budget.checked_sub(1)?;

    let leaf_idx = trace_leaf(store, leaves, concrete)?;
    let leaf = &leaves[leaf_idx];
    let (params, param_facts) = canonical_params(combinators, concrete);

    let mut premises = Vec::with_capacity(leaf.path.len());
    for &(cond, _lit) in &leaf.path {
        let (_, _, proof) = eval_and_prove(store, cond, combinators, &params, concrete, &param_facts)?;
        premises.push(proof);
    }

    let mut vs = Vec::with_capacity(leaf.calls.len());
    let mut es = Vec::with_capacity(leaf.calls.len());
    for call in &leaf.calls {
        let mut new_concrete = Vec::with_capacity(self_call.arity);
        let mut denoted_args = Vec::with_capacity(self_call.arity);
        let mut denoted_facts = Vec::with_capacity(self_call.arity);
        for i in 0..self_call.arity {
            let arg = call[self_call.arity - 1 - i];
            let (x, denoted, pf) = eval_and_prove(store, arg, combinators, &params, concrete, &param_facts)?;
            new_concrete.push(x);
            denoted_args.push(denoted);
            denoted_facts.push(pf);
        }

        // The recursive call's own witness, always in canonical
        // (literal-params) form -- valid regardless of whether this came
        // from a fresh derivation or a `memo` hit.
        let (v, e_canonical) = build_ev_witness(
            store,
            combinators,
            self_call,
            leaves,
            ev_leaf_positions,
            combines,
            ev_pos,
            &new_concrete,
            budget,
            memo,
        )?;

        // Recast `e_canonical : Ev(lit_params, v)` to `Ev(denoted_params,
        // v)` -- what *this* leaf's own `Ev` constructor actually expects
        // for its e_i (its type was built from the call's real argument
        // expressions, not just their values) -- via congruence over the
        // params (`cong_n`, `Ev` held fixed at `v`) and transport along the
        // resulting type equality.
        let int_ty = combinators.cp.arith.int_ty();
        let lit_params: Vec<Expr> = new_concrete.iter().map(|&x| combinators.cp.arith.lit_ref(x)).collect();
        let ps: Vec<Expr> = denoted_facts
            .iter()
            .zip(&denoted_args)
            .zip(&lit_params)
            .map(|((pf, dp), lp)| kernel::sym(&int_ty, dp, lp, pf.clone()))
            .collect();
        let v_resolved = v.clone();
        let f = params_and_close(&mut combinators.cp.arith, self_call.arity, kernel::Binder::Lam, |arith, pp| {
            Some(ev_of(arith, ev_pos, pp, v_resolved.clone()))
        })?;
        let ev_eq = kernel::cong_n(&int_ty, &kernel::sort(0), &f, &lit_params, &denoted_args, ps);
        let e = kernel::transport(
            0,
            ev_of(&combinators.cp.arith, ev_pos, &lit_params, v_resolved.clone()),
            ev_of(&combinators.cp.arith, ev_pos, &denoted_args, v_resolved),
            ev_eq,
            e_canonical.clone(),
        );
        vs.push(v);
        es.push(e);
    }

    let args = params.iter().cloned().chain(premises).chain(vs.iter().cloned()).chain(es);
    let e = apply_n(combinators.cp.arith.p.get(ev_leaf_positions[leaf_idx]), args);
    let v = combine_of(&combines[leaf_idx], &params, &vs);
    let int_ty_check = combinators.cp.arith.int_ty();
    debug_assert_has_type(&combinators.cp.arith.p, &v, &int_ty_check, "build_ev_witness: v");
    let ev_check = ev_of(&combinators.cp.arith, ev_pos, &params, v.clone());
    debug_assert_has_type(&combinators.cp.arith.p, &e, &ev_check, "build_ev_witness: e");
    memo.insert(concrete.to_vec(), (v.clone(), e.clone()));
    Some((v, e))
}

/// A kernel-checked witness, concrete to one call `h(args)`, that the
/// universal theorem's `loop_val` reconstruction and the value the
/// recursion actually produces agree -- see `prove_tail_recursive_instance`.
pub struct UniversalInstanceProof {
    pub globals: Globals,
    pub arity: usize,
    pub int_ty: Expr,
    pub lhs: Expr,
    pub rhs: Expr,
    /// `: Id(int_ty, lhs, rhs)`.
    pub proof: Expr,
}

/// Instantiates `prove_tail_recursive_universal`'s reusable theorem at one
/// specific call `h(args)`: builds a concrete `Ev`-witness for it
/// (`build_ev_witness`) and applies the (already-proved) theorem to that
/// witness, giving a genuine kernel-checked fact about *this* call rather
/// than only the theorem's abstract shape -- the payoff `prove_tail_recursive_universal`'s
/// own docs describe as still missing. Building the witness reuses the
/// one-time theorem instead of `prove_tail_recursive_call`'s from-scratch
/// `cong1`/`trans_proof` chaining, so it's cheap per call once the theorem
/// exists.
///
/// Returns `None` for anything `prove_tail_recursive_universal` itself
/// would, an arity mismatch, a call whose trace reaches a leaf with more
/// than one self-call, or a witness that would exceed
/// [`WITNESS_NODE_BUDGET`] (see the section docs above for both).
///
/// Builds its own scaffold from scratch (`build_universal`, the expensive
/// part -- see [`UniversalScaffold`]'s docs). A caller that wants several
/// instances for the same `h` (`jit.rs`'s `kernel_verify`, trying a handful
/// of samples) should use [`prove_tail_recursive_universal_with_instances`]
/// instead, which pays that cost once and clones the scaffold per attempt.
pub fn prove_tail_recursive_instance(store: &TermStore, h: Hash, args: &[i64]) -> Option<UniversalInstanceProof> {
    let scaffold = build_universal(store, h)?;
    instance_from_scaffold(store, scaffold, args)
}

/// Builds the universal theorem once and, from a clone of the same
/// scaffold, attempts a concrete instance (`prove_tail_recursive_instance`)
/// for each of `args_list` -- see [`UniversalScaffold`]'s docs for why
/// cloning beats rebuilding. Each entry of the returned `Vec` is `None`
/// exactly where a standalone `prove_tail_recursive_instance` call would
/// have been. Returns `None` outright for anything
/// `prove_tail_recursive_universal` itself would.
pub fn prove_tail_recursive_universal_with_instances(
    store: &TermStore,
    h: Hash,
    args_list: &[Vec<i64>],
) -> Option<(UniversalTailProof, Vec<Option<UniversalInstanceProof>>)> {
    let scaffold = build_universal(store, h)?;
    let theorem = UniversalTailProof {
        globals: scaffold.combinators.cp.arith.p.globals.clone(),
        arity: scaffold.arity,
        theorem_ty: scaffold.theorem_ty.clone(),
        theorem_proof: scaffold.theorem_proof.clone(),
    };
    let instances = args_list
        .iter()
        .map(|args| instance_from_scaffold(store, scaffold.clone(), args))
        .collect();
    Some((theorem, instances))
}

pub(super) fn instance_from_scaffold(store: &TermStore, mut scaffold: UniversalScaffold<'_>, args: &[i64]) -> Option<UniversalInstanceProof> {
    if args.len() != scaffold.arity {
        return None;
    }
    // A concrete instance needs a concrete `i64` per parameter -- there's no
    // way to represent a `Clo` value in that model (see `eval_and_prove`'s
    // own docs, which reject `App`/`Abs` outright for the same reason), so
    // any `Clo`-typed parameter takes this out of scope. The universal
    // theorem itself is unaffected (`kernel_verified` doesn't depend on an
    // instance also succeeding -- see `jit.rs`'s own docs); only this
    // per-call specialization declines.
    if scaffold.param_types.iter().any(Option::is_some) {
        return None;
    }

    let concrete: Vec<i64> = (0..scaffold.arity).map(|i| args[scaffold.arity - 1 - i]).collect();
    for &c in &concrete {
        scaffold.combinators.lit(c);
    }

    let mut budget = WITNESS_NODE_BUDGET;
    let mut memo = HashMap::new();
    let (v, e) = build_ev_witness(
        store,
        &mut scaffold.combinators,
        scaffold.self_call,
        &scaffold.leaves,
        &scaffold.ev_leaf_positions,
        &scaffold.combines,
        scaffold.ev_pos,
        &concrete,
        &mut budget,
        &mut memo,
    )?;

    let params: Vec<Expr> = concrete.iter().map(|&c| scaffold.combinators.lit_ref(c)).collect();
    let applied = apply_n(scaffold.theorem_proof.clone(), params.into_iter().chain([v, e]));
    let ty = scaffold.combinators.cp.arith.p.infer(&applied).ok()?;
    let (lhs, rhs) = match kernel::whnf(&ty) {
        Expr::Id(_, ref lhs, ref rhs) => ((**lhs).clone(), (**rhs).clone()),
        _ => return None,
    };

    Some(UniversalInstanceProof {
        int_ty: scaffold.combinators.int_ty(),
        globals: scaffold.combinators.cp.arith.p.globals,
        arity: scaffold.arity,
        lhs,
        rhs,
        proof: applied,
    })
}
