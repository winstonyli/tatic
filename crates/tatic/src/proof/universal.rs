use super::*;

// --- a universal proof for recursion, tail or not, via genuine induction -

// See the module docs above for the concept (`Ev`, gating, `combine`,
// `cong_n`); this is the implementation-level map from that to the code
// below.
//
// `classify_tree` turns `body` into a [`DecisionTree`] (an arbitrary
// nested-`If` shape, `build_node` already accepts it fine); a single
// top-level `If` (the historically-first, narrower shape this covered) is
// just the case where the tree has depth one. `flatten_tree` reduces that
// to a flat `Vec<Leaf>`, each carrying its root-to-leaf path of
// `(cond, literal)` premises and its self-call occurrences (via
// `find_self_calls`, `Vec<Vec<Hash>>` -- one argument list per occurrence,
// left-to-right/depth-first).
//
// Per leaf `i`, with `k_i` self-calls: `combine_i` (built once, reused at
// several deeper points) is leaf `i`'s own expression with each
// self-call occurrence replaced by one of `k_i` placeholders
// (placeholder-mode `denote_closure`); `ev_leaf_i` is `Ev`'s constructor for this
// leaf (`push_path` for the path premises, then `v_1..v_{k_i}` and
// `e_1:Ev(new_params_1,v_1)..e_{k_i}:..` for each self-call, concluding
// `Ev(params, combine_i(params,vs))`); `leaf_case_ty_i` is `ev_rec`'s
// corresponding case-handler type (same shape, plus `k_i` induction-
// hypothesis premises `P(new_params_j,v_j,e_j)`, one per self-call, ahead
// of the conclusion). `ev_rec`'s own type folds `leaf_case_ty_i` for every
// leaf, in order, into one case-handler argument each.
//
// `loop_val` is then *defined* via `ev_rec` (motive: constant `Int`) --
// not postulated -- with leaf `i`'s handler applying `combine_i` to
// whatever its `k_i` induction hypotheses (`ih`s) actually turned out to
// be: `k_i == 0` reduces to returning the base value directly, `k_i == 1`
// with the self-call as the whole leaf reduces to passing the one `ih`
// through unchanged (the old tail-recursion shape), anything else
// genuinely recombines them. Since a postulated eliminator has no built-in
// reduction rule the way `WRec` does, `loop_val`'s computation rule for
// *this specific* `loop_val` is postulated directly as a propositional
// (`Id`-typed) axiom per leaf (`loop_val_leaf_eq_i`) -- not a fully
// generic "for any motive" schema, since `loop_val` is the only thing that
// needs it.
//
// The theorem -- `Pi params v (e : Ev(params,v)). Id(Int, loop_val(params,v,e), v)`
// -- says the witness's own claimed value is always what `loop_val`
// reconstructs from it, and is proved by one more use of `ev_rec` (motive:
// the theorem statement itself). Leaf `i`'s case combines its `k_i`
// induction hypotheses (`ih_j : loop_val(new_params_j,v_j,e_j) = v_j`)
// into `combine_i([loop_val(..)]) = combine_i(vs)` via `kernel::cong_n`
// (substituting each recursively-computed value for its claimed one, one
// argument position at a time), then chains that with `loop_val_leaf_eq_i`
// (relates `loop_val` at this leaf to `combine_i([loop_val(..)])`) via
// `kernel::trans_proof` to reach the goal.
//
// Scope: every `If` on the way to any leaf must have a direct comparison
// as its condition (`build_node`'s `If` arm in `compile.rs` requires that too; also
// what lets the gating above use plain equality, since a comparison only
// ever denotes to `0` or `1`); `body` must have at least one leaf with a
// self-call in it somewhere. A leaf's own expression *may* contain a
// further nested `If`, purely arithmetic or choosing between two
// `Clo`-typed values (`find_self_calls`/placeholder-mode `denote_closure` both
// recurse into one, embedding it opaquely via `ite_ref`/`ite_clo_ref`,
// same as `denote_closure` always has). `prove_closure_expr_instance`
// already handles arbitrary branching
// *and* arbitrary self-call placement on its own (it just follows one
// concrete path through the tree per call, denoting whatever it finds
// along the way), so neither of those needed widening.
//
// `prove_tail_recursive_universal` also covers a *closure-typed parameter*, threaded
// through the recursion unchanged or called via ordinary `App` (`Clo_k`,
// see `ClosurePostulates::clo_ty`, is a literal `Int -> .. -> Int` kernel
// Pi type, not an opaque postulate, so calling one needs no axiom at all)
// within a leaf or a self-call argument (`param_types`, the same
// `Var`-index-keyed classification `denote_closure`'s own fragment uses,
// computed once via `shape::infer_closure_arities` on the whole body
// including self-call sites) -- e.g. "iterate a closure `n` times": `rec f
// n g x = if n<=0 then x else f(n-1, g, g(x))`. This part needs only
// `ClosurePostulates::clo_ty`, reused directly (`ClosurePostulates:
// Deref<Target = ArithPostulates>` lets this whole pipeline keep calling
// every plain-arithmetic postulate method unchanged). A closure-typed
// self-call argument, or one fed to a closure call, may also be a freshly
// *created* closure (`denote_closure` handles `Term::Abs`/`Term::Rec` via
// `ClosureCombinators` in every self-call mode), not just a bare parameter
// reference, and an `If` choosing between two `Clo`-typed values is in scope
// too (`ite_clo_ref`) -- see `prove_tail_recursive_universal`'s own doc comment below
// for the one thing still out of scope here (a captured free variable).
// `params_and_close_typed`'s scope locals are `Free`s (`docs/related-work/`
// §70), never pushed onto `globals`; a lazily-memoized postulate
// (`ClosureCombinators::register`/`call_ref`/`pap_ref`,
// `ClosurePostulates::mk_env_ref`/`env_ty`/`ite_clo_ref`) may be pushed from
// inside one.
//
// A self-call *argument* may also genuinely *create* a closure and (fully
// or partially) call it right there, e.g. `f(n-1, (\y. acc+y)(n))` --
// exactly the shape `compile.rs`'s own
// `self_recursion_creating_a_fresh_capturing_closure_every_iteration_compiles`
// test and `capturing_closure_loop` benchmark already exercise, previously
// compiled but never proven. `denote_closure` (in `SelfCalls::Reject` mode,
// the self-call-argument denotation `new_params_for` uses) handles them as it
// does for `prove_closure_expr`, now that `arith` is a full
// `ClosureCombinators` (not just `ClosurePostulates`) -- registering a
// combinator, calling one directly, or partially applying one (still never
// a *recursive* root, per `pap_ref`'s own restriction) all reuse the exact
// same methods `prove_closure_expr` does. A leaf's own *top-level*
// expression gets the identical treatment: `denote_closure` in
// `SelfCalls::Placeholders` mode (what `combine_i`'s body uses) and
// `find_self_calls` (which recurses into a closure call's own arguments, or
// treats a bare closure value as opaque, the same way `collect_literals`
// already does) -- e.g. `(\y. n+y)(5) + f(n-1)`, a
// closure-call's result combined arithmetically with the recursive call
// directly, not nested inside any self-call's own argument list.
// `register`/`call_ref`/`pap_ref`, and transitively `mk_env_ref`/`env_ty`
// for a capturing one, are all lazily memoized; `denote_closure`'s first
// real call in either mode (from inside a temporary scope) may trigger any of them for the first time. (The concrete-witness instance prover that once
// rejected `App`/`Abs` here, `prove_tail_recursive_instance`, was deleted
// 2026-10-26, "CU3"; `prove_closure_expr_instance` follows the trace instead.)

/// `Ev(params, v) : Sort(0)` -- `ev_pos`'s postulate (see `prove_tail_recursive_universal`)
/// applied to `params` then `v`, via `arith.p.get`. A free function (not
/// just `prove_tail_recursive_universal`'s own local closure) so the helpers
/// below can build the same `Ev(...)` application.
pub(super) fn ev_of(arith: &ArithPostulates, ev_pos: usize, params: &[Expr], v: Expr) -> Expr {
    apply_n(arith.p.get(ev_pos), params.iter().cloned().chain([v]))
}

/// `combine`'s value at `params`/`ihs`.
pub(super) fn combine_of(combine: &Expr, params: &[Expr], ihs: &[Expr]) -> Expr {
    apply_n(*combine, params.iter().cloned().chain(ihs.iter().cloned()))
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
/// `denote_closure` the same way a `Prim` is.
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
        if !matches!(store.resolve(c), Term::Prim(op, _, _) if shape::is_comparison(*op)) {
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
/// `denote_closure` walks the same expression -- the two must
/// agree, since a leaf's `i`-th `Ev`/induction-hypothesis premise and its
/// `i`-th occurrence in the rebuilt expression have to be the same call.
#[derive(Clone)]
pub(super) struct Leaf {
    pub(super) path: Vec<(Hash, i64)>,
    pub(super) expr: Hash,
    pub(super) calls: Vec<Vec<Hash>>,
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
/// `denote_closure` will later substitute them in. A fully-
/// saturated call through a `Clo`-typed parameter (`Var(i)` with
/// `param_types[i] = Some(k)`, `k` arguments -- `param_types[i] = None`
/// throughout for a term with no closures at all, the same
/// closures-blind behavior as before) is recursed into (its own arguments
/// may still contain further self-call occurrences), not rejected outright.
/// A nested `If`'s condition/branches are recursed into the same way (a
/// self-call may occur in any of them), whether it stays purely
/// arithmetic or chooses between two `Clo`-typed values (e.g. a self-call
/// argument `f(n-1, if c then g else h)`) -- which of those it is doesn't
/// matter here (only to `denote_closure`'s own type-directed
/// dispatch), since finding a self-call occurrence never depends on the
/// type of the expression it's found in.
pub(super) fn find_self_calls(store: &TermStore, h: Hash, self_call: SelfCall, param_types: &[Option<usize>], out: &mut Vec<Vec<Hash>>) -> bool {
    let all = |hs: &[Hash], out: &mut Vec<Vec<Hash>>| hs.iter().all(|&a| find_self_calls(store, a, self_call, param_types, out));
    match shape::classify(store, h, self_call.arity, Some(self_call.idx)) {
        Shape::SelfCall(args) => {
            out.push(args);
            true
        }
        Shape::VarCall { var, args, .. } => param_types.get(var as usize).copied().flatten() == Some(args.len()) && all(&args, out),
        // A closure created and (fully or partially) called right here --
        // see `denote_closure`'s own docs. Recurses into the
        // arguments only, never into the combinator's own body: a genuine
        // self-call occurring *inside* a nested closure's body would need
        // `self_call.idx` shifted by that closure's own arity to still
        // refer to the same absolute position, which
        // `shape::match_self_call`'s unadjusted check can't see -- the
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
        // `denote_closure`'s matching arm): recurse into all
        // three the same way `Prim` does, so a self-call inside either
        // branch is still found, in the same left-to-right, depth-first
        // order `denote_closure` will later walk.
        Shape::If(c, t, e) => all(&[c, t, e], out),
    }
}

/// Binds one fresh parameter per entry of `param_types` in a new scope, typed
/// `Clo_k` or `Int` to match, lets `build` bind more of its own and construct
/// a body term, then closes *everything* bound since entry (the params plus
/// anything `build` itself bound, e.g. `v` or `e`) into nested binders around
/// that body, rolling them back afterward. Pass `kernel::Binder::Pi` to build
/// a *type* (quantifying over these params) or `kernel::Binder::Lam` to build
/// a *value* of that type (e.g. a motive or a proof to pass as an argument) --
/// getting this wrong is a real, easy-to-make mistake (a `Pi` where a `Lam`
/// was needed), not a hypothetical one.
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
/// compiled code's own recursive structure (`loop_val`, the recursor over the witness; it models the recursion, not the emitted text) reconstructs from
/// that witness -- covers tail recursion and general (non-tail) recursion
/// alike (see module docs).
pub struct UniversalTailProof {
    pub globals: Globals,
    pub arity: usize,
    /// `: Pi p_0..p_{arity-1} v (e : Ev(p_0,..,v)). Id(Int, loop_val(..,e), v)`.
    pub theorem_ty: Expr,
    pub theorem_proof: Expr,
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
    let (arity, body, is_rec) = shape::peel(store, h)?;
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
    // `denote_closure` (used by `new_params_for` below) also covers
    // closure *creation* inside a self-call argument -- registering a
    // combinator, calling one directly, or partially applying one -- and a
    // nested `If` choosing between two `Clo`-typed values, both via the
    // same `ClosureCombinators` machinery `prove_closure_expr` itself uses.
    // Still out of scope: a captured free variable used as a closure here
    // (this function has no enclosing frame to resolve one against).
    let found = shape::infer_closure_arities(store, body, arity, Some(self_idx))?;
    // See `param_types_for`'s own docs: an inconsistently-called `Var` is
    // declined the same way an absent one already is.
    let param_types: Vec<Option<usize>> = (0..arity as u32)
        .map(|i| match found.get(&i) {
            Some(shape::ArityUse::Consistent(k)) => Some(*k),
            Some(shape::ArityUse::Inconsistent) | None => None,
        })
        .collect();

    let tree = classify_tree(store, body)?;
    let leaves = flatten_tree(store, &tree, self_call, &param_types)?;
    if leaves.iter().all(|l| l.calls.is_empty()) {
        return None; // no recursion anywhere: not this function's job (see `prove_closure_expr`)
    }

    let mut lits = Vec::new();
    if !collect_literals(store, body, &LitScope::Closure { arity, self_idx: Some(self_idx), param_types: &param_types }, &mut lits) {
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
    // `prove_closure_expr_instance`'s convention exactly) -- closure-aware
    // via `denote_closure` (a loop-carried `Clo`-typed argument, or a
    // plain `Int` one possibly computed by calling one), each checked
    // against `param_types[i]`, the *target* slot's own type.
    let new_params_for = |arith: &mut ClosureCombinators<'_>, call_args: &[Hash], params: &[Expr]| -> Option<Vec<Expr>> {
        (0..arity)
            .map(|i| {
                let d = denote_closure(call_args[arity - 1 - i], &mut SelfCalls::Reject(self_call), &param_types, arith, params)?;
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
            ty = kernel::arrow(*dom, ty);
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
            let ev_np = ev_of(arith, &np, *v);
            es.push(arith.p.bind(ev_np));
        }
        Some((vs, es))
    };

    // combine_i : Pi params. Pi ih_1:Int .. ih_{k_i}:Int. Int -- leaf i's
    // own arithmetic expression with each self-call occurrence replaced
    // by the corresponding `ih_j` (`SelfCalls::Placeholders`), closed
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
                denote_closure(leaf.expr, &mut SelfCalls::Placeholders(self_call, pp2, 0), &param_types, arith, pp)?.int()
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
        apply_n(p_ref, params.iter().cloned().chain([v, e]))
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
                ih_tys.push(p_of(arith, &np, *v, *e));
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
        // out of `prove_tail_recursive_universal`, leaving `p_scope` (and `P`) open.
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
        let ev_pv = ev_of(arith, pp, v);
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

    let ev_rec_ty_body = leaf_case_tys.iter().rev().fold(concl_ty, |acc, ty| kernel::arrow(*ty, acc));
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
        ev_rec_ref(arith, const_int_motive, &loop_leaves, params, v, e)
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
                recursive_vals.push(loop_val(arith, &np, *v, *e));
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
        let ev_pv = ev_of(arith, pp, v);
        let e = arith.p.bind(ev_pv);
        Some(kernel::id(arith.int_ty(), loop_val(arith, pp, v, e), v))
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
                let ih_ty = kernel::id(arith.int_ty(), loop_val(arith, &np, *v, *e), *v);
                ihs.push(arith.p.bind(ih_ty));
            }

            let mut recursive_vals = Vec::with_capacity(leaf.calls.len());
            for ((call, v), e) in leaf.calls.iter().zip(&vs).zip(&es) {
                let np = new_params_for(arith, call, pp)?;
                recursive_vals.push(loop_val(arith, &np, *v, *e));
            }

            let eb = apply_n(
                arith.p.get(ev_leaf_pos),
                pp.iter().cloned().chain(premises.iter().cloned()).chain(vs.iter().cloned()).chain(es.iter().cloned()),
            );
            let step_eq = apply_n(
                arith.p.get(loop_val_leaf_eq_pos),
                pp.iter().cloned().chain(premises).chain(vs.iter().cloned()).chain(es),
            );
            let f_partial = apply_n(*combine, pp.iter().cloned());
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
        let ev_pv = ev_of(arith, pp, v);
        let e = arith.p.bind(ev_pv);
        Some(kernel::id(arith.int_ty(), loop_val(arith, pp, v, e), v))
    })?;

    let theorem_proof = params_and_close_typed(&mut arith, &param_types, kernel::Binder::Lam, |arith, pp| {
        let v = { let ty = arith.int_ty(); arith.p.bind(ty) };
        let ev_pv = ev_of(arith, pp, v);
        let e = arith.p.bind(ev_pv);
        Some(ev_rec_ref(arith, id_motive, &theorem_leaves, pp, v, e))
    })?;

    arith.p.check(&theorem_proof, &theorem_ty).ok()?;

    Some(UniversalTailProof { globals: arith.cp.arith.p.globals, arity, theorem_ty, theorem_proof })
}
